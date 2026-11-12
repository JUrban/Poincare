(* ========================================================================= *)
(* Unit pc_p2a_lgeo3: smooth dependence of L-geodesics on the initial vector *)
(* (clauses 4-6 of P2A_LGEOD_FLOW_STATEMENT), generic in N, and the          *)
(* statement L1 itself: P2A_LGEOD_FLOW_GEN for every N and P2A_LGEOD_FLOW at *)
(* N = 3.                                                                    *)
(*                                                                           *)
(* First: localization of derivatives within sets, uniqueness against chart  *)
(* solutions (P2A_LGEOD_CHART_UNIQUE), and gluing an L-geodesic with a chart *)
(* solution beyond its end (P2A_LGEOD_GLUE).                                 *)
(* ========================================================================= *)

needs "src/pc_p2a_lgeo2.ml";;
needs "src/pc_grg_vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* The e-ball form of ODE_HAS_VECTOR_DERIVATIVE_WITHIN_LOCAL (pc_ode_found). *)

let P2A_HVD_WITHIN_LOCAL = prove
 (`!(f:real^1->real^N) f' x s t e.
     &0 < e /\ x IN s /\ x IN t /\ (!y. dist(y,x) < e ==> (y IN s <=> y IN t))
     ==> ((f has_vector_derivative f') (at x within s) <=>
          (f has_vector_derivative f') (at x within t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_WITHIN_LOCAL THEN
  REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[]);;

let P2A_LGEOD_CHART_UNIQUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s0 W1 a1 b1 U1 (phi1:A->real^N) sa sb (Y1:real^1->real^N) A1 J1 r.
     p2a_Lgeod V tt gamma b /\ &0 < b /\ &0 <= s0 /\ s0 pow 2 <= b /\
     p2a_region V W1 a1 b1 /\ (U1,phi1) IN p2a_vatlas V b1 /\
     sa < s0 /\ s0 < sb /\
     (!s. sa < s /\ s < sb ==> a1 < tt - s pow 2 /\ tt - s pow 2 <= b1) /\
     ode_solution (p2a_lfield (p2a_rlocal V W1 b1 (U1 INTER W1,phi1)) tt)
       (interval(lift sa,lift sb) PCROSS (IMAGE phi1 (U1 INTER W1) PCROSS (:real^N))) J1
       (\u. pastecart (Y1 u) (A1 u)) /\
     &0 < r /\
     (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < r ==> u IN J1) /\
     gamma(s0 pow 2) IN U1 INTER W1 /\ Y1(lift s0) = phi1(gamma(s0 pow 2)) /\
     ((\v. phi1(gamma(drop v pow 2))) has_vector_derivative A1(lift s0))
       (at (lift s0) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < e
                 ==> phi1(gamma(s pow 2)) = Y1(lift s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`]
                P2A_LGEOD_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:A->bool` (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real`
    (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N` (X_CHOOSE_THEN `d2:real`
    (X_CHOOSE_THEN `A2:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `t0 = tt - s0 pow 2` THEN
  ABBREV_TAC `p = (gamma:real->A)(s0 pow 2)` THEN
  SUBGOAL_THEN `a1 < t0 /\ t0 <= b1 /\ a2 < t0 /\ t0 <= b2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN U2 INTER W2` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_MESON_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `t0:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) t0) (U1 INTER W1) /\
    open_in (p2a_vtop V t0) (U2 INTER W2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_OPEN_BACK THENL
     [MAP_EVERY EXISTS_TAC [`W1:A->bool`; `a1:real`; `b1:real`];
      MAP_EVERY EXISTS_TAC [`W2:A->bool`; `a2:real`; `b2:real`]] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b1`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b1`;
                     `(U1:A->bool,phi1:A->real^N)`] MFDM_CHART);
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b2`;
                     `(U2:A->bool,phi2:A->real^N)`] MFDM_CHART)] THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  ABBREV_TAC `O = (U1 INTER W1) INTER (U2 INTER W2):A->bool` THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) t0) (O:A->bool) /\ (p:A) IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`;
                 `O:A->bool`] P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (min d2 e2) (min r (min (s0 - sa) (sb - s0)))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= d2 /\ e <= e2 /\ e <= r /\ e <= s0 - sa /\ e <= sb - s0`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = chart_trans (U2 INTER W2:A->bool,phi2:A->real^N) (U1 INTER W1,phi1)` THEN
  SUBGOAL_THEN `!q:A. q IN U1 INTER W1 /\ q IN U2 INTER W2 ==> (h:real^N->real^N)(phi2 q) = phi1 q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans; SND] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                   `U2:A->bool`; `phi2:A->real^N`; `W2:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = {u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e}` THEN
  SUBGOAL_THEN `is_interval (J:real^1->bool) /\
                J SUBSET {v | &0 <= drop v /\ drop v pow 2 <= b} /\ lift s0 IN J /\
                J SUBSET J1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[P2A_SWIN_INTERVAL; SUBSET; IN_ELIM_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* gamma's piece moved to chart c1 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W1:A->bool`; `a1:real`; `b1:real`; `U1:A->bool`; `phi1:A->real^N`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`;
                 `t0:real`; `tt:real`; `gamma:real->A`; `b:real`; `A2:real^1->real^N`;
                 `J:real^1->bool`; `sa:real`; `sb:real`] P2A_TRANS_ODE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `u:real^1` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(gamma:real->A)(drop u pow 2) IN O` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "O" THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a1 < tt - drop(u:real^1) pow 2 /\ tt - drop u pow 2 <= b1) /\
                  (a2 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `sb:real`)) (concl th) &&
          can (find_term ((=) `b1:real`)) (concl th)));
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `d2:real`)) (concl th) &&
          can (find_term ((=) `b2:real`)) (concl th)))] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u" &&
      can (find_term ((=) `A2:real^1->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  (* the velocities agree at s0 *)
  ABBREV_TAC `B2 = frechet_derivative (h:real^N->real^N) (at ((phi2:A->real^N) p))
                                      ((A2:real^1->real^N)(lift s0))` THEN
  SUBGOAL_THEN `(B2:real^N) = (A1:real^1->real^N)(lift s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC
     [`\v:real^1. (phi1:A->real^N)((gamma:real->A)(drop v pow 2))`;
      `vec 0:real^1`; `lift(sqrt b)`; `lift s0`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP P2A_SDOM_INTERVAL
      (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < b`))]) THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`\r:real^1. (h:real^N->real^N)((phi2:A->real^N)((gamma:real->A)(drop r pow 2)))`;
      `e:real`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN `(gamma:real->A)(drop v pow 2) IN O` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2A_SQRT_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
          UNDISCH_TAC `dist(v:real^1,lift s0) < e` THEN
          REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
        EXPAND_TAC "O" THEN SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s0` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `J:real^1->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_solution")) (concl th)))) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN
      SUBGOAL_THEN `interval[vec 0,lift(sqrt b)] = {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the s-family of region 1 on (sa,sb) *)
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi1:A->real^N) (U1 INTER W1)) sa sb
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1) W1`; `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b1) W1`;
      `a1:real`; `b1:real`; `p2a_rmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1`;
      `(U1 INTER W1:A->bool,phi1:A->real^N)`; `tt:real`; `sa:real`; `sb:real`]
     P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 a1 b1` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U1:A->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (phi1:A->real^N) (U1 INTER W1)`; `sa:real`; `sb:real`;
    `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W1 b1 (U1 INTER W1,phi1)`; `tt:real`; `J:real^1->bool`; `J:real^1->bool`;
    `Y1:real^1->real^N`; `A1:real^1->real^N`;
    `\u:real^1. (h:real^N->real^N)((phi2:A->real^N)((gamma:real->A)(drop u pow 2)))`;
    `\u:real^1. frechet_derivative (h:real^N->real^N)
                  (at ((phi2:A->real^N)((gamma:real->A)(drop u pow 2))))
                  ((A2:real^1->real^N) u)`;
    `lift s0`] P2A_LSOL_UNIQUE) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN EXISTS_TAC `J1:real^1->bool` THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `A1:real^1->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
    can (find_term ((=) `J:real^1->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "J" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN O` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "O" THEN SET_TAC[]]);;

let P2A_SWIN_LOCAL_EQ = prove
 (`!b1 b2 (y:real^1). &0 < b1 /\ b1 <= b2 /\ drop y < sqrt b1
                      ==> (&0 <= drop y /\ drop y pow 2 <= b1 <=>
                           &0 <= drop y /\ drop y pow 2 <= b2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= drop(y:real^1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `drop(y:real^1) pow 2 < b1` ASSUME_TAC THENL
   [SUBGOAL_THEN `b1 = sqrt b1 pow 2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ];
    ASM_REAL_ARITH_TAC]);;

let P2A_LGEOD_GLUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b1 b2 W a' b' U (phi:A->real^N) sa sb (Y:real^1->real^N) A J.
     p2a_Lgeod V tt gamma b1 /\ b1 < b2 /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     sa < sqrt b1 /\ sqrt b2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     ode_solution (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
       (interval(lift sa,lift sb) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N))) J
       (\u. pastecart (Y u) (A u)) /\
     open J /\ is_interval J /\ lift(sqrt b1) IN J /\ lift(sqrt b2) IN J /\
     gamma b1 IN U INTER W /\ Y(lift(sqrt b1)) = phi(gamma b1) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt b1)))
       (at (lift(sqrt b1)) within {v | &0 <= drop v /\ drop v pow 2 <= b1})
     ==> p2a_Lgeod V tt
           (\tau. if tau <= b1 then gamma tau
                  else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) b2 /\
         (\tau. if tau <= b1 then gamma tau
                else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) b2 IN U INTER W /\
         phi((\tau. if tau <= b1 then gamma tau
                    else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) b2) =
         Y(lift(sqrt b2)) /\
         ((\v. phi((\tau. if tau <= b1 then gamma tau
                          else chart_inv (U INTER W,phi) (Y(lift(sqrt tau))))
                   (drop v pow 2))) has_vector_derivative A(lift(sqrt b2)))
           (at (lift(sqrt b2)) within {v | &0 <= drop v /\ drop v pow 2 <= b2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b1` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b1 /\ sqrt b1 < sqrt b2 /\ sqrt b1 pow 2 = b1 /\
                sqrt b2 pow 2 = b2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < b2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; SQRT_MONO_LT];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = sqrt b1` THEN ABBREV_TAC `s2 = sqrt b2` THEN
  ABBREV_TAC `c = (U INTER W:A->bool,phi:A->real^N)` THEN
  (* chart facts of c *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `b':real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `sb:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology (p2a_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W`;
                 `restrict_atlas (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b') W`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "c" THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
      EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  (* left agreement of the chart curve of gamma with Y *)
  FIRST_ASSUM(MP_TAC o SPEC `lift s1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open (J:real^1->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b1:real`; `s1:real`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `sa:real`; `sb:real`; `Y:real^1->real^N`; `A:real^1->real^N`;
                 `J:real^1->bool`; `r0:real`] P2A_LGEOD_CHART_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
      REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  (* gamma stays in the chart near s1 *)
  SUBGOAL_THEN `a' < tt - b1 /\ tt - b1 <= b'` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `sb:real`)) (concl th) &&
      can (find_term ((=) `b':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - s1 pow 2`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - s1 pow 2`;
                 `U INTER W:A->bool`] P2A_REGION_OPEN_BACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b'`; `(U:A->bool,phi:A->real^N)`]
                    MFDM_CHART) THEN
      ASM_SIMP_TAC[FST];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b1:real`; `s1:real`; `U INTER W:A->bool`]
                P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `dd = min (min dl r0) (min (s1 - sa) (min s1 ec))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= dl /\ dd <= r0 /\ dd <= s1 - sa /\ dd <= s1 /\ dd <= ec`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "dd" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Y on J *)
  SUBGOAL_THEN `!v:real^1. v IN J ==> sa < drop v /\ drop v < sb /\
                                     (Y:real^1->real^N) v IN IMAGE (phi:A->real^N) (U INTER W)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_solution")) (concl th))) THEN
    REWRITE_TAC[P2A_LSOL_ODE] THEN DISCH_THEN(MP_TAC o SPEC `v:real^1` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the agreement of the glued curve with Y beyond s1 - dd *)
  ABBREV_TAC `gamma' = \tau. if tau <= b1 then (gamma:real->A) tau
                             else chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau)))` THEN
  SUBGOAL_THEN
   `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b2 /\ s1 - dd < drop v
               ==> v IN J /\ (phi:A->real^N)((gamma':real->A)(drop v pow 2)) = Y v /\
                   gamma'(drop v pow 2) IN U INTER W`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `drop v <= s2` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM(ASSUME `sqrt b2 = s2`)] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^1) IN J` ASSUME_TAC THENL
     [ASM_CASES_TAC `drop v <= s1` THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
        REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `is_interval (J:real^1->bool)` THEN REWRITE_TAC[IS_INTERVAL_1] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`lift s1`; `lift s2`] THEN
        ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "gamma'" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `drop(v:real^1) <= s1` ASSUME_TAC THENL
       [ONCE_REWRITE_TAC[GSYM(ASSUME `sqrt b1 = s1`)] THEN
        MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `drop(v:real^1)` o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `dl:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `ec:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[POW_2_SQRT; LIFT_DROP] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tau. tau <= b1 ==> (gamma':real->A) tau = gamma tau` ASSUME_TAC THENL
   [EXPAND_TAC "gamma'" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!tau. (if tau <= b1 then (gamma:real->A) tau
                       else chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^1->real^N)(lift(sqrt tau)))) =
                gamma' tau`
  (fun th -> REWRITE_TAC[th; ETA_AX]) THENL
   [EXPAND_TAC "gamma'" THEN EXPAND_TAC "c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(if b2 <= b1 then (gamma:real->A) b2
                 else chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^1->real^N)(lift s2))) =
                gamma' b2` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "gamma'" THEN EXPAND_TAC "c" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(gamma':real->A) b2 IN U INTER W /\ (phi:A->real^N)(gamma' b2) = Y(lift s2) /\
    ((\v. phi(gamma'(drop v pow 2))) has_vector_derivative (A:real^1->real^N)(lift s2))
      (at (lift s2) within {v | &0 <= drop v /\ drop v pow 2 <= b2})`
  (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o SPEC `lift s2` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    REWRITE_TAC[LIFT_DROP; ASSUME `s2 pow 2 = b2`; REAL_LE_REFL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b' (U INTER W:A->bool,phi:A->real^N)`;
                   `tt:real`;
                   `interval(lift sa,lift sb) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `J:real^1->bool`; `Y:real^1->real^N`; `A:real^1->real^N`; `lift s2`]
                  P2A_LSOL_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `dd:real`] THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b1` THEN
  REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!tau. b1 < tau /\ tau <= b2
                      ==> (gamma':real->A) tau IN U INTER W /\
                          a' < tt - tau /\ tt - tau < b'`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s1 < sqrt tau /\ sqrt tau <= s2 /\ sqrt tau pow 2 = tau`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY (fun v -> ONCE_REWRITE_TAC[GSYM(ASSUME v)])
        [`sqrt b1 = s1`; `sqrt b2 = s2`] THEN
      ASM_SIMP_TAC[SQRT_MONO_LT; SQRT_MONO_LE; SQRT_POW_2];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(sqrt tau)` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    ASM_SIMP_TAC[LIFT_DROP; SQRT_POS_LE] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `sb:real`)) (concl th) &&
      can (find_term ((=) `b':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* in the slices *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b1` THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `b2:real`)) (concl th) &&
      not (can (find_term ((=) `dd:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - tau`] P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    (* smooth points *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b1` THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `b2:real`)) (concl th) &&
      not (can (find_term ((=) `dd:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[p2a_smooth] THEN MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the chart pieces *)
  X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^1. drop y < s1
                           ==> (&0 <= drop y /\ drop y pow 2 <= b1 <=>
                                &0 <= drop y /\ drop y pow 2 <= b2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC P2A_SWIN_LOCAL_EQ THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s0 < s1` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "s0")) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `s1 pow 2 = b1`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `a0:real` (X_CHOOSE_THEN `b0:real`
      (X_CHOOSE_THEN `c0:(A->bool)#(A->real^N)` (X_CHOOSE_THEN `d0:real`
      (X_CHOOSE_THEN `A0:real^1->real^N` STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC [`W0:A->bool`; `a0:real`; `b0:real`; `c0:(A->bool)#(A->real^N)`;
                          `min d0 (s1 - s0)`; `A0:real^1->real^N`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN
    SUBGOAL_THEN `!s. &0 <= s /\ s < s1 ==> s pow 2 <= b1` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `s1 pow 2 = b1`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 <= b1` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `d0:real`)) (concl th) &&
        fst(dest_var(fst(dest_forall(concl th)))) = "s")) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `drop(u:real^1) pow 2 <= b1` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `d0:real`)) (concl th) &&
      fst(dest_var(fst(dest_forall(concl th)))) = "u")) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!f (f':real^N).
                    (f has_vector_derivative f')
                      (at u within {v | &0 <= drop v /\ drop v pow 2 <= b1}) <=>
                    (f has_vector_derivative f')
                      (at u within {v | &0 <= drop v /\ drop v pow 2 <= b2})`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC P2A_HVD_WITHIN_LOCAL THEN
      EXISTS_TAC `s1 - drop(u:real^1)` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "y")) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))`;
      `s1 - drop(u:real^1)`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop] THEN STRIP_TAC THEN
    SUBGOAL_THEN `drop(v:real^1) pow 2 <= b1` (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* s0 >= s1: the chart of Y *)
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`; `(U INTER W:A->bool,phi:A->real^N)`;
                        `dd / &2`; `A:real^1->real^N`] THEN
  ASM_REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `sb:real`)) (concl th) &&
      can (find_term ((=) `b':real`)) (concl th))) THEN
    SUBGOAL_THEN `s <= s2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM(ASSUME `sqrt b2 = s2`)] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real^1` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b' (U INTER W:A->bool,phi:A->real^N)`; `tt:real`;
                   `interval(lift sa,lift sb) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `J:real^1->bool`; `Y:real^1->real^N`; `A:real^1->real^N`; `u:real^1`]
                  P2A_LSOL_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `dd / &2`] THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `gamma':real->A`)) (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;


(* ========================================================================= *)
(* Gluing for L-geodesics from x with initial vector Z (the end state of the *)
(* glued curve in the chart of Y).                                           *)
(* ========================================================================= *)

let P2A_LGEOD_FROM_GLUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z gamma b1 b2 W a' b' U (phi:A->real^N) sa sb (Y:real^1->real^N) A J.
     p2a_Lgeod_from V tt x Z b1 gamma /\ b1 < b2 /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     sa < sqrt b1 /\ sqrt b2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
     ode_solution (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
       (interval(lift sa,lift sb) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N))) J
       (\u. pastecart (Y u) (A u)) /\
     open J /\ is_interval J /\ lift(sqrt b1) IN J /\ lift(sqrt b2) IN J /\
     gamma b1 IN U INTER W /\ Y(lift(sqrt b1)) = phi(gamma b1) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt b1)))
       (at (lift(sqrt b1)) within {v | &0 <= drop v /\ drop v pow 2 <= b1})
     ==> p2a_Lgeod_from V tt x Z b2
           (\tau. if tau <= b1 then gamma tau
                  else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) /\
         (\tau. if tau <= b1 then gamma tau
                else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) b2 IN U INTER W /\
         phi((\tau. if tau <= b1 then gamma tau
                    else chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) b2) =
         Y(lift(sqrt b2)) /\
         ((\v. phi((\tau. if tau <= b1 then gamma tau
                          else chart_inv (U INTER W,phi) (Y(lift(sqrt tau))))
                   (drop v pow 2))) has_vector_derivative A(lift(sqrt b2)))
           (at (lift(sqrt b2)) within {v | &0 <= drop v /\ drop v pow 2 <= b2})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b1` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b1:real`; `b2:real`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `sa:real`; `sb:real`; `Y:real^1->real^N`; `A:real^1->real^N`;
                 `J:real^1->bool`] P2A_LGEOD_GLUE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f (f':real^N).
      (f has_vector_derivative f')
        (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b1}) <=>
      (f has_vector_derivative f')
        (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b2})`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2A_HVD_WITHIN_LOCAL THEN
    EXISTS_TAC `sqrt b1` THEN
    ASM_SIMP_TAC[SQRT_POS_LT; IN_ELIM_THM; DROP_VEC; REAL_LE_REFL; REAL_POW_ZERO; ARITH_EQ;
                 REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_0; NORM_REAL; GSYM drop] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2A_SWIN_LOCAL_EQ THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`\v:real^1. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A)) ((gamma:real->A)(drop v pow 2))`;
    `sqrt b1`] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; IN_ELIM_THM; DROP_VEC; REAL_LE_REFL; REAL_POW_ZERO; ARITH_EQ;
               REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_0; NORM_REAL; GSYM drop] THEN STRIP_TAC THEN
  SUBGOAL_THEN `drop(v:real^1) pow 2 <= b1` (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `b1 = sqrt b1 pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The propagation property p2a_lprop and its transport along the flow of    *)
(* the chart system (P2A_LPROP_FLOW, P2A_LPROP_STEP).                        *)
(* ========================================================================= *)

(* The propagation property: on an open set N of initial vectors around Z0, *)
(* the L-geodesics from x exist up to s^2 and their state at s in a fixed  *)
(* region chart (position and chart velocity) is a smooth function Phi of  *)
(* the initial vector.                                                       *)

let p2a_lprop = new_definition
 `p2a_lprop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
            (tt:real) (x:A) (Z0:real^N) (s:real) <=>
    ?N W a' b' U (phi:A->real^N) r (Phi:real^N->real^(N,N)finite_sum).
      open N /\ Z0 IN N /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
      &0 < r /\ (!s'. abs(s' - s) < r ==> a' < tt - s' pow 2 /\ tt - s' pow 2 <= b') /\
      smooth_map_on N Phi /\
      !Z. Z IN N
          ==> ?gamma. p2a_Lgeod_from V tt x Z (s pow 2) gamma /\
                      gamma(s pow 2) IN U INTER W /\
                      phi(gamma(s pow 2)) = fstcart(Phi Z) /\
                      ((\v. phi(gamma(drop v pow 2))) has_vector_derivative sndcart(Phi Z))
                        (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= s pow 2})`;;

let P2A_LPROP_FLOW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0 s1 s2 N W a' b' U (phi:A->real^N) r (Phi:real^N->real^(N,N)finite_sum).
     open N /\ Z0 IN N /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < r /\ (!s'. abs(s' - s1) < r ==> a' < tt - s' pow 2 /\ tt - s' pow 2 <= b') /\
     smooth_map_on N Phi /\
     (!Z. Z IN N
          ==> ?gamma. p2a_Lgeod_from V tt x Z (s1 pow 2) gamma /\
                      gamma(s1 pow 2) IN U INTER W /\
                      phi(gamma(s1 pow 2)) = fstcart(Phi Z) /\
                      ((\v. phi(gamma(drop v pow 2))) has_vector_derivative sndcart(Phi Z))
                        (at (lift s1) within {v | &0 <= drop v /\ drop v pow 2 <= s1 pow 2})) /\
     &0 < s1 /\ s1 < s2 /\ s2 < s1 + r /\
     pastecart (lift s2) (pastecart (lift s1) (Phi Z0)) IN
       ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
         (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
     ==> p2a_lprop V tt x Z0 s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'
                   (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  (* ODE facts *)
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) W b' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b') W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b') W`;
      `a':real`; `b':real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'`;
      `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `s1 - r`; `s1 + r`] P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) W a' b'` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open {Z | Z IN N /\
              pastecart (lift s2) (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z))
              IN ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D} /\
    (Z0:real^N) IN {Z | Z IN N /\ pastecart (lift s2) (pastecart (lift s1) (Phi Z))
                                  IN ode_domain f D} /\
    {Z | Z IN N /\ pastecart (lift s2) (pastecart (lift s1) (Phi Z)) IN ode_domain f D}
    SUBSET N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC `N' = {Z | Z IN N /\
                        pastecart (lift s2) (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z))
                        IN ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D}` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  REWRITE_TAC[p2a_lprop] THEN
  MAP_EVERY EXISTS_TAC
   [`N':real^N->bool`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
    `r - (s2 - s1)`;
    `\Z. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (lift s2)
                  (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s':real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* smoothness of the new state map *)
    SUBGOAL_THEN
     `(\Z. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (lift s2)
                    (pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z))) =
      (\w. ode_flow f D (fstcart w) (sndcart w)) o
      (\Z. pastecart (lift s2) (pastecart (lift s1) (Phi Z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "N'" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `N:real^N->bool` THEN ASM_REWRITE_TAC[]];
    (* the L-geodesics up to s2 *)
    X_GEN_TAC `Z:real^N` THEN EXPAND_TAC "N'" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "Z")) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `z = pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z)` THEN
    MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `lift s2`;
                   `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_IN_DOMAIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                   `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `fstcart(z:real^(1,(N,N)finite_sum)finite_sum) = lift s1 /\
                  sndcart z = (Phi:real^N->real^(N,N)finite_sum) Z`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `J = ode_maxint (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D z` THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `gamma:real->A`; `s1 pow 2`; `s2 pow 2`;
                   `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                   `s1 - r`; `s1 + r`;
                   `\t. fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                         D t z)`;
                   `\t. sndcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                         D t z)`;
                   `J:real^1->bool`] P2A_LGEOD_FROM_GLUE) THEN
    SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s2 pow 2) = s2 /\ s1 pow 2 < s2 pow 2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN EXISTS_TAC
     `\tau. if tau <= s1 pow 2 then (gamma:real->A) tau
            else chart_inv (U INTER W,phi:A->real^N)
                   (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                     D (lift(sqrt tau)) z))` THEN
    ASM_REWRITE_TAC[]]);;

let P2A_LPROP_STEP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0 s.
     &0 < s /\ p2a_lprop V tt x Z0 s
     ==> ?e. &0 < e /\ !s'. s <= s' /\ s' < s + e ==> p2a_lprop V tt x Z0 s'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[p2a_lprop] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC)))))))) THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'
                   (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(s - r),lift(s + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s - r) (s + r)
      (\s'. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) W b' (U INTER W,phi) (tt - s' pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b') W`;
      `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b') W`;
      `a':real`; `b':real`; `p2a_rmetric (V:(real->A topology)#
                               (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'`;
      `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `s - r`; `s + r`] P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) W a' b'` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z0 = pastecart (lift s) ((Phi:real^N->real^(N,N)finite_sum) Z0)` THEN
  SUBGOAL_THEN `(z0:real^(1,(N,N)finite_sum)finite_sum) IN D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z0"; "D"] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; GEOL_IN_PCROSS; IN_UNIV] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Z0:real^N` o check (fun th ->
      is_forall (concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "Z")) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) z0 IN
                ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D`
  ASSUME_TAC THENL
   [REWRITE_TAC[ODE_IN_DOMAIN] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                   `z0:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "z0" THEN REWRITE_TAC[FSTCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `pastecart (lift s) (z0:real^(1,(N,N)finite_sum)finite_sum)` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
      concl th = `open (ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 r` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s':real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s':real = s` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2A_LPROP_FLOW THEN
  MAP_EVERY EXISTS_TAC [`s:real`; `N:real^N->bool`; `W:A->bool`; `a':real`; `b':real`;
                        `U:A->bool`; `phi:A->real^N`; `r:real`;
                        `Phi:real^N->real^(N,N)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
  REWRITE_TAC[IN_BALL; DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* L-geodesics from a chart solution in the base region chart                *)
(* (P2A_LGEOD_FROM_SOL) and the start of the propagation at small s          *)
(* (P2A_LPROP_START).                                                        *)
(* ========================================================================= *)

let P2A_LGEOD_FROM_SOL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z W a U (phi:A->real^N) (Y:real^1->real^N) A J sf.
     p2a_region V W a tt /\ x IN W /\
     chart_at (p2a_vatlas V tt) x = (U,phi) /\
     ode_solution (p2a_lfield (p2a_rlocal V W tt (U INTER W,phi)) tt)
       (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
        (IMAGE phi (U INTER W) PCROSS (:real^N))) J
       (\u. pastecart (Y u) (A u)) /\
     open J /\ is_interval J /\ vec 0 IN J /\ lift sf IN J /\ &0 < sf /\
     Y(vec 0) = phi x /\ A(vec 0) = &2 % Z
     ==> p2a_Lgeod_from V tt x Z (sf pow 2)
           (\tau. chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) /\
         chart_inv (U INTER W,phi) (Y(lift sf)) IN U INTER W /\
         phi(chart_inv (U INTER W,phi) (Y(lift sf))) = Y(lift sf) /\
         ((\v. phi((\tau. chart_inv (U INTER W,phi) (Y(lift(sqrt tau)))) (drop v pow 2)))
          has_vector_derivative A(lift sf))
           (at (lift sf) within {v | &0 <= drop v /\ drop v pow 2 <= sf pow 2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < tt` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_region; p2a_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\ (x:A) IN U` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  ABBREV_TAC `c = (U INTER W:A->bool,phi:A->real^N)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = sqrt(tt - a)` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = tt - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`;
                 `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`; `c:(A->bool)#(A->real^N)`]
                MFDM_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN U INTER W` ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^1. t IN J ==> --r < drop t /\ drop t < r /\
                                       (Y:real^1->real^N) t IN
                                       IMAGE (phi:A->real^N) (U INTER W:A->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_solution")) (concl th))) THEN
    REWRITE_TAC[P2A_LSOL_ODE] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b = sf pow 2` THEN
  SUBGOAL_THEN `&0 < b /\ sqrt b = sf` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b ==> v IN J` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_interval (J:real^1->bool)` THEN REWRITE_TAC[IS_INTERVAL_1] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `lift sf`] THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN
    ONCE_REWRITE_TAC[GSYM(ASSUME `sqrt b = sf`)] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b < tt - a` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `r pow 2 = tt - a`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift sf` o check (fun th ->
      can (find_term ((=) `--r`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b
               ==> chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^1->real^N)(lift(sqrt(drop v pow 2)))) =
                   chart_inv c (Y v) /\
                   chart_inv c (Y v) IN U INTER W /\
                   (phi:A->real^N)(chart_inv c (Y v)) = Y v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[POW_2_SQRT; LIFT_DROP] THEN
    SUBGOAL_THEN `(Y:real^1->real^N) v IN IMAGE (phi:A->real^N) (U INTER W)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "c" THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b
                           ==> ((Y:real^1->real^N) has_vector_derivative (A:real^1->real^N) v)
                                 (at v within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                               (A has_vector_derivative
                                  p2a_lacc (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (c:(A->bool)#(A->real^N))) tt
                                           (drop v) (Y v) (A v))
                                 (at v within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (c:(A->bool)#(A->real^N))`; `tt:real`;
                   `interval(lift(--r),lift r) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `J:real^1->bool`; `Y:real^1->real^N`; `A:real^1->real^N`; `v:real^1`]
                  P2A_LSOL_AT) THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) = c` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^1->real^N)(lift sf)) IN U INTER W /\
    (phi:A->real^N)(chart_inv c (Y(lift sf))) = Y(lift sf) /\
    ((\v. phi(chart_inv c (Y(lift(sqrt(drop v pow 2)))))) has_vector_derivative
     (A:real^1->real^N)(lift sf))
      (at (lift sf) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o SPEC `lift sf` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift sf` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
        is_forall (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_Lgeod_from; p2a_Lgeod] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s pow 2 <= b ==> a < tt - s pow 2 /\ tt - s pow 2 <= tt`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN TRY(MP_TAC(SPEC `s:real` REAL_LE_POW_2)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* in the slices *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(sqrt tau)` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_SIMP_TAC[LIFT_DROP; SQRT_POS_LE; SQRT_POW_2] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt - tau`] P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    (* smooth points *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_smooth] THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift(sqrt tau)` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      is_forall (concl th))) THEN
    ASM_SIMP_TAC[LIFT_DROP; SQRT_POS_LE; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    (* the chart pieces *)
    X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`; `c:(A->bool)#(A->real^N)`;
                          `&1`; `A:real^1->real^N`] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) = U INTER W` SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC[FST]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) = phi` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[SND]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!v:real^1. &0 <= drop v /\ drop v pow 2 <= b
                 ==> (phi:A->real^N) (chart_inv (c:(A->bool)#(A->real^N))
                        ((Y:real^1->real^N) (lift (sqrt (drop v pow 2))))) = Y v`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^1` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
        is_forall (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    TRY(MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
        MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `&1`] THEN
        ASM_SIMP_TAC[REAL_LT_01; IN_ELIM_THM]);
    (* gamma 0 = x *)
    REWRITE_TAC[SQRT_0; LIFT_NUM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN ASM_SIMP_TAC[];
    (* the initial vector *)
    SUBGOAL_THEN `&2 % (Z:real^N) = (A:real^1->real^N)(vec 0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`Y:real^1->real^N`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; DROP_VEC] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      is_forall (concl th))) THEN
    REWRITE_TAC[DROP_VEC] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P2A_LPROP_START = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> ?e. &0 < e /\ !s. &0 < s /\ s < e ==> p2a_lprop V tt x Z0 s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_bsmooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))` THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))` THEN
  SUBGOAL_THEN `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A) = (U,phi:A->real^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\ (x:A) IN U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  ABBREV_TAC `r = sqrt(tt - a)` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = tt - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(--r),lift r) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  SUBGOAL_THEN
   `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (--r) r
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`; `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) W`;
      `a:real`; `tt:real`; `p2a_rmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt`;
      `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `--r`; `r:real`] P2A_UPTO_SFAMILY) THEN
    REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a tt` THEN
    REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 < r pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `zz = \Z:real^N. pastecart (vec 0:real^1) (pastecart ((phi:A->real^N) x) (&2 % Z))` THEN
  SUBGOAL_THEN `!S:real^N->bool. open S
                 ==> smooth_map_on S (zz:real^N->real^(1,(N,N)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "zz" THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N. (zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z IN D` ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["zz"; "D"] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_UNIV] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (vec 0:real^1) ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z0) IN
                ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D`
  ASSUME_TAC THENL
   [REWRITE_TAC[ODE_IN_DOMAIN] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                   `(zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z0`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "zz" THEN REWRITE_TAC[FSTCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `pastecart (vec 0:real^1) ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z0)` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o check (fun th ->
      concl th = `open (ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 r` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open {Z:real^N | pastecart (lift s) ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z) IN
                     ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D} /\
    (Z0:real^N) IN {Z | pastecart (lift s) (zz Z) IN ode_domain f D}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{Z:real^N | P Z} = {Z | Z IN (:real^N) /\ P Z}`] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
      EXPAND_TAC "zz" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      REWRITE_TAC[IN_ELIM_THM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
      REWRITE_TAC[IN_BALL; DIST_PASTECART_CANCEL; DIST_0; NORM_LIFT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lprop] THEN
  MAP_EVERY EXISTS_TAC
   [`{Z:real^N | pastecart (lift s) ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z) IN
                 ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D}`;
    `W:A->bool`; `a:real`; `tt:real`; `U:A->bool`; `phi:A->real^N`; `r - s`;
    `\Z:real^N. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (lift s)
                  ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s' pow 2 < r pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `s':real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN
     `(\Z:real^N. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (lift s)
                    ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z)) =
      (\w. ode_flow f D (fstcart w) (sndcart w)) o (\Z. pastecart (lift s) (zz Z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `Z:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `lift s`;
                 `(zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z`] ODE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `(zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fstcart((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z) = vec 0 /\
                sndcart(zz Z) = pastecart ((phi:A->real^N) x) (&2 % Z)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `W:A->bool`; `a:real`; `U:A->bool`;
                 `phi:A->real^N`;
                 `\t. fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                       D t ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z))`;
                 `\t. sndcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                       D t ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z))`;
                 `ode_maxint (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D
                    ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z)`;
                 `s:real`] P2A_LGEOD_FROM_SOL) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  TRY(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN
  EXISTS_TAC `\tau. chart_inv (U INTER W,phi:A->real^N)
                      (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                        D (lift(sqrt tau))
                                        ((zz:real^N->real^(1,(N,N)finite_sum)finite_sum) Z)))` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]);;


(* ========================================================================= *)
(* Change of the region chart in the propagation data (P2A_LPROP_CHANGE,     *)
(* with the tangent map of a smooth map P2A_SMOOTH_JAC_STATE), flow-domain   *)
(* membership from a solution segment (P2A_ODE_DOMAIN_SEG) and uniqueness of *)
(* s-velocities (P2A_SVEL_UNIQUE).                                           *)
(* ========================================================================= *)

let P2A_SMOOTH_JAC_STATE = prove
 (`!O (h:real^N->real^N).
     open O /\ smooth_map_on O h
     ==> smooth_map_on (O PCROSS (:real^N))
           (\z. pastecart (h(fstcart z)) (frechet_derivative h (at (fstcart z)) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open((O:real^N->bool) PCROSS (:real^N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((O:real^N->bool) PCROSS (:real^N))
                  (fstcart:real^(N,N)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (fstcart:real^(N,N)finite_sum->real^N) (O PCROSS (:real^N)) SUBSET O`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS] THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\z:real^(N,N)finite_sum. (h:real^N->real^N)(fstcart z)) = h o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(O:real^N->bool) PCROSS (:real^N)`;
                 `\z:real^(N,N)finite_sum. frechet_derivative (h:real^N->real^N) (at (fstcart z))`;
                 `\z:real^(N,N)finite_sum. sndcart z`] P2A_SMOOTH_LINEAR_ARG) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GEOL_IN_PCROSS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\z:real^(N,N)finite_sum. frechet_derivative (h:real^N->real^N)
                                             (at (fstcart z)) (basis j)) =
                  (\y. frechet_derivative h (at y) (basis j)) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_SNDCART]]);;

let P2A_LPROP_CHANGE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0 s N W a' b' U (phi:A->real^N) r (Phi:real^N->real^(N,N)finite_sum)
    W2 a2 b2 U2 (phi2:A->real^N).
     &0 < s /\
     open N /\ Z0 IN N /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < r /\ (!s'. abs(s' - s) < r ==> a' < tt - s' pow 2 /\ tt - s' pow 2 <= b') /\
     smooth_map_on N Phi /\
     (!Z. Z IN N
          ==> ?gamma. p2a_Lgeod_from V tt x Z (s pow 2) gamma /\
                      gamma(s pow 2) IN U INTER W /\
                      phi(gamma(s pow 2)) = fstcart(Phi Z) /\
                      ((\v. phi(gamma(drop v pow 2))) has_vector_derivative sndcart(Phi Z))
                        (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= s pow 2})) /\
     p2a_region V W2 a2 b2 /\ (U2,phi2) IN p2a_vatlas V b2 /\
     a2 < tt - s pow 2 /\ tt - s pow 2 <= b2 /\
     fstcart(Phi Z0) IN IMAGE phi ((U INTER W) INTER (U2 INTER W2))
     ==> ?N2 (Phi2:real^N->real^(N,N)finite_sum).
           open N2 /\ Z0 IN N2 /\ smooth_map_on N2 Phi2 /\
           (!Z. Z IN N2
                ==> ?gamma. p2a_Lgeod_from V tt x Z (s pow 2) gamma /\
                            gamma(s pow 2) IN U2 INTER W2 /\
                            phi2(gamma(s pow 2)) = fstcart(Phi2 Z) /\
                            ((\v. phi2(gamma(drop v pow 2))) has_vector_derivative
                             sndcart(Phi2 Z))
                              (at (lift s) within
                               {v | &0 <= drop v /\ drop v pow 2 <= s pow 2}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a' < tt - s pow 2 /\ tt - s pow 2 <= b'` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - s pow 2`]
                P2A_REGION_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `tt - s pow 2`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) (tt - s pow 2)) (U INTER W) /\
    open_in (p2a_vtop V (tt - s pow 2)) (U2 INTER W2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_OPEN_BACK THENL
     [MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`];
      MAP_EVERY EXISTS_TAC [`W2:A->bool`; `a2:real`; `b2:real`]] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b'`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART);
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b2`;
                     `(U2:A->bool,phi2:A->real^N)`] MFDM_CHART)] THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `tt - s pow 2`;
                 `U:A->bool`; `phi:A->real^N`; `U2:A->bool`; `phi2:A->real^N`]
                P2A_REGION_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `O1 = IMAGE (phi:A->real^N) ((U INTER W) INTER (U2 INTER W2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) (U2 INTER W2,phi2)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W ==> chart_inv (U INTER W,phi:A->real^N) (phi q) = q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W ==> (h:real^N->real^N)(phi q) = phi2 q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans; SND] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W /\ (phi:A->real^N) q IN O1 ==> q IN U2 INTER W2`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:A` THEN EXPAND_TAC "O1" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q':A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(q:A) = q'` (fun th -> ASM_REWRITE_TAC[th] THEN ASM SET_TAC[]) THEN
    SUBGOAL_THEN `q' IN U INTER (W:A->bool)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {Z:real^N | Z IN N /\ fstcart((Phi:real^N->real^(N,N)finite_sum) Z) IN O1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\Z:real^N. fstcart((Phi:real^N->real^(N,N)finite_sum) Z)) = fstcart o Phi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    ALL_TAC] THEN
  ABBREV_TAC `N2 = {Z:real^N | Z IN N /\ fstcart((Phi:real^N->real^(N,N)finite_sum) Z) IN O1}` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(Z0:real^N) IN N2 /\ N2 SUBSET N` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N2" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`N2:real^N->bool`;
    `\Z:real^N. pastecart ((h:real^N->real^N)(fstcart((Phi:real^N->real^(N,N)finite_sum) Z)))
                         (frechet_derivative h (at (fstcart(Phi Z))) (sndcart(Phi Z)))`] THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\Z:real^N. pastecart ((h:real^N->real^N)(fstcart((Phi:real^N->real^(N,N)finite_sum) Z)))
                          (frechet_derivative h (at (fstcart(Phi Z))) (sndcart(Phi Z)))) =
      (\z. pastecart (h(fstcart z)) (frechet_derivative h (at (fstcart z)) (sndcart z))) o Phi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(O1:real^N->bool) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[P2A_SMOOTH_JAC_STATE; OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
     [EXPAND_TAC "N2" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; GEOL_IN_PCROSS; IN_UNIV] THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `N:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN N /\ fstcart((Phi:real^N->real^(N,N)finite_sum) Z) IN O1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^N) IN N2` THEN EXPAND_TAC "N2" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z:real^N) IN N`) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lgeod_from")) (concl th))) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN U2 INTER W2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `O1:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:A->real^N)((gamma:real->A)(s pow 2)) =
                  fstcart((Phi:real^N->real^(N,N)finite_sum) Z)`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt (gamma:real->A) (s pow 2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `s pow 2`; `s:real`;
                 `(U INTER W) INTER (U2 INTER W2):A->bool`] P2A_LGEOD_CONT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; OPEN_IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^N->real^N) o (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))`;
    `e:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `v:real^1` THEN
    REWRITE_TAC[IN_ELIM_THM; dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(gamma:real->A)(drop(v:real^1) pow 2) IN (U INTER W) INTER (U2 INTER W2)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `phi2:A->real^N`)) (concl th) &&
      can (find_term ((=) `h:real^N->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O1:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P2A_ODE_DOMAIN_SEG = prove
 (`!(f:real^(1,N)finite_sum->real^N) D Dp Jp (u:real^1->real^N) t1 t2.
     ode_solution f Dp Jp u /\ drop t1 <= drop t2 /\ interval[t1,t2] SUBSET Jp /\
     (!t. t IN interval[t1,t2] /\ pastecart t (u t) IN Dp ==> pastecart t (u t) IN D)
     ==> pastecart t2 (pastecart t1 (u t1)) IN ode_domain f D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t1:real^1) IN interval[t1,t2] /\ t2 IN interval[t1,t2]` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `ode_solution (f:real^(1,N)finite_sum->real^N) D (interval[t1,t2]) u`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) Dp Jp u` THEN
    REWRITE_TAC[ode_solution; IS_INTERVAL_INTERVAL] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^1) IN Jp` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `Jp:real^1->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[ODE_IN_DOMAIN; ODE_IN_MAXINT; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D (interval[t1,t2]) u` THEN
    REWRITE_TAC[ode_solution] THEN ASM_MESON_TAC[];
    MAP_EVERY EXISTS_TAC [`interval[t1:real^1,t2]`; `u:real^1->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let P2A_SVEL_UNIQUE = prove
 (`!(f:real^1->real^N) g b b' s w w'.
     &0 < s /\ s pow 2 <= b /\ s pow 2 <= b' /\
     (!v. &0 <= drop v /\ drop v <= s ==> f v = g v) /\
     (f has_vector_derivative w)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
     (g has_vector_derivative w')
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b'})
     ==> w = w'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c. s pow 2 <= c
                    ==> interval[vec 0,lift s] SUBSET
                        {v:real^1 | &0 <= drop v /\ drop v pow 2 <= c}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
  MAP_EVERY EXISTS_TAC [`f:real^1->real^N`; `vec 0:real^1`; `lift s`; `lift s`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP];
    REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`g:real^1->real^N`; `&1`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_01];
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b'}` THEN ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The closed step of the propagation (P2A_LPROP_CLOSED) and the propagation *)
(* along the whole L-geodesic by open-closed induction on [0, sqrt b0]       *)
(* (P2A_LPROP_ALL).                                                          *)
(* ========================================================================= *)

let P2A_LPROP_CLOSED = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0 b0 Tm.
     p2a_svs V /\ Z0 IN p2a_Ldom V tt x b0 /\ &0 < Tm /\ Tm pow 2 <= b0 /\
     (!s. &0 < s /\ s < Tm ==> p2a_lprop V tt x Z0 s)
     ==> p2a_lprop V tt x Z0 Tm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `gamma0:real->A`) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt (gamma0:real->A) b0`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma0:real->A`; `b0:real`; `Tm:real`]
                P2A_LGEOD_PIECE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:A->bool` (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real`
    (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N` (X_CHOOSE_THEN `d:real`
    (X_CHOOSE_THEN `A:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `del = min d Tm` THEN
  SUBGOAL_THEN `&0 < del /\ del <= d /\ del <= Tm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s1 = Tm - del / &3` THEN
  ABBREV_TAC `r = del / &2` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < Tm /\ &0 < r /\ Tm < s1 + r /\ Tm - s1 < d /\
                (!s'. abs(s' - s1) < r ==> abs(s' - Tm) < d)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN EXPAND_TAC "r" THEN REPEAT CONJ_TAC THEN TRY GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 pow 2 /\ s1 pow 2 <= b0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Tm pow 2` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the propagation data at s1 *)
  FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lprop")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[p2a_lprop]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:real^N->bool` (X_CHOOSE_THEN `W1:A->bool`
    (X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `b1:real` (X_CHOOSE_THEN `U1:A->bool`
    (X_CHOOSE_THEN `phi1:A->real^N` (X_CHOOSE_THEN `r1:real`
    (X_CHOOSE_THEN `Phi1:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma1:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z0:real^N) IN N1`) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lgeod_from")) (concl th))) THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x Z0 (s1 pow 2) (gamma0:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LGEOD_FROM_RESTRICT THEN EXISTS_TAC `b0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1 pow 2`;
                 `gamma1:real->A`; `gamma0:real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma0:real->A)(s1 pow 2) IN U2 INTER W2 /\
                a2 < tt - s1 pow 2 /\ tt - s1 pow 2 <= b2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `U2:A->bool`)) (concl th) &&
        not (can (find_term ((=) `A:real^1->real^N`)) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lfield"))
                            (concl th)))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `b2:real`)) (concl th) &&
        can (find_term ((=) `d:real`)) (concl th) &&
        not (can (find_term ((=) `U2:A->bool`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s1 pow 2) = gamma0(s1 pow 2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart((Phi1:real^N->real^(N,N)finite_sum) Z0) IN
                IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER (U2 INTER W2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gamma0:real->A)(s1 pow 2)` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `(gamma1:real->A)(s1 pow 2) = gamma0(s1 pow 2)`)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* move to the chart of gamma0 at Tm *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1:real`;
                 `N1:real^N->bool`; `W1:A->bool`; `a1:real`; `b1:real`; `U1:A->bool`;
                 `phi1:A->real^N`; `r1:real`; `Phi1:real^N->real^(N,N)finite_sum`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`]
                P2A_LPROP_CHANGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:real^N->bool`
    (X_CHOOSE_THEN `Phi2:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma2:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z0:real^N) IN N2`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `N2:real^N->bool`)) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1 pow 2`;
                 `gamma2:real->A`; `gamma0:real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma2:real->A)(s1 pow 2) = gamma0(s1 pow 2)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `sndcart((Phi2:real^N->real^(N,N)finite_sum) Z0) = (A:real^1->real^N)(lift s1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_SVEL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`\v:real^1. (phi2:A->real^N)((gamma2:real->A)(drop v pow 2))`;
                          `\v:real^1. (phi2:A->real^N)((gamma0:real->A)(drop v pow 2))`;
                          `s1 pow 2`; `b0:real`; `s1:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s1` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `A:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Phi2:real^N->real^(N,N)finite_sum) Z0 =
    (\u:real^1. pastecart ((phi2:A->real^N)((gamma0:real->A)(drop u pow 2)))
                          ((A:real^1->real^N) u)) (lift s1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi2:A->real^N)((gamma2:real->A)(s1 pow 2)) =
                  fstcart((Phi2:real^N->real^(N,N)finite_sum) Z0)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. abs(s' - s1) < r ==> a2 < tt - s' pow 2 /\ tt - s' pow 2 <= b2`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `b2:real`)) (concl th) &&
      can (find_term ((=) `d:real`)) (concl th) &&
      not (can (find_term ((=) `U2:A->bool`)) (concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pastecart (lift Tm) (pastecart (lift s1) ((Phi2:real^N->real^(N,N)finite_sum) Z0)) IN
    ode_domain (p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2:A->real^N)) tt)
      (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi2 (U2 INTER W2) PCROSS (:real^N)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs(concl th) = `(Phi2:real^N->real^(N,N)finite_sum) Z0`)) THEN
    MATCH_MP_TAC P2A_ODE_DOMAIN_SEG THEN
    MAP_EVERY EXISTS_TAC
     [`interval(lift(Tm - d),lift(Tm + d)) PCROSS
       (IMAGE (phi2:A->real^N) (U2 INTER W2) PCROSS (:real^N))`;
      `{u:real^1 | &0 <= drop u /\ drop u pow 2 <= b0 /\ abs(drop u - Tm) < d}`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
      X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tm pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; PASTECART_IN_PCROSS; IN_UNIV] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1:real`; `Tm:real`;
                 `N2:real^N->bool`; `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`;
                 `phi2:A->real^N`; `r:real`; `Phi2:real^N->real^(N,N)finite_sum`]
                P2A_LPROP_FLOW) THEN
  ASM_REWRITE_TAC[]);;

let P2A_LPROP_ALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0 b0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b0
     ==> !s. &0 < s /\ s pow 2 <= b0 ==> p2a_lprop V tt x Z0 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b0` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x b0` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`] P2A_LPROP_START) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\s. &0 < s ==> p2a_lprop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt x (Z0:real^N) s`; `sqrt b0`] P2A_REAL_CONT_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      EXISTS_TAC `e0:real` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC P2A_LPROP_CLOSED THEN EXISTS_TAC `b0:real` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `b0 = sqrt b0 pow 2` SUBST1_TAC THENL
         [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `Tm = &0` THENL
       [EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `p2a_lprop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)) tt x (Z0:real^N) Tm` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `Tm:real` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `Tm:real`]
                    P2A_LPROP_STEP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN DISCH_TAC THEN
      ASM_CASES_TAC `s <= Tm` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `Tm:real`)) (concl th) &&
          not (can (find_term ((=) `e:real`)) (concl th)))) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RSQRT]);;

(* ========================================================================= *)
(* Local representation of Lexp^b near Z0 in a region chart                  *)
(* (P2A_LEXP_LOCAL), openness of Ldom (P2A_LDOM_OPEN, L1 clause 4), the      *)
(* derivative of Lexp^b in slice charts (P2A_LEXP_CHART_REP) and its         *)
(* differentiability (P2A_LEXP_DIFFERENTIABLE, L1 clause 5).                 *)
(* ========================================================================= *)

let P2A_LEXP_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> ?N W a' b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum).
           open N /\ Z0 IN N /\ N SUBSET p2a_Ldom V tt x b /\
           p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
           a' < tt - b /\ tt - b <= b' /\ smooth_map_on N Phi /\
           !Z. Z IN N ==> p2a_Lexp V tt x b Z IN U INTER W /\
                          phi(p2a_Lexp V tt x b Z) = fstcart(Phi Z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `b:real`]
                P2A_LPROP_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sqrt b`) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REWRITE_TAC[p2a_lprop] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `W:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` (X_CHOOSE_THEN `r:real`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC)))))))) THEN
  MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                        `phi:A->real^N`; `Phi:real^N->real^(N,N)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a' < tt - b /\ tt - b <= b'` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o SPEC `sqrt b` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; ASSUME `&0 < r`; ASSUME `sqrt b pow 2 = b`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z:real^N. Z IN N
               ==> Z IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt x b /\
                   p2a_Lexp V tt x b Z IN U INTER W /\
                   (phi:A->real^N)(p2a_Lexp V tt x b Z) =
                   fstcart((Phi:real^N->real^(N,N)finite_sum) Z)`
  (fun th -> REWRITE_TAC[SUBSET] THEN MESON_TAC[th]) THEN
  X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z:real^N) IN N`) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lgeod_from")) (concl th))) THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt x b` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b Z = gamma b`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[p2a_Lexp] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `b:real`;
                 `p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x Z b`; `gamma:real->A`]
                P2A_LGEOD_UNIQUE) THEN
  ASM_SIMP_TAC[P2A_LGEO_PROP; REAL_LT_IMP_LE; REAL_LE_REFL]);;

let P2A_LDOM_OPEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> open(p2a_Ldom V tt x b)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
  X_GEN_TAC `Z0:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`]
                P2A_LEXP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let P2A_LEXP_CHART_REP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b N Wr a' b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum) Z
    (c':(A->bool)#(A->real^N)).
     open N /\ p2a_region V Wr a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - b /\ tt - b <= b' /\ smooth_map_on N Phi /\
     (!Z. Z IN N ==> p2a_Lexp V tt x b Z IN U INTER Wr /\
                     phi(p2a_Lexp V tt x b Z) = fstcart(Phi Z)) /\
     Z IN N /\ c' IN p2a_vatlas V (tt - b) /\ p2a_Lexp V tt x b Z IN FST c'
     ==> ((\W. SND c' (p2a_Lexp V tt x b W)) has_derivative
          (frechet_derivative (chart_trans (U INTER Wr,phi) c') (at (fstcart(Phi Z))) o
           frechet_derivative (fstcart o Phi) (at Z))) (at Z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `tt - b`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - b`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) ((U INTER Wr) INTER FST(c':(A->bool)#(A->real^N)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `h = chart_trans (U INTER Wr:A->bool,phi:A->real^N) c'` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!q:A. q IN U INTER Wr ==> (h:real^N->real^N)(phi q) = SND(c':(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `Wr:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN N`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `Phi:real^N->real^(N,N)finite_sum`)) (concl th))) THEN
  SUBGOAL_THEN `fstcart((Phi:real^N->real^(N,N)finite_sum) Z) IN O` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs(concl th) = `fstcart((Phi:real^N->real^(N,N)finite_sum) Z)`)) THEN
    EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {W:real^N | W IN N /\ fstcart((Phi:real^N->real^(N,N)finite_sum) W) IN O}`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\W:real^N. fstcart((Phi:real^N->real^(N,N)finite_sum) W)) = fstcart o Phi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `Z:real^N`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`(h:real^N->real^N) o (fstcart o (Phi:real^N->real^(N,N)finite_sum))`;
                        `e:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `W:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(W:real^N) IN N` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(Z:real^N,e) SUBSET {W | W IN N /\ fstcart((Phi:real^N->real^(N,N)finite_sum) W) IN O}` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `W:real^N`) THEN ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(W:real^N) IN N`) o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `Phi:real^N->real^(N,N)finite_sum`)) (concl th))) THEN
    REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs(concl th) = `fstcart((Phi:real^N->real^(N,N)finite_sum) W)`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[o_THM; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let P2A_LEXP_DIFFERENTIABLE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> (\W. SND(chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z0))
                 (p2a_Lexp V tt x b W)) differentiable (at Z0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`]
                P2A_LEXP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `Wr:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `tt - b`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(Z0:real^N) IN N`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `Phi:real^N->real^(N,N)finite_sum`)) (concl th))) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - b)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - b)`;
                 `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b Z0`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (tt - b)) (Wr:A->bool)`)) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `frechet_derivative
                (chart_trans (U INTER Wr:A->bool,phi:A->real^N)
                   (chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                            (real->A->real^N^N)) (tt - b))
                             (p2a_Lexp V tt x b Z0)))
                (at (fstcart((Phi:real^N->real^(N,N)finite_sum) Z0))) o
              frechet_derivative (fstcart o Phi) (at Z0)` THEN
  MATCH_MP_TAC P2A_LEXP_CHART_REP THEN
  MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `a':real`; `b':real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The Jacobian p2a_J in a region chart (P2A_RLOCAL_DENSITY, P2A_J_REGION)   *)
(* and its continuity on the domain (P2A_J_CONTINUOUS_LOCAL,                 *)
(* P2A_J_CONTINUOUS).                                                        *)
(* ========================================================================= *)

let P2A_RLOCAL_DENSITY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b (U:A->bool) (phi:A->real^N) s (c':(A->bool)#(A->real^N)) q (F':real^N->real^N).
     p2a_region V W a b /\ (U,phi) IN p2a_vatlas V b /\ a < s /\ s <= b /\
     c' IN p2a_vatlas V s /\ q IN U /\ q IN W /\ q IN FST c' /\ linear F'
     ==> abs(det(matrix(frechet_derivative (chart_trans (U INTER W,phi) c') (at (phi q)) o
                        F'))) *
         mfd_density (p2a_vatlas V s) c' (p2a_vmetric V s) (SND c' q) =
         abs(det(matrix F')) * sqrt(det(p2a_rlocal V W b (U INTER W,phi) s (phi q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^N`; `s:real`; `c':(A->bool)#(A->real^N)`; `q:A`]
                P2A_RLOCAL_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^N`; `s:real`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) c'` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(h:real^N->real^N)((phi:A->real^N) q) = SND(c':(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) q)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; GRGV_DET_PULLBACK_SQRT; mfd_density] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

let P2A_J_REGION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b N Wr a' b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum) Z.
     open N /\ p2a_region V Wr a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - b /\ tt - b <= b' /\ smooth_map_on N Phi /\
     (!Z. Z IN N ==> p2a_Lexp V tt x b Z IN U INTER Wr /\
                     phi(p2a_Lexp V tt x b Z) = fstcart(Phi Z)) /\
     Z IN N
     ==> p2a_J V tt x b Z =
         abs(det(matrix(frechet_derivative (fstcart o Phi) (at Z)))) *
         sqrt(det(p2a_rlocal V Wr b' (U INTER Wr,phi) (tt - b) (fstcart(Phi Z)))) /
         mfd_density (p2a_vatlas V tt) (chart_at (p2a_vatlas V tt) x) (p2a_vmetric V tt)
                     (SND(chart_at (p2a_vatlas V tt) x) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`; `tt - b`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN N`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `Phi:real^N->real^(N,N)finite_sum`)) (concl th))) THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - b)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - b)`;
                 `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b Z`] CHART_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (tt - b)) (Wr:A->bool)`)) THEN
    ASM SET_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                         (real->A->real^N^N)) (tt - b))
                           (p2a_Lexp V tt x b Z)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `N:real^N->bool`;
                 `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`; `c:(A->bool)#(A->real^N)`]
                P2A_LEXP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[p2a_J] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `fstcart((Phi:real^N->real^(N,N)finite_sum) Z) =
                (phi:A->real^N)(p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                            (real->A->real^N^N)) tt x b Z)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2A_RLOCAL_DENSITY THEN
  MAP_EVERY EXISTS_TAC [`a':real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM SET_TAC[]) THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^N->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN]);;

let P2A_MATRIX_DERIV_CONTINUOUS = prove
 (`!N (f:real^N->real^M).
     open N /\ smooth_map_on N f
     ==> !i j. 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (\Z. lift(matrix(frechet_derivative f (at Z))$i$j)) continuous_on N`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix; LAMBDA_BETA] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]);;

let P2A_J_CONTINUOUS_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b N Wr a' b' U (phi:A->real^N) (Phi:real^N->real^(N,N)finite_sum).
     open N /\ p2a_region V Wr a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - b /\ tt - b <= b' /\ smooth_map_on N Phi /\
     (!Z. Z IN N ==> p2a_Lexp V tt x b Z IN U INTER Wr /\
                     phi(p2a_Lexp V tt x b Z) = fstcart(Phi Z))
     ==> (\Z. lift(p2a_J V tt x b Z)) continuous_on N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\Z:real^N. abs(det(matrix(frechet_derivative
                 (fstcart o (Phi:real^N->real^(N,N)finite_sum)) (at Z)))) %
               (inv(mfd_density (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                               (real->A->real^N^N)) tt)
                        (chart_at (p2a_vatlas V tt) x) (p2a_vmetric V tt)
                        (SND(chart_at (p2a_vatlas V tt) x) x)) %
                lift(sqrt(det(p2a_rlocal V Wr b' (U INTER Wr,phi:A->real^N) (tt - b)
                               (fstcart(Phi Z))))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `N:real^N->bool`;
                   `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                   `Phi:real^N->real^(N,N)finite_sum`; `Z:real^N`] P2A_J_REGION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL; VECTOR_MUL_ASSOC; real_div] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [o_DEF] THEN BETA_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
    MATCH_MP_TAC P2A_MATRIX_DERIV_CONTINUOUS THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [o_DEF] THEN BETA_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
  SUBGOAL_THEN
   `(\Z:real^N. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) Wr b' (U INTER Wr,phi:A->real^N) (tt - b)
                    (fstcart((Phi:real^N->real^(N,N)finite_sum) Z)))) =
    (vectorize o p2a_rlocal V Wr b' (U INTER Wr,phi) (tt - b)) o (fstcart o Phi)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER Wr)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `Wr:A->bool`; `a':real`; `b':real`;
                   `(U INTER Wr:A->bool,phi:A->real^N)`; `tt - b`] P2A_RLOCAL_FIELD) THEN
    ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[metric_field]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(Z:real^N) IN N`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P2A_J_CONTINUOUS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> (\Z. lift(p2a_J V tt x b Z)) continuous_on p2a_Ldom V tt x b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `Z0:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`]
                P2A_LEXP_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `Wr:A->bool`
    (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `Phi:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `N:real^N->bool`;
                 `Wr:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `Phi:real^N->real^(N,N)finite_sum`] P2A_J_CONTINUOUS_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The s-form of the L-integrand. p2a_lsint is the integrand of L in the     *)
(* variable s = sqrt tau (half the squared s-speed plus 2 s^2 R), computed   *)
(* in a region chart (P2A_LSINT_CHART) and related to the tau-integrand      *)
(* (P2A_LINT_SINT); smoothness of the L-Lagrangian in chart state            *)
(* (P2A_LLAG_SMOOTH); locality of p2a_lsint (P2A_LSINT_AGREE,                *)
(* P2A_LSINT_RESTRICT).                                                      *)
(* ========================================================================= *)

let p2a_lsint = new_definition
 `p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
            (tt:real) (gamma:real->A) (b:real) (s:real) =
    inv(&2) *
    (vector_derivative
       (\v. SND(chart_at (p2a_vatlas V (tt - s pow 2)) (gamma(s pow 2)))
               (gamma(drop v pow 2)))
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b}) dot
     (p2a_vmetric V (tt - s pow 2) (gamma(s pow 2)) **
      vector_derivative
       (\v. SND(chart_at (p2a_vatlas V (tt - s pow 2)) (gamma(s pow 2)))
               (gamma(drop v pow 2)))
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b}))) +
    &2 * s pow 2 * mfd_scalar (p2a_vatlas V (tt - s pow 2)) (p2a_vmetric V (tt - s pow 2))
                              (gamma(s pow 2))`;;


let P2A_LSINT_CHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s W a' b' U (phi:A->real^N) A.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\ &0 <= s /\ s pow 2 <= b /\
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     a' < tt - s pow 2 /\ tt - s pow 2 <= b' /\ gamma(s pow 2) IN U INTER W /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})
     ==> p2a_lsint V tt gamma b s =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s (phi(gamma(s pow 2))) A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `tt - s pow 2`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME
      `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) (tt - s pow 2)) (W:A->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `tt - s pow 2`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_lsint; mfd_scalar] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                            ((gamma:real->A)(s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `p = (gamma:real->A)(s pow 2)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - s pow 2`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `O2 = IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `h = chart_trans (U INTER W:A->bool,phi:A->real^N) c'` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `G' = metric_local (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                              (real->A->real^N^N)) (tt - s pow 2))
                                c' (p2a_vmetric V (tt - s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!q:A. q IN U INTER W ==> (h:real^N->real^N)(phi q) = SND(c':(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[chart_trans] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b'`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `q:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) p IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N) (tt - s pow 2) y =
            mpullback (h:real^N->real^N) G' y`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN EXPAND_TAC "h" THEN EXPAND_TAC "G'" THEN
    MATCH_MP_TAC P2A_RLOCAL_SLICE THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field O2 (G':real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "G'" THEN
      UNDISCH_TAC `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "O2" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) W b' (U INTER W,phi:A->real^N) (tt - s pow 2))
            (phi p) =
    lscalar G' (SND(c':(A->bool)#(A->real^N)) p)`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `lscalar (mpullback (h:real^N->real^N) G') ((phi:A->real^N) p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`O2:real^N->bool`; `O:real^N->bool`; `h:real^N->real^N`;
                   `chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)`;
                   `G':real^N->real^N^N`; `(phi:A->real^N) p`] LSCALAR_PULLBACK) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the velocity in the slice chart *)
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                        ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b':real`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b'`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b'`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[FST];
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)`;
                     `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN (U INTER W) INTER FST(c':(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`;
                 `(U INTER W) INTER FST(c':(A->bool)#(A->real^N))`] P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `((\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))) has_vector_derivative
     frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)) A)
    (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`(h:real^N->real^N) o (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))`;
      `e:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^1` THEN
      REWRITE_TAC[IN_ELIM_THM; dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(gamma:real->A)(drop(v:real^1) pow 2) IN
                    (U INTER W) INTER FST(c':(A->bool)#(A->real^N))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall (concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `h:real^N->real^N`)) (concl th) &&
        can (find_term ((=) `phi:A->real^N`)) (concl th) &&
        not (can (find_term ((=) `O:real^N->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative (\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2)))
      (at (lift s) within interval[vec 0,lift(sqrt b)]) =
    frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)) A`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LE_RSQRT];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_llag] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[mpullback] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS (ASSUME
    `linear(frechet_derivative (h:real^N->real^N) (at ((phi:A->real^N) p)))`))] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P2A_LINT_SINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\ &0 < s /\ s pow 2 <= b
     ==> &2 * s * p2a_L_integrand V tt gamma b (s pow 2) = p2a_lsint V tt gamma b s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ sqrt(s pow 2) = s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt gamma b` THEN
    REWRITE_TAC[p2a_Lgeod] THEN DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) (tt - s pow 2))
                          (p2a_vatlas V (tt - s pow 2)) /\
    riemannian_metric (p2a_vatlas V (tt - s pow 2)) (p2a_vmetric V (tt - s pow 2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `tt - s pow 2`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`;
                 `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                           ((gamma:real->A)(s pow 2))`] P2A_LGEOD_SLICE_VEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN
  SUBGOAL_THEN
   `!v:real^N. &0 <= v dot (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2)
                                 ((gamma:real->A)(s pow 2)) ** v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `(gamma:real->A)(s pow 2)`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `riemannian_metric (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))
                                  (p2a_vmetric V (tt - s pow 2))` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)) ((gamma:real->A)(s pow 2))`) THEN
    ASM_REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2)) ((gamma:real->A)(s pow 2)))
                                ((gamma:real->A)(s pow 2))` o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                            ((gamma:real->A)(s pow 2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\r. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))) has_vector_derivative
     (inv(&2 * s) % w)) (at (lift(s pow 2)) within interval[lift(&0),lift b])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`(\v. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop v pow 2))) o
       (lift o sqrt o drop)`; `&1`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_01];
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; o_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * s) % (w:real^N) =
                  drop(lift(inv(&2 * sqrt(s pow 2)))) % w` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
      (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP; o_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_L_integrand; p2a_lsint; mfd_speed; mfd_velocity] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vector_derivative (\r. SND(c':(A->bool)#(A->real^N)) ((gamma:real->A)(drop r)))
      (at (lift(s pow 2)) within interval[lift(&0),lift b]) = inv(&2 * s) % w /\
    vector_derivative (\v. SND c' (gamma(drop v pow 2)))
      (at (lift s) within interval[vec 0,lift(sqrt b)]) = w`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LE_RSQRT; REAL_LT_IMP_LE] THEN
    UNDISCH_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} = interval[vec 0,lift(sqrt b)]`
      (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GRGD_QUAD_HOMOG; SQRT_POW_2; REAL_LE_MUL; REAL_LE_SQUARE] THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let P2A_LLAG_SMOOTH = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))
     ==> smooth_map_on (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))
           (\z. lift(p2a_llag Gt tt (drop(fstcart z)) (fstcart(sndcart z))
                               (sndcart(sndcart z))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o BETA_RULE o MATCH_MP P2A_LSMOOTH_LSCALAR) THEN
  ABBREV_TAC `B = interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
  SUBGOAL_THEN `open(B:real^(1,(N,N)finite_sum)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on B
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\z:real^(1,(N,N)finite_sum)finite_sum.
          (Gt:real->real^N->real^N^N) (tt - drop(fstcart z) pow 2) (fstcart(sndcart z))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sa:real`; `sb:real`; `U:real^N->bool`;
                   `\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((Gt:real->real^N->real^N^N) (tt - drop(fstcart z) pow 2) (sndcart z))`]
                  P2A_SMOOTH_PROJ) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on B
      (\z:real^(1,(N,N)finite_sum)finite_sum.
         lift(lscalar ((Gt:real->real^N->real^N^N) (tt - drop(fstcart z) pow 2))
                      (fstcart(sndcart z))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sa:real`; `sb:real`; `U:real^N->bool`;
                   `\z:real^(1,N)finite_sum.
                      lift(lscalar ((Gt:real->real^N->real^N^N) (tt - drop(fstcart z) pow 2))
                                   (sndcart z))`] P2A_SMOOTH_PROJ) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on B (\z:real^(1,(N,N)finite_sum)finite_sum. sndcart(sndcart z)) /\
    (!j. smooth_map_on B (\z:real^(1,(N,N)finite_sum)finite_sum. lift(sndcart(sndcart z)$j))) /\
    smooth_map_on B (\z:real^(1,(N,N)finite_sum)finite_sum. lift(drop(fstcart z) pow 2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL];
      GEN_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; SNDCART_ADD; SNDCART_CMUL; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC P2A_SMOOTH_LIFT_MUL THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN
      ASM_REWRITE_TAC[ETA_AX; LINEAR_FSTCART]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_llag; LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`B:real^(1,(N,N)finite_sum)finite_sum->bool`;
                   `\z:real^(1,(N,N)finite_sum)finite_sum.
                      (Gt:real->real^N->real^N^N) (tt - drop(fstcart z) pow 2)
                        (fstcart(sndcart z))`;
                   `\z:real^(1,(N,N)finite_sum)finite_sum. sndcart(sndcart z)`]
                  LRG_SMOOTH_MATVEC) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_SMOOTH_RMUL THEN ASM_REWRITE_TAC[]]);;

let P2A_VDERIV_WITHIN_EQ = prove
 (`!(f:real^1->real^N) g S x.
     (!v. v IN S ==> f v = g v) /\ x IN S
     ==> vector_derivative f (at x within S) = vector_derivative g (at x within S)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_derivative] THEN AP_TERM_TAC THEN
  ABS_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THENL
   [EXISTS_TAC `f:real^1->real^N`; EXISTS_TAC `g:real^1->real^N`] THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[REAL_LT_01]);;

let P2A_LSINT_AGREE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b s.
     (!tau. &0 <= tau /\ tau <= b ==> gamma1 tau = gamma2 tau) /\ &0 <= s /\ s pow 2 <= b
     ==> p2a_lsint V tt gamma1 b s = p2a_lsint V tt gamma2 b s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lsint] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s pow 2) = gamma2(s pow 2)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\v. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) (tt - s pow 2))
                        ((gamma2:real->A)(s pow 2))) ((gamma1:real->A)(drop v pow 2)))
      (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b}) =
    vector_derivative
      (\v. SND(chart_at (p2a_vatlas V (tt - s pow 2)) (gamma2(s pow 2))) (gamma2(drop v pow 2)))
      (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC P2A_VDERIV_WITHIN_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LIFT_DROP; REAL_LE_POW_2]);;

let P2A_LSINT_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b s.
     p2a_Lgeod V tt gamma b /\ &0 < s /\ s pow 2 <= b
     ==> p2a_lsint V tt gamma b s = p2a_lsint V tt gamma (s pow 2) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ sqrt(s pow 2) = s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt gamma b` THEN
    REWRITE_TAC[p2a_Lgeod] THEN DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                         (real->A->real^N^N)) (tt - s pow 2))
                                      (p2a_vatlas V (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt gamma b` THEN
    REWRITE_TAC[p2a_Lgeod] THEN
    DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[p2a_smooth] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b':real`; `tt - s pow 2`]
                  P2A_REGION_SLICE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`;
                 `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) (tt - s pow 2))
                           ((gamma:real->A)(s pow 2))`] P2A_LGEOD_SLICE_VEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^N`) THEN
  REWRITE_TAC[p2a_lsint] THEN
  SUBGOAL_THEN
   `!c. c = b \/ c = s pow 2
        ==> vector_derivative
              (\v. SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                               (real->A->real^N^N)) (tt - s pow 2))
                                ((gamma:real->A)(s pow 2))) (gamma(drop v pow 2)))
              (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= c}) = w`
  (fun th -> SIMP_TAC[th]) THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < c /\ s pow 2 <= c /\ c <= b` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= c} = interval[vec 0,lift(sqrt c)]`
  SUBST1_TAC THENL [MATCH_MP_TAC P2A_SDOM_INTERVAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_SIMP_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1; SQRT_POS_LT; REAL_LE_RSQRT;
               REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; LIFT_DROP] THEN
  X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt c pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]]);;

(* ========================================================================= *)
(* Joint continuity of the s-integrand (s, Z) |-> p2a_lsint of the           *)
(* L-geodesic gamma_Z on [0, sqrt b] x Ldom(b) (P2A_LSINT_JOINT). Near s0 >  *)
(* 0 the integrand is the L-Lagrangian of the chart flow started at s1 < s0  *)
(* (P2A_LPROP_NEAR, P2A_LSINT_FLOW), near s0 = 0 of the flow from (phi x, 2  *)
(* Z) (P2A_LSINT_START); both are continuous (P2A_LLAG_FLOW_CONTINUOUS).     *)
(* ========================================================================= *)

let P2A_REGION_LSMOOTH = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' U (phi:A->real^N) tt sa sb.
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\ sa < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b')
     ==> p2a_lsmooth (IMAGE phi (U INTER W)) sa sb
                     (\s. p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`subtopology (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) b') W`;
    `restrict_atlas (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b') W`;
    `a':real`; `b':real`; `p2a_rmetric (V:(real->A topology)#
                             (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'`;
    `(U INTER W:A->bool,phi:A->real^N)`; `tt:real`; `sa:real`; `sb:real`] P2A_UPTO_SFAMILY) THEN
  REWRITE_TAC[p2a_rlocal; FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) W a' b'` THEN
  REWRITE_TAC[p2a_region] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]);;

let P2A_LSINT_FLOW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z s1 s W a' b' U (phi:A->real^N) r (P:real^(N,N)finite_sum) gamma1 gamma b.
     p2a_svs V /\ p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\
     &0 < r /\ (!s'. abs(s' - s1) < r ==> a' < tt - s' pow 2 /\ tt - s' pow 2 <= b') /\
     p2a_Lgeod_from V tt x Z (s1 pow 2) gamma1 /\ gamma1(s1 pow 2) IN U INTER W /\
     phi(gamma1(s1 pow 2)) = fstcart P /\
     ((\v. phi(gamma1(drop v pow 2))) has_vector_derivative sndcart P)
       (at (lift s1) within {v | &0 <= drop v /\ drop v pow 2 <= s1 pow 2}) /\
     &0 < s1 /\ s1 < s /\ s < s1 + r /\
     pastecart (lift s) (pastecart (lift s1) P) IN
       ode_domain (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
         (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N))) /\
     p2a_Lgeod_from V tt x Z b gamma /\ s pow 2 <= b
     ==> p2a_lsint V tt gamma b s =
         p2a_llag (p2a_rlocal V W b' (U INTER W,phi)) tt s
           (fstcart(ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                      (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                       (IMAGE phi (U INTER W) PCROSS (:real^N)))
                      (lift s) (pastecart (lift s1) P)))
           (sndcart(ode_flow (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
                      (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                       (IMAGE phi (U INTER W) PCROSS (:real^N)))
                      (lift s) (pastecart (lift s1) P)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `s1 - r`; `s1 + r`] P2A_REGION_LSMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b'
                   (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(s1 - r),lift(s1 + r)) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z = pastecart (lift s1) (P:real^(N,N)finite_sum)` THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `lift s`;
                 `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fstcart(z:real^(1,(N,N)finite_sum)finite_sum) = lift s1 /\
                sndcart z = (P:real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = ode_maxint (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D z` THEN
  SUBGOAL_THEN `sqrt(s1 pow 2) = s1 /\ sqrt(s pow 2) = s /\ s1 pow 2 < s pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`;
                 `tt:real`; `x:A`; `Z:real^N`; `gamma1:real->A`; `s1 pow 2`; `s pow 2`;
                 `W:A->bool`; `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1 - r`; `s1 + r`;
                 `\t. fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                       D t z)`;
                 `\t. sndcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                       D t z)`;
                 `J:real^1->bool`] P2A_LGEOD_FROM_GLUE) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `gamma' = \tau. if tau <= s1 pow 2 then (gamma1:real->A) tau
                             else chart_inv (U INTER W,phi:A->real^N)
                                    (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->
                                                         real^(N,N)finite_sum) D (lift(sqrt tau)) z))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(!tau. (if tau <= s1 pow 2 then (gamma1:real->A) tau
            else chart_inv (U INTER W,phi:A->real^N)
                   (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                     D (lift(sqrt tau)) z))) = gamma' tau) /\
    ((if s pow 2 <= s1 pow 2 then (gamma1:real->A)(s pow 2)
     else chart_inv (U INTER W,phi:A->real^N)
            (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                              D (lift s) z))) = gamma'(s pow 2))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "gamma'" THEN REWRITE_TAC[];
      EXPAND_TAC "gamma'" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x Z (s pow 2) (gamma:real->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LGEOD_FROM_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `s pow 2`;
                 `gamma:real->A`; `gamma':real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt (gamma:real->A) b /\
                p2a_Lgeod V tt (gamma':real->A) (s pow 2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Lgeod_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`]
                P2A_LSINT_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `gamma':real->A`;
                 `s pow 2`; `s:real`] P2A_LSINT_AGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rhs(concl th) = `fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                      D (lift s) z)`)) THEN
  MATCH_MP_TAC P2A_LSINT_CHART THEN EXISTS_TAC `a':real` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2A_LSINT_START = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z W a U (phi:A->real^N) s gamma b.
     p2a_svs V /\ p2a_region V W a tt /\ x IN W /\ chart_at (p2a_vatlas V tt) x = (U,phi) /\
     &0 <= s /\
     pastecart (lift s) (pastecart (vec 0) (pastecart (phi x) (&2 % Z))) IN
       ode_domain (p2a_lfield (p2a_rlocal V W tt (U INTER W,phi)) tt)
         (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
          (IMAGE phi (U INTER W) PCROSS (:real^N))) /\
     p2a_Lgeod_from V tt x Z b gamma /\ s pow 2 <= b
     ==> p2a_lsint V tt gamma b s =
         p2a_llag (p2a_rlocal V W tt (U INTER W,phi)) tt s
           (fstcart(ode_flow (p2a_lfield (p2a_rlocal V W tt (U INTER W,phi)) tt)
                      (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                       (IMAGE phi (U INTER W) PCROSS (:real^N)))
                      (lift s) (pastecart (vec 0) (pastecart (phi x) (&2 % Z)))))
           (sndcart(ode_flow (p2a_lfield (p2a_rlocal V W tt (U INTER W,phi)) tt)
                      (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                       (IMAGE phi (U INTER W) PCROSS (:real^N)))
                      (lift s) (pastecart (vec 0) (pastecart (phi x) (&2 % Z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < tt` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_region; p2a_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`;
                 `W:A->bool`; `a:real`; `tt:real`; `tt:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\ (x:A) IN U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  ABBREV_TAC `r = sqrt(tt - a)` THEN
  SUBGOAL_THEN `&0 < r /\ r pow 2 = tt - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `--r`; `r:real`] P2A_REGION_LSMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t pow 2 < r pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  ABBREV_TAC `f = p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt` THEN
  ABBREV_TAC `D = interval(lift(--r),lift r) PCROSS
                  (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z = pastecart (vec 0:real^1) (pastecart ((phi:A->real^N) x) (&2 % (Z:real^N)))` THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`; `lift s`;
                 `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_IN_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `z:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fstcart(z:real^(1,(N,N)finite_sum)finite_sum) = vec 0 /\
                sndcart z = pastecart ((phi:A->real^N) x) (&2 % (Z:real^N))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = ode_maxint (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D z` THEN
  SUBGOAL_THEN `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt (gamma:real->A) b /\ gamma(&0) = x /\
                ((\v. (phi:A->real^N)(gamma(drop v pow 2))) has_vector_derivative (&2 % Z))
                  (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x Z b (gamma:real->A)` THEN
    ASM_REWRITE_TAC[p2a_Lgeod_from] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIFT_NUM]) THEN REWRITE_TAC[LIFT_NUM] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `&0`;
                   `W:A->bool`; `a:real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                   `&2 % (Z:real^N)`] P2A_LSINT_CHART) THEN
    ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO; REAL_LE_REFL; LIFT_NUM;
                    IN_INTER] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[p2a_Lgeod];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ sqrt(s pow 2) = s /\ s < r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; POW_2_SQRT; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `J:real^1->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`;
                 `tt:real`; `x:A`; `Z:real^N`; `W:A->bool`; `a:real`; `U:A->bool`; `phi:A->real^N`;
                 `\t. fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                       D t z)`;
                 `\t. sndcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                       D t z)`;
                 `J:real^1->bool`; `s:real`] P2A_LGEOD_FROM_SOL) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND; ETA_AX; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  STRIP_TAC THEN
  ABBREV_TAC `gamma' = \tau. chart_inv (U INTER W:A->bool,phi:A->real^N)
                         (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                           D (lift(sqrt tau)) z))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `(!tau. chart_inv (U INTER W:A->bool,phi:A->real^N)
             (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                               D (lift(sqrt tau)) z)) = gamma' tau) /\
    (chart_inv (U INTER W:A->bool,phi:A->real^N)
       (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                         D (lift s) z)) = gamma'(s pow 2))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "gamma'" THEN REWRITE_TAC[];
      EXPAND_TAC "gamma'" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x Z (s pow 2) (gamma:real->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LGEOD_FROM_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `s pow 2`;
                 `gamma:real->A`; `gamma':real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt (gamma':real->A) (s pow 2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_Lgeod_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`]
                P2A_LSINT_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `gamma':real->A`;
                 `s pow 2`; `s:real`] P2A_LSINT_AGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    rhs(concl th) = `fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum)
                                      D (lift s) z)`)) THEN
  MATCH_MP_TAC P2A_LSINT_CHART THEN EXISTS_TAC `a:real` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN
  SUBGOAL_THEN `s pow 2 < r pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2A_LPROP_NEAR = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z0 b0 Tm.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b0 /\ &0 < Tm /\ Tm pow 2 <= b0
     ==> ?s1 r W2 a2 b2 U2 (phi2:A->real^N) N2 (Phi2:real^N->real^(N,N)finite_sum).
           &0 < s1 /\ s1 < Tm /\ &0 < r /\ Tm < s1 + r /\
           p2a_region V W2 a2 b2 /\ (U2,phi2) IN p2a_vatlas V b2 /\
           (!s'. abs(s' - s1) < r ==> a2 < tt - s' pow 2 /\ tt - s' pow 2 <= b2) /\
           open N2 /\ Z0 IN N2 /\ smooth_map_on N2 Phi2 /\
           (!Z. Z IN N2
                ==> ?gamma. p2a_Lgeod_from V tt x Z (s1 pow 2) gamma /\
                            gamma(s1 pow 2) IN U2 INTER W2 /\
                            phi2(gamma(s1 pow 2)) = fstcart(Phi2 Z) /\
                            ((\v. phi2(gamma(drop v pow 2))) has_vector_derivative
                             sndcart(Phi2 Z))
                              (at (lift s1) within
                               {v | &0 <= drop v /\ drop v pow 2 <= s1 pow 2})) /\
           pastecart (lift Tm) (pastecart (lift s1) (Phi2 Z0)) IN
             ode_domain (p2a_lfield (p2a_rlocal V W2 b2 (U2 INTER W2,phi2)) tt)
               (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                (IMAGE phi2 (U2 INTER W2) PCROSS (:real^N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `b0:real`]
                P2A_LPROP_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                         (real->A->real^N^N)) tt x b0` THEN
  REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `gamma0:real->A`) THEN
  SUBGOAL_THEN `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt (gamma0:real->A) b0`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma0:real->A`; `b0:real`; `Tm:real`]
                P2A_LGEOD_PIECE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:A->bool` (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real`
    (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N` (X_CHOOSE_THEN `d:real`
    (X_CHOOSE_THEN `A:real^1->real^N` STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `del = min d Tm` THEN
  SUBGOAL_THEN `&0 < del /\ del <= d /\ del <= Tm` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s1 = Tm - del / &3` THEN
  ABBREV_TAC `r = del / &2` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < Tm /\ &0 < r /\ Tm < s1 + r /\ Tm - s1 < d /\
                (!s'. abs(s' - s1) < r ==> abs(s' - Tm) < d)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN EXPAND_TAC "r" THEN REPEAT CONJ_TAC THEN TRY GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s1 pow 2 /\ s1 pow 2 <= b0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Tm pow 2` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the propagation data at s1 *)
  FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lprop")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[p2a_lprop]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:real^N->bool` (X_CHOOSE_THEN `W1:A->bool`
    (X_CHOOSE_THEN `a1:real` (X_CHOOSE_THEN `b1:real` (X_CHOOSE_THEN `U1:A->bool`
    (X_CHOOSE_THEN `phi1:A->real^N` (X_CHOOSE_THEN `r1:real`
    (X_CHOOSE_THEN `Phi1:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma1:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z0:real^N) IN N1`) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Lgeod_from")) (concl th))) THEN
  SUBGOAL_THEN `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x Z0 (s1 pow 2) (gamma0:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LGEOD_FROM_RESTRICT THEN EXISTS_TAC `b0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1 pow 2`;
                 `gamma1:real->A`; `gamma0:real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma0:real->A)(s1 pow 2) IN U2 INTER W2 /\
                a2 < tt - s1 pow 2 /\ tt - s1 pow 2 <= b2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `U2:A->bool`)) (concl th) &&
        not (can (find_term ((=) `A:real^1->real^N`)) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lfield"))
                            (concl th)))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `b2:real`)) (concl th) &&
        can (find_term ((=) `d:real`)) (concl th) &&
        not (can (find_term ((=) `U2:A->bool`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s1 pow 2) = gamma0(s1 pow 2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart((Phi1:real^N->real^(N,N)finite_sum) Z0) IN
                IMAGE (phi1:A->real^N) ((U1 INTER W1) INTER (U2 INTER W2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gamma0:real->A)(s1 pow 2)` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `(gamma1:real->A)(s1 pow 2) = gamma0(s1 pow 2)`)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* move to the chart of gamma0 at Tm *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1:real`;
                 `N1:real^N->bool`; `W1:A->bool`; `a1:real`; `b1:real`; `U1:A->bool`;
                 `phi1:A->real^N`; `r1:real`; `Phi1:real^N->real^(N,N)finite_sum`;
                 `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`]
                P2A_LPROP_CHANGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:real^N->bool`
    (X_CHOOSE_THEN `Phi2:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma2:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z0:real^N) IN N2`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `N2:real^N->bool`)) (concl th))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `s1 pow 2`;
                 `gamma2:real->A`; `gamma0:real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma2:real->A)(s1 pow 2) = gamma0(s1 pow 2)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `sndcart((Phi2:real^N->real^(N,N)finite_sum) Z0) = (A:real^1->real^N)(lift s1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_SVEL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`\v:real^1. (phi2:A->real^N)((gamma2:real->A)(drop v pow 2))`;
                          `\v:real^1. (phi2:A->real^N)((gamma0:real->A)(drop v pow 2))`;
                          `s1 pow 2`; `b0:real`; `s1:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `lift s1` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `A:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Phi2:real^N->real^(N,N)finite_sum) Z0 =
    (\u:real^1. pastecart ((phi2:A->real^N)((gamma0:real->A)(drop u pow 2)))
                          ((A:real^1->real^N) u)) (lift s1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi2:A->real^N)((gamma2:real->A)(s1 pow 2)) =
                  fstcart((Phi2:real^N->real^(N,N)finite_sum) Z0)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s'. abs(s' - s1) < r ==> a2 < tt - s' pow 2 /\ tt - s' pow 2 <= b2`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `b2:real`)) (concl th) &&
      can (find_term ((=) `d:real`)) (concl th) &&
      not (can (find_term ((=) `U2:A->bool`)) (concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pastecart (lift Tm) (pastecart (lift s1) ((Phi2:real^N->real^(N,N)finite_sum) Z0)) IN
    ode_domain (p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                          (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2:A->real^N)) tt)
      (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi2 (U2 INTER W2) PCROSS (:real^N)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs(concl th) = `(Phi2:real^N->real^(N,N)finite_sum) Z0`)) THEN
    MATCH_MP_TAC P2A_ODE_DOMAIN_SEG THEN
    MAP_EVERY EXISTS_TAC
     [`interval(lift(Tm - d),lift(Tm + d)) PCROSS
       (IMAGE (phi2:A->real^N) (U2 INTER W2) PCROSS (:real^N))`;
      `{u:real^1 | &0 <= drop u /\ drop u pow 2 <= b0 /\ abs(drop u - Tm) < d}`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
      X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tm pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; PASTECART_IN_PCROSS; IN_UNIV] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `r:real`; `W2:A->bool`; `a2:real`; `b2:real`;
                        `U2:A->bool`; `phi2:A->real^N`; `N2:real^N->bool`;
                        `Phi2:real^N->real^(N,N)finite_sum`] THEN
  ASM_REWRITE_TAC[]);;

let P2A_CONTINUOUS_WITHIN_LOCAL_EQ = prove
 (`!(f:real^M->real^N) g Q T x.
     open Q /\ x IN Q /\ x IN T /\ g continuous_on Q /\
     (!y. y IN Q /\ y IN T ==> f y = g y)
     ==> f continuous (at x within T)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `Q:real^M->bool`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `open(Q:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `e:real`] THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_WITHIN] THEN
  X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ball(x:real^M,e) SUBSET Q` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let P2A_LLAG_FLOW_CONTINUOUS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (Q:real^M->bool)
    (Zm:real^M->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum).
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ Zm continuous_on Q /\
     (!z. z IN Q ==> Zm z IN ode_domain (p2a_lfield Gt tt)
                               (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N))))
     ==> (\z. lift(p2a_llag Gt tt (drop(fstcart(Zm z)))
                    (fstcart(ode_flow (p2a_lfield Gt tt)
                               (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))
                               (fstcart(Zm z)) (sndcart(Zm z))))
                    (sndcart(ode_flow (p2a_lfield Gt tt)
                               (interval(lift sa,lift sb) PCROSS (U PCROSS (:real^N)))
                               (fstcart(Zm z)) (sndcart(Zm z)))))) continuous_on Q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN
  ABBREV_TAC `f = p2a_lfield (Gt:real->real^N->real^N^N) tt` THEN
  ABBREV_TAC `D = interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
  MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D
        ==> pastecart (fstcart w) (ode_flow f D (fstcart w) (sndcart w)) IN D`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ODE_IN_DOMAIN_ALT] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                   `sndcart(w:real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum)`] ODE_MAXIMAL_SOLUTION) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(p2a_llag (Gt:real->real^N->real^N^N) tt
                (drop(fstcart((Zm:real^M->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z)))
                (fstcart(ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D
                           (fstcart(Zm z)) (sndcart(Zm z))))
                (sndcart(ode_flow f D (fstcart(Zm z)) (sndcart(Zm z)))))) =
    (\w. lift(p2a_llag Gt tt (drop(fstcart w)) (fstcart(sndcart w)) (sndcart(sndcart w)))) o
    (\z. pastecart (fstcart(Zm z)) (ode_flow f D (fstcart(Zm z)) (sndcart(Zm z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z. fstcart((Zm:real^M->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z)) =
                    fstcart o Zm` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z. ode_flow (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D
             (fstcart((Zm:real^M->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z)) (sndcart(Zm z))) =
      (\w. ode_flow f D (fstcart w) (sndcart w)) o Zm`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ode_domain (f:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^(1,(N,N)finite_sum)finite_sum->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "D" THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `D:real^(1,(N,N)finite_sum)finite_sum->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pastecart")) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

let P2A_LSINT_CONT_POS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b s0 Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b /\ &0 < s0 /\ s0 pow 2 <= b
     ==> (\z. lift(p2a_lsint V tt (p2a_Lgeo V tt x (sndcart z) b) b (drop(fstcart z))))
         continuous (at (pastecart (lift s0) Z0) within
                     (interval[vec 0,lift(sqrt b)] PCROSS p2a_Ldom V tt x b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z0:real^N`; `b:real`; `s0:real`]
                P2A_LPROP_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `W2:A->bool`
    (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real` (X_CHOOSE_THEN `U2:A->bool`
    (X_CHOOSE_THEN `phi2:A->real^N` (X_CHOOSE_THEN `N2:real^N->bool`
    (X_CHOOSE_THEN `Phi2:real^N->real^(N,N)finite_sum` STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`;
                 `phi2:A->real^N`; `tt:real`; `s1 - r`; `s1 + r`] P2A_REGION_LSMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `Zm = \z:real^(1,N)finite_sum.
                     pastecart (fstcart z)
                       (pastecart (lift s1) ((Phi2:real^N->real^(N,N)finite_sum) (sndcart z)))` THEN
  ABBREV_TAC `Q = {z:real^(1,N)finite_sum |
                   z IN interval(lift s1,lift(s1 + r)) PCROSS N2 /\
                   (Zm:real^(1,N)finite_sum->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z IN
                   ode_domain (p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2:A->real^N)) tt)
                     (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                      (IMAGE phi2 (U2 INTER W2) PCROSS (:real^N)))}` THEN
  SUBGOAL_THEN `(Zm:real^(1,N)finite_sum->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum)
                continuous_on (interval(lift s1,lift(s1 + r)) PCROSS N2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Zm" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (Phi2:real^N->real^(N,N)finite_sum) (sndcart z)) =
                  Phi2 o sndcart` SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `N2:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(Q:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2:A->real^N)) tt`;
                   `interval(lift(s1 - r),lift(s1 + r)) PCROSS
                    (IMAGE (phi2:A->real^N) (U2 INTER W2) PCROSS (:real^N))`] ODE_FLOW_SMOOTH) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_CONTINUOUS_WITHIN_LOCAL_EQ THEN
  EXISTS_TAC
   `\z:real^(1,N)finite_sum.
      lift(p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) W2 b2 (U2 INTER W2,phi2:A->real^N)) tt
             (drop(fstcart((Zm:real^(1,N)finite_sum->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z)))
             (fstcart(ode_flow (p2a_lfield (p2a_rlocal V W2 b2 (U2 INTER W2,phi2)) tt)
                        (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                         (IMAGE phi2 (U2 INTER W2) PCROSS (:real^N)))
                        (fstcart(Zm z)) (sndcart(Zm z))))
             (sndcart(ode_flow (p2a_lfield (p2a_rlocal V W2 b2 (U2 INTER W2,phi2)) tt)
                        (interval(lift(s1 - r),lift(s1 + r)) PCROSS
                         (IMAGE phi2 (U2 INTER W2) PCROSS (:real^N)))
                        (fstcart(Zm z)) (sndcart(Zm z)))))` THEN
  EXISTS_TAC `Q:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Q" THEN EXPAND_TAC "Zm" THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RSQRT];
    MATCH_MP_TAC P2A_LLAG_FLOW_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift s1,lift(s1 + r)) PCROSS (N2:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN SET_TAC[];
      EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^(1,N)finite_sum` THEN
  SUBGOAL_THEN `?s (Z:real^N). y = pastecart (lift s) Z`
  (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `Z:real^N` SUBST1_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(y:real^(1,N)finite_sum))`;
                          `sndcart(y:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  EXPAND_TAC "Q" THEN EXPAND_TAC "Zm" THEN
  REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  STRIP_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `gamma1:real->A` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(Z:real^N) IN N2`) o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `N2:real^N->bool`)) (concl th))) THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `s0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_LSINT_FLOW THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `Z:real^N`; `a2:real`; `gamma1:real->A`] THEN
  ASM_SIMP_TAC[P2A_LGEO_PROP]);;

let P2A_LSINT_CONT_ZERO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z0.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z0 IN p2a_Ldom V tt x b
     ==> (\z. lift(p2a_lsint V tt (p2a_Lgeo V tt x (sndcart z) b) b (drop(fstcart z))))
         continuous (at (pastecart (lift(&0)) Z0) within
                     (interval[vec 0,lift(sqrt b)] PCROSS p2a_Ldom V tt x b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) x tt` THEN
  REWRITE_TAC[p2a_bsmooth] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)`;
                 `W:A->bool`; `a:real`; `tt:real`; `tt:real`] P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))` THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))` THEN
  SUBGOAL_THEN `chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A) = (U,phi:A->real^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\ (x:A) IN U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(tt - a) /\ sqrt(tt - a) pow 2 = tt - a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_SUB_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `--sqrt(tt - a)`; `sqrt(tt - a)`]
                P2A_REGION_LSMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t pow 2 < sqrt(tt - a) pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LFIELD_ODE_FACTS) THEN
  ABBREV_TAC `Zm = \z:real^(1,N)finite_sum.
                     pastecart (fstcart z)
                       (pastecart (vec 0:real^1)
                          (pastecart ((phi:A->real^N) x) (&2 % sndcart z)))` THEN
  ABBREV_TAC `Q = {z:real^(1,N)finite_sum |
                   z IN interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS (:real^N) /\
                   (Zm:real^(1,N)finite_sum->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z IN
                   ode_domain (p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt)
                     (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                      (IMAGE phi (U INTER W) PCROSS (:real^N)))}` THEN
  SUBGOAL_THEN `(Zm:real^(1,N)finite_sum->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum)
                continuous_on (:real^(1,N)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Zm" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(Q:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt`;
                   `interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`] ODE_FLOW_SMOOTH) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_CONTINUOUS_WITHIN_LOCAL_EQ THEN
  EXISTS_TAC
   `\z:real^(1,N)finite_sum.
      lift(p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt
             (drop(fstcart((Zm:real^(1,N)finite_sum->real^(1,(1,(N,N)finite_sum)finite_sum)finite_sum) z)))
             (fstcart(ode_flow (p2a_lfield (p2a_rlocal V W tt (U INTER W,phi)) tt)
                        (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                         (IMAGE phi (U INTER W) PCROSS (:real^N)))
                        (fstcart(Zm z)) (sndcart(Zm z))))
             (sndcart(ode_flow (p2a_lfield (p2a_rlocal V W tt (U INTER W,phi)) tt)
                        (interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                         (IMAGE phi (U INTER W) PCROSS (:real^N)))
                        (fstcart(Zm z)) (sndcart(Zm z)))))` THEN
  EXISTS_TAC `Q:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Q" THEN EXPAND_TAC "Zm" THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIFT_NUM; ODE_IN_DOMAIN] THEN
    SUBGOAL_THEN `pastecart (vec 0:real^1) (pastecart ((phi:A->real^N) x) (&2 % (Z0:real^N))) IN
                  interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                  (IMAGE phi (U INTER W) PCROSS (:real^N))` ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_UNIV] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt`;
                   `interval(lift(--sqrt(tt - a)),lift(sqrt(tt - a))) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `pastecart (vec 0:real^1) (pastecart ((phi:A->real^N) x) (&2 % (Z0:real^N)))`]
                  ODE_MAXINT_INITIAL) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART];
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; SQRT_POS_LE] THEN
    SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
     [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                     (real->A->real^N^N)) tt x b` THEN
      REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]];
    MATCH_MP_TAC P2A_LLAG_FLOW_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^(1,N)finite_sum` THEN
  SUBGOAL_THEN `?s (Z:real^N). y = pastecart (lift s) Z`
  (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `Z:real^N` SUBST1_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(y:real^(1,N)finite_sum))`;
                          `sndcart(y:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  EXPAND_TAC "Q" THEN EXPAND_TAC "Zm" THEN
  REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              IN_INTERVAL_1; LIFT_DROP; DROP_VEC; IN_UNIV] THEN
  STRIP_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `s pow 2 <= b` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      UNDISCH_TAC `(Z:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                     (real->A->real^N^N)) tt x b` THEN
      REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN
      MESON_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_LSINT_START THEN
  ASM_SIMP_TAC[P2A_LGEO_PROP]);;

let P2A_LSINT_JOINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> (\z. lift(p2a_lsint V tt (p2a_Lgeo V tt x (sndcart z) b) b (drop(fstcart z))))
         continuous_on (interval[vec 0,lift(sqrt b)] PCROSS p2a_Ldom V tt x b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN
  SUBGOAL_THEN `?s (Z:real^N). z = pastecart (lift s) Z`
  (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `Z:real^N` SUBST1_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(z:real^(1,N)finite_sum))`;
                          `sndcart(z:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_LSINT_CONT_ZERO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_LSINT_CONT_POS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]]);;


(* ========================================================================= *)
(* The L-length in the variable s (P2A_L_LENGTH_SFORM, substitution tau =    *)
(* s^2), continuity of parametric real integrals                             *)
(* (P2A_PARAM_REAL_INTEGRAL_CONTINUOUS), continuity of l~ and of the         *)
(* reduced-volume integrand (P2A_LTIL_CONTINUOUS, P2A_RVI_CONTINUOUS, L1     *)
(* clause 6), and L1 itself: P2A_LGEOD_FLOW_GEN (generic N) and              *)
(* P2A_LGEOD_FLOW (the statement at N = 3).                                  *)
(* ========================================================================= *)

let P2A_L_LENGTH_SFORM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\
     (p2a_lsint V tt gamma b) real_continuous_on real_interval[&0,sqrt b]
     ==> (p2a_L_integrand V tt gamma b has_real_integral
          real_integral (real_interval[&0,sqrt b]) (p2a_lsint V tt gamma b))
           (real_interval[&0,b]) /\
         p2a_L_length V tt gamma b =
         real_integral (real_interval[&0,sqrt b]) (p2a_lsint V tt gamma b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[p2a_L_length] THEN MESON_TAC[REAL_INTEGRAL_UNIQUE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt gamma b`;
                 `sqrt`; `\x. inv(&2 * sqrt x)`; `&0`; `b:real`; `&0`; `sqrt b`; `{&0}`]
                HAS_REAL_INTEGRAL_SUBSTITUTION_STRONG) THEN
  REWRITE_TAC[SQRT_0; COUNTABLE_SING; REAL_CONTINUOUS_ON_SQRT; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE];
      ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt gamma b) real_continuous_on real_interval[&0,sqrt b]` THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; SQRT_POS_LE; SQRT_MONO_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
  X_GEN_TAC `y:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `y = &0` THENL
   [ASM_REWRITE_TAC[SQRT_0; REAL_MUL_RZERO; REAL_INV_0; p2a_L_integrand; REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt y /\ sqrt y pow 2 = y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `sqrt y`]
                P2A_LINT_SINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `&0 < sqrt y` THEN CONV_TAC REAL_FIELD);;

let P2A_PARAM_REAL_INTEGRAL_CONTINUOUS = prove
 (`!(h:real^N->real->real) a b K.
     a <= b /\ compact K /\
     (\z. lift(h (sndcart z) (drop(fstcart z)))) continuous_on
       (interval[lift a,lift b] PCROSS K)
     ==> (!Z. Z IN K ==> (h Z) real_continuous_on real_interval[a,b]) /\
         (\Z. lift(real_integral (real_interval[a,b]) (h Z))) continuous_on K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!Z:real^N. Z IN K ==> (h Z) real_continuous_on real_interval[a,b]`
  ASSUME_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
    SUBGOAL_THEN `lift o (h:real^N->real->real) Z o drop =
                  (\z. lift(h (sndcart z) (drop(fstcart z)))) o (\t. pastecart t Z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[lift a,lift b] PCROSS (K:real^N->bool)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. lift((h:real^N->real->real) (sndcart z) (drop(fstcart z)))`;
                 `interval[lift a,lift b] PCROSS (K:real^N->bool)`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; uniformly_continuous_on] THEN DISCH_TAC THEN
  REWRITE_TAC[continuous_on] THEN
  X_GEN_TAC `Z0:real^N` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (b - a + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `Z:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real->real) Z real_integrable_on real_interval[a,b] /\
                h Z0 real_integrable_on real_interval[a,b]` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS]; ALL_TAC] THEN
  REWRITE_TAC[DIST_LIFT] THEN ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e / (b - a + &1) * (b - a)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_BOUND THEN
    EXISTS_TAC `\s. (h:real^N->real->real) Z s - h Z0 s` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift s) (Z0:real^N)`;
                                    `pastecart (lift s) (Z:real^N)`]) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DIST_PASTECART_CANCEL;
                      FSTCART_PASTECART; SNDCART_PASTECART; DIST_LIFT] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 < b - a + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> e / c * x = (e * x) / c`; REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC]);;

let P2A_LTIL_CONTINUOUS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> (\Z. lift(p2a_ltil V tt x b Z)) continuous_on p2a_Ldom V tt x b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `Z0:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z0:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                   (real->A->real^N^N)) tt x b` THEN
    REWRITE_TAC[p2a_Ldom; IN_ELIM_THM; p2a_Lgeod_from; p2a_Lgeod] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_LDOM_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `Z0:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\Z s. p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt (p2a_Lgeo V tt x Z b) b s`;
                 `&0`; `sqrt b`; `cball(Z0:real^N,e)`] P2A_PARAM_REAL_INTEGRAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; COMPACT_CBALL; LIFT_NUM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[vec 0,lift(sqrt b)] PCROSS
                p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x b` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_LSINT_JOINT) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; GEOL_IN_PCROSS] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `cball(Z0:real^N,e)` THEN
  ASM_SIMP_TAC[INTERIOR_CBALL; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\Z. inv(&2 * sqrt b) %
                  lift(real_integral (real_interval[&0,sqrt b])
                         (\s. p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                         (real->A->real^N^N)) tt (p2a_Lgeo V tt x Z b) b s))` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CMUL] THEN
  X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) tt x b` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2a_ltil; p2a_Ltil; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt x Z b`; `b:real`] P2A_L_LENGTH_SFORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[P2A_LGEO_PROP; p2a_Lgeod_from];
      FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N` o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "real_continuous_on")) (concl th))) THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[ETA_AX] THEN
  REWRITE_TAC[real_div; REAL_MUL_SYM]);;

let P2A_RVI_CONTINUOUS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> (\Z. lift(p2a_rvi V tt x b Z)) continuous_on p2a_Ldom V tt x b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\Z. exp(--(p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt x b Z)) %
                  (inv(sqrt b pow dimindex(:N)) % lift(p2a_J V tt x b Z))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[p2a_rvi; GSYM LIFT_CMUL; VECTOR_MUL_ASSOC; real_div] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `lift o (\Z. exp(--(p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt x b Z))) =
      (lift o exp o drop) o (\Z. --(lift(p2a_ltil V tt x b Z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_NEG THEN MATCH_MP_TAC P2A_LTIL_CONTINUOUS THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPEC `(:real)` REAL_CONTINUOUS_ON_EXP) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_UNIV]];
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC P2A_J_CONTINUOUS THEN
    ASM_REWRITE_TAC[]]);;

let P2A_LGEOD_FLOW_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> (!Z b gamma gamma'.
             p2a_Lgeod_from V tt x Z b gamma /\ p2a_Lgeod_from V tt x Z b gamma'
             ==> !tau. &0 <= tau /\ tau <= b ==> gamma tau = gamma' tau) /\
         (!Z b b'. Z IN p2a_Ldom V tt x b /\ &0 < b' /\ b' <= b
                   ==> Z IN p2a_Ldom V tt x b' /\
                       !tau. &0 <= tau /\ tau <= b'
                             ==> p2a_Lgeo V tt x Z b' tau = p2a_Lgeo V tt x Z b tau) /\
         (!Z. ?b. &0 < b /\ Z IN p2a_Ldom V tt x b) /\
         (!b. open(p2a_Ldom V tt x b)) /\
         (!b Z. Z IN p2a_Ldom V tt x b
                ==> (\W. SND(chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
                            (p2a_Lexp V tt x b W)) differentiable (at Z)) /\
         (!b. (\Z. lift(p2a_rvi V tt x b Z)) continuous_on p2a_Ldom V tt x b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LGEOD_UNIQUE THEN
    EXISTS_TAC `V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)` THEN
    MAP_EVERY EXISTS_TAC [`tt:real`; `x:A`; `Z:real^N`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LDOM_RESTRICT THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2A_LGEOD_EXISTS_LOCAL THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2A_LDOM_OPEN THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_LEXP_DIFFERENTIABLE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2A_RVI_CONTINUOUS THEN ASM_REWRITE_TAC[]]);;

let P2A_LGEOD_FLOW = prove
 (`!u:A->bool. P2A_LGEOD_FLOW_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_LGEOD_FLOW_STATEMENT; GSYM P2A_VIEW_PROJ_3] THEN
  MATCH_ACCEPT_TAC P2A_LGEOD_FLOW_GEN);;


