(* ========================================================================= *)
(* pc_p2a_inj: injectivity of Lexp on initial vectors of minimizers (MT Prop *)
(* 6.30 first half, with the corner-cutting argument that MT omits; L4 FIX). *)
(* The first part: backward uniqueness of L-geodesics: two L-geodesics that  *)
(* agree on [b1,b] (0 < b1 < b) agree on [0,b].                              *)
(* ========================================================================= *)

needs "src/pc_p2a_reg.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_LGEOD_BACK_CLOSED = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b Tm Tu.
     p2a_svs V /\ p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     &0 <= Tm /\ Tm < Tu /\ Tu pow 2 <= b /\
     (!s. Tm < s /\ s <= Tu ==> gamma1(s pow 2) = gamma2(s pow 2))
     ==> gamma1(Tm pow 2) = gamma2(Tm pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `Tm pow 2 <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tu pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(gamma1:real->A)(Tm pow 2) IN
      topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) (tt - Tm pow 2)) /\
    (gamma2:real->A)(Tm pow 2) IN topspace(p2a_vtop V (tt - Tm pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma1 b`;
      UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma2 b`] THEN
    REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - Tm pow 2))`
  MP_TAC THENL [ASM_MESON_TAC[p2a_svs]; ALL_TAC] THEN
  REWRITE_TAC[hausdorff_space] THEN
  DISCH_THEN(MP_TAC o SPECL [`(gamma1:real->A)(Tm pow 2)`; `(gamma2:real->A)(Tm pow 2)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:A->bool` (X_CHOOSE_THEN `O2:A->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `b:real`; `Tm:real`;
                 `O1:A->bool`] P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma2:real->A`; `b:real`; `Tm:real`;
                 `O2:A->bool`] P2A_LGEOD_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = Tm + min (min e1 e2) (Tu - Tm) / &2` THEN
  SUBGOAL_THEN `Tm < s /\ s <= Tu /\ &0 <= s /\ s pow 2 <= b /\
                abs(s - Tm) < e1 /\ abs(s - Tm) < e2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SUBGOAL_THEN `&0 < min (min e1 e2) (Tu - Tm)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tu pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s pow 2) IN O1 /\ (gamma2:real->A)(s pow 2) IN O2`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A)(s pow 2) = gamma2(s pow 2)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]);;

let P2A_LGEOD_BACK_OPEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b Tm Tu.
     p2a_svs V /\ p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     &0 < Tm /\ Tm < Tu /\ Tu pow 2 <= b /\
     (!s. Tm <= s /\ s <= Tu ==> gamma1(s pow 2) = gamma2(s pow 2))
     ==> ?e. &0 < e /\
             !s. &0 <= s /\ s pow 2 <= b /\ abs(s - Tm) < e
                 ==> gamma1(s pow 2) = gamma2(s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN `Tm pow 2 <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tu pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t0 = tt - Tm pow 2` THEN
  ABBREV_TAC `p = (gamma1:real->A)(Tm pow 2)` THEN
  SUBGOAL_THEN `(gamma2:real->A)(Tm pow 2) = p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(gamma1:real->A)(Tm pow 2) IN
                    topspace(p2a_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - Tm pow 2))`
    MP_TAC THENL
     [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt gamma1 b` THEN
      REWRITE_TAC[p2a_Lgeod] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0)
                  (p2a_vatlas V t0)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t0) (p:A)` THEN
  SUBGOAL_THEN `(c0:(A->bool)#(A->real^N)) IN p2a_vatlas V t0 /\ (p:A) IN FST c0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) t0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `b:real`; `Tm:real`;
                 `c0:(A->bool)#(A->real^N)`] P2A_LGEOD_SLICE_VEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma2:real->A`; `b:real`; `Tm:real`;
                 `c0:(A->bool)#(A->real^N)`] P2A_LGEOD_SLICE_VEL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N` ASSUME_TAC) THEN
  SUBGOAL_THEN `interval[lift Tm,lift Tu] SUBSET {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tu pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `w2:real^N = w1` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC
     [`\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma2:real->A)(drop v pow 2))`;
      `lift Tm`; `lift Tu`; `lift Tm`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC
       [`\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma1:real->A)(drop v pow 2))`;
        `&1`] THEN
      REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_LGEOD_LOCAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)`; `tt:real`; `c0:(A->bool)#(A->real^N)`;
                        `w1:real^N`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `((\v:real^1. SND(c0:(A->bool)#(A->real^N)) ((gamma2:real->A)(drop v pow 2)))
                has_vector_derivative w2)
               (at (lift Tm) within {v | &0 <= drop v /\ drop v pow 2 <= b})` THEN
  ASM_REWRITE_TAC[]);;

let P2A_LGEOD_BACK_UNIQUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma1 gamma2 b b1.
     p2a_svs V /\ p2a_Lgeod V tt gamma1 b /\ p2a_Lgeod V tt gamma2 b /\
     &0 < b1 /\ b1 < b /\
     (!tau. b1 <= tau /\ tau <= b ==> gamma1 tau = gamma2 tau)
     ==> !tau. &0 <= tau /\ tau <= b ==> gamma1 tau = gamma2 tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?S Sb. &0 < S /\ S < Sb /\ S pow 2 = b1 /\ Sb pow 2 = b`
    (X_CHOOSE_THEN `S:real` (X_CHOOSE_THEN `Sb:real` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`sqrt b1`; `sqrt b`] THEN
    SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; SQRT_MONO_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. S <= s /\ s <= Sb ==> (gamma1:real->A)(s pow 2) = gamma2(s pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [EXPAND_TAC "b1" THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. (gamma1:real->A)((S - r) pow 2) = gamma2((S - r) pow 2)`; `S:real`]
                P2A_REAL_CONT_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `gamma2:real->A`;
                     `b:real`; `S:real`; `Sb:real`] P2A_LGEOD_BACK_OPEN) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2A_LGEOD_BACK_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)`; `tt:real`; `b:real`; `Sb:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN P2A_ARITH_CONJS_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= S` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `S - s` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `S - (S - s) = s`]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `Tm:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma1:real->A`; `gamma2:real->A`;
                   `b:real`; `S - Tm`; `Sb:real`] P2A_LGEOD_BACK_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN P2A_ARITH_CONJS_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= S` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `S - s` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Tm:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `S - (S - s) = s`]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= Sb /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
  ASM_CASES_TAC `sqrt tau <= S` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `S - sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `S:real`)) (concl th) &&
      not (can (find_term ((=) `Sb:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `S - (S - x) = x`]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* L4 FIX.  If two minimizing L-geodesics from x meet at b1 < b, the        *)
(* broken curve (the second up to b1, then the first) has the same length   *)
(* as the first, so it is a minimizer, hence an L-geodesic from x with the  *)
(* initial vector of the second (L2 FIX); it is then the second, so the two *)
(* agree on [b1,b], hence everywhere (backward uniqueness), and the initial *)
(* vectors coincide.                                                        *)
(* ========================================================================= *)

(* The initial vector of an L-geodesic from x is determined by the curve.  *)

let P2A_LGEOD_FROM_INIT_UNIQUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z Z' b (g1:real->A) g2.
     p2a_Lgeod_from V tt x Z b g1 /\ p2a_Lgeod_from V tt x Z' b g2 /\
     (!tau. &0 <= tau /\ tau <= b ==> g1 tau = g2 tau)
     ==> Z = Z'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[vec 0,lift(sqrt b)] SUBSET {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `drop(v:real^1) pow 2 <= sqrt b pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 % (Z:real^N) = &2 % Z'` MP_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC
     [`\v:real^1. SND(chart_at (p2a_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))
         ((g1:real->A)(drop v pow 2))`;
      `vec 0:real^1`; `lift(sqrt b)`; `vec 0:real^1`] THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POS_LE; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC
       [`\v:real^1. SND(chart_at (p2a_vatlas (V:(real->A topology)#
           (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))
           ((g2:real->A)(drop v pow 2))`; `&1`] THEN
      REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; REAL_LE_REFL] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
        SUBGOAL_THEN `drop(y:real^1) pow 2 <= sqrt b pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= b}` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_OF_NUM_EQ; ARITH_EQ]]);;

(* A curve agreeing near 0 with an L-geodesic from x, and itself an        *)
(* L-geodesic, is an L-geodesic from x with the same initial vector.        *)

let P2A_LGEOD_FROM_NEAR0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z b b1 (gg:real->A) g2.
     p2a_Lgeod V tt gg b /\ p2a_Lgeod_from V tt x Z b g2 /\ &0 < b1 /\ b1 <= b /\
     (!tau. &0 <= tau /\ tau <= b1 ==> gg tau = g2 tau)
     ==> p2a_Lgeod_from V tt x Z b gg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS `(g2:real->A)(&0)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`\v:real^1. SND(chart_at (p2a_vatlas (V:(real->A topology)#
       (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (x:A))
       ((g2:real->A)(drop v pow 2))`; `sqrt b1`] THEN
  ASM_SIMP_TAC[SQRT_POS_LT] THEN
  REWRITE_TAC[IN_ELIM_THM; DROP_VEC; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_0; NORM_REAL; GSYM drop] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  SUBGOAL_THEN `drop(y:real^1) pow 2 <= sqrt b1 pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]]);;

(* L4, generic N.                                                            *)

let P2A_INJ_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b b1 Z Z'.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\
     Z IN p2a_Smin V tt x b /\ Z' IN p2a_Smin V tt x b /\ &0 < b1 /\ b1 < b /\
     p2a_Lexp V tt x b1 Z = p2a_Lexp V tt x b1 Z'
     ==> Z = Z'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Smin; IN_ELIM_THM; p2a_Lexp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `b:real`; `b1:real`]
                P2A_LDOM_RESTRICT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z':real^N`; `b:real`; `b1:real`]
                P2A_LDOM_RESTRICT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z:real^N`; `b:real`]
                P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z':real^N`; `b:real`]
                P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `g1 = p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt x Z b` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `g2 = p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt x Z' b` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(g1:real->A) b1 = g2 b1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= b1 /\ b1 <= b1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the restrictions to [0,b1] are minimizers with the same end point *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `b1:real`;
                 `g1:real->A`] P2A_MIN_RESTRICT_GEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `b1:real`;
                 `g2:real->A`] P2A_MIN_RESTRICT_GEN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  SUBGOAL_THEN `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt g2 b1 = p2a_L_length V tt g1 b1`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b1 g2` THEN
      REWRITE_TAC[p2a_min] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_MESON_TAC[p2a_min];
      UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b1 g1` THEN
      REWRITE_TAC[p2a_min] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_MESON_TAC[p2a_min]];
    ALL_TAC] THEN
  (* the broken curve *)
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt x b g1 /\
                p2a_adm V tt x b1 g2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `g1:real->A`; `g2:real->A`;
                 `\tau. if tau <= b1 then (g2:real->A) tau else g1 tau`; `b:real`; `b1:real`]
                P2A_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau:real = b1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `g1:real->A`; `b:real`;
                 `b1:real`] P2A_LENGTH_SPLIT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  ABBREV_TAC `gg = \tau. if tau <= b1 then (g2:real->A) tau else g1 tau` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(gg:real->A) b = g1 b /\ (!tau. tau <= b1 ==> gg tau = g2 tau) /\
                (!tau. b1 <= tau ==> gg tau = g1 tau)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b <= b1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `tau:real = b1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the broken curve is a minimizer, hence an L-geodesic from x with vector Z' *)
  SUBGOAL_THEN `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt x b gg`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_min] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `g3:real->A` THEN STRIP_TAC THEN
    UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b g1` THEN
    REWRITE_TAC[p2a_min] THEN DISCH_THEN(MP_TAC o SPEC `g3:real->A` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g3:real->A) b = g1 b` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gg:real->A`]
                P2A_MIN_LGEOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z':real^N`; `b:real`; `b1:real`;
                 `gg:real->A`; `g2:real->A`] P2A_LGEOD_FROM_NEAR0) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `Z':real^N`; `b:real`;
                 `gg:real->A`; `g2:real->A`] P2A_LGEOD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* hence the two minimizers agree on [b1,b], so everywhere *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `g1:real->A`; `g2:real->A`; `b:real`;
                 `b1:real`] P2A_LGEOD_BACK_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[p2a_Lgeod_from];
      ASM_MESON_TAC[p2a_Lgeod_from];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      TRANS_TAC EQ_TRANS `(gg:real->A) tau` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    DISCH_TAC] THEN
  MATCH_MP_TAC P2A_LGEOD_FROM_INIT_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`;
                        `g1:real->A`; `g2:real->A`] THEN
  ASM_REWRITE_TAC[]);;

let P2A_INJ_FIX = prove
 (`!u:A->bool. P2A_INJ_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_INJ_FIX_STATEMENT] THEN MESON_TAC[P2A_INJ_GEN]);;

(* ========================================================================= *)
(* The route obligations O7 and O8 against the FIX forms (their conclusions  *)
(* hold outright).                                                           *)
(* ========================================================================= *)

let P2A_ROUTE_MIN_LGEOD_FIX = prove
 (`!u:A->bool. P2A_ROUTE_MIN_LGEOD_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_ROUTE_MIN_LGEOD_FIX_STATEMENT; P2A_MIN_LGEOD_FIX]);;

let P2A_ROUTE_INJ_FIX = prove
 (`!u:A->bool. P2A_ROUTE_INJ_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_ROUTE_INJ_FIX_STATEMENT; P2A_INJ_FIX]);;

