(* ========================================================================= *)
(* Unit pc_p2a_wk4: the pointwise sharp barrier for the weak inequality T2   *)
(* (p2bw_t2) of W3.  The window framework of pc_p2a_ljac (windows p2al_lwin  *)
(* / p2al_wok, Jacobi data p2al_jy, p2al_jb, first variation P2AL_FV_ALL)    *)
(* and of pc_p2a_lmono (the comparison P2AL_GF_EQ, P2AL_GF_NONPOS) is used   *)
(* in a PRESCRIBED chart c of the atlas: the states of P2A_LPROP_ALL are     *)
(* transported to c by the chart transition, and the window flow in c        *)
(* reaches the end of a minimizer because its chart curve solves the         *)
(* L-geodesic system there.                                                  *)
(* ========================================================================= *)

needs "src/pc_p2a_wk6.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The maximal interval of the window flow, and a solution on a closed       *)
(* interval gives the window condition p2al_lin at its end.                  *)
(* ------------------------------------------------------------------------- *)

let P2AW_MAXINT_BETWEEN = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z s t.
     z IN D /\ t IN ode_maxint f D z /\ drop(fstcart z) <= drop s /\ drop s <= drop t
     ==> s IN ode_maxint f D z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_MAXINT_IS_INTERVAL) THEN
  REWRITE_TAC[IS_INTERVAL_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`fstcart(z:real^(1,N)finite_sum)`; `t:real^1`] THEN
  ASM_SIMP_TAC[ODE_MAXINT_INITIAL]);;

let P2AW_LIN_BETWEEN = prove
 (`!(V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s t.
     p2al_lin V tt s1 r W b' U phi Phi Z t /\ s1 <= s /\ s <= t
     ==> p2al_lin V tt s1 r W b' U phi Phi Z s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al_lin; ODE_IN_DOMAIN] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AW_MAXINT_BETWEEN THEN
  EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP]);;

let P2AW_SOLUTION_LIN = prove
 (`!(V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z t (u:real^1->real^(N,N)finite_sum).
     s1 <= t /\ u(lift s1) = Phi Z /\
     ode_solution (p2a_lfield (p2a_rlocal V W b' (U INTER W,phi)) tt)
       (interval(lift(s1 - r),lift(s1 + r)) PCROSS (IMAGE phi (U INTER W) PCROSS (:real^N)))
       (interval[lift s1,lift t]) u
     ==> p2al_lin V tt s1 r W b' U phi Phi Z t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2al_lin; ODE_IN_DOMAIN] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lift s1` o CONJUNCT2 o GEN_REWRITE_RULE I [ode_solution]) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN SIMP_TAC[];
    REWRITE_TAC[ODE_IN_MAXINT; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY EXISTS_TAC [`interval[lift s1,lift t]`; `u:real^1->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Transport of the L-geodesic states of P2A_LPROP_ALL at a time s1 into a   *)
(* prescribed chart (U,phi) of the atlas of a flow by the chart transition:  *)
(* a window p2al_lwin based at s1 in (U,phi), with region U, whenever the    *)
(* L-geodesic of Z0 is in U at s1.                                           *)
(* ------------------------------------------------------------------------- *)

let P2AW_VDERIV_CHAIN = prove
 (`!(Fc:real^1->real^N) (Tr:real^N->real^M) v x s.
     (Fc has_vector_derivative v) (at x within s) /\ Tr differentiable (at (Fc x))
     ==> ((Tr o Fc) has_vector_derivative (frechet_derivative Tr (at (Fc x)) v))
           (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t:real^1. drop t % frechet_derivative (Tr:real^N->real^M) (at ((Fc:real^1->real^N) x)) v) =
    frechet_derivative Tr (at (Fc x)) o (\t. drop t % v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LINEAR_CMUL THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let P2AW_FLOW_LPROP_CHART = prove
 (`!top atlas a b (g:real->A->real^3^3) p Z0 s1 r U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas /\
     p2a_lprop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0 s1 /\
     &0 < s1 /\ &0 < r /\ (s1 + r) pow 2 < b - a /\
     (?gamma. p2a_Lgeod_from (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0
                             (s1 pow 2) gamma /\ gamma(s1 pow 2) IN U)
     ==> ?N Phi. p2al_lwin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s1 r U a b
                           U phi N Phi /\ Z0 IN N`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `gamma0:real->A` STRIP_ASSUME_TAC))))))) THEN
  REWRITE_TAC[p2a_lprop] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:real^3->bool` (X_CHOOSE_THEN `W2:A->bool`
    (X_CHOOSE_THEN `a2:real` (X_CHOOSE_THEN `b2:real` (X_CHOOSE_THEN `U2:A->bool`
    (X_CHOOSE_THEN `phi2:A->real^3` (X_CHOOSE_THEN `r2:real`
    (X_CHOOSE_THEN `Phi2:real^3->real^(3,3)finite_sum`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "REP")))))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `(U2:A->bool,phi2:A->real^3) IN atlas` ASSUME_TAC THENL
   [UNDISCH_TAC `(U2:A->bool,phi2:A->real^3) IN
                   p2a_vatlas (p2a_flow_view (top,atlas) (real_interval[a,b])
                                 (g:real->A->real^3^3)) b2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U2:A->bool`;
                 `phi2:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U2:A->bool`;
                 `phi2:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < b - a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(s1 + r) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                         (b - s1 pow 2) = top`
  ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a2 < b - s1 pow 2 /\ b - s1 pow 2 <= b2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `s1:real` (ASSUME `!s'. abs(s' - s1) < r2 ==> a2 < b - s' pow 2 /\
                                        b - s' pow 2 <= b2`)) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (W2:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `W2:A->bool`; `a2:real`; `b2:real`; `b - s1 pow 2`] P2A_REGION_SLICE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi2:A->real^3) (U2 INTER W2 INTER U))` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `U2:A->bool`] THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi2:A->real^3) (U2 INTER U))` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `phi:A->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Tr = chart_trans (U2:A->bool,phi2:A->real^3) (U,phi)` THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (phi2:A->real^3) (U2 INTER U)) (Tr:real^3->real^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Tr" THEN MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:A. q IN U2 ==> (Tr:real^3->real^3)((phi2:A->real^3) q) = phi q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Tr" THEN REWRITE_TAC[chart_trans; SND] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `N = {Z | Z IN N2 /\
             fstcart((Phi2:real^3->real^(3,3)finite_sum) Z) IN
             IMAGE (phi2:A->real^3) (U2 INTER W2 INTER U)}` THEN
  SUBGOAL_THEN `open(N:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    MP_TAC(ISPECL [`fstcart o (Phi2:real^3->real^(3,3)finite_sum)`; `N2:real^3->bool`;
                   `IMAGE (phi2:A->real^3) (U2 INTER W2 INTER U)`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N:real^3->bool) SUBSET N2 /\
                IMAGE (fstcart o (Phi2:real^3->real^(3,3)finite_sum)) N SUBSET
                IMAGE (phi2:A->real^3) (U2 INTER U)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Phi = \Z:real^3. pastecart ((Tr:real^3->real^3)
                                  (fstcart((Phi2:real^3->real^(3,3)finite_sum) Z)))
                               (frechet_derivative Tr (at (fstcart(Phi2 Z))) (sndcart(Phi2 Z)))` THEN
  SUBGOAL_THEN `smooth_map_on N (Phi:real^3->real^(3,3)finite_sum)` ASSUME_TAC THENL
   [SUBGOAL_THEN `smooth_map_on N (Phi2:real^3->real^(3,3)finite_sum)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `N2:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "Phi" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\Z:real^3. (Tr:real^3->real^3)(fstcart((Phi2:real^3->real^(3,3)finite_sum) Z))) =
        Tr o (fstcart o Phi2)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (phi2:A->real^3) (U2 INTER U)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
      SUBGOAL_THEN
       `(\Z:real^3. frechet_derivative (Tr:real^3->real^3)
                      (at (fstcart((Phi2:real^3->real^(3,3)finite_sum) Z))) (sndcart(Phi2 Z))) =
        (\q:real^(3,3)finite_sum. frechet_derivative Tr (at (fstcart q)) (sndcart q)) o Phi2`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`IMAGE (phi2:A->real^3) (U2 INTER U)`; `Tr:real^3->real^3`]
                    GRGE_SMOOTH_DERIV_APPLY) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{q:real^(3,3)finite_sum | fstcart q IN IMAGE (phi2:A->real^3) (U2 INTER U)}` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (fstcart o (Phi2:real^3->real^(3,3)finite_sum)) N SUBSET
                   IMAGE (phi2:A->real^3) (U2 INTER U)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`N:real^3->bool`; `Phi:real^3->real^(3,3)finite_sum`] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "REP" (MP_TAC o SPEC `Z0:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(gm:real->A)(s1 pow 2) IN U` ASSUME_TAC THENL
     [SUBGOAL_THEN `(gm:real->A)(s1 pow 2) = gamma0(s1 pow 2)` SUBST1_TAC THENL
       [MP_TAC(ISPECL
         [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
          `b:real`; `p:A`; `Z0:real^3`; `s1 pow 2`; `gm:real->A`; `gamma0:real->A`]
         P2A_LGEOD_UNIQUE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s1 pow 2`) THEN
        REWRITE_TAC[REAL_LE_REFL; REAL_LE_POW_2];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(gm:real->A)(s1 pow 2)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_REWRITE_TAC[IN_INTER]] THEN
  REWRITE_TAC[p2al_lwin; p2al_lwa] THEN ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `s':real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s' pow 2 < (s1 + r) pow 2` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[REAL_ABS_POS; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `s':real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real^3) IN N2 /\
                fstcart((Phi2:real^3->real^(3,3)finite_sum) Z) IN
                IMAGE (phi2:A->real^3) (U2 INTER W2 INTER U)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^3) IN N` THEN EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  USE_THEN "REP" (MP_TAC o SPEC `Z:real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gm:real->A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gm:real->A)(s1 pow 2) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `fstcart((Phi2:real^3->real^(3,3)finite_sum) Z) IN
                 IMAGE (phi2:A->real^3) (U2 INTER W2 INTER U)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:A) = gm(s1 pow 2)` (fun th -> ASM_MESON_TAC[th]) THEN
    UNDISCH_TAC `(gm:real->A)(s1 pow 2) IN U2 INTER W2` THEN REWRITE_TAC[IN_INTER] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gm:real->A)(s1 pow 2) IN U2` ASSUME_TAC THENL
   [UNDISCH_TAC `(gm:real->A)(s1 pow 2) IN U2 INTER W2` THEN SIMP_TAC[IN_INTER]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[FSTCART_PASTECART] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term ((=) `fstcart((Phi2:real^3->real^(3,3)finite_sum) Z)`)) (concl th) &&
      is_eq (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "Phi" THEN REWRITE_TAC[SNDCART_PASTECART] THEN
  SUBGOAL_THEN `fstcart((Phi2:real^3->real^(3,3)finite_sum) Z) = (phi2:A->real^3)(gm(s1 pow 2))`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_Lgeod (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b gm
              (s1 pow 2)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `gm:real->A`; `s1 pow 2`; `s1:real`; `U2 INTER U:A->bool`]
                P2A_LGEOD_CONT) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; OPEN_IN_INTER; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`(Tr:real^3->real^3) o (\v. (phi2:A->real^3)(gm(drop v pow 2)))`;
                        `e:real`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_LIFT; IN_ELIM_THM; LIFT_DROP; DIST_LIFT; o_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gm:real->A)(s pow 2) IN U2 /\ gm(s pow 2) IN U` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v. (phi2:A->real^3)((gm:real->A)(drop v pow 2))`; `Tr:real^3->real^3`;
                 `sndcart((Phi2:real^3->real^(3,3)finite_sum) Z)`; `lift s1`;
                 `{v | &0 <= drop v /\ drop v pow 2 <= s1 pow 2}`] P2AW_VDERIV_CHAIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi2:A->real^3) (U2 INTER U)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `fstcart((Phi2:real^3->real^(3,3)finite_sum) Z) IN
                   IMAGE (phi2:A->real^3) (U2 INTER W2 INTER U)`) THEN
    SET_TAC[];
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The window in a prescribed chart (U,phi) around the end of a minimizer    *)
(* gamma = Lgeo Z0 of a flow: based at s1 in the end window of               *)
(* P2AW_FLOW_MIN_WINDOW, it reaches sqrt(tau), and its flow at Z0 is the     *)
(* chart state (phi(gamma(s^2)), A(s)) of the minimizer on [s1, sqrt tau].   *)
(* ------------------------------------------------------------------------- *)

let P2AW_CURVE_VEL_ID = prove
 (`!(phi:A->real^N) (g1:real->A) gamma v1 A' s0 s.
     &0 <= s0 /\ s0 < s /\
     (!t. &0 <= t /\ t <= s pow 2 ==> g1 t = gamma t) /\
     ((\v. phi(g1(drop v pow 2))) has_vector_derivative v1)
       (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= s pow 2}) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A')
       (at (lift s) within interval[lift s0,lift s])
     ==> v1 = A'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
  MAP_EVERY EXISTS_TAC [`\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                        `lift s0`; `lift s`; `lift s`] THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `{v | &0 <= drop v /\ drop v pow 2 <= s pow 2}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`\v. (phi:A->real^N)((g1:real->A)(drop v pow 2))`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]]);;

let P2AW_LIN_BASE = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z.
     p2al_lwin V tt x s1 r W a' b' U phi N Phi /\ Z IN N
     ==> p2al_lin V tt s1 r W b' U phi Phi Z s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2al_lwin; p2al_lwa] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N:real^N->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Phi:real^N->real^(N,N)finite_sum) Z IN
                IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2al_lin; ODE_IN_DOMAIN] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_lfield (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N)) tt`;
                   `interval(lift(s1 - r),lift(s1 + r)) PCROSS
                    (IMAGE (phi:A->real^N) (U INTER W) PCROSS (:real^N))`;
                   `pastecart (lift s1) ((Phi:real^N->real^(N,N)finite_sum) Z)`]
                  ODE_MAXINT_INITIAL) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART]]);;

let P2AW_FLOW_CWIN = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) Z0 s0 A.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     tau < b - a /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     Z0 IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
     (!t. &0 <= t /\ t <= tau
          ==> gamma t = p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0
                                 tau t) /\
     &0 < s0 /\ s0 < sqrt tau /\
     (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift(sqrt tau)] /\
     (!s. s0 < s /\ s < sqrt tau
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
       (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
     (!s. s0 <= s /\ s <= sqrt tau
          ==> (A has_vector_derivative
                 p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                      U b (U,phi)) b s
                          (phi(gamma(s pow 2))) (A(lift s)))
              (at (lift s) within interval[lift s0,lift(sqrt tau)]))
     ==> ?s1 r N Phi.
           s0 < s1 /\ s1 < sqrt tau /\ sqrt tau < s1 + r /\
           p2al_lwin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s1 r U a b U phi
                     N Phi /\
           Z0 IN N /\
           p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z0
                    (sqrt tau) /\
           (!s. s1 <= s /\ s <= sqrt tau
                ==> p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U
                             phi Phi Z0 s =
                    pastecart (phi(gamma(s pow 2))) (A(lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau < sqrt(b - a) /\ sqrt(b - a) pow 2 = b - a` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= b - a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[SQRT_MONO_LT; SQRT_POW_2]];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = (s0 + sqrt tau) / &2` THEN
  ABBREV_TAC `r = (sqrt tau - s1) + (sqrt(b - a) - sqrt tau) / &2` THEN
  SUBGOAL_THEN `s0 < s1 /\ s1 < sqrt tau /\ &0 < r /\ sqrt tau < s1 + r /\
                s1 + r < sqrt(b - a)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "s1"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s1 + r) pow 2 < b - a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(b - a) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 <= tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `s1 pow 2 <= sqrt tau pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_Lgeod_from (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                   b p Z0 tau
                   (p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0 tau)`
  ASSUME_TAC THENL [MATCH_MP_TAC P2A_LGEO_PROP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 < s /\ s pow 2 <= tau
        ==> p2a_Lgeod_from (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) b p Z0 (s pow 2)
              (p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0 tau)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_LGEOD_FROM_RESTRICT THEN
    EXISTS_TAC `tau:real` THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                           (g:real->A->real^3^3)) b = top` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `Z0:real^3`; `tau:real`] P2A_LPROP_ALL) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s1:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `Z0:real^3`; `s1:real`; `r:real`;
                 `U:A->bool`; `phi:A->real^3`] P2AW_FLOW_LPROP_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b])
                            (g:real->A->real^3^3)) b p Z0 tau` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                 b p Z0 tau (s1 pow 2) = gamma(s1 pow 2)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[REAL_LE_POW_2];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum`
      STRIP_ASSUME_TAC))] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2al_lwin]) THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sqrt tau
        ==> ((\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))) has_vector_derivative
             (A:real^1->real^3)(lift s)) (at (lift s) within interval[lift s0,lift(sqrt tau)])`
  (LABEL_TAC "VEL") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = sqrt tau` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sqrt tau /\
        p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                 b s1 r U b U phi Phi Z0 s
        ==> p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                     Z0 s =
            pastecart ((phi:A->real^3)((gamma:real->A)(s pow 2))) ((A:real^1->real^3)(lift s))`
  (LABEL_TAC "ID") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?gm. p2a_Lgeod_from (p2a_flow_view (top,atlas) (real_interval[a,b])
                             (g:real->A->real^3^3)) b p Z0 (s pow 2) gm /\
           (phi:A->real^3)(gm(s pow 2)) =
             fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U
                              phi Phi Z0 s) /\
           ((\v. phi(gm(drop v pow 2))) has_vector_derivative
            sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U
                             phi Phi Z0 s))
             (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= s pow 2})`
    MP_TAC THENL
     [ASM_CASES_TAC `(s:real) = s1` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                       `b:real`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`;
                       `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                       `Phi:real^3->real^(3,3)finite_sum`; `Z0:real^3`; `s1:real`]
                      P2AL_LFL_BASE) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `Z0:real^3` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `N:real^3->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                       `b:real`; `p:A`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`;
                       `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                       `Phi:real^3->real^(3,3)finite_sum`; `Z0:real^3`; `s:real`]
                      P2AL_LWIN_LGEOD) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= s pow 2 ==> (gm:real->A) t = gamma t` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 <= tau` ASSUME_TAC THENL
       [SUBGOAL_THEN `s pow 2 <= sqrt tau pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(gamma:real->A) t =
                    p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) b p Z0 tau t`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                     `b:real`; `p:A`; `Z0:real^3`; `s pow 2`; `gm:real->A`;
                     `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) b p Z0 tau`] P2A_LGEOD_UNIQUE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN REWRITE_TAC[PASTECART_INJ] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "fstcart")) (concl th))) THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_POW_2];
      MATCH_MP_TAC P2AW_CURVE_VEL_ID THEN
      MAP_EVERY EXISTS_TAC [`phi:A->real^3`; `gm:real->A`; `gamma:real->A`; `s0:real`;
                            `s:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[lift s0,lift(sqrt tau)]` THEN CONJ_TAC THENL
       [USE_THEN "VEL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
             b s1 r U b U phi Phi Z0 (sqrt tau)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_SOLUTION_LIN THEN
    EXISTS_TAC `\v. pastecart ((phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                              ((A:real^1->real^3) v)` THEN
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                 b s1 r U b U phi Phi Z0 s1`
      ASSUME_TAC THENL
       [MATCH_MP_TAC P2AW_LIN_BASE THEN
        MAP_EVERY EXISTS_TAC [`p:A`; `a:real`; `N:real^3->bool`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                     `b:real`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`;
                     `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                     `Phi:real^3->real^(3,3)finite_sum`; `Z0:real^3`; `s1:real`]
                    P2AL_LFL_BASE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN USE_THEN "ID" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ode_solution; IS_INTERVAL_INTERVAL; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV; INTER_IDEMPOT] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; INTER_IDEMPOT] THEN
    MATCH_MP_TAC P2AW_VDERIV_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[lift s0,lift(sqrt tau)]` THEN CONJ_TAC THENL
       [USE_THEN "VEL" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[lift s0,lift(sqrt tau)]` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `r:real`; `N:real^3->bool`;
                        `Phi:real^3->real^(3,3)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "ID" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AW_LIN_BETWEEN THEN EXISTS_TAC `sqrt tau` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness from a smooth derivative, the window flow on a time slice, and *)
(* the reduced length L~(Z, s^2) as a smooth function of the initial vector  *)
(* in a window (its derivative is the first variation P2AL_FV_ALL, smooth in *)
(* Z).                                                                       *)
(* ------------------------------------------------------------------------- *)

let P2AW_SMOOTH_FROM_DERIV = prove
 (`!s (f:real^M->real^N) f'.
     open s /\ (!x. x IN s ==> (f has_derivative f' x) (at x)) /\
     (!h. smooth_map_on s (\x. f' x h))
     ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[continuously_differentiable] THEN
    EXISTS_TAC `f':real^M->real^M->real^N` THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN] THEN
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `h:real^M`) THEN
    SIMP_TAC[smooth_map_on]]);;

let P2AW_WIN_SLICE_SMOOTH = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi
     ==> open {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s} /\
         smooth_map_on {Z | Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s}
           (\Z. p2al_lfl V tt s1 r W b' U phi Phi Z s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  ABBREV_TAC
   `O2 = {z:real^(1,N)finite_sum |
          sndcart z IN N /\
          p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart z) (drop(fstcart z))}` THEN
  SUBGOAL_THEN
   `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s} =
    {Z:real^N | pastecart (lift s) Z IN O2}`
  SUBST1_TAC THENL
   [EXPAND_TAC "O2" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; FSTCART_PASTECART;
                                     SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N. (\Z. pastecart (lift s) Z) continuous (at Z)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {Z:real^N | pastecart (lift s) Z IN O2}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\Z:real^N. pastecart (lift s) Z`; `O2:real^(1,N)finite_sum->bool`]
                  CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s) =
    (\z. p2al_lfl V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z))) o
    (\Z:real^N. pastecart (lift s) Z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O2:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

let P2AW_LTIL_HASDER = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z IN N /\ s1 < s /\ s < s1 + r /\
     &0 < s /\ s pow 2 < b /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
     Z IN p2a_Ldom V tt x b
     ==> ((\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) has_derivative
          (\c. lift((p2al_jy V tt s1 r W b' U phi Phi Z s ** c) dot
                    (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2)
                       (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) **
                     sndcart(p2al_lfl V tt s1 r W b' U phi Phi Z s))))) (at Z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`] P2AL_FV_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[p2al_fvp] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a':real`; `N:real^N->bool`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Calculus helpers for the divergence of the barrier: a Frechet derivative  *)
(* in a direction is the derivative along the line, the density sqrt(det G)  *)
(* of a metric field is differentiable with derivative sqrt(det G) tg(G, x,  *)
(* v) (Jacobi's formula, P2AL_TG_TRACE), and the trace of the matrix of a    *)
(* linear map.                                                               *)
(* ------------------------------------------------------------------------- *)

let P2AW_LINE_REAL_DERIV = prove
 (`!(f:real^M->real) z d.
     (\w. lift(f w)) differentiable (at z)
     ==> ((\t. f(z + t % d)) has_real_derivative
          drop(frechet_derivative (\w. lift(f w)) (at z) d)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN `lift o (\t. (f:real^M->real)(z + t % d)) o drop =
                (\w. lift(f w)) o (\v:real^1. z + drop v % d)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. drop(frechet_derivative (\w. lift((f:real^M->real) w)) (at z) d) % x) =
    frechet_derivative (\w. lift(f w)) (at z) o (\v:real^1. drop v % d)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^1` THEN
    SUBGOAL_THEN `linear(frechet_derivative (\w. lift((f:real^M->real) w)) (at z))` ASSUME_TAC
    THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `((\v:real^1. drop v % (d:real^M)) has_derivative (\v. drop v % d))
                    (at (lift(&0)))` ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\v:real^1. z:real^M`; `\h:real^1. vec 0:real^M`;
                   `\v:real^1. drop v % (d:real^M)`; `\v:real^1. drop v % (d:real^M)`;
                   `at (lift(&0))`] HAS_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID];
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let P2AW_FRECHET_DIRECTIONAL = prove
 (`!(f:real^M->real) z d D.
     (\w. lift(f w)) differentiable (at z) /\
     ((\t. f(z + t % d)) has_real_derivative D) (atreal (&0))
     ==> drop(frechet_derivative (\w. lift(f w)) (at z) d) = D`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\t. (f:real^M->real)(z + t % d)`; `&0`] THEN
  ASM_SIMP_TAC[P2AW_LINE_REAL_DERIV]);;

let P2AW_SQRTDET_LINE = prove
 (`!U (G:real^N->real^N^N) x v.
     metric_field U G /\ x IN U
     ==> ((\t. sqrt(det(G(x + t % v)))) has_real_derivative
          sqrt(det(G x)) * p2al_tg G x v) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < det((G:real^N->real^N^N) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
                differentiable (at (x:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (G:real^N->real^N^N)(x + t % v)`; `mderiv (G:real^N->real^N^N) x v`;
                 `&0`] CMPF_DET_DERIV) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_IMP_NZ]] THEN
    REWRITE_TAC[mderiv; VECTORIZE_MATRIFY; has_vector_derivative] THEN
    SUBGOAL_THEN
     `(\s:real^1. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:real^N->real^N^N)
                    (x + drop s % v))) =
      ((vectorize:real^N^N->real^(N,N)finite_prod) o G) o (\s:real^1. x + drop s % v)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h:real^1. drop h % frechet_derivative
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
                    (at x) v) =
      frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G) (at x) o
      (\h:real^1. drop h % v)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LINEAR_CMUL THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `((\h:real^1. drop h % (v:real^N)) has_derivative (\h. drop h % v))
                      (at (lift(&0)))` ASSUME_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`\s:real^1. x:real^N`; `\h:real^1. vec 0:real^N`;
                     `\h:real^1. drop h % (v:real^N)`; `\h:real^1. drop h % (v:real^N)`;
                     `at (lift(&0))`] HAS_DERIVATIVE_ADD) THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID];
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM o_DEF; GSYM(REWRITE_RULE[o_DEF] HAS_REAL_VECTOR_DERIVATIVE_AT)] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\t. det((G:real^N->real^N^N)(x + t % v))) has_real_derivative
                 det(G x) * trace(matrix_inv(G x) ** mderiv G x v)) (atreal (&0))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_DIFF_CHAIN_ATREAL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`sqrt`; `inv(&2 * sqrt(det((G:real^N->real^N^N) x)))`]) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC(MESON[] `!f a b. a = b ==> (f has_real_derivative a) (atreal (&0)) ==>
                                            (f has_real_derivative b) (atreal (&0))`) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `x:real^N`; `v:real^N`]
                P2AL_TG_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `sqrt(det((G:real^N->real^N^N) x)) pow 2 = det(G x) /\ &0 < sqrt(det(G x))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `q = sqrt(det((G:real^N->real^N^N) x))` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `det((G:real^N->real^N^N) x)`)) THEN
  UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD);;

let P2AW_SQRTDET_DIFFERENTIABLE = prove
 (`!U (G:real^N->real^N^N) x.
     metric_field U G /\ x IN U
     ==> (\y. lift(sqrt(det(G y)))) differentiable (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < det((G:real^N->real^N^N) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(sqrt(det((G:real^N->real^N^N) y)))) =
                (lift o sqrt o drop) o (\x. lift(det(matrify x:real^N^N))) o
                ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN REWRITE_TAC[LRG_DET_DIFFERENTIABLE] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    REWRITE_TAC[o_THM; MATRIFY_VECTORIZE] THEN
    MP_TAC(SPEC `det((G:real^N->real^N^N) x)` HAS_REAL_DERIVATIVE_SQRT) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP] THEN
    MESON_TAC[differentiable]]);;

let P2AW_SQRTDET_FRECHET = prove
 (`!U (G:real^N->real^N^N) x v.
     metric_field U G /\ x IN U
     ==> drop(frechet_derivative (\y. lift(sqrt(det(G y)))) (at x) v) =
         sqrt(det(G x)) * p2al_tg G x v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_FRECHET_DIRECTIONAL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_SQRTDET_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AW_SQRTDET_LINE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let P2AW_TRACE_MATRIX_SUM = prove
 (`!L:real^N->real^N.
     trace(matrix L) = sum(1..dimindex(:N)) (\a. (L(basis a))$a)`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[MATRIX_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* The W3 chart coefficients of a flow on the space-time chart domain:       *)
(* p2bw_cmet is the region-view chart metric at time b - tau, it is smooth   *)
(* in (x, tau), and A = rho G^-1 is smooth, symmetric and positive definite  *)
(* (the hypotheses of the barrier principle P2AW_NBP_MATRIX).                *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_CMET_LOCAL = prove
 (`!top atlas a b (g:real->A->real^3^3) U (phi:A->real^3) w.
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas /\ w IN p2bw_cdom (U,phi) (b - a)
     ==> p2bw_cmet atlas (U,phi) b g w =
         p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                    (b - drop(sndcart w)) (fstcart w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bw_cdom; p2bw_cmet; IN_ELIM_THM; FST; SND] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `fstcart(w:real^(3,1)finite_sum)` o
    CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`;
                 `b - drop(sndcart(w:real^(3,1)finite_sum))`;
                 `chart_inv (U,phi:A->real^3) (fstcart(w:real^(3,1)finite_sum))`]
                P2AW_FLOW_RLOCAL_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2AW_FLOW_CMET_SMOOTH = prove
 (`!top atlas a b (g:real->A->real^3^3) U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas
     ==> open(p2bw_cdom (U,phi) (b - a)) /\
         smooth_map_on (p2bw_cdom (U,phi) (b - a))
           ((vectorize:real^3^3->real^(3,3)finite_prod) o p2bw_cmet atlas (U,phi) b g) /\
         (!w. w IN p2bw_cdom (U,phi) (b - a)
              ==> metric_field (IMAGE phi U)
                    (metric_local atlas (U,phi) (g(b - drop(sndcart w)))) /\
                  fstcart w IN IMAGE phi U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CDOM_OPEN THEN ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FST; SND] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `b - drop(sndcart(w:real^(3,1)finite_sum))` (CONJUNCT2 (MATCH_MP
      P2AW_CBFLOW_METRICS (ASSUME `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)`)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
    ASM_REWRITE_TAC[FST; SND]] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH o CONJUNCT1) THEN
  REWRITE_TAC[lrg_lsmooth] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `(\z. (vectorize:real^3^3->real^(3,3)finite_prod)
           (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                       U b (U,phi) (drop(fstcart z)) (sndcart z))) o
    (\w:real^(3,1)finite_sum. pastecart (lift(b - drop(sndcart w))) (fstcart w))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AW_FLOW_CMET_LOCAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (phi:A->real^3) U` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\w:real^(3,1)finite_sum. lift(b - drop(sndcart w))) =
                    (\w. lift b + --(sndcart w))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; DROP_ADD; DROP_NEG; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2AW_SMOOTH_SNDCART THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2AW_SMOOTH_FSTCART THEN ASM_REWRITE_TAC[]]]);;

let P2AW_FLOW_CA_FACTS = prove
 (`!top atlas a b (g:real->A->real^3^3) U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas
     ==> (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                ==> smooth_map_on (p2bw_cdom (U,phi) (b - a))
                      (\w. lift(p2bw_cA atlas (U,phi) b g w$i$j))) /\
         smooth_map_on (p2bw_cdom (U,phi) (b - a))
           (\w. lift(p2bw_crho atlas (U,phi) b g w)) /\
         (!w. w IN p2bw_cdom (U,phi) (b - a)
              ==> &0 < p2bw_crho atlas (U,phi) b g w /\
                  symmetric_matrix(p2bw_cA atlas (U,phi) b g w) /\
                  !v. ~(v = vec 0) ==> &0 < v dot (p2bw_cA atlas (U,phi) b g w ** v))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_CMET_SMOOTH) THEN
  ABBREV_TAC `s = p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN
  ABBREV_TAC `G = p2bw_cmet atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `!w. w IN s ==> metric_field (IMAGE (phi:A->real^3) U)
                                 (metric_local atlas (U,phi) ((g:real->A->real^3^3)
                                    (b - drop(sndcart w)))) /\
                               (G:real^(3,1)finite_sum->real^3^3) w =
                               metric_local atlas (U,phi) (g(b - drop(sndcart w))) (fstcart w) /\
                               fstcart w IN IMAGE phi U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[p2bw_cmet];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN s ==> positive_definite((G:real^(3,1)finite_sum->real^3^3) w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^(3,1)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN s ==> &0 < det((G:real^(3,1)finite_sum->real^3^3) w)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DET_POSITIVE_DEFINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                      ==> smooth_map_on s (\w. lift((G:real^(3,1)finite_sum->real^3^3) w$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`; `G:real^(3,1)finite_sum->real^3^3`]
                  LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. p2bw_crho atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3) w =
                    sqrt(det((G:real^(3,1)finite_sum->real^3^3) w)) /\
                    p2bw_cA atlas (U,phi) b g w = sqrt(det(G w)) %% matrix_inv(G w)`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[p2bw_crho; p2bw_cA]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\w. lift(sqrt(det((G:real^(3,1)finite_sum->real^3^3) w))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`;
                   `\w. lift(det((G:real^(3,1)finite_sum->real^3^3) w))`]
                  SMOOTH_MAP_ON_LIFT_SQRT) THEN
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN
    ASM_MESON_TAC[smooth_map_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
    MP_TAC(ISPECL [`s:real^(3,1)finite_sum->bool`;
                   `\w. lift(sqrt(det((G:real^(3,1)finite_sum->real^3^3) w)))`;
                   `\w. lift(matrix_inv((G:real^(3,1)finite_sum->real^3^3) w)$i$j)`]
                  SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MATRIX_INV_ENTRY_OPEN THEN
    ASM_SIMP_TAC[DIMINDEX_3; REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[smooth_map_on];
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(det((G:real^(3,1)finite_sum->real^3^3) w))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `positive_definite(matrix_inv((G:real^(3,1)finite_sum->real^3^3) w))`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^(3,1)finite_sum` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LRG_METRIC_INV_POSDEF THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[positive_definite] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SYMMETRIC_MATRIX_CMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* In a window of pc_p2a_ljac, L~(Z, s^2) is smooth in the initial vector,   *)
(* and composed with a smooth local inverse Wi of the end position map Z ->  *)
(* y(Z, s) it is a smooth function of the end point y with derivative h -> h *)
(* . G(y) A'(Wi y) (first variation P2AL_FV_ALL, the chain rule and y(Wi y)  *)
(* = y).                                                                     *)
(* ------------------------------------------------------------------------- *)

let P2AW_LTIL_SMOOTH = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi s O.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ s1 < s /\ s < s1 + r /\ &0 < s /\
     s pow 2 < b /\ open O /\
     (!Z. Z IN O ==> Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
                     Z IN p2a_Ldom V tt x b)
     ==> smooth_map_on O (\Z. lift(p2a_Ltil V tt x (s pow 2) Z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                 `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `s:real`] P2AW_WIN_SLICE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `lf = \Z. p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s` THEN
  SUBGOAL_THEN `smooth_map_on O (lf:real^N->real^(N,N)finite_sum)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{Z | Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}` THEN
    EXPAND_TAC "lf" THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Gs = p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) (U INTER W)) Gs` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s1 - r) (s1 + r)
                   (\s. p2a_rlocal (V:p2alv) W b' (U INTER W,phi) (tt - s pow 2))` THEN
    REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN EXPAND_TAC "Gs" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z. Z IN O ==> fstcart((lf:real^N->real^(N,N)finite_sum) Z) IN
                                IMAGE (phi:A->real^N) (U INTER W)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "lf" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^N`; `s:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `IMAGE (phi:A->real^N) (U INTER W)`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_lin")) (concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AW_SMOOTH_FROM_DERIV THEN
  EXISTS_TAC
   `\Z c. lift((p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s ** c) dot
               ((Gs:real^N->real^N^N) (fstcart((lf:real^N->real^(N,N)finite_sum) Z)) **
                sndcart(lf Z)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MAP_EVERY EXPAND_TAC ["lf"; "Gs"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AW_LTIL_HASDER THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `a':real`; `N:real^N->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:real^N` THEN BETA_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\Z. frechet_derivative (fstcart o (lf:real^N->real^(N,N)finite_sum)) (at Z) c` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[p2al_jy] THEN
      SUBGOAL_THEN `(\Z. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)) =
                    fstcart o (lf:real^N->real^(N,N)finite_sum)` SUBST1_TAC THENL
       [EXPAND_TAC "lf" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `linear(frechet_derivative (fstcart o (lf:real^N->real^(N,N)finite_sum))
                                              (at Z))`
        (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN];
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN]];
    MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\Z. (Gs:real^N->real^N^N) (fstcart((lf:real^N->real^(N,N)finite_sum) Z))) =
        ((vectorize:real^N^N->real^(N,N)finite_prod) o Gs) o (fstcart o lf)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[metric_field];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[];
        ASM_MESON_TAC[metric_field]];
      SUBGOAL_THEN `(\Z. sndcart((lf:real^N->real^(N,N)finite_sum) Z)) = sndcart o lf`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_SNDCART_OPEN]]]);;

let P2AW_WIN_BARRIER_FN = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi s t u Wi.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ s1 < s /\ s < s1 + r /\ &0 < s /\
     s pow 2 < b /\
     (!Z. Z IN t ==> Z IN N /\ p2al_lin V tt s1 r W b' U phi Phi Z s /\
                     Z IN p2a_Ldom V tt x b) /\
     diffeomorphism_on t u (\Z. fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)) Wi
     ==> smooth_map_on u (\y. lift(p2a_Ltil V tt x (s pow 2) (Wi y))) /\
         !y. y IN u
             ==> ((\y. lift(p2a_Ltil V tt x (s pow 2) (Wi y))) has_derivative
                  (\h. lift(h dot (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2) y **
                                   sndcart(p2al_lfl V tt s1 r W b' U phi Phi (Wi y) s)))))
                 (at y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `smooth_map_on t (\Z. lift(p2a_Ltil (V:p2alv) tt (x:A) (s pow 2) Z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_LTIL_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                          `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                          `Phi:real^N->real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\y. lift(p2a_Ltil (V:p2alv) tt (x:A) (s pow 2) ((Wi:real^N->real^N) y))) =
                  (\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) o Wi` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Wi:real^N->real^N) y IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi
                                 ((Wi:real^N->real^N) y) s) = y`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `u:real^N->bool`)) (concl th) &&
      can (find_term ((=) `Wi:real^N->real^N`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
             (concl th)))) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `yf = \Z. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)` THEN
  SUBGOAL_THEN `(yf:real^N->real^N) differentiable (at ((Wi:real^N->real^N) y)) /\
                Wi differentiable (at y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `t:real^N->bool`; EXISTS_TAC `u:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. frechet_derivative (yf:real^N->real^N) (at ((Wi:real^N->real^N) y))
          (frechet_derivative Wi (at y) h) = h`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `frechet_derivative (yf:real^N->real^N) (at ((Wi:real^N->real^N) y)) o
      frechet_derivative Wi (at y) = (\h. h)`
     (fun th -> X_GEN_TAC `h:real^N` THEN MP_TAC(AP_THM th `h:real^N`) THEN
                REWRITE_TAC[o_THM]) THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(yf:real^N->real^N) o (Wi:real^N->real^N)` THEN EXISTS_TAC `y:real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `u:real^N->bool`] THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `(Wi:real^N->real^N) y`; `s:real`]
                P2AW_LTIL_HASDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(Wi:real^N->real^N) y` (ASSUME
     `!Z. Z IN t ==> Z IN N /\ p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s /\
                     Z IN p2a_Ldom V tt (x:A) b`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. lift(p2a_Ltil (V:p2alv) tt (x:A) (s pow 2) ((Wi:real^N->real^N) y))) =
    (\Z. lift(p2a_Ltil V tt x (s pow 2) Z)) o Wi`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. lift(h dot (p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2) y **
                     sndcart(p2al_lfl V tt s1 r W b' U phi Phi ((Wi:real^N->real^N) y) s)))) =
    (\c. lift((p2al_jy V tt s1 r W b' U phi Phi (Wi y) s ** c) dot
              (p2a_rlocal V W b' (U INTER W,phi) (tt - s pow 2) y **
               sndcart(p2al_lfl V tt s1 r W b' U phi Phi (Wi y) s)))) o
    frechet_derivative Wi (at y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; p2al_jy] THEN X_GEN_TAC `h:real^N` THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(\Z. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s)) =
                  (yf:real^N->real^N)` SUBST1_TAC THENL
     [EXPAND_TAC "yf" THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (yf:real^N->real^N) (at ((Wi:real^N->real^N) y)))`
      (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

(* ------------------------------------------------------------------------- *)
(* The divergence of (c sqrt(det G)) V for a metric field G                  *)
(* and a vector field V differentiable at x:                              *)
(*   sum_a d_a((c sqrt(det G)) V^a)(x) = c sqrt(det G(x)) (tg(G,x,V(x)) +   *)
(*   trace(DV(x)))  (product rule, Jacobi's formula P2AW_SQRTDET_FRECHET).  *)
(* ------------------------------------------------------------------------- *)

let P2AW_DIV_RHO_FIELD = prove
 (`!U (G:real^N->real^N^N) (Af:real^N->real^N) x c.
     metric_field U G /\ x IN U /\ Af differentiable (at x)
     ==> sum(1..dimindex(:N))
           (\a. (frechet_derivative (\y. (c * sqrt(det(G y))) % Af y) (at x) (basis a))$a) =
         c * sqrt(det(G x)) *
         (p2al_tg G x (Af x) + trace(matrix(frechet_derivative Af (at x))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Dr = frechet_derivative (\y. lift(sqrt(det((G:real^N->real^N^N) y)))) (at x)` THEN
  ABBREV_TAC `DA = frechet_derivative (Af:real^N->real^N) (at x)` THEN
  SUBGOAL_THEN `((\y. lift(sqrt(det((G:real^N->real^N^N) y)))) has_derivative Dr) (at x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Dr" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC P2AW_SQRTDET_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(Dr:real^N->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `((Af:real^N->real^N) has_derivative DA) (at x)` ASSUME_TAC THENL
   [EXPAND_TAC "DA" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. (c * sqrt(det((G:real^N->real^N^N) y))) % (Af:real^N->real^N) y)
                       (at x) =
    (\h. (c * sqrt(det(G x))) % DA h + (c * drop((Dr:real^N->real^1) h)) % Af x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`\y. c * sqrt(det((G:real^N->real^N^N) y))`;
                   `\h. c * drop((Dr:real^N->real^1) h)`; `Af:real^N->real^N`;
                   `DA:real^N->real^N`; `x:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lift o (\y. c * sqrt(det((G:real^N->real^N^N) y))) =
                  (\y. c % lift(sqrt(det(G y)))) /\
                  lift o (\h. c * drop((Dr:real^N->real^1) h)) = (\h. c % Dr h)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\a. (DA:real^N->real^N)(basis a)$a) = trace(matrix DA)`
  SUBST1_TAC THENL [REWRITE_TAC[P2AW_TRACE_MATRIX_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. (c * drop((Dr:real^N->real^1)(basis a))) * (Af:real^N->real^N) x$a) =
    c * drop(Dr(Af x))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; DROP_VSUM; o_DEF; LINEAR_CMUL; DROP_CMUL] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drop((Dr:real^N->real^1)((Af:real^N->real^N) x)) =
                sqrt(det((G:real^N->real^N^N) x)) * p2al_tg G x (Af x)`
  SUBST1_TAC THENL
   [EXPAND_TAC "Dr" THEN MATCH_MP_TAC P2AW_SQRTDET_FRECHET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The arithmetic of the sharp barrier inequality, and the data at a good    *)
(* point of a flow: the end window of a minimizer gamma = Lgeo Z0 in the     *)
(* prescribed chart (U,phi), a window in (U,phi) reaching beyond sqrt tau,   *)
(* and a smooth local inverse Wi of the end position map near Z0 (the end of *)
(* gamma is not conjugate: J > 0).                                           *)
(* ------------------------------------------------------------------------- *)

let P2AW_BAR_ARITH = prove
 (`!sb rho tr tg R KX Lt l tau.
     &0 < sb /\ &0 < rho /\ sb pow 2 = tau /\ Lt = &2 * sb * l /\
     sb pow 2 * (tr + tg) -
     (&3 * sb - sb pow 3 * R + sb * (&4 * tau * KX) / &4 - Lt / &2) <= &0
     ==> inv(&2 * sb) * rho * (tg + tr) <= (rho * KX - rho * (R + (l - &3) / tau)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gw = sb pow 2 * (tr + tg) -
                   (&3 * sb - sb pow 3 * R + sb * (&4 * tau * KX) / &4 - Lt / &2)` THEN
  SUBGOAL_THEN `(rho * KX - rho * (R + (l - &3) / tau)) / &2 - inv(&2 * sb) * rho * (tg + tr) =
                rho * (--gw) / (&2 * sb pow 3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "gw" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `tau:real`)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < sb` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rho * (--gw) / (&2 * sb pow 3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2AW_FLOW_BAR_SETUP = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) x Z0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     x IN IMAGE phi U /\ tau < b - a /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     gamma tau = chart_inv (U,phi) x /\
     Z0 IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
     (!t. &0 <= t /\ t <= tau
          ==> gamma t = p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0
                                 tau t) /\
     &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z0
     ==> ?s0 Av s1 r N Phi sb' t u Wi.
           &0 < s0 /\ s0 < sqrt tau /\
           ((\v. phi(gamma(drop v pow 2))) has_vector_derivative Av(lift(sqrt tau)))
             (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
           p2al_wok (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s1 r U a b U phi
                    N Phi /\
           s1 < sqrt tau /\ sqrt tau < sb' /\ sb' < s1 + r /\ sb' pow 2 < b - a /\
           (!Z. Z IN t
                ==> Z IN N /\
                    p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U
                             phi Phi Z (sqrt tau) /\
                    Z IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                  (sb' pow 2)) /\
           diffeomorphism_on t u
             (\Z. fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r
                                   U b U phi Phi Z (sqrt tau))) Wi /\
           Z0 IN t /\ x IN u /\ Wi x = Z0 /\ u SUBSET IMAGE phi U /\
           p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z0
                    (sqrt tau) = pastecart x (Av(lift(sqrt tau))) /\
           ~(det(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi
                         Phi Z0 (sqrt tau)) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN U /\ (phi:A->real^3)(gamma tau) = x /\
                (phi:A->real^3)(chart_inv (U,phi) x) = x` STRIP_ASSUME_TAC
  THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau < sqrt(b - a) /\ sqrt(b - a) pow 2 = b - a` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= b - a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[SQRT_MONO_LT; SQRT_POW_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`] P2AW_FLOW_MIN_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `Av:real^1->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `Z0:real^3`; `s0:real`; `Av:real^1->real^3`]
                P2AW_FLOW_CWIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:real^3->bool`
    (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AL_LWIN_WOK) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_lwin]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  SUBGOAL_THEN
   `p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b s1 r
             U b U phi Phi Z0 (sqrt tau) = pastecart x ((Av:real^1->real^3)(lift(sqrt tau)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_lfl")) (concl th) &&
      can (find_term ((=) `s1:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_lin")) (concl th))))
    THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`Z0:real^3`; `sqrt tau`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ode_domain")) (concl th) = false &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lfield")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  ABBREV_TAC `sb' = sqrt tau + min e (min (s1 + r - sqrt tau) (sqrt(b - a) - sqrt tau)) / &2` THEN
  SUBGOAL_THEN `sqrt tau < sb' /\ sb' < s1 + r /\ sb' < sqrt(b - a) /\ abs(sb' - sqrt tau) < e`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "sb'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sb' pow 2 < b - a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(b - a) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b s1 r
             U b U phi Phi Z0 sb'`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^3`; `N:real^3->bool`; `Phi:real^3->real^(3,3)finite_sum`;
                 `sqrt tau`] P2AW_WIN_SLICE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^3`; `N:real^3->bool`; `Phi:real^3->real^(3,3)finite_sum`;
                 `sb':real`] P2AW_WIN_SLICE_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `O1 = {Z | Z IN N /\
              p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                       b s1 r U b U phi Phi Z (sqrt tau)} INTER
         {Z | Z IN N /\
              p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                       Z sb'}` THEN
  SUBGOAL_THEN `open(O1:real^3->bool) /\ (Z0:real^3) IN O1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O1" THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `yf = \Z. fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                                 (g:real->A->real^3^3)) b s1 r U b U phi Phi Z (sqrt tau))` THEN
  SUBGOAL_THEN `smooth_map_on O1 (yf:real^3->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC
     `{Z | Z IN N /\
           p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                    b s1 r U b U phi Phi Z (sqrt tau)}` THEN
    CONJ_TAC THENL [EXPAND_TAC "O1" THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(yf:real^3->real^3) =
      fstcart o (\Z. p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) b s1 r U b U phi Phi Z (sqrt tau))`
    SUBST1_TAC THENL [EXPAND_TAC "yf" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(det(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  b s1 r U b U phi Phi Z0 (sqrt tau)) = &0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`;
                   `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                   `Phi:real^3->real^(3,3)finite_sum`; `Z0:real^3`; `sqrt tau`] P2AL_WOK_J) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_MUL_LZERO; real_div] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`yf:real^3->real^3`; `O1:real^3->bool`; `Z0:real^3`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `~(det(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                    b s1 r U b U phi Phi Z0 (sqrt tau)) = &0)` THEN
    EXPAND_TAC "yf" THEN REWRITE_TAC[p2al_jy];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `u:real^3->bool`
    (X_CHOOSE_THEN `Wi:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(yf:real^3->real^3) Z0 = x` ASSUME_TAC THENL
   [EXPAND_TAC "yf" THEN ASM_REWRITE_TAC[FSTCART_PASTECART]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`s0:real`; `Av:real^1->real^3`; `s1:real`; `r:real`; `N:real^3->bool`;
    `Phi:real^3->real^(3,3)finite_sum`; `sb':real`; `t:real^3->bool`; `u:real^3->bool`;
    `Wi:real^3->real^3`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(x:real^3) IN u /\ (Wi:real^3->real^3) x = Z0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(yf:real^3->real^3) Z0 = x` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Z:real^3) IN O1` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "O1" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`;
                   `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                   `Phi:real^3->real^(3,3)finite_sum`; `Z:real^3`; `sb':real`]
                  P2AL_LWIN_LGEOD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[]];
    UNDISCH_TAC `IMAGE (yf:real^3->real^3) t = u` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Z:real^3) IN O1` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "O1" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "yf" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Z:real^3`; `sqrt tau`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lfield")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[INTER_IDEMPOT] THEN SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The sharp barrier at a good point of a flow: at z = (x, tau) where l is   *)
(* differentiable and a minimizer gamma = Lgeo Z0 ends without a conjugate   *)
(* point (J > 0), psi(y,tau') = L~(Wi y, tau)/(2 sqrt tau) is a smooth upper *)
(* barrier for l along spatial lines through z, touching at z, and div(A     *)
(* grad psi)(z) <= Fb(z), the barrier input of P2AW_NBP_MATRIX for T2.       *)
(* ------------------------------------------------------------------------- *)

let P2AW_PSI_XDER = prove
 (`!(f:real^N->real) (Df:real^N->real^N) d u (w:real^(N,1)finite_sum) j.
     fstcart w IN u /\ open u /\
     (!y. y IN u ==> ((\y. lift(f y)) has_derivative (\h. lift(h dot Df y))) (at y)) /\
     1 <= j /\ j <= dimindex(:N)
     ==> wan_xder j (\w. f(fstcart w) / d) w = Df(fstcart w)$j / d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_xder] THEN
  SUBGOAL_THEN
   `((\w:real^(N,1)finite_sum. lift((f:real^N->real)(fstcart w) / d)) has_derivative
     (\h. inv d % ((\k. lift(k dot (Df:real^N->real^N)(fstcart(w:real^(N,1)finite_sum)))) o
                   fstcart) h)) (at w)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w:real^(N,1)finite_sum. lift((f:real^N->real)(fstcart w) / d)) =
                  (\w. inv d % ((\y. lift(f y)) o fstcart) w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; real_div; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_FSTCART] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM; DROP_CMUL; LIFT_DROP; FSTCART_PASTECART] THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2AW_WAN_XDER_LOCAL = prove
 (`!(f:real^(N,1)finite_sum->real) g s z i.
     open s /\ z IN s /\ (!w. w IN s ==> f w = g w) /\
     (\w. lift(g w)) differentiable (at z)
     ==> wan_xder i f z = wan_xder i g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_xder] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`\w. lift((g:real^(N,1)finite_sum->real) w)`;
                        `s:real^(N,1)finite_sum->bool`] THEN
  ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let P2AW_COMPONENT_LINE_DERIV = prove
 (`!(Fv:real^N->real^N) x d i.
     Fv differentiable (at x)
     ==> ((\t. Fv(x + t % d)$i) has_real_derivative
          (frechet_derivative Fv (at x) d)$i) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w. lift((Fv:real^N->real^N) w$i)) = (\v. lift(v$i)) o Fv` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `linear (\v:real^N. lift(v$i))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\w. lift((Fv:real^N->real^N) w$i)) has_derivative
                 (\v. lift(v$i)) o frechet_derivative Fv (at x)) (at x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. (Fv:real^N->real^N) w$i`; `x:real^N`; `d:real^N`]
                P2AW_LINE_REAL_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM; LIFT_DROP]);;

let P2AW_RHO_MATVEC_ID = prove
 (`!(G:real^N^N) rho (v:real^N) c i.
     invertible G /\ 1 <= i /\ i <= dimindex(:N)
     ==> sum(1..dimindex(:N)) (\j. (rho %% matrix_inv G)$i$j * ((G ** v)$j / c)) =
         (inv c * rho) * v$i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(matrix_inv G ** ((G:real^N^N) ** v):real^N) = v` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `(matrix_inv G ** ((G:real^N^N) ** v):real^N)$i =
                sum(1..dimindex(:N)) (\j. matrix_inv G$i$j * (G ** v)$j)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_COMPONENT; real_div] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\j. (rho * matrix_inv (G:real^N^N)$i$j) * ((G ** v:real^N)$j * inv c)) =
    (inv c * rho) * sum(1..dimindex(:N)) (\j. matrix_inv G$i$j * (G ** v)$j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let P2AW_BAR_DIVCALC = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) (Gm:real^N->real^N^N) (Ltw:real^N->real)
    (Ap:real^N->real^N) S u x tau c r0.
     open S /\ open u /\ x IN u /\ u SUBSET S /\ metric_field S Gm /\ &0 < r0 /\
     (!w. w IN ball(pastecart x (lift tau),r0) ==> fstcart w IN u) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (ball(pastecart x (lift tau),r0)) (\w. lift(A w$i$j))) /\
     (!y. y IN u ==> A(pastecart y (lift tau)) = sqrt(det(Gm y)) %% matrix_inv(Gm y)) /\
     (!y. y IN u ==> ((\y. lift(Ltw y)) has_derivative (\h. lift(h dot (Gm y ** Ap y)))) (at y)) /\
     smooth_map_on u Ap /\ ~(c = &0)
     ==> sum(1..dimindex(:N))
           (\i. wan_xder i (\w. sum(1..dimindex(:N))
                                  (\j. A w$i$j * wan_xder j (\w. Ltw(fstcart w) / c) w))
                (pastecart x (lift tau))) =
         inv c * sqrt(det(Gm x)) *
         (p2al_tg Gm x (Ap x) + trace(matrix(frechet_derivative Ap (at x))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `z = pastecart (x:real^N) (lift tau)` THEN
  ABBREV_TAC `B = ball(z:real^(N,1)finite_sum,r0)` THEN
  SUBGOAL_THEN `open(B:real^(N,1)finite_sum->bool) /\ z IN B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (S:real^N->bool)
                  ((vectorize:real^N^N->real^(N,N)finite_prod) o (Gm:real^N->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN u ==> invertible((Gm:real^N->real^N^N) y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`S:real^N->bool`; `Gm:real^N->real^N^N`; `y:real^N`]
                                        LRG_METRIC_INVERTIBLE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Pv = \y. inv c % ((Gm:real^N->real^N^N) y ** (Ap:real^N->real^N) y)` THEN
  SUBGOAL_THEN `smooth_map_on u (Pv:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Pv" THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `S:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w j. w IN B /\ 1 <= j /\ j <= dimindex(:N)
          ==> wan_xder j (\w. (Ltw:real^N->real)(fstcart w) / c) w =
              ((Gm:real^N->real^N^N)(fstcart w) ** (Ap:real^N->real^N)(fstcart w))$j / c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`Ltw:real^N->real`; `\y. (Gm:real^N->real^N^N) y ** (Ap:real^N->real^N) y`;
                   `c:real`; `u:real^N->bool`; `w:real^(N,1)finite_sum`; `j:num`]
                  P2AW_PSI_XDER) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(w:real^(N,1)finite_sum) IN B` THEN
    EXPAND_TAC "B" THEN EXPAND_TAC "z" THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Vs = \y. (inv c * sqrt(det((Gm:real^N->real^N^N) y))) % (Ap:real^N->real^N) y` THEN
  SUBGOAL_THEN `(Ap:real^N->real^N) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Vs:real^N->real^N) differentiable (at x)` ASSUME_TAC THENL
   [EXPAND_TAC "Vs" THEN MATCH_MP_TAC DIFFERENTIABLE_MUL_AT THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lift o (\y. inv c * sqrt(det((Gm:real^N->real^N^N) y))) =
                  (\y. inv c % lift(sqrt(det(Gm y))))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN MATCH_MP_TAC P2AW_SQRTDET_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_xder i (\w. sum(1..dimindex(:N))
                              (\j. (A:real^(N,1)finite_sum->real^N^N) w$i$j *
                                   wan_xder j (\w. (Ltw:real^N->real)(fstcart w) / c) w)) z =
            (frechet_derivative (Vs:real^N->real^N) (at x) (basis i))$i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ABBREV_TAC
     `Fi = \w. sum(1..dimindex(:N))
                 (\j. (A:real^(N,1)finite_sum->real^N^N) w$i$j *
                      (((Gm:real^N->real^N^N)(fstcart w) ** (Ap:real^N->real^N)(fstcart w))$j / c))` THEN
    SUBGOAL_THEN `!w. w IN B ==> (Fi:real^(N,1)finite_sum->real) w =
                                 ((A:real^(N,1)finite_sum->real^N^N) w **
                                  (Pv:real^N->real^N)(fstcart w))$i`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["Fi"; "Pv"] THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; VECTOR_MUL_COMPONENT] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on B (\w. lift((Fi:real^(N,1)finite_sum->real) w))` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `\w. lift(((A:real^(N,1)finite_sum->real^N^N) w **
                            (Pv:real^N->real^N)(fstcart w))$i)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE];
        SUBGOAL_THEN `(\w. (Pv:real^N->real^N)(fstcart w)) =
                      Pv o (fstcart:real^(N,1)finite_sum->real^N)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
          MATCH_MP_TAC P2AW_SMOOTH_FSTCART THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\w. lift((Fi:real^(N,1)finite_sum->real) w)) differentiable (at z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `B:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_xder i (\w. sum(1..dimindex(:N))
                        (\j. (A:real^(N,1)finite_sum->real^N^N) w$i$j *
                             wan_xder j (\w. (Ltw:real^N->real)(fstcart w) / c) w)) z =
      wan_xder i Fi z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P2AW_WAN_XDER_LOCAL THEN EXISTS_TAC `B:real^(N,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      EXPAND_TAC "Fi" THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[wan_xder] THEN MATCH_MP_TAC P2AW_FRECHET_DIRECTIONAL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\t. (Vs:real^N->real^N)(x + t % basis i)$i`; `r0:real`] THEN
    ASM_SIMP_TAC[P2AW_COMPONENT_LINE_DERIV] THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
    SUBGOAL_THEN `z + t % pastecart (basis i) (vec 0) =
                  pastecart ((x:real^N) + t % basis i) (lift tau)` SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD] THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    SUBGOAL_THEN `pastecart ((x:real^N) + t % basis i) (lift tau) IN B` ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN EXPAND_TAC "z" THEN
      REWRITE_TAC[IN_BALL; dist; PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART; NORM_0] THEN
      REWRITE_TAC[VECTOR_ARITH `x - (x + v):real^N = --v`; NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[NORM_BASIS] THEN
      REWRITE_TAC[REAL_MUL_RID; REAL_ARITH `&0 pow 2 = &0`; REAL_ADD_RID; POW_2_SQRT_ABS] THEN
      REWRITE_TAC[REAL_ABS_ABS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) + t % basis i IN u` ASSUME_TAC THENL
     [MP_TAC(SPEC `pastecart ((x:real^N) + t % basis i) (lift tau)`
        (ASSUME `!w:real^(N,1)finite_sum. w IN B ==> fstcart w IN u`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[FSTCART_PASTECART]];
      ALL_TAC] THEN
    EXPAND_TAC "Fi" THEN EXPAND_TAC "Vs" THEN REWRITE_TAC[FSTCART_PASTECART] THEN
    ASM_SIMP_TAC[P2AW_RHO_MATVEC_ID; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. wan_xder i (\w. sum(1..dimindex(:N))
                             (\j. (A:real^(N,1)finite_sum->real^N^N) w$i$j *
                                  wan_xder j (\w. (Ltw:real^N->real)(fstcart w) / c) w)) z) =
    sum(1..dimindex(:N)) (\i. (frechet_derivative (Vs:real^N->real^N) (at x) (basis i))$i)`
  SUBST1_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "Vs" THEN MATCH_MP_TAC P2AW_DIV_RHO_FIELD THEN EXISTS_TAC `S:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let P2AW_INV_CHAIN_MATRIX = prove
 (`!(yf:real^N->real^N) (sf:real^N->real^M) (Wi:real^N->real^N) u x Z0.
     open u /\ x IN u /\ Wi x = Z0 /\ yf differentiable (at Z0) /\
     sf differentiable (at Z0) /\ Wi differentiable (at x) /\
     (!y. y IN u ==> yf(Wi y) = y)
     ==> matrix(frechet_derivative (\y. sf(Wi y)) (at x)) =
         matrix(frechet_derivative sf (at Z0)) **
         matrix_inv(matrix(frechet_derivative yf (at Z0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `Z0:real^N`)) THEN
  SUBGOAL_THEN `linear(frechet_derivative (yf:real^N->real^N) (at ((Wi:real^N->real^N) x))) /\
                linear(frechet_derivative (sf:real^N->real^M) (at (Wi x))) /\
                linear(frechet_derivative Wi (at x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. (sf:real^N->real^M)((Wi:real^N->real^N) y)) (at x) =
    frechet_derivative sf (at (Wi x)) o frechet_derivative Wi (at x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN `(\y. (sf:real^N->real^M)((Wi:real^N->real^N) y)) = sf o Wi` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (yf:real^N->real^N) (at ((Wi:real^N->real^N) x)) o
    frechet_derivative Wi (at x) = (\h. h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(yf:real^N->real^N) o (Wi:real^N->real^N)` THEN EXISTS_TAC `x:real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `u:real^N->bool`] THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix_inv(matrix(frechet_derivative (yf:real^N->real^N) (at ((Wi:real^N->real^N) x)))) =
    matrix(frechet_derivative Wi (at x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MATRIX_INV_UNIQUE_RIGHT THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; MATRIX_ID];
    ASM_SIMP_TAC[MATRIX_COMPOSE]]);;

let P2AW_WIN_GW_NONPOS = prove
 (`!(V:p2alv) tt (x:A) b s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z0 IN N /\ s1 < s /\ s < s1 + r /\
     &0 < s /\ p2al_lin V tt s1 r W b' U phi Phi Z0 s /\ Z0 IN p2a_Ldom V tt x b /\
     s pow 2 < b /\ ~(det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0) /\
     Z0 IN p2a_Smin V tt x (s pow 2) /\ &0 < p2a_J V tt x (s pow 2) Z0
     ==> p2al_gw V tt x s1 r W b' U phi Phi Z0 s <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `s1:real`; `r:real`; `W:A->bool`;
                 `a':real`; `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_GF_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z0:real^N`; `s:real`]
                P2AL_GF_NONPOS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s':real = s` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2AL_NO_CONJ THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P2AW_FLOW_BAR_DIV = prove
 (`!top atlas a b (g:real->A->real^3^3) p U (phi:A->real^3) x tau s1 r N Phi sb' t u
    (Wi:real^3->real^3) Z0 X r0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     x IN IMAGE phi U /\ &0 < tau /\ tau < b - a /\
     p2al_wok (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s1 r U a b U phi N Phi /\
     s1 < sqrt tau /\ sqrt tau < sb' /\ sb' < s1 + r /\ sb' pow 2 < b - a /\
     (!Z. Z IN t
          ==> Z IN N /\
              p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                       Z (sqrt tau) /\
              Z IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (sb' pow 2)) /\
     diffeomorphism_on t u
       (\Z. fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U
                             phi Phi Z (sqrt tau))) Wi /\
     Z0 IN t /\ x IN u /\ Wi x = Z0 /\ u SUBSET IMAGE phi U /\
     p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z0
              (sqrt tau) = pastecart x ((&2 * sqrt tau) % X) /\
     ~(det(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z0
                   (sqrt tau)) = &0) /\
     Z0 IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
     &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z0 /\
     (!i. 1 <= i /\ i <= 3
          ==> wan_xder i (p2bw_cfun (U,phi)
                           (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                         (pastecart x (lift tau)) =
              (p2bw_cmet atlas (U,phi) b g (pastecart x (lift tau)) ** X)$i) /\
     p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z0 / (&2 * sqrt tau) =
     p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
               (pastecart x (lift tau)) /\
     &0 < r0 /\ ball(pastecart x (lift tau),r0) SUBSET p2bw_cdom (U,phi) (b - a) /\
     (!w. w IN ball(pastecart x (lift tau),r0) ==> fstcart w IN u)
     ==> sum(1..dimindex(:3))
           (\i. wan_xder i
                  (\w. sum(1..dimindex(:3))
                         (\j. p2bw_cA atlas (U,phi) b g w$i$j *
                              wan_xder j
                                (\w. p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                              b p tau (Wi(fstcart w)) / (&2 * sqrt tau)) w))
                  (pastecart x (lift tau))) <=
         (p2bw_bil (p2bw_cA atlas (U,phi) b g)
            (p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
            (p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
            (pastecart x (lift tau)) -
          p2bw_crho atlas (U,phi) b g (pastecart x (lift tau)) *
          (p2bw_cscal atlas (U,phi) b g (pastecart x (lift tau)) +
           (p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
                      (pastecart x (lift tau)) - &3) / tau)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U,phi) (x:real^3) IN U /\
                (phi:A->real^3)(chart_inv (U,phi) x) = x` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 < sb' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tau < sb' pow 2 /\ sqrt tau < s1 + r /\ ~(&2 * sqrt tau = &0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sqrt tau pow 2 < sb' pow 2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                           (g:real->A->real^3^3)) b = top` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) p b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2al_lwa]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `Z0:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `t:real^3->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Ldom")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^3) U)
      (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                  U b (U,phi) (b - tau))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2a_lsmooth]) THEN
    REWRITE_TAC[INTER_IDEMPOT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < det(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        U b (U,phi) (b - tau) x) /\
    invertible(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                          (b - tau) x)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `positive_definite(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                          (g:real->A->real^3^3)) U b (U,phi) (b - tau) x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AL_METRIC_PD THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[DET_POSITIVE_DEFINITE; INVERTIBLE_DET_NZ; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN u ==> pastecart y (lift tau) IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                FST; SND] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN u
        ==> p2bw_cmet atlas (U,phi:A->real^3) b (g:real->A->real^3^3) (pastecart y (lift tau)) =
            p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi) (b - tau) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`;
                   `pastecart (y:real^3) (lift tau)`] P2AW_FLOW_CMET_LOCAL) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN u
        ==> p2bw_cA atlas (U,phi:A->real^3) b (g:real->A->real^3^3) (pastecart y (lift tau)) =
            sqrt(det(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                                (b - tau) y)) %%
            matrix_inv(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                                  (b - tau) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_cA; p2bw_crho] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bw_cmet atlas (U,phi:A->real^3) b (g:real->A->real^3^3) (pastecart x (lift tau)) =
    p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi) (b - tau) x /\
    p2bw_crho atlas (U,phi) b g (pastecart x (lift tau)) =
    sqrt(det(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                        (b - tau) x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_crho] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        U b (U,phi) (b - tau)) x =
    p2bw_cscal atlas (U,phi:A->real^3) b g (pastecart x (lift tau))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_cscal; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`; `b - tau`;
                   `chart_inv (U,phi:A->real^3) x`] P2AW_FLOW_RLOCAL_ID) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bw_bil (p2bw_cA atlas (U,phi:A->real^3) b (g:real->A->real^3^3))
      (p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
      (p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
      (pastecart x (lift tau)) =
    sqrt(det(p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                        (b - tau) x)) *
    (X dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi)
                       (b - tau) x ** X))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_BIL_DOT THEN ASM_SIMP_TAC[DIMINDEX_3]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((&2 * sqrt tau) % X) dot
    (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) U b
                (U,phi:A->real^3) (b - tau) x ** ((&2 * sqrt tau) % X)) =
    &4 * tau * (X dot (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b
                                  (U,phi) (b - tau) x ** X))`
  ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    UNDISCH_TAC `sqrt tau pow 2 = tau` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> smooth_map_on (ball(pastecart x (lift tau),r0))
                (\w. lift(p2bw_cA atlas (U,phi:A->real^3) b (g:real->A->real^3^3) w$i$j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`] P2AW_FLOW_CA_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `sb' pow 2`; `s1:real`; `r:real`; `U:A->bool`; `a:real`;
                 `b:real`; `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                 `Phi:real^3->real^(3,3)finite_sum`; `sqrt tau`; `t:real^3->bool`;
                 `u:real^3->bool`; `Wi:real^3->real^3`] P2AW_WIN_BARRIER_FN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `sqrt tau pow 2 = tau`; INTER_IDEMPOT])] THEN
  SUBGOAL_THEN
   `smooth_map_on
      {Z | Z IN N /\
           p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b s1 r
                    U b U phi Phi Z (sqrt tau)}
      (\Z. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi
                            Phi Z (sqrt tau))) /\
    open {Z | Z IN N /\
              p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z
                       (sqrt tau)} /\
    t SUBSET {Z | Z IN N /\
                  p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                           Z (sqrt tau)}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                   `phi:A->real^3`; `N:real^3->bool`; `Phi:real^3->real^(3,3)finite_sum`;
                   `sqrt tau`] P2AW_WIN_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\Z. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) b s1 r U b U phi Phi Z (sqrt tau))) =
        sndcart o (\Z. p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U
                                phi Phi Z (sqrt tau))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `t:real^3->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Ldom")) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\Z. fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                          b s1 r U b U phi Phi Z (sqrt tau))) differentiable (at Z0) /\
    (\Z. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                          Z (sqrt tau))) differentiable (at Z0) /\
    (Wi:real^3->real^3) differentiable (at x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC
       `{Z | Z IN N /\
             p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b s1
                      r U b U phi Phi Z (sqrt tau)}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on u
      (\y. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                            b s1 r U b U phi Phi ((Wi:real^3->real^3) y) (sqrt tau)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                               (g:real->A->real^3^3)) b s1 r U b U phi Phi
                             ((Wi:real^3->real^3) y) (sqrt tau))) =
      (\Z. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi
                            Phi Z (sqrt tau))) o Wi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC
     `{Z | Z IN N /\
           p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b s1 r
                    U b U phi Phi Z (sqrt tau)}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix(frechet_derivative
             (\y. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                                     (g:real->A->real^3^3)) b s1 r U b U phi Phi
                                   ((Wi:real^3->real^3) y) (sqrt tau))) (at x)) =
    p2al_jb (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z0
            (sqrt tau) **
    matrix_inv(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                       Z0 (sqrt tau))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2al_jb; p2al_jy] THEN
    MP_TAC(ISPECL
     [`\Z. fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) b s1 r U b U phi Phi Z (sqrt tau))`;
      `\Z. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) b s1 r U b U phi Phi Z (sqrt tau))`;
      `Wi:real^3->real^3`; `u:real^3->bool`; `x:real^3`; `Z0:real^3`] P2AW_INV_CHAIN_MATRIX) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `sb' pow 2`; `s1:real`; `r:real`; `U:A->bool`; `a:real`;
                 `b:real`; `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                 `Phi:real^3->real^(3,3)finite_sum`; `Z0:real^3`; `sqrt tau`]
                P2AW_WIN_GW_NONPOS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`p2bw_cA atlas (U,phi:A->real^3) b (g:real->A->real^3^3)`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                             U b (U,phi:A->real^3) (b - tau)`;
                 `\y. p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b])
                                 (g:real->A->real^3^3)) b p tau ((Wi:real^3->real^3) y)`;
                 `\y. sndcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                                         (g:real->A->real^3^3)) b s1 r U b U phi Phi
                                       ((Wi:real^3->real^3) y) (sqrt tau))`;
                 `IMAGE (phi:A->real^3) U`; `u:real^3->bool`; `x:real^3`; `tau:real`;
                 `&2 * sqrt tau`; `r0:real`] P2AW_BAR_DIVCALC) THEN
  REWRITE_TAC[DIMINDEX_3] THEN BETA_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[SNDCART_PASTECART] THEN
  MATCH_MP_TAC P2AW_BAR_ARITH THEN
  EXISTS_TAC `p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                       b p tau Z0` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POS_LT];
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Ltil")) (lhs(concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bw_cfun")) (rand(concl th)))) THEN
    UNDISCH_TAC `&0 < sqrt tau` THEN CONV_TAC REAL_FIELD;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_gw")) (concl th))) THEN
    REWRITE_TAC[p2al_gw; INTER_IDEMPOT; DIMINDEX_3] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]]);;

let P2AW_FLOW_SHARP_BARRIER = prove
 (`!top atlas a b (g:real->A->real^3^3) p U (phi:A->real^3) z (gamma:real->A) Z0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     z IN p2bw_cdom (U,phi) (b - a) /\
     (\w. lift(p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p) w))
       differentiable (at z) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (drop(sndcart z)) gamma /\
     gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z) /\
     Z0 IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (drop(sndcart z)) /\
     (!t. &0 <= t /\ t <= drop(sndcart z)
          ==> gamma t = p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0
                                 (drop(sndcart z)) t) /\
     &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (drop(sndcart z)) Z0
     ==> ?psi r. &0 < r /\ ball(z,r) SUBSET p2bw_cdom (U,phi) (b - a) /\
                 smooth_map_on (ball(z,r)) (\y. lift(psi y)) /\
                 (!v t. norm v <= &2 /\ z + t % pastecart v (vec 0) IN ball(z,r) /\
                        z - t % pastecart v (vec 0) IN ball(z,r)
                        ==> p2bw_cfun (U,phi)
                              (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
                              (z + t % pastecart v (vec 0)) <= psi(z + t % pastecart v (vec 0)) /\
                            p2bw_cfun (U,phi)
                              (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
                              (z - t % pastecart v (vec 0)) <= psi(z - t % pastecart v (vec 0))) /\
                 psi z = p2bw_cfun (U,phi)
                           (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) z /\
                 sum(1..dimindex(:3))
                   (\i. wan_xder i (\w. sum(1..dimindex(:3))
                                          (\j. p2bw_cA atlas (U,phi) b g w$i$j *
                                               wan_xder j psi w)) z) <=
                 (p2bw_bil (p2bw_cA atlas (U,phi) b g)
                    (p2bw_cfun (U,phi)
                       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                    (p2bw_cfun (U,phi)
                       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z -
                  p2bw_crho atlas (U,phi) b g z *
                  (p2bw_cscal atlas (U,phi) b g z +
                   (p2bw_cfun (U,phi)
                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) z - &3) /
                   drop(sndcart z))) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = fstcart(z:real^(3,1)finite_sum)` THEN
  ABBREV_TAC `tau = drop(sndcart(z:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `z = pastecart (x:real^3) (lift tau)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "tau"] THEN REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (phi:A->real^3) U /\ &0 < tau /\ tau < b - a` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pastecart (x:real^3) (lift tau) IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `Z0 IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b])
                                 (g:real->A->real^3^3)) b p tau`
  ASSUME_TAC THENL
   [UNDISCH_TAC `Z0 IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b])
                                   (g:real->A->real^3^3)) b p tau` THEN
    REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `x:real^3`; `Z0:real^3`] P2AW_FLOW_BAR_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `Av:real^1->real^3`
    (X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:real^3->bool`
    (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum` (X_CHOOSE_THEN `sb':real`
    (X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `u:real^3->bool`
    (X_CHOOSE_THEN `Wi:real^3->real^3` STRIP_ASSUME_TAC)))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `(U:A->bool,phi:A->real^3)`; `x:real^3`;
                 `tau:real`; `gamma:real->A`] P2AW_FLOW_LX_DERIV) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Av:real^1->real^3)(lift(sqrt tau)) = (&2 * sqrt tau) % X` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`; `lift s0`;
                          `lift(sqrt tau)`; `lift(sqrt tau)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v | &0 <= drop v /\ drop v pow 2 <= tau}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `drop v pow 2 <= sqrt tau pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                           (g:real->A->real^3^3)) b = top` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau pow 2 < sb' pow 2 /\ sqrt tau < s1 + r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `sb' pow 2`; `s1:real`; `r:real`; `U:A->bool`; `a:real`;
                 `b:real`; `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                 `Phi:real^3->real^(3,3)finite_sum`; `sqrt tau`; `t:real^3->bool`;
                 `u:real^3->bool`; `Wi:real^3->real^3`] P2AW_WIN_BARRIER_FN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[];
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `sqrt tau pow 2 = tau`])] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `!y'. y' IN u
         ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
                    tau (chart_inv (U,phi) y') <=
             p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                      ((Wi:real^3->real^3) y') / (&2 * sqrt tau)`
  (LABEL_TAC "BLE") THENL
   [X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Wi:real^3->real^3) y' IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `Zy = (Wi:real^3->real^3) y'` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Zy:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t:real^3->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_Ldom")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `Zy:real^3`; `sb' pow 2`; `tau:real`] P2AL_LGEO_AGREE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `sqrt tau pow 2 < sb' pow 2` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN
     `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p Zy
               tau tau = chart_inv (U,phi:A->real^3) y'`
    ASSUME_TAC THENL
     [UNDISCH_TAC `p2al_wok (p2a_flow_view (top,atlas) (real_interval[a,b])
                     (g:real->A->real^3^3)) b p s1 r U a b U phi N Phi` THEN
      REWRITE_TAC[p2al_wok] THEN
      DISCH_THEN(MP_TAC o SPECL [`Zy:real^3`; `sqrt tau`] o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
      DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(phi:A->real^3)((gm:real->A) tau) = y'` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_lfl")) (concl th))) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y':real^3` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `u:real^3->bool`)) (concl th) &&
          not (can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
                 (concl th)) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_lfl")) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                     `b:real`; `p:A`; `Zy:real^3`; `tau:real`; `gm:real->A`;
                     `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) b p Zy tau`] P2A_LGEOD_UNIQUE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[P2A_LGEO_PROP]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `tau:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `y':real^3`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`;
                   `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) b p Zy tau`] P2AW_FLOW_LX_LE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC P2AL_LGEO_ADM THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p2a_lx; p2a_Ltil] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r0. &0 < r0 /\
         ball(pastecart (x:real^3) (lift tau),r0) SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a) /\
         (!w. w IN ball(pastecart x (lift tau),r0) ==> fstcart w IN u)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(U:A->bool,phi:A->real^3)`; `b - a`] P2AW_CDOM_OPEN) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FST; SND] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; DISCH_TAC] THEN
    SUBGOAL_THEN `open {w:real^(3,1)finite_sum | fstcart w IN u}` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
      ALL_TAC] THEN
    MP_TAC(ISPEC `p2bw_cdom (U:A->bool,phi:A->real^3) (b - a) INTER
                  {w:real^(3,1)finite_sum | fstcart w IN u}` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (x:real^3) (lift tau)`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; FSTCART_PASTECART] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ball(pastecart (x:real^3) (lift tau),r0) /\ sndcart w = lift tau
        ==> p2bw_cfun (U,phi:A->real^3)
              (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                      b p) w <=
            p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                     ((Wi:real^3->real^3)(fstcart w)) / (&2 * sqrt tau)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    USE_THEN "BLE" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p tau Z0 /
    (&2 * sqrt tau) =
    p2bw_cfun (U,phi:A->real^3) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
              (pastecart x (lift tau))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FSTCART_PASTECART; p2bw_cfun; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[p2a_lx; p2a_Ltil] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `chart_inv (U:A->bool,phi:A->real^3) x`)) THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC P2AW_L_LENGTH_CONG THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\w:real^(3,1)finite_sum.
                p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                         b p tau ((Wi:real^3->real^3)(fstcart w)) / (&2 * sqrt tau)` THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\y:real^(3,1)finite_sum.
         lift(p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                       b p tau ((Wi:real^3->real^3)(fstcart y)) / (&2 * sqrt tau))) =
      (\y. inv(&2 * sqrt tau) %
           ((\y'. lift(p2a_Ltil (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                                tau (Wi y'))) o fstcart) y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; real_div; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC P2AW_SMOOTH_FSTCART THEN REWRITE_TAC[OPEN_BALL]];
    MAP_EVERY X_GEN_TAC [`v:real^3`; `tt':real`] THEN STRIP_TAC THEN BETA_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SNDCART_ADD; SNDCART_SUB; SNDCART_CMUL; SNDCART_PASTECART] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_SUB_RZERO];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `U:A->bool`; `phi:A->real^3`; `x:real^3`;
                   `tau:real`; `s1:real`; `r:real`; `N:real^3->bool`;
                   `Phi:real^3->real^(3,3)finite_sum`; `sb':real`; `t:real^3->bool`;
                   `u:real^3->bool`; `Wi:real^3->real^3`; `Z0:real^3`; `X:real^3`; `r0:real`]
                  P2AW_FLOW_BAR_DIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The Sard null set.  In a chart (U,phi) of a flow, the points z = (x, tau) *)
(* at which some minimizer gamma = Lgeo Z0 ends at a conjugate point (J = 0) *)
(* lie in the image of the critical set of the space-time end map (s, Z) ->  *)
(* (phi(Lgeo Z (s^2) (s^2)), s^2), which is smooth on every window domain;   *)
(* BABY_SARD makes the image negligible.                                     *)
(* ------------------------------------------------------------------------- *)

let P2AW_SMIN_OF_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     p2a_min V tt x b gamma /\ Z IN p2a_Ldom V tt x b /\
     (!t. &0 <= t /\ t <= b ==> gamma t = p2a_Lgeo V tt x Z b t)
     ==> Z IN p2a_Smin V tt x b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min; p2a_adm]; ALL_TAC] THEN
  REWRITE_TAC[p2a_Smin; IN_ELIM_THM] THEN ASM_REWRITE_TAC[p2a_min] THEN
  SUBGOAL_THEN
   `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt (p2a_Lgeo V tt x Z b) b =
    p2a_L_length V tt (gamma:real->A) b /\
    p2a_Lgeo V tt x Z b b = gamma b`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2AW_L_LENGTH_CONG THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC P2AL_LGEO_ADM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[p2a_min]);;

let P2AW_WOK_LGEO_END = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z s.
     p2a_svs V /\ p2al_wok V tt x s1 r W a' b' U phi N Phi /\ Z IN N /\ s1 <= s /\ &0 < s /\
     s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z s
     ==> Z IN p2a_Ldom V tt x (s pow 2) /\
         p2a_Lgeo V tt x Z (s pow 2) (s pow 2) IN U INTER W /\
         phi(p2a_Lgeo V tt x Z (s pow 2) (s pow 2)) =
         fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2al_wok (V:p2alv) tt (x:A) s1 r W a' b' U phi N Phi` THEN
  REWRITE_TAC[p2al_wok] THEN
  DISCH_THEN(MP_TAC o SPECL [`Z:real^N`; `s:real`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gm:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Z:real^N) IN p2a_Ldom (V:p2alv) tt (x:A) (s pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_Ldom; IN_ELIM_THM] THEN EXISTS_TAC `gm:real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`; `s pow 2`; `gm:real->A`;
                 `p2a_Lgeo (V:p2alv) tt (x:A) (Z:real^N) (s pow 2)`] P2A_LGEOD_UNIQUE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2A_LGEO_PROP]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s pow 2`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let P2AW_PARTIAL_SND = prove
 (`!(Fm:real^(M,N)finite_sum->real^P) (G:real^N->real^P) c Z0.
     Fm differentiable (at (pastecart c Z0)) /\ (!Z. Fm(pastecart c Z) = G Z)
     ==> (G has_derivative
          (\v. frechet_derivative Fm (at (pastecart c Z0)) (pastecart (vec 0) v))) (at Z0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^P) = (Fm:real^(M,N)finite_sum->real^P) o (\Z. pastecart c Z)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. frechet_derivative (Fm:real^(M,N)finite_sum->real^P) (at (pastecart c Z0))
           (pastecart (vec 0) v)) =
    frechet_derivative Fm (at (pastecart c Z0)) o (\v:real^N. pastecart (vec 0:real^M) v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    BETA_TAC THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let P2AW_RANK_DEFICIENT = prove
 (`!(D:real^(1,N)finite_sum->real^(N,1)finite_sum) h.
     linear D /\ ~(h = vec 0) /\ D h = vec 0
     ==> rank(matrix D) < dimindex(:(N,1)finite_sum)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(rank(matrix(D:real^(1,N)finite_sum->real^(N,1)finite_sum)) =
                  dimindex(:(1,N)finite_sum))` MP_TAC THENL
   [REWRITE_TAC[FULL_RANK_INJECTIVE] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
    DISCH_THEN(MP_TAC o SPECL [`h:real^(1,N)finite_sum`; `vec 0:real^(1,N)finite_sum`]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `matrix(D:real^(1,N)finite_sum->real^(N,1)finite_sum)` RANK_BOUND) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC);;

let P2AW_WIN_ST_CRIT = prove
 (`!(V:p2alv) tt s1 r W a' b' U (phi:A->real^N) N Phi Z s.
     p2al_lwa V tt s1 r W a' b' U phi N Phi /\ Z IN N /\
     p2al_lin V tt s1 r W b' U phi Phi Z s /\
     det(p2al_jy V tt s1 r W b' U phi Phi Z s) = &0
     ==> ?D. ((\w. pastecart (fstcart(p2al_lfl V tt s1 r W b' U phi Phi (sndcart w)
                                               (drop(fstcart w))))
                             (lift(drop(fstcart w) pow 2))) has_derivative D)
             (at (pastecart (lift s) Z)) /\
             rank(matrix D) < dimindex(:(N,1)finite_sum)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  ABBREV_TAC
   `Fw = \w:real^(1,N)finite_sum.
           pastecart (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart w)
                                       (drop(fstcart w))))
                     (lift(drop(fstcart w) pow 2))` THEN
  SUBGOAL_THEN
   `smooth_map_on
      {z:real^(1,N)finite_sum | sndcart z IN N /\
           p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart z) (drop(fstcart z))}
      (Fw:real^(1,N)finite_sum->real^(N,1)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Fw" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum.
           fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart w)
                            (drop(fstcart w)))) =
        fstcart o (\z. p2al_lfl V tt s1 r W b' U phi Phi (sndcart z) (drop(fstcart z)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN
      ASM_SIMP_TAC[P2AW_SMOOTH_FSTCART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fw:real^(1,N)finite_sum->real^(N,1)finite_sum) differentiable
                (at (pastecart (lift s) Z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `{z:real^(1,N)finite_sum | sndcart z IN N /\
           p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi (sndcart z) (drop(fstcart z))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  EXISTS_TAC `frechet_derivative (Fw:real^(1,N)finite_sum->real^(N,1)finite_sum)
                                 (at (pastecart (lift s) Z))` THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MP_TAC(ISPEC `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s`
               HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2AW_RANK_DEFICIENT THEN EXISTS_TAC `pastecart (vec 0:real^1) (v:real^N)` THEN
  ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE; PASTECART_EQ_VEC] THEN
  SUBGOAL_THEN
   `(\Z'. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z' s))
      differentiable (at Z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `s1:real`; `r:real`; `W:A->bool`; `a':real`; `b':real`;
                   `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                   `Phi:real^N->real^(N,N)finite_sum`; `s:real`] P2AW_WIN_SLICE_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{Z:real^N | Z IN N /\
                            p2al_lin (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `(\Z'. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z' s)) =
      fstcart o (\Z. p2al_lfl V tt s1 r W b' U phi Phi Z s)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. frechet_derivative (Fw:real^(1,N)finite_sum->real^(N,1)finite_sum)
           (at (pastecart (lift s) Z)) (pastecart (vec 0) v)) =
    (\v. pastecart (frechet_derivative
                     (\Z'. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z' s))
                     (at Z) v) (vec 0))`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\Z'. pastecart (fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi
                                                 Z' s))
                               (lift(s pow 2))` THEN
    EXISTS_TAC `Z:real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AW_PARTIAL_SND THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Fw" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      REWRITE_TAC[HAS_DERIVATIVE_PASTECART_EQ; HAS_DERIVATIVE_CONST] THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^N`) THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PASTECART_EQ_VEC] THEN
  UNDISCH_TAC `p2al_jy (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z s ** v = vec 0` THEN
  REWRITE_TAC[p2al_jy] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
             (\Z'. fstcart(p2al_lfl (V:p2alv) tt s1 r W b' U (phi:A->real^N) Phi Z' s)) (at Z))`
  (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let P2AW_WOK_J_ZERO = prove
 (`!(V:p2alv) tt (x:A) s1 r W a' b' U (phi:A->real^N) N Phi Z0 s.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\
     p2al_wok V tt x s1 r W a' b' U phi N Phi /\
     Z0 IN N /\ s1 <= s /\ &0 < s /\ s < s1 + r /\ p2al_lin V tt s1 r W b' U phi Phi Z0 s /\
     p2a_J V tt x (s pow 2) Z0 = &0
     ==> det(p2al_jy V tt s1 r W b' U phi Phi Z0 s) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2al_lwa]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AL_LWIN_FACTS) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `s1:real`; `r:real`; `W:A->bool`; `a':real`;
                 `b':real`; `U:A->bool`; `phi:A->real^N`; `N:real^N->bool`;
                 `Phi:real^N->real^(N,N)finite_sum`; `Z0:real^N`; `s:real`] P2AL_WOK_J) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < p2a_zdens (V:p2alv) tt (x:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AL_ZDENS_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < sqrt(det(p2a_rlocal (V:p2alv) W b' (U INTER W,phi:A->real^N) (tt - s pow 2)
                   (fstcart(p2al_lfl V tt s1 r W b' U phi Phi Z0 s))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
    MATCH_MP_TAC P2AL_METRIC_PD THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2a_lsmooth] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th) &&
        not(is_forall(concl th)))) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`Z0:real^N`; `s:real`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lfield")) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `p2a_J (V:p2alv) tt (x:A) (s pow 2) Z0 = &0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_ENTIRE; REAL_ABS_ZERO; REAL_INV_EQ_0] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let P2AW_FLOW_END_WINDOW = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) x Z0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     x IN IMAGE phi U /\ tau < b - a /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     gamma tau = chart_inv (U,phi) x /\
     Z0 IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
     (!t. &0 <= t /\ t <= tau
          ==> gamma t = p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p Z0
                                 tau t)
     ==> ?s1 r N Phi.
           p2al_wok (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p s1 r U a b U phi
                    N Phi /\
           s1 < sqrt tau /\ sqrt tau < s1 + r /\ Z0 IN N /\
           p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi Z0
                    (sqrt tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN U` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`] P2AW_FLOW_MIN_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `Av:real^1->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `Z0:real^3`; `s0:real`; `Av:real^1->real^3`]
                P2AW_FLOW_CWIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:real^3->bool`
    (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `r:real`; `N:real^3->bool`;
                        `Phi:real^3->real^(3,3)finite_sum`] THEN
  ASM_SIMP_TAC[P2AL_LWIN_WOK]);;

let P2AW_FLOW_CONJ_NULL = prove
 (`!top atlas a b (g:real->A->real^3^3) p U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas
     ==> ?Nb. negligible Nb /\
              !x tau gamma Z0.
                x IN IMAGE phi U /\ tau < b - a /\
                p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
                gamma tau = chart_inv (U,phi) x /\
                Z0 IN p2a_Ldom (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau /\
                (!t. &0 <= t /\ t <= tau
                     ==> gamma t = p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                            b p Z0 tau t) /\
                ~(pastecart x (lift tau) IN Nb)
                ==> &0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau Z0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                           (g:real->A->real^3^3)) b = top` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) p b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `Hc = \w:real^(1,3)finite_sum.
           pastecart ((phi:A->real^3)
                        (p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b])
                                     (g:real->A->real^3^3)) b p (sndcart w)
                                  (drop(fstcart w) pow 2) (drop(fstcart w) pow 2)))
                     (lift(drop(fstcart w) pow 2))` THEN
  ABBREV_TAC
   `S = {w:real^(1,3)finite_sum |
           ?s1 r N Phi.
             p2al_wok (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                      b p s1 r U a b U (phi:A->real^3) N Phi /\
             sndcart w IN N /\ s1 < drop(fstcart w) /\ drop(fstcart w) < s1 + r /\
             p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                      (sndcart w) (drop(fstcart w)) /\
             det(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                         (sndcart w) (drop(fstcart w))) = &0}` THEN
  EXISTS_TAC `IMAGE (Hc:real^(1,3)finite_sum->real^(3,1)finite_sum) S` THEN CONJ_TAC THENL
   [MATCH_MP_TAC BABY_SARD THEN
    EXISTS_TAC `\w. frechet_derivative (Hc:real^(1,3)finite_sum->real^(3,1)finite_sum) (at w)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_3] THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real^(1,3)finite_sum` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `?s1 r N Phi.
        p2al_wok (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                 b p s1 r U a b U (phi:A->real^3) N Phi /\
        sndcart(w:real^(1,3)finite_sum) IN N /\ s1 < drop(fstcart w) /\
        drop(fstcart w) < s1 + r /\
        p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                 (sndcart w) (drop(fstcart w)) /\
        det(p2al_jy (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b s1 r U b U phi Phi
                    (sndcart w) (drop(fstcart w))) = &0`
    MP_TAC THENL
     [UNDISCH_TAC `(w:real^(1,3)finite_sum) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:real^3->bool`
      (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum` STRIP_ASSUME_TAC)))) THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2al_wok]) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o MATCH_MP P2AL_LWIN_FACTS) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                   `phi:A->real^3`; `N:real^3->bool`; `Phi:real^3->real^(3,3)finite_sum`;
                   `sndcart(w:real^(1,3)finite_sum)`; `drop(fstcart(w:real^(1,3)finite_sum))`]
                  P2AW_WIN_ST_CRIT) THEN
    ASM_REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real^(1,3)finite_sum->real^(3,1)finite_sum` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `((Hc:real^(1,3)finite_sum->real^(3,1)finite_sum) has_derivative D) (at w)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC
       `\w:real^(1,3)finite_sum.
          pastecart (fstcart(p2al_lfl (p2a_flow_view (top,atlas) (real_interval[a,b])
                                        (g:real->A->real^3^3)) b s1 r U b U phi Phi
                                      (sndcart w) (drop(fstcart w))))
                    (lift(drop(fstcart w) pow 2))` THEN
      EXISTS_TAC
       `{z:real^(1,3)finite_sum |
           sndcart z IN N /\
           p2al_lin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b s1
                    r U b U phi Phi (sndcart z) (drop(fstcart z))} INTER
        {z:real^(1,3)finite_sum | fstcart z IN interval(lift s1,lift(s1 + r))}` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
        SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART; OPEN_INTERVAL];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP];
        X_GEN_TAC `w':real^(1,3)finite_sum` THEN
        REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
        EXPAND_TAC "Hc" THEN REWRITE_TAC[PASTECART_INJ] THEN CONV_TAC SYM_CONV THEN
        MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                       `b:real`; `p:A`; `s1:real`; `r:real`; `U:A->bool`; `a:real`; `b:real`;
                       `U:A->bool`; `phi:A->real^3`; `N:real^3->bool`;
                       `Phi:real^3->real^(3,3)finite_sum`; `sndcart(w':real^(1,3)finite_sum)`;
                       `drop(fstcart(w':real^(1,3)finite_sum))`] P2AW_WOK_LGEO_END) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2al_wok] o check (fun th ->
            can (find_term (fun t -> is_const t && fst(dest_const t) = "p2al_wok")) (concl th) &&
            not(is_forall(concl th)))) THEN
          ASM_REAL_ARITH_TAC;
          SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (Hc:real^(1,3)finite_sum->real^(3,1)finite_sum) (at w) = D`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `tau:real`; `gamma:real->A`; `Z0:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_min; p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p tau Z0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `tau:real`; `Z0:real^3`; `sqrt tau`] P2AL_J_NONNEG) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= j /\ ~(j = &0) ==> &0 < j`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `x:real^3`; `Z0:real^3`] P2AW_FLOW_END_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:real^3->bool`
    (X_CHOOSE_THEN `Phi:real^3->real^(3,3)finite_sum` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `pastecart (lift(sqrt tau)) (Z0:real^3) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MAP_EVERY EXISTS_TAC [`s1:real`; `r:real`; `N:real^3->bool`;
                          `Phi:real^3->real^(3,3)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AW_WOK_J_ZERO THEN
    MAP_EVERY EXISTS_TAC [`p:A`; `a:real`; `N:real^3->bool`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (x:real^3) (lift tau) =
                (Hc:real^(1,3)finite_sum->real^(3,1)finite_sum) (pastecart (lift(sqrt tau)) Z0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Hc" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[PASTECART_INJ] THEN
    SUBGOAL_THEN `p2a_Lgeo (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                           b p Z0 tau tau = (gamma:real->A) tau` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift(sqrt tau)) (Z0:real^3)` o
    REWRITE_RULE[IN_IMAGE; NOT_EXISTS_THM] o check (fun th -> is_neg(concl th) &&
    can (find_term ((=) `Hc:real^(1,3)finite_sum->real^(3,1)finite_sum`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;


