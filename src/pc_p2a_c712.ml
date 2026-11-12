(* ========================================================================= *)
(* pc_p2a_c712: route obligation O11 against the FIX forms (MT              *)
(* Thm 7.10 / Cor 7.12): the barrier at slice minima (L13 FIX), the         *)
(* Dini comparison lemma and the small-time bound from the constant curve   *)
(* at x give the bound 3/2 for the slice minima of lx (C3 FIX).             *)
(* The first part: the constant curve at x in a backward region is          *)
(* admissible and its L-length is O(tau^(3/2)).                             *)
(* ========================================================================= *)

needs "src/pc_p2a_defs3.ml";;
needs "src/pc_p2a_lconv.ml";;
needs "src/pc_p2a_seg.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_CONST_SMALL_TIME = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x W a'.
     p2a_svs V /\ p2a_region V W a' tt /\ x IN W /\ a' < tt
     ==> ?t0 Kr. &0 < t0 /\
                 !tau. &0 < tau /\ tau < t0
                       ==> p2a_adm V tt x tau (\s. x) /\
                           p2a_L_length V tt (\s. x) tau <= Kr * tau * sqrt tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(W:A->bool) SUBSET topspace(p2a_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?U (phi:A->real^N). (U,phi) IN p2a_vatlas (V:(real->A topology)#
                          (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\
                        x IN U`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) tt`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt) (x:A))`;
      `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt) (x:A))`] THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  ABBREV_TAC `h = sqrt((tt - a') / &2)` THEN
  SUBGOAL_THEN `&0 < h /\ h pow 2 = (tt - a') / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SUBGOAL_THEN `&0 < (tt - a') / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. --h < s /\ s < h ==> s pow 2 < (tt - a') / &2` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `h pow 2 = (tt - a') / &2`)) THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (--h) h
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W tt (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LSMOOTH_LSCALAR) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN DISCH_TAC THEN
  ABBREV_TAC `ls = \s. lscalar (p2a_rlocal (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt
                   (U INTER W,phi:A->real^N) (tt - s pow 2)) (phi(x:A))` THEN
  SUBGOAL_THEN `(\s. lift((ls:real->real) (drop s))) continuous_on
                interval[lift(&0),lift(h / &2)]` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. lift((ls:real->real) (drop s))) =
                  (\z. lift(lscalar ((\s. p2a_rlocal (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt
                     (U INTER W,phi:A->real^N) (tt - s pow 2)) (drop(fstcart z)))
                     (sndcart z))) o (\s. pastecart s ((phi:A->real^N) x))`
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
  SUBGOAL_THEN `?Kr. !s. &0 <= s /\ s <= h / &2 ==> abs((ls:real->real) s) <= Kr`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\s. lift((ls:real->real) (drop s))) (interval[lift(&0),lift(h / &2)])`
                 COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                NORM_LIFT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(h / &2) pow 2` THEN EXISTS_TAC `abs Kr` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt tau < h / &2 /\ &0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt((h / &2) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < tt - tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `tau < (tt - a') / &2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* membership of x in the slices *)
  SUBGOAL_THEN `!sig. &0 <= sig /\ sig <= tau
                      ==> (x:A) IN topspace(p2a_vtop (V:(real->A topology)#
                            (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - sig))`
  ASSUME_TAC THENL
   [X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `tt - sig`]
                  P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(W:A->bool) SUBSET topspace(p2a_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - sig))`
    MP_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the integrand *)
  SUBGOAL_THEN
   `!sig. &0 <= sig /\ sig <= tau
          ==> p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) tt (\s. x:A) tau sig =
              sqrt sig * (ls:real->real) (sqrt sig)`
  ASSUME_TAC THENL
   [X_GEN_TAC `sig:real` THEN STRIP_TAC THEN ASM_CASES_TAC `sig = &0` THENL
     [ASM_REWRITE_TAC[p2a_L_integrand; SQRT_0; REAL_MUL_LZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sig` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt sig /\ sqrt sig pow 2 = sig` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `\s:real. (x:A)`; `tau:real`; `sqrt sig`;
                   `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                   `vec 0:real^N`] P2A_LINT_REGION) THEN
    ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; IN_INTER] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[REAL_LT_01];
      ALL_TAC] THEN
    REWRITE_TAC[p2a_llag; DOT_LZERO; MATRIX_VECTOR_MUL_RZERO; REAL_MUL_RZERO;
                REAL_ADD_LID] THEN
    EXPAND_TAC "ls" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sqrt sig pow 2 = sig` THEN
    UNDISCH_TAC `&0 < sqrt sig` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\sig. sqrt sig * (ls:real->real) (sqrt sig)) real_continuous_on
                real_interval[&0,tau]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
    SUBGOAL_THEN `(\sig. (ls:real->real) (sqrt sig)) = ls o sqrt` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,h / &2]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `sig:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau` THEN
      ASM_SIMP_TAC[SQRT_MONO_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (\s. x:A) tau has_real_integral
     real_integral (real_interval[&0,tau]) (\sig. sqrt sig * (ls:real->real) (sqrt sig)))
    (real_interval[&0,tau])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\sig. sqrt sig * (ls:real->real) (sqrt sig)` THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_INTEGRABLE_INTEGRAL; REAL_INTEGRABLE_CONTINUOUS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2a_adm] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
      EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
      MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC P2A_CD1_FROM_AT THEN
      EXISTS_TAC `\s:real^1. vec 0:real^N` THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; CONTINUOUS_CONST];
      X_GEN_TAC `sig:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_smooth] THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `tt:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_L_length] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  MP_TAC(ISPECL [`\sig. sqrt sig * (ls:real->real) (sqrt sig)`; `&0`; `tau:real`;
                 `real_integral (real_interval[&0,tau])
                    (\sig. sqrt sig * (ls:real->real) (sqrt sig))`;
                 `abs Kr * sqrt tau`] HAS_REAL_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; SQRT_POS_LE; REAL_LT_IMP_LE;
                 REAL_INTEGRABLE_INTEGRAL; REAL_INTEGRABLE_CONTINUOUS] THEN
    X_GEN_TAC `sig:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(sqrt sig) = sqrt sig` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL; SQRT_POS_LE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; SQRT_POS_LE; SQRT_MONO_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt tau` THEN ASM_SIMP_TAC[SQRT_MONO_LE; REAL_LT_IMP_LE];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The route obligation O11 against the FIX forms, P2A_ROUTE_COR_7_12_FIX.  *)
(* f(tau) is lx at a chosen slice minimum m tau of U(tt - tau).  It is      *)
(* lower semicontinuous by hypothesis; its upper Dini derivative is bounded *)
(* by the barrier L13 FIX at m tau, which minimizes L over the open set W   *)
(* of its slice given by p2a_st_open; it is small near 0 by the constant    *)
(* curve at x.  P2A_DINI then gives f <= 3/2.                               *)
(* ========================================================================= *)

let P2A_VBALL_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x r.
     rfs_vball V t x r =
     mfd_ball (p2a_vtop V t,p2a_vatlas V t) (p2a_vmetric V t) x r`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; p2a_vtop; p2a_vatlas; p2a_vmetric]);;

let P2A_C712_VBALL_CENTRE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r.
     p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ &0 < r ==> x IN rfs_vball V tt x r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_VBALL_ALT; GSYM P2A_VIEW_PROJ_3; p2a_svs] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `tt:real`) THEN
  SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) = {})` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]);;

let P2A_C712_LX_LE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x U tau y g.
     (!t y. y IN U t ==> ?gamma. p2a_min V tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
     y IN U (tt - tau) /\ p2a_adm V tt x tau g /\ g tau = y
     ==> p2a_Lx V tt x tau y <= p2a_L_length V tt g tau`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`tt - tau:real`; `y:A`]) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `tt - (tt - tau) = tau:real`] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_MIN_LX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau gamma` THEN
  REWRITE_TAC[p2a_min] THEN DISCH_THEN(MP_TAC o SPEC `g:real->A` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* C3 FIX needs only the barrier L13 FIX and P2A_DINI (L3 is not used).     *)

let P2A_COR_7_12_FIX_FROM_BARRIER = prove
 (`!u:A->bool. P2A_BARRIER_FIX_STATEMENT u ==> P2A_COR_7_12_VIEW_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_COR_7_12_VIEW_FIX_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "bar") THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `tt:real`; `a:real`; `U:real->A->bool`; `r:real`; `dt:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sto") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hmin") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hball") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hne") (LABEL_TAC "hlsc")) THEN
  SUBGOAL_THEN `(x:A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_C712_VBALL_CENTRE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x tt` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_bsmooth] THEN
    MAP_EVERY EXISTS_TAC [`rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - dt:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a slice minimum m tau of U(tt - tau) for each tau in (0,tt - a] *)
  SUBGOAL_THEN
   `?m:real->A. !tau. &0 < tau /\ tau <= tt - a
        ==> m tau IN U (tt - tau) /\
            !z. z IN U (tt - tau)
                ==> p2a_Lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau (m tau) <= p2a_Lx V tt x tau z`
  (X_CHOOSE_THEN `m:real->A` (LABEL_TAC "m")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    USE_THEN "hne" (MP_TAC o SPEC `tt - tau:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; p2a_Lmin_set; IN_ELIM_THM;
                REAL_ARITH `tt - (tt - tau) = tau:real`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau z. &0 < tau /\ tau <= tt - a /\ z IN U (tt - tau)
            ==> p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau ((m:real->A) tau) <= p2a_lx V tt x tau z`
  (LABEL_TAC "mle") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lx] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    USE_THEN "m" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau g. &0 < tau /\ tau <= tt - a /\ p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau g /\
            (g:real->A) tau IN U (tt - tau)
            ==> p2a_lx V tt x tau ((m:real->A) tau) <=
                p2a_L_length V tt g tau / (&2 * sqrt tau)`
  (LABEL_TAC "mlx") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau ((g:real->A) tau)` THEN CONJ_TAC THENL
     [USE_THEN "mle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p2a_lx] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC P2A_C712_LX_LE THEN EXISTS_TAC `U:real->A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the Dini comparison for f = lx at the slice minima *)
  MP_TAC(SPECL
    [`\tau. p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau ((m:real->A) tau)`; `&3 / &2`; `tt - a:real`]
    (REWRITE_RULE[P2A_DINI_STATEMENT] P2A_DINI)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      (* lower semicontinuity *)
      MAP_EVERY X_GEN_TAC [`tau:real`; `e:real`] THEN STRIP_TAC THEN
      USE_THEN "hlsc" (MP_TAC o SPECL [`tt - tau:real`; `e:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dl"))) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
      USE_THEN "m" (MP_TAC o SPEC `tau':real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      USE_THEN "dl" (MP_TAC o SPECL [`tt - tau':real`; `(m:real->A) tau'`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `tt - (tt - s) = s:real`] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau y` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "mle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      (* the upper Dini derivative, by the barrier at m tau *)
      MAP_EVERY X_GEN_TAC [`tau:real`; `e:real`] THEN STRIP_TAC THEN
      USE_THEN "m" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mmin")) THEN
      USE_THEN "hmin" (MP_TAC o SPECL [`tt - tau:real`; `(m:real->A) tau`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `tt - (tt - s) = s:real`] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      USE_THEN "sto" (MP_TAC o SPECL [`tt - tau:real`; `(m:real->A) tau`] o
                      CONJUNCT2 o REWRITE_RULE[p2a_st_open]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `eta:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wsub")))))) THEN
      SUBGOAL_THEN
       `!g':real->A. p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau g' /\ g' tau IN W
                     ==> p2a_L_length V tt gamma tau <= p2a_L_length V tt g' tau`
      ASSUME_TAC THENL
       [X_GEN_TAC `g':real->A` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(g':real->A) tau IN U (tt - tau)` ASSUME_TAC THENL
         [USE_THEN "wsub" (MP_TAC o SPEC `tt - tau:real`) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `p2a_Lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau ((g':real->A) tau)` THEN CONJ_TAC THENL
         [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP P2A_MIN_LX) THEN
          ASM_REWRITE_TAC[] THEN USE_THEN "mmin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC P2A_C712_LX_LE THEN EXISTS_TAC `U:real->A->bool` THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      USE_THEN "bar" (MP_TAC o SPECL
        [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
         `tt:real`; `x:A`; `tau:real`; `gamma:real->A`; `W:A->bool`; `e:real`] o
        REWRITE_RULE[P2A_BARRIER_FIX_STATEMENT]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MP_TAC o SPEC `tt - tau:real` o GEN_REWRITE_RULE I [P2A_PERSISTS_ALT]) THEN
        REWRITE_TAC[P2A_VIEW_PROJ_3] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
      EXISTS_TAC `min d eta` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `tau' < tau + d /\ tau' < tau + eta` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "bd" (MP_TAC o SPEC `tau':real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau ((m:real->A) tau) =
        p2a_L_length V tt gamma tau / (&2 * sqrt tau)`
      SUBST1_TAC THENL
       [REWRITE_TAC[p2a_lx] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP P2A_MIN_LX) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!b:real. a <= b /\ b - c <= k ==> a - c <= k`) THEN
      EXISTS_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt g tau' / (&2 * sqrt tau')` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "mlx" MATCH_MP_TAC THEN
      UNDISCH_TAC `p2a_adm1 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x tau' g` THEN REWRITE_TAC[p2a_adm1] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "wsub" (MP_TAC o SPEC `tt - tau':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      (* small times, by the constant curve at x *)
      MP_TAC(ISPECL
        [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
         `tt:real`; `x:A`; `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt x r`; `tt - dt:real`]
        P2A_CONST_SMALL_TIME) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `Kr:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kr")))) THEN
      EXISTS_TAC `min t0 (min dt (&3 / (abs Kr + &1)))` THEN
      SUBGOAL_THEN `&0 < &3 / (abs Kr + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `tau < t0 /\ tau < dt /\ tau < &3 / (abs Kr + &1)` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "kr" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (\s:real. (x:A)) tau / (&2 * sqrt tau)` THEN
      CONJ_TAC THENL
       [USE_THEN "mlx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "hball" (MP_TAC o SPEC `tt - tau:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt tau` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kr * tau * sqrt tau` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `Kr * tau <= &3` ASSUME_TAC THENL
       [SUBGOAL_THEN `tau * (abs Kr + &1) < &3` MP_TAC THENL
         [UNDISCH_TAC `tau < &3 / (abs Kr + &1)` THEN
          SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs x + &1`];
          ALL_TAC] THEN
        SUBGOAL_THEN `Kr * tau <= abs Kr * tau` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_ABS_LE; REAL_LT_IMP_LE];
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(Kr * tau) * sqrt tau <= &3 * sqrt tau` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  EXISTS_TAC `(m:real->A) (tt - t)` THEN
  SUBGOAL_THEN `&0 < tt - t /\ tt - t <= tt - a` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "m" (MP_TAC o SPEC `tt - t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `tt - (tt - t) = t:real`] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `tt - t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[]]);;

let P2A_ROUTE_COR_7_12_FIX = prove
 (`!u:A->bool. P2A_ROUTE_COR_7_12_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_ROUTE_COR_7_12_FIX_STATEMENT] THEN
  MESON_TAC[P2A_COR_7_12_FIX_FROM_BARRIER]);;

(* The statement P2_COR_7_12_STATEMENT (MT Cor 7.12) from the barrier L13   *)
(* FIX and the history bridge.                                              *)

let P2A_COR_7_12_FROM_BARRIER = prove
 (`!u:A->bool. P2A_BARRIER_FIX_STATEMENT u /\ P2A_HIST_VIEW_STATEMENT u
               ==> P2_COR_7_12_STATEMENT u`,
  MESON_TAC[P2A_T3_FIX; P2A_COR_7_12_FIX_FROM_BARRIER]);;

