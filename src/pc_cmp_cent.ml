(* ========================================================================= *)
(* Unit pc_cmp_cent (comparison-geometry layer CMP, third unit of the        *)
(* Cheeger-Gromov-Taylor bound CMP_T2_CGT): iterates of a deck map and their *)
(* distinctness.  The iterates tau^k of a deck map tau_p are deck maps on    *)
(* shrinking balls with |tau^k w| <= k|p| + |w|; a fixed point of a deck map *)
(* makes it the identity; and if tau^m = id near 0 then the centre of mass   *)
(* of the orbit, the minimiser of F(y) = sum_{k<m} |tau^k y|^2 (strictly     *)
(* convex along geodesics of the pullback, tau-invariant), is fixed by tau,  *)
(* so p = 0.  Hence for p <> 0 no iterate tau_p^m has a fixed point near 0   *)
(* (CMPY_NO_PERIOD).                                                         *)
(* ========================================================================= *)

needs "src/pc_cmp_deck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Restriction and iterates of deck maps; a deck map with a fixed point on a *)
(* connected set is the identity there.                                      *)
(* ========================================================================= *)

let CMPY_DECK_SUBSET = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho W W' sigma.
        cmp_deck (top,atlas) g x E rho W sigma /\ open W' /\ W' SUBSET W
        ==> cmp_deck (top,atlas) g x E rho W' sigma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_deck] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[]]);;

let CMPY_ITER = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) rho s l tau.
        cmp_deck (top,atlas) g x E rho (ball(vec 0,s)) tau /\ &0 <= l /\ s <= rho /\
        (!w. norm w < s ==> norm(tau w) <= l + norm w)
        ==> !k. cmp_deck (top,atlas) g x E rho (ball(vec 0,s - &k * l)) (ITER k tau) /\
                (!w. norm w < s - &k * l ==> norm(ITER k tau w) <= &k * l + norm w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_ADD_LID; ITER; REAL_LE_REFL] THEN
    SUBGOAL_THEN `ITER 0 (tau:real^N->real^N) = (\w. w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; ITER]; ALL_TAC] THEN
    MATCH_MP_TAC CMPK_DECK_ID THEN REWRITE_TAC[OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nk")) THEN
  SUBGOAL_THEN `ITER (SUC k) (tau:real^N->real^N) = tau o ITER k tau` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ITER; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID; o_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPK_DECK_COMPOSE THEN EXISTS_TAC `ball(vec 0:real^N,s)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPY_DECK_SUBSET THEN EXISTS_TAC `ball(vec 0:real^N,s - &k * l)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^N` THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&k * l + norm(w:real^N)` THEN CONJ_TAC THENL
       [USE_THEN "nk" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(ITER k (tau:real^N->real^N) w) <= &k * l + norm(w:real^N)`
    ASSUME_TAC THENL
     [USE_THEN "nk" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `l + norm(ITER k (tau:real^N->real^N) w)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let CMPY_FIXED_ID = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma c.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma /\ connected W /\ c IN W /\ sigma c = c
        ==> !w. w IN W ==> sigma w = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `sigma:real^N->real^N`; `\w:real^N. w`; `c:real^N`]
    CMPK_DECK_RIGID) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPK_DECK_ID THEN ASM_MESON_TAC[cmp_deck]);;

(* ========================================================================= *)
(* A function on [0,1] with phi' = 2 psi, psi' >= d > 0 and phi(1) = phi(0)  *)
(* <= phi cannot exist (strict convexity).                                   *)
(* ========================================================================= *)

let CMPY_CONVEX_CONTRA = prove
 (`!(phi:real->real) phi' psi psi' J d.
        is_realinterval J /\ &0 IN J /\ &1 IN J /\ &0 < d /\
        (!t. t IN J ==> (phi has_real_derivative phi'(t)) (atreal t) /\
                        (psi has_real_derivative psi'(t)) (atreal t) /\
                        phi'(t) = &2 * psi(t) /\ d <= psi'(t)) /\
        phi(&1) = phi(&0) /\ (!t. &0 <= t /\ t <= &1 ==> phi(&0) <= phi(t))
        ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "der") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `!a b. &0 <= a /\ b <= &1 ==> real_interval[a,b] SUBSET (J:real->bool)`
  (LABEL_TAC "sub") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval (J:real->bool)` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!t. t IN J ==> ((phi:real->real) has_real_derivative phi'(t)) (atreal t)) /\
    (!t. t IN J ==> ((psi:real->real) has_real_derivative psi'(t)) (atreal t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "der" (fun th -> MP_TAC(MATCH_MP (SPEC `t:real` th)
      (ASSUME `(t:real) IN J`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f f' a b. &0 <= a /\ a <= b /\ b <= &1 /\
               (!t. t IN J ==> (f has_real_derivative f'(t)) (atreal t))
               ==> ?z. z IN real_interval[a,b] /\ f b - f a = f' z * (b - a)`
  (LABEL_TAC "mvt") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MVT_VERY_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "sub" (MP_TAC o SPECL [`a:real`; `b:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `phi':real->real`; `&0`; `&1`] REAL_MVT_SIMPLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPECL [`&0`; `&1`]) THEN
      REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(xi:real) IN J` ASSUME_TAC THENL
   [USE_THEN "sub" (MP_TAC o SPECL [`&0`; `&1`]) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real->real) xi = &0` ASSUME_TAC THENL
   [USE_THEN "der" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `xi:real` th)
      (ASSUME `(xi:real) IN J`))) THEN UNDISCH_TAC `(phi:real->real) (&1) - phi (&0) = phi' (xi:real)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. xi < t /\ t <= &1 ==> &0 < (psi:real->real) t` (LABEL_TAC "pos") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "mvt" (MP_TAC o SPECL [`psi:real->real`; `psi':real->real`; `xi:real`;
                                    `t:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(eta:real) IN J` ASSUME_TAC THENL
     [USE_THEN "sub" (MP_TAC o SPECL [`xi:real`; `t:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "der" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `eta:real` th)
      (ASSUME `(eta:real) IN J`))) THEN
    SUBGOAL_THEN `d * (t - xi) <= (psi':real->real) eta * (t - xi)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d * (t - xi)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t2 = (xi + &1) / &2` THEN
  SUBGOAL_THEN `xi < t2 /\ t2 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "mvt" (MP_TAC o SPECL [`phi:real->real`; `phi':real->real`; `t2:real`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(eta:real) IN J` ASSUME_TAC THENL
   [USE_THEN "sub" (MP_TAC o SPECL [`t2:real`; `&1`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "der" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `eta:real` th)
      (ASSUME `(eta:real) IN J`))) THEN
  USE_THEN "pos" (MP_TAC o SPEC `eta:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < (phi':real->real) eta * (&1 - t2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t2:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `(phi:real->real) (&0)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* For m geodesics beta_k of the pullback with K |beta_k|^2 <= 1/2 and       *)
(* common energy sig2, phi = sum |beta_k|^2 has phi' = 2 psi with psi = sum  *)
(* beta_k . V_k and psi' >= m sig2 / 2.                                      *)
(* ========================================================================= *)

let CMPY_SUM_CONVEX = prove
 (`!U (G:real^N->real^N^N) K m (bt:num->real->real^N) J sig2 t.
        open U /\ metric_field U G /\ (!z. z IN U ==> G z ** z = z) /\ &0 <= K /\
        (!w a. w IN U /\ ~(w = vec 0)
               ==> (inv(norm w) - K * norm w) *
                   (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2) <=
                   cmp_lhess G (\z. norm z) w a a) /\
        (!k. k <= m - 1
             ==> mfd_geodesic (subtopology euclidean U,open_set_atlas U) G (bt k) J) /\
        (!k s. k <= m - 1 /\ s IN J
               ==> K * (bt k s dot bt k s) <= inv(&2) /\
                   mfd_vel (open_set_atlas U) (bt k) s dot
                   (G(bt k s) ** mfd_vel (open_set_atlas U) (bt k) s) = sig2) /\
        1 <= m /\ t IN J
        ==> ((\s. sum(0..m-1) (\k. bt k s dot bt k s)) has_real_derivative
             (&2 * sum(0..m-1) (\k. bt k t dot mfd_vel (open_set_atlas U) (bt k) t)))
            (atreal t) /\
            ((\s. sum(0..m-1) (\k. bt k s dot mfd_vel (open_set_atlas U) (bt k) s))
             has_real_derivative
             sum(0..m-1) (\k. mfd_vel (open_set_atlas U) (bt k) t dot
                              mfd_vel (open_set_atlas U) (bt k) t -
                              bt k t dot christoffel G (bt k t)
                                (mfd_vel (open_set_atlas U) (bt k) t)
                                (mfd_vel (open_set_atlas U) (bt k) t))) (atreal t) /\
            &m * (inv(&2) * sig2) <=
            sum(0..m-1) (\k. mfd_vel (open_set_atlas U) (bt k) t dot
                             mfd_vel (open_set_atlas U) (bt k) t -
                             bt k t dot christoffel G (bt k t)
                               (mfd_vel (open_set_atlas U) (bt k) t)
                               (mfd_vel (open_set_atlas U) (bt k) t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "geo")
    (CONJUNCTS_THEN2 (LABEL_TAC "bd") STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN
   `!k. k <= m - 1
        ==> ((\s. (bt:num->real->real^N) k s dot bt k s) has_real_derivative
             (&2 * (bt k t dot mfd_vel (open_set_atlas U) (bt k) t))) (atreal t) /\
            ((\s. bt k s dot mfd_vel (open_set_atlas U) (bt k) s) has_real_derivative
             (mfd_vel (open_set_atlas U) (bt k) t dot mfd_vel (open_set_atlas U) (bt k) t -
              bt k t dot christoffel (G:real^N->real^N^N) (bt k t)
                (mfd_vel (open_set_atlas U) (bt k) t)
                (mfd_vel (open_set_atlas U) (bt k) t))) (atreal t) /\
            (&1 - K * (bt k t dot bt k t)) *
            (mfd_vel (open_set_atlas U) (bt k) t dot
             (G(bt k t) ** mfd_vel (open_set_atlas U) (bt k) t)) <=
            mfd_vel (open_set_atlas U) (bt k) t dot mfd_vel (open_set_atlas U) (bt k) t -
            bt k t dot christoffel G (bt k t)
              (mfd_vel (open_set_atlas U) (bt k) t) (mfd_vel (open_set_atlas U) (bt k) t)`
  (LABEL_TAC "cd") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC CMPW_CONVEX_DERIV THEN
    EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "geo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "cd" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
      (ASSUME `k <= m - 1`)))) THEN REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "cd" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP th
      (ASSUME `k <= m - 1`))))) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..m-1) (\k:num. inv(&2) * sig2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    SUBGOAL_THEN `(m - 1 + 1) - 0 = m` SUBST1_TAC THENL
     [UNDISCH_TAC `1 <= m` THEN ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[LE_0] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "cd" (fun th -> MP_TAC(CONJUNCT2(CONJUNCT2(MATCH_MP th
    (ASSUME `k <= m - 1`))))) THEN
  USE_THEN "bd" (fun th -> MP_TAC(MATCH_MP (SPECL [`k:num`; `t:real`] th)
    (CONJ (ASSUME `k <= m - 1`) (ASSUME `(t:real) IN J`)))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sig2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `sig2:real`)) THEN
    MATCH_MP_TAC CMPW_METRIC_POS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(bt:num->real->real^N) k`;
                   `J:real->bool`] CMPW_GEO_ODE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "geo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (inv(&2) - K * ((bt:num->real->real^N) k t dot bt k t)) * sig2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A short geodesic of the pullback from c to tau_p c (local Hopf-Rinow;     *)
(* d(c, tau c) <= d(c,0) + d(0,p) + d(p,tau c) <= 2|c| + |p|).               *)
(* ========================================================================= *)

let CMPY_SHORT = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R p c b1.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm p < R /\
        cmp_psi (top,atlas) g x E p = x /\ norm c < R - norm p /\
        norm c + b1 <= R /\ &2 * norm c + norm p < b1
        ==> ?v. v IN mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),
                                  open_set_atlas (ball(vec 0,rho)))
                                 (cmp_expmetric (top,atlas) g x E) c /\
                mfd_tnorm (cmp_expmetric (top,atlas) g x E) c v <= &2 * norm c + norm p /\
                mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                         open_set_atlas (ball(vec 0,rho)))
                        (cmp_expmetric (top,atlas) g x E) c v =
                cmp_tau (top,atlas) g x E rho p c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN ball(vec 0:real^N,rho)
                    ==> cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) z ** z = z`
  ASSUME_TAC THENL [REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,R) SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(c:real^N) < rho /\ norm(p:real^N) < rho /\
                (c:real^N) IN ball(vec 0,rho) /\ (p:real^N) IN ball(vec 0,rho) /\
                vec 0 IN ball(vec 0:real^N,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; NORM_0] THEN
    MP_TAC(ISPEC `p:real^N` NORM_POS_LE) THEN MP_TAC(ISPEC `c:real^N` NORM_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G = cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)` THEN
  SUBGOAL_THEN `!w:real^N. norm w < rho
                ==> mfd_joinable (subtopology euclidean (ball(vec 0,rho)),
                                  open_set_atlas (ball(vec 0,rho))) (vec 0) w /\
                    mfd_dist (subtopology euclidean (ball(vec 0,rho)),
                              open_set_atlas (ball(vec 0,rho))) (G:real^N->real^N^N)
                             (vec 0) w <= norm w`
  (LABEL_TAC "zero") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `rho:real`; `w:real^N`] CMPW_EXP_ZERO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `vec 0:real^N`; `w:real^N`] CMPH_EXP_DIST_LE) THEN
    ASM_REWRITE_TAC[mfd_tnorm; MATRIX_VECTOR_MUL_LID; GSYM vector_norm];
    ALL_TAC] THEN
  ABBREV_TAC `L = matrix_inv(cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) p) ** E` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `p:real^N`;
                 `c:real^N`] CMPK_LP_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `R:real`; `p:real^N`;
                 `(L:real^N^N) ** c`] CMPW_EXP_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `p:real^N`; `(L:real^N^N) ** c`] CMPH_EXP_DIST_LE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_exp (subtopology euclidean (ball(vec 0:real^N,rho)),open_set_atlas (ball(vec 0,rho)))
            (G:real^N->real^N^N) p ((L:real^N^N) ** c) =
    cmp_tau (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho p c`
  SUBST1_TAC THENL
   [EXPAND_TAC "L" THEN EXPAND_TAC "G" THEN REWRITE_TAC[cmp_tau]; ALL_TAC] THEN
  STRIP_TAC THEN
  ABBREV_TAC `tc = cmp_tau (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho p c` THEN
  USE_THEN "zero" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `c:real^N` th)
    (ASSUME `norm(c:real^N) < rho`))) THEN
  USE_THEN "zero" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `p:real^N` th)
    (ASSUME `norm(p:real^N) < rho`))) THEN
  SUBGOAL_THEN
   `mfd_joinable (subtopology euclidean (ball(vec 0:real^N,rho)),
                  open_set_atlas (ball(vec 0,rho))) c tc /\
    mfd_dist (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
             (G:real^N->real^N^N) c tc <= &2 * norm(c:real^N) + norm(p:real^N)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `mfd_joinable (subtopology euclidean (ball(vec 0:real^N,rho)),
                    open_set_atlas (ball(vec 0,rho))) c (vec 0) /\
      mfd_joinable (subtopology euclidean (ball(vec 0:real^N,rho)),
                    open_set_atlas (ball(vec 0,rho))) (vec 0) tc`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ASM_MESON_TAC[MFD_JOINABLE_TRANS]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `c:real^N`; `vec 0:real^N`; `tc:real^N`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `vec 0:real^N`; `p:real^N`; `tc:real^N`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `c:real^N`; `vec 0:real^N`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_tball (G:real^N->real^N^N) c b1 SUBSET
    mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                G c`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `R:real`; `c:real^N`;
                   `v:real^N`] CMPW_EXP_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `c:real^N`; `b1:real`; `tc:real^N`] MFD_LOCAL_HOPF_RINOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    is_binary "SUBSET" (concl th) &&
    can (find_term ((=) `mfd_tball (G:real^N->real^N^N) c b1`)) (concl th))) THEN
  ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A geodesic of the pullback from c is defined on an open interval (-d, 1 + *)
(* d) and satisfies |gamma t| <= |c| + |t| |v|_G there.                      *)
(* ========================================================================= *)

let CMPY_GEO_BOUND = prove
 (`!U (G:real^N->real^N^N) c v.
        open U /\ metric_field U G /\ (!z. z IN U ==> G z ** z = z) /\ c IN U /\
        v IN mfd_exp_dom (subtopology euclidean U,open_set_atlas U) G c
        ==> ?d. &0 < d /\ d <= inv(&2) /\
                real_interval(--d,&1 + d) SUBSET
                mfd_geo_maxint (subtopology euclidean U,open_set_atlas U) G c v /\
                !t. t IN real_interval(--d,&1 + d)
                    ==> norm(mfd_geo (subtopology euclidean U,open_set_atlas U) G c v t) <=
                        norm c + abs t * mfd_tnorm G c v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `U:real^N->bool` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas U) (G:real^N->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `G:real^N->real^N^N`; `c:real^N`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (subtopology euclidean U,open_set_atlas U)
                    (G:real^N->real^N^N) c v` THEN
  ABBREV_TAC `geo = mfd_geo (subtopology euclidean U,open_set_atlas U)
                      (G:real^N->real^N^N) c v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN M` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (subtopology euclidean U,open_set_atlas U)
                   (G:real^N->real^N^N) c` THEN
    ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ d <= inv(&2) /\ real_interval(--d,&1 + d) SUBSET M`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open (M:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `&0` th) THEN MP_TAC(SPEC `&1` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (min d0 d1) (inv(&2))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t < &0` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d0:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `&1 < t` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d1:real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `is_realinterval (M:real->bool)` THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real) IN M` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= t` THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `geo:real->real^N`;
                   `M:real->bool`; `&0`; `t:real`] CMPW_GROWTH) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `G:real^N->real^N^N`; `geo:real->real^N`; `M:real->bool`;
                 `--(&1)`; `&0`] MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LNEG; REAL_MUL_LID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\s. (geo:real->real^N)(--s)`;
                 `{s | --s IN M}`; `&0`; `--t`] CMPW_GROWTH) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_NEG_0; REAL_NEG_NEG; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `mfd_vel (open_set_atlas (U:real^N->bool))`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_NEG_0] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_tnorm; VECTOR_MUL_LNEG; VECTOR_MUL_LID; MATRIX_VECTOR_MUL_RNEG;
              DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(&0 <= t) ==> abs t = --t`]);;

(* ========================================================================= *)
(* The function F(y) = sum_{k<m} |tau^k y|^2 for tau = tau_p: a minimiser c  *)
(* over cball(0,b1) has |c| < b1/4, |tau c| < b1/2, and F(tau c) = F(c) when *)
(* tau^m = id on ball(0,b1).                                                 *)
(* ========================================================================= *)

let cmp_comf = new_definition
 `cmp_comf (tau:real^N->real^N) (m:num) (y:real^N) =
    sum(0..m-1) (\k. ITER k tau y dot ITER k tau y)`;;

let CMPY_F_MIN = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R p m b1.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm p < R /\
        cmp_psi (top,atlas) g x E p = x /\ 1 <= m /\ &0 < b1 /\
        &16 * &m pow 3 * norm p pow 2 < b1 pow 2 /\ &4 * norm p <= b1 /\
        &2 * b1 + &(m + 1) * norm p <= R /\
        (!w. norm w < b1 ==> ITER m (cmp_tau (top,atlas) g x E rho p) w = w)
        ==> ?c. norm c < b1 / &4 /\
                norm(cmp_tau (top,atlas) g x E rho p c) < b1 / &2 /\
                (!y. norm y <= b1
                     ==> cmp_comf (cmp_tau (top,atlas) g x E rho p) m c <=
                         cmp_comf (cmp_tau (top,atlas) g x E rho p) m y) /\
                cmp_comf (cmp_tau (top,atlas) g x E rho p) m
                  (cmp_tau (top,atlas) g x E rho p c) =
                cmp_comf (cmp_tau (top,atlas) g x E rho p) m c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `p:real^N`] CMPK_TAU) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tau = cmp_tau (top,atlas) (g:A->real^N^N) (x:A) (E:real^N^N) rho p` THEN
  ABBREV_TAC `l = norm(p:real^N)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * b1 + l + &m * l <= R /\ &0 <= &m * l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&2 * b1 + &(m + 1) * l <= R` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `rho:real`; `R - l`; `l:real`;
                 `tau:real^N->real^N`] CMPY_ITER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "it") THEN
  SUBGOAL_THEN
   `!k. k <= m
        ==> (ITER k (tau:real^N->real^N)) continuous_on cball(vec 0,b1) /\
            !w. norm w <= b1 ==> norm(ITER k tau w) <= &k * l + norm w`
  (LABEL_TAC "itk") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "it" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    SUBGOAL_THEN `b1 < R - l - &k * l` ASSUME_TAC THENL
     [SUBGOAL_THEN `&k * l <= &m * l` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^N,R - l - &k * l)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_MESON_TAC[cmp_deck];
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o cmp_comf (tau:real^N->real^N) m) continuous_on cball(vec 0,b1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[o_DEF; cmp_comf; LIFT_SUM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    USE_THEN "itk" (MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cmp_comf (tau:real^N->real^N) m`; `cball(vec 0:real^N,b1)`]
    CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; CBALL_EQ_EMPTY] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^N` THEN
  SUBGOAL_THEN `cmp_comf (tau:real^N->real^N) m (vec 0) <= &m * (&m * l) pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmp_comf] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..m-1) (\k:num. (&m * l) pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[LE_0] THEN
      DISCH_TAC THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      USE_THEN "itk" (MP_TAC o SPEC `k:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^N` o CONJUNCT2) THEN
      REWRITE_TAC[NORM_0; REAL_ADD_RID] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG] THEN
      SUBGOAL_THEN `(m - 1 + 1) - 0 = m` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(c:real^N) pow 2 <= cmp_comf (tau:real^N->real^N) m c`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmp_comf] THEN
    SUBGOAL_THEN `0 <= m - 1` MP_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT] THEN DISCH_TAC THEN REWRITE_TAC[ITER; NORM_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[DOT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(c:real^N) < b1 / &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(c:real^N) pow 2 < (b1 / &4) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `cmp_comf (tau:real^N->real^N) m (vec 0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `cmp_comf (tau:real^N->real^N) m c` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&m * (&m * l) pow 2` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&16 * &m pow 3 * l pow 2 < b1 pow 2` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN REWRITE_TAC[REAL_ABS_NORM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm((tau:real^N->real^N) c) < b1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `l + norm(c:real^N)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `R - l`)) (concl th) &&
        can (find_term ((=) `(tau:real^N->real^N) w`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `ITER m (tau:real^N->real^N) c = c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `ITER m (tau:real^N->real^N) w`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cmp_comf] THEN
  SUBGOAL_THEN `!k. ITER k (tau:real^N->real^N) (tau c) = ITER (k + 1) tau c`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM ADD1; ITER_ALT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `\k. ITER k (tau:real^N->real^N) c dot ITER k tau c`; `0`; `m - 1`]
   SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `m - 1 + 1 = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?n. m = SUC n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `m - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ITER] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A deck map carries geodesics of the pullback to geodesics with the same   *)
(* energy; the iterates tau^k o gamma (k < m) of a geodesic gamma inside     *)
(* B(0,2 b1) are geodesics with K |tau^k gamma|^2 <= 1/2.                    *)
(* ========================================================================= *)

let CMPY_DECK_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma (gamma:real->real^N) J.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma /\
        mfd_geodesic (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                     (cmp_expmetric (top,atlas) g x E) gamma J /\
        (!t. t IN J ==> gamma t IN W)
        ==> mfd_geodesic (subtopology euclidean (ball(vec 0,rho)),
                          open_set_atlas (ball(vec 0,rho)))
                         (cmp_expmetric (top,atlas) g x E) (sigma o gamma) J /\
            !t. t IN J
                ==> mfd_vel (open_set_atlas (ball(vec 0,rho))) (sigma o gamma) t dot
                    (cmp_expmetric (top,atlas) g x E ((sigma o gamma) t) **
                     mfd_vel (open_set_atlas (ball(vec 0,rho))) (sigma o gamma) t) =
                    mfd_vel (open_set_atlas (ball(vec 0,rho))) gamma t dot
                    (cmp_expmetric (top,atlas) g x E (gamma t) **
                     mfd_vel (open_set_atlas (ball(vec 0,rho))) gamma t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `sigma:real^N->real^N`] CMPK_DECK_LISOM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
                 `subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`;
                 `cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)`;
                 `W:real^N->bool`; `sigma:real^N->real^N`; `gamma:real->real^N`;
                 `J:real->bool`] MFD_LOCAL_ISOMETRY_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->real^N) t IN W` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->real^N) t IN ball(vec 0,rho) /\
                (sigma:real^N->real^N) (gamma t) IN ball(vec 0,rho)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[cmp_deck]) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `sigma:real^N->real^N`; `(gamma:real->real^N) t`]
    CMPK_DECK_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (sigma:real^N->real^N) (at (gamma(t:real))))`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `sigma:real^N->real^N`; `(gamma:real->real^N) t`]
    CMPK_DECK_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CMPK_PM_DIFF2; OPEN_BALL; o_THM] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; CMPP_DOT_TRANSP] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let CMPY_ITER_FAMILY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R p m b1 (gamma:real->real^N) J.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm p < R /\
        cmp_psi (top,atlas) g x E p = x /\
        &2 * b1 + &(m + 1) * norm p <= R /\
        K * (&m * norm p + &2 * b1) pow 2 <= inv(&2) /\
        mfd_geodesic (subtopology euclidean (ball(vec 0,rho)),open_set_atlas (ball(vec 0,rho)))
                     (cmp_expmetric (top,atlas) g x E) gamma J /\
        (!t. t IN J ==> norm(gamma t) < &2 * b1)
        ==> !k. k <= m - 1
                ==> mfd_geodesic (subtopology euclidean (ball(vec 0,rho)),
                                  open_set_atlas (ball(vec 0,rho)))
                                 (cmp_expmetric (top,atlas) g x E)
                                 (ITER k (cmp_tau (top,atlas) g x E rho p) o gamma) J /\
                    !s. s IN J
                        ==> K * ((ITER k (cmp_tau (top,atlas) g x E rho p) o gamma) s dot
                                 (ITER k (cmp_tau (top,atlas) g x E rho p) o gamma) s)
                            <= inv(&2) /\
                            mfd_vel (open_set_atlas (ball(vec 0,rho)))
                              (ITER k (cmp_tau (top,atlas) g x E rho p) o gamma) s dot
                            (cmp_expmetric (top,atlas) g x E
                               ((ITER k (cmp_tau (top,atlas) g x E rho p) o gamma) s) **
                             mfd_vel (open_set_atlas (ball(vec 0,rho)))
                               (ITER k (cmp_tau (top,atlas) g x E rho p) o gamma) s) =
                            mfd_vel (open_set_atlas (ball(vec 0,rho))) gamma s dot
                            (cmp_expmetric (top,atlas) g x E (gamma s) **
                             mfd_vel (open_set_atlas (ball(vec 0,rho))) gamma s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `p:real^N`] CMPK_TAU) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tau = cmp_tau (top,atlas) (g:A->real^N^N) (x:A) (E:real^N^N) rho p` THEN
  ABBREV_TAC `l = norm(p:real^N)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * b1 + l + &m * l <= R` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 * b1 + &(m + 1) * l <= R` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `rho:real`; `R - l`; `l:real`;
                 `tau:real^N->real^N`] CMPY_ITER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "it") THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "it" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  SUBGOAL_THEN `&k * l <= &m * l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> (gamma:real->real^N) t IN ball(vec 0,R - l - &k * l)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&2 * b1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `ball(vec 0:real^N,R - l - &k * l)`; `ITER k (tau:real^N->real^N)`;
                 `gamma:real->real^N`; `J:real->bool`] CMPY_DECK_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[o_THM; GSYM NORM_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * (&m * l + &2 * b1) pow 2` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  SUBGOAL_THEN `norm((gamma:real->real^N) s) < &2 * b1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&2 * b1`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k * l + norm((gamma:real->real^N) s)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ITER k (tau:real^N->real^N) w`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* If tau^m = id on B(0,b1) (b1 large against m |p|, K small) then tau has a *)
(* fixed point c with |c| < b1: the minimiser of the centre of mass          *)
(* function; otherwise the strictly convex sum of squared norms along the    *)
(* short geodesic from c to tau c would give a contradiction.                *)
(* ========================================================================= *)

let CMPY_FIXED = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R p m b1.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm p < R /\
        cmp_psi (top,atlas) g x E p = x /\ 1 <= m /\ &0 < b1 /\
        &16 * &m pow 3 * norm p pow 2 < b1 pow 2 /\ &4 * norm p <= b1 /\
        &2 * b1 + &(m + 1) * norm p <= R /\
        K * (&m * norm p + &2 * b1) pow 2 <= inv(&2) /\
        (!w. norm w < b1 ==> ITER m (cmp_tau (top,atlas) g x E rho p) w = w)
        ==> ?c. norm c < b1 /\ cmp_tau (top,atlas) g x E rho p c = c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * b1 + norm(p:real^N) + &m * norm p <= R /\ &0 <= &m * norm(p:real^N) /\
                &0 <= norm(p:real^N)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&2 * b1 + &(m + 1) * norm(p:real^N) <= R` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; NORM_POS_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `p:real^N`; `m:num`; `b1:real`] CMPY_F_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^N` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `p:real^N`; `c:real^N`; `b1:real`] CMPY_SHORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,rho)` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(c:real^N) < rho /\ (c:real^N) IN ball(vec 0,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `tau = cmp_tau (top,atlas) (g:A->real^N^N) (x:A) (E:real^N^N) rho p` THEN
  ABBREV_TAC `G = cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)` THEN
  SUBGOAL_THEN `~(v:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `c:real^N`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_tnorm (G:real^N->real^N^N) c v` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC CMPW_METRIC_POS_LE THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `c:real^N`; `v:real^N`]
    CMPY_GEO_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                 `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                 `c:real^N`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (subtopology euclidean (ball(vec 0:real^N,rho)),
                         open_set_atlas (ball(vec 0,rho))) (G:real^N->real^N^N) c v (&1) =
                (tau:real^N->real^N) c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM mfd_exp] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `geo = mfd_geo (subtopology euclidean (ball(vec 0:real^N,rho)),
                             open_set_atlas (ball(vec 0,rho))) (G:real^N->real^N^N) c v` THEN
  ABBREV_TAC `M = mfd_geo_maxint (subtopology euclidean (ball(vec 0:real^N,rho)),
                             open_set_atlas (ball(vec 0,rho))) (G:real^N->real^N^N) c v` THEN
  SUBGOAL_THEN `is_realinterval(real_interval(--d,&1 + d)) /\ real_open(real_interval(--d,&1 + d)) /\
                &0 IN real_interval(--d,&1 + d) /\ &1 IN real_interval(--d,&1 + d) /\
                (!t. t IN real_interval(--d,&1 + d) ==> abs t <= &3 / &2) /\
                (!t. &0 <= t /\ t <= &1 ==> t IN real_interval(--d,&1 + d))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `J = real_interval(--d,&1 + d)` THEN
  SUBGOAL_THEN `mfd_geodesic (subtopology euclidean (ball(vec 0:real^N,rho)),
                              open_set_atlas (ball(vec 0,rho))) (G:real^N->real^N^N) geo J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `M:real->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> norm((geo:real->real^N) t) < &2 * b1` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(c:real^N) + abs t * mfd_tnorm (G:real^N->real^N^N) c v` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs t * mfd_tnorm (G:real^N->real^N^N) c v <= &3 / &2 * mfd_tnorm G c v`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `p:real^N`; `m:num`; `b1:real`; `geo:real->real^N`; `J:real->bool`]
   CMPY_ITER_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "fam") THEN
  SUBGOAL_THEN `!s. s IN J
                    ==> mfd_vel (open_set_atlas (ball(vec 0:real^N,rho))) geo s dot
                        ((G:real^N->real^N^N) (geo s) **
                         mfd_vel (open_set_atlas (ball(vec 0:real^N,rho))) geo s) =
                        v dot (G c ** v)`
  (LABEL_TAC "speed") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^N,rho))`;
                   `open_set_atlas (ball(vec 0:real^N,rho))`; `G:real^N->real^N^N`;
                   `geo:real->real^N`; `M:real->bool`; `s:real`; `&0`] MFD_GEODESIC_SPEED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_tnorm; SQRT_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < v dot ((G:real^N->real^N^N) c ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sig2 = v dot ((G:real^N->real^N^N) c ** v)` THEN
  MATCH_MP_TAC CMPY_CONVEX_CONTRA THEN
  MAP_EVERY EXISTS_TAC
   [`\s. sum(0..m-1) (\k. (ITER k (tau:real^N->real^N) o (geo:real->real^N)) s dot
                          (ITER k tau o geo) s)`;
    `\t. &2 * sum(0..m-1) (\k. (ITER k (tau:real^N->real^N) o (geo:real->real^N)) t dot
                               mfd_vel (open_set_atlas (ball(vec 0:real^N,rho)))
                                       (ITER k tau o geo) t)`;
    `\s. sum(0..m-1) (\k. (ITER k (tau:real^N->real^N) o (geo:real->real^N)) s dot
                          mfd_vel (open_set_atlas (ball(vec 0:real^N,rho)))
                                  (ITER k tau o geo) s)`;
    `\t. sum(0..m-1) (\k. mfd_vel (open_set_atlas (ball(vec 0:real^N,rho)))
                                  (ITER k (tau:real^N->real^N) o (geo:real->real^N)) t dot
                          mfd_vel (open_set_atlas (ball(vec 0:real^N,rho)))
                                  (ITER k tau o geo) t -
                          (ITER k tau o geo) t dot
                          christoffel (G:real^N->real^N^N) ((ITER k tau o geo) t)
                            (mfd_vel (open_set_atlas (ball(vec 0:real^N,rho)))
                                     (ITER k tau o geo) t)
                            (mfd_vel (open_set_atlas (ball(vec 0:real^N,rho)))
                                     (ITER k tau o geo) t))`;
    `J:real->bool`;
    `&m * (inv(&2) * sig2)`] THEN
  REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `K:real`; `m:num`;
                   `\k:num. ITER k (tau:real^N->real^N) o (geo:real->real^N)`;
                   `J:real->bool`; `sig2:real`; `t:real`] CMPY_SUM_CONVEX) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `inv(norm(w:real^N))`)) (concl th))) THEN
      ASM_REWRITE_TAC[NORM_POS_LT];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "fam" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k <= m - 1`))) THEN
      SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "fam" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k <= m - 1`))) THEN
      DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "speed" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(s:real) IN J`)])];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM cmp_comf] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `cmp_comf (tau:real^N->real^N) m c`)) (concl th))) THEN
  SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(c:real^N) + abs t * mfd_tnorm (G:real^N->real^N^N) c v` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs t * mfd_tnorm (G:real^N->real^N^N) c v <= &1 * mfd_tnorm G c v`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* For a deck point q <> 0 the iterate tau_q^m has no fixed point in         *)
(* B(0,b1): such a fixed point makes tau_q^m = id by rigidity, then tau_q    *)
(* has a fixed point by CMPY_FIXED, so tau_q = id and q = tau_q 0 = 0.       *)
(* ========================================================================= *)

let CMPY_NO_PERIOD = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R q m b1 b.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm q < R /\
        cmp_psi (top,atlas) g x E q = x /\ ~(q = vec 0) /\ 1 <= m /\ &0 < b1 /\
        &16 * &m pow 3 * norm q pow 2 < b1 pow 2 /\ &4 * norm q <= b1 /\
        &2 * b1 + &(m + 1) * norm q <= R /\
        K * (&m * norm q + &2 * b1) pow 2 <= inv(&2) /\
        norm b < b1 /\ ITER m (cmp_tau (top,atlas) g x E rho q) b = b
        ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `q:real^N`] CMPK_TAU) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tau = cmp_tau (top,atlas) (g:A->real^N^N) (x:A) (E:real^N^N) rho q` THEN
  ABBREV_TAC `l = norm(q:real^N)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * b1 + l + &m * l <= R /\ &0 <= &m * l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&2 * b1 + &(m + 1) * l <= R` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `rho:real`; `R - l`; `l:real`;
                 `tau:real^N->real^N`] CMPY_ITER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `ball(vec 0:real^N,R - l - &m * l)`; `ITER m (tau:real^N->real^N)`;
                 `\w:real^N. w`; `b:real^N`] CMPK_DECK_RIGID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_BALL; IN_BALL_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPK_DECK_ID THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `?c:real^N. norm c < b1 /\ tau c = c` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                   `q:real^N`; `m:num`; `b1:real`] CMPY_FIXED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `ball(vec 0:real^N,R - l)`; `tau:real^N->real^N`;
                 `\w:real^N. w`; `c:real^N`] CMPK_DECK_RIGID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_BALL; IN_BALL_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPK_DECK_ID THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
  ASM_REWRITE_TAC[IN_BALL_0; NORM_0] THEN ASM_REAL_ARITH_TAC);;

