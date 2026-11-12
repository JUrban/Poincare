(* ========================================================================= *)
(* Unit pc_cmp_topo (comparison-geometry layer CMP, the second of three      *)
(* units for MT Lemma 11.13, with pc_cmp_hup and pc_cmp_a7): the hinge form  *)
(* of Toponogov's comparison under sec >= 0 on a complete manifold.  A       *)
(* continuous function with smooth upper barriers of arbitrarily small       *)
(* second derivative at every interior point is concave (Calabi's            *)
(* 1-dimensional lemma); h(t) = d(q,sigma t)^2 - t^2 has such barriers along *)
(* every unit-speed geodesic sigma (CMPE_BARRIER), and the barrier at t = 0  *)
(* has slope -2 s <u1,u2> when q = exp_p(s u1) with the segment minimizing,  *)
(* so d(q, exp_p(t u2))^2 <= s^2 + t^2 - 2 s t <u1,u2>.                      *)
(* ========================================================================= *)

needs "src/pc_cmp_hup.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Calabi's lemma.  A local minimum of a function whose                      *)
(* derivative has a negative derivative at the point is impossible; hence a  *)
(* continuous h on [a,c] with smooth upper barriers bf (bf = h at t0,        *)
(* bf >= h near t0) of second derivative at most e at every interior t0,    *)
(* for every e > 0, lies above its chords.                                   *)
(* ========================================================================= *)

let CMPA_NEG_SECOND = prove
 (`!(beta:real->real) beta' D t d.
        &0 < d /\
        (!s. abs(s - t) < d ==> (beta has_real_derivative beta'(s)) (atreal s)) /\
        (beta' has_real_derivative D) (atreal t) /\ D < &0 /\ beta' t = &0
        ==> ?s. t < s /\ s < t + d /\ beta s < beta t`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `((beta':real->real) has_real_derivative D) (atreal t)` THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `--D`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. t < y /\ y - t < k ==> (beta':real->real) y < &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < y - t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`y - t`,`r:real`) THEN SPEC_TAC(`(beta':real->real) y`,`b:real`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `b / r < &0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  EXISTS_TAC `t + min d k / &2` THEN
  SUBGOAL_THEN `&0 < min d k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`beta:real->real`; `beta':real->real`; `t:real`; `t + min d k / &2`]
    REAL_MVT_SIMPLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPECL [`d:real`; `k:real`] REAL_MIN_LE) THEN
    DISCH_THEN(MP_TAC o SPEC `d:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(beta':real->real) xi < &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPECL [`d:real`; `k:real`] REAL_MIN_LE) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(beta':real->real) xi * ((t + min d k / &2) - t) < &0` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(t + x) - t = x`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < --a * b ==> a * b < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let CMPA_CALABI = prove
 (`!(h:real->real) a c.
        a < c /\ h real_continuous_on real_interval[a,c] /\
        (!t0 e. a < t0 /\ t0 < c /\ &0 < e
                ==> ?d bf bf' bf2.
                      &0 < d /\
                      (!s. abs(s - t0) < d ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
                      (bf' has_real_derivative bf2) (atreal t0) /\ bf2 <= e /\
                      bf t0 = h t0 /\
                      (!s. abs(s - t0) < d ==> h s <= bf s))
        ==> !x. a <= x /\ x <= c ==> h a + (x - a) / (c - a) * (h c - h a) <= h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ABBREV_TAC `k = (h c - h a) / (c - a)` THEN
  SUBGOAL_THEN `!y. h a + (y - a) / (c - a) * (h c - h a) = h a + k * (y - a)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "k" THEN UNDISCH_TAC `a < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real->real) a + k * (c - a) = h c` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ARITH `a < c ==> ~(c - a = &0)`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `m = (h:real->real) a + k * (x - a) - h x` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real = a) /\ ~(x:real = c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&0 < m` THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
    UNDISCH_TAC `(h:real->real) a + k * (c - a) = h c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < x /\ x < c` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = m / (&2 * (x - a) * (c - x))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta * (x - a) * (c - x) = m / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(x - a = &0) /\ ~(c - x = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  ABBREV_TAC `psi = \t. (h:real->real) t - (h a + k * (t - a)) + eta * (t - a) * (c - t)` THEN
  SUBGOAL_THEN `(psi:real->real) real_continuous_on real_interval[a,c]` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real->real`; `real_interval[a,c]`] REAL_CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(psi:real->real) x = --(m / &2)` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `eta * (x - a) * (c - x) = m / &2` THEN EXPAND_TAC "m" THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real->real) a = &0 /\ psi c = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real->real) ts <= --(m / &2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `psi:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ts:real = a) /\ ~(ts:real = c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < ts /\ ts < c` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ts:real`; `eta:real`] o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `dd = min d (min (ts - a) (c - ts))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d /\ dd <= ts - a /\ dd <= c - ts` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `beta = \s. (bf:real->real) s +
                        (--((h:real->real) a + k * (s - a)) + eta * (s - a) * (c - s))` THEN
  ABBREV_TAC `beta' = \s. (bf':real->real) s + (--k + eta * ((c - s) - (s - a)))` THEN
  SUBGOAL_THEN `!s. abs(s - ts) < dd
                    ==> ((beta:real->real) has_real_derivative beta'(s)) (atreal s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "beta" THEN EXPAND_TAC "beta'" THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `bf:real->real`)) (concl th) &&
        can (find_term ((=) `bf':real->real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      REAL_DIFF_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((beta':real->real) has_real_derivative (bf2 - &2 * eta)) (atreal ts)`
  ASSUME_TAC THENL
   [EXPAND_TAC "beta'" THEN
    SUBGOAL_THEN `bf2 - &2 * eta = bf2 + eta * ((&0 - &1) - (&1 - &0))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
    REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. abs(s - ts) < dd ==> (beta:real->real) ts <= beta s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "beta" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(psi:real->real) s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(psi:real->real) ts` THEN CONJ_TAC THENL
       [EXPAND_TAC "psi" THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `psi:real->real`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - a + b <= y + (--a + b)`) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `bf:real->real`)) (concl th) &&
        not(can (find_term ((=) `bf':real->real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(beta':real->real) ts = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`beta:real->real`; `ts:real`; `real_interval(ts - dd,ts + dd)`] THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISJ2_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`beta:real->real`; `beta':real->real`; `bf2 - &2 * eta`; `ts:real`; `dd:real`]
    CMPA_NEG_SECOND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `(beta:real->real) ts`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The tangent bound.  If h lies above its chords on [0,T] and               *)
(* below a function bf near 0 with bf(0) = h(0) and bf'(0) = D, then        *)
(* h(T) <= h(0) + T D.                                                       *)
(* ========================================================================= *)

let CMPA_TANGENT_BOUND = prove
 (`!(h:real->real) bf D Tm e.
        &0 < Tm /\ &0 < e /\
        (!x. &0 <= x /\ x <= Tm ==> h(&0) + (x - &0) / (Tm - &0) * (h Tm - h(&0)) <= h x) /\
        (bf has_real_derivative D) (atreal (&0)) /\ bf(&0) = h(&0) /\
        (!s. abs(s - &0) < e ==> h s <= bf s)
        ==> h Tm <= h(&0) + Tm * D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `Q = (h Tm - h(&0)) / Tm` THEN
  SUBGOAL_THEN `D < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `((bf:real->real) has_real_derivative D) (atreal (&0))` THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `(Q - D) / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tau = min Tm (min e k) / &2` THEN
  SUBGOAL_THEN `&0 < tau /\ tau < Tm /\ tau < e /\ tau < k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN REWRITE_TAC[real_min] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `k:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(bf tau - h(&0)) / tau < Q` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(((bf:real->real) tau - h(&0)) / tau - D) < (Q - D) / &2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real->real) tau <= bf tau` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h(&0) + tau * Q <= (h:real->real) tau` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Tm:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN EXPAND_TAC "Q" THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> h0 + a <= x ==> h0 + b <= x`) THEN
    UNDISCH_TAC `&0 < Tm` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `tau * Q <= bf tau - h(&0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(bf tau - h(&0)) / tau < Q` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Barriers for h(s) = d(q, sigma s)^2 - s^2 at every t0, for                *)
(* sigma = geo(p,u) of unit speed (M complete, connected, sec >= 0): at a    *)
(* point z = sigma(t0) = q the affine function t0^2 - 2 s t0; otherwise the *)
(* Calabi barrier of a minimizing geodesic from z to q with delta small.    *)
(* Also the continuity of h.                                                 *)
(* ========================================================================= *)

let CMPA_HBARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (q:A) t0 e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\ q IN topspace top /\ &0 < e
        ==> ?d bf bf' bf2.
              &0 < d /\
              (!s. abs(s - t0) < d ==> (bf has_real_derivative bf'(s)) (atreal s)) /\
              (bf' has_real_derivative bf2) (atreal t0) /\ bf2 <= e /\
              bf t0 = mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u t0) pow 2 -
                      t0 pow 2 /\
              (!s. abs(s - t0) < d
                   ==> mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) pow 2 -
                       s pow 2 <= bf s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. (sigma:real->A) s IN topspace top` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. mfd_tnorm (g:A->real^N^N) ((sigma:real->A) s) (mfd_vel atlas sigma s) = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_CASES_TAC `(sigma:real->A) t0 = q` THENL
   [EXISTS_TAC `&1` THEN
    EXISTS_TAC `\s. t0 pow 2 - &2 * s * t0` THEN
    EXISTS_TAC `\s:real. --(&2 * t0)` THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `t0:real`; `s:real`]
        GEOH_GEO_SEG_DIST) THEN
      ASM_REWRITE_TAC[IN_UNIV; REAL_MUL_RID] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `q:A`; `(sigma:real->A) s`] MFD_DIST_POS_LE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) q ((sigma:real->A) s) pow 2 <=
                    (s - t0) pow 2` MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z = (sigma:real->A) t0` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) z q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `q:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) z q` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `q:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `q:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `delta = min (L / &2) (e * L / &4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= L / &2 /\ delta <= e * L / &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < e * L / &4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "delta" THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `z:A`; `w:real^N`; `q:A`;
                 `delta:real`] CMPE_BARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `bf2 <= &2 * delta / (mfd_tnorm (g:A->real^N^N) z w - delta)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * delta / (L - delta)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < L - delta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `!x y. &2 * x / y = (&2 * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `e * L / &2 <= e * (L - delta)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `bf:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Toponogov's hinge comparison for sec >= 0.  On a complete                 *)
(* connected manifold with sec >= 0, for unit vectors u1, u2 at p and s > 0  *)
(* with t |-> exp_p(t u1) minimizing on [0,s]:                               *)
(*   d(exp_p(s u1), exp_p(T u2))^2 <= s^2 + T^2 - 2 s T <u1,u2>  (T >= 0).   *)
(* h(t) = d(q, exp_p(t u2))^2 - t^2 is concave (CMPA_CALABI with the         *)
(* barriers CMPA_HBARRIER) and lies below its tangent at 0, whose slope is   *)
(* -2 s <u1,u2> (CMPE_BARRIER with w = s u1).                                *)
(* ========================================================================= *)

let CMPA_HCONT = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (q:A) a c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top
        ==> (\t. mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u t) pow 2 - t pow 2)
            real_continuous_on real_interval[a,c]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`] GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t. mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g p u t))
                real_continuous_on real_interval[a,c]` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(\t. mfd_dist (top,atlas) (g:A->real^N^N) q (mfd_geo (top,atlas) g p u t)) =
                  (\y. mfd_dist (top,atlas) g q y) o mfd_geo (top,atlas) g p u`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID]]);;

let CMPA_HINGE = prove
 (`!top atlas (g:A->real^N^N) (p:A) u1 u2 s Tm.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u1 = &1 /\ mfd_tnorm g p u2 = &1 /\ &0 < s /\
        mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (s % u1)) = s /\ &0 <= Tm
        ==> mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p (s % u1))
                                   (mfd_exp (top,atlas) g p (Tm % u2)) pow 2
            <= s pow 2 + Tm pow 2 - &2 * s * Tm * (u1 dot (g p ** u2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u2 = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p = (:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[mfd_exp_dom; EXTENSION; IN_UNIV; IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `q = mfd_exp (top,atlas) (g:A->real^N^N) p (s % u1)` THEN
  SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u2:real^N`; `Tm:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u2:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `h = \t. mfd_dist (top,atlas) (g:A->real^N^N) q
                        (mfd_geo (top,atlas) g p u2 t) pow 2 - t pow 2` THEN
  SUBGOAL_THEN `(h:real->real) (&0) = s pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `Tm = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Tm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. &0 <= x /\ x <= Tm ==> h(&0) + (x - &0) / (Tm - &0) * (h Tm - h(&0)) <= h x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPA_CALABI THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC CMPA_HCONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t0:real`; `e:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `u2:real^N`; `q:A`; `t0:real`; `e:real`]
      CMPA_HBARRIER) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u2:real^N`; `&0`; `p:A`; `s % (u1:real^N)`;
                 `q:A`; `s / &2`] CMPE_BARRIER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`; REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e0:real`; `bf:real->real`; `bf':real->real`; `bf2:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(u1:real^N) dot ((g:A->real^N^N) p ** u1) = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u1:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(v:real^N) dot ((g:A->real^N^N) p ** v)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `bf:real->real`; `(bf':real->real) (&0)`; `Tm:real`;
                 `e0:real`] CMPA_TANGENT_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `bf':real->real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL] THEN REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                                 with Failure _ -> false)) (concl th) &&
        can (find_term ((=) `bf:real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_LMUL; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN REAL_ARITH_TAC);;

