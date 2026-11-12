(* ========================================================================= *)
(* pc_p2a_fl99: FL8, P2A_FLOW_PROP_9_9 at N = 3 (MT Prop 9.9 on a finite     *)
(* interval: for a flow with nonnegative sectional curvature,                *)
(*   |grad l|^2 + R <= (1 + 2/c) l/tau  and  R - (1 + 1/c) l/tau <= l_tau    *)
(* for tau <= (1 - c)(b - a)), from Hamilton's Harnack inequality            *)
(* (P2B_REQ_RFA_HARNACK_STATEMENT), the first variation of l at              *)
(* differentiability points (P2AW_FLOW_LX_DERIV of pc_p2a_wk3) and the       *)
(* energy identity along minimizers:                                         *)
(*   d/ds llag = -4 s^3 H(X),  H(X) = R_t - R/s^2 - 2 dR(X) + 2 Ric(X,X),    *)
(* so with the Harnack bound H >= -R/(c s^2):                                *)
(* (s/2) llag(s) <= (1/2 + 1/c) L.                                           *)
(* ========================================================================= *)

needs "src/pc_p2a_flow2.ml";;
needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2b_scalpos.ml";;
needs "src/pc_p2a_lxreq.ml";;
needs "src/pc_p2a_wk3.ml";;
needs "src/pc_p2a_l72f.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Harnack inequality of P2B_REQ_RFA_HARNACK_STATEMENT for a complete   *)
(* flow of bounded curvature with nonnegative sectional curvature on [a,b], *)
(* in the form used along L-geodesics (direction -X):                       *)
(*   0 <= R_t + R/(t - a) - 2 dR(X) + 2 Ric(X,X).                            *)
(* ------------------------------------------------------------------------- *)

let P2AU_HARNACK_FLOW = prove
 (`!(w:A->bool) top atlas a b (g:real->A->real^3^3).
     P2B_REQ_RFA_HARNACK_STATEMENT w /\ p2a_cbflow (top,atlas) a b g /\
     (!t x v1 v2. a <= t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                  ==> &0 <= mfd_sectional atlas (g t) x v1 v2)
     ==> !t x dR X.
           a < t /\ t < b /\ x IN topspace top /\
           ((\s. mfd_scalar atlas (g s) x) has_real_derivative dR) (atreal t)
           ==> &0 <= dR + mfd_scalar atlas (g t) x / (t - a) -
                     &2 * drop(frechet_derivative
                                (\y. lift(lscalar (metric_local atlas (chart_at atlas x) (g t))
                                                  y))
                                (at (SND(chart_at atlas x) x)) X) +
                     &2 * mfd_ricci atlas (g t) x X X`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEC"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  REWRITE_TAC[P2B_REQ_RFA_HARNACK_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `a:real`; `b:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM P2A_FLOW_UPTO_3] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "mfd_complete" th)) THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "SEC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `K:real` THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "mfd_rm_norm" th)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "H") THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `dR:real`; `X:real^3`] THEN STRIP_TAC THEN
  USE_THEN "H" (MP_TAC o SPECL [`t:real`; `x:A`; `dR:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `--X:real^3` o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                  (metric_local atlas c ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative
            (\y. lift(lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3) t)) y))
            (at (SND c x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v w:real^3. lricci (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))
                        (SND c x) (--v) (--w) =
                 lricci (metric_local atlas c (g t)) (SND c x) v w`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LIFT_EQ] THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                   `SND(c:(A->bool)#(A->real^3)) x`] LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `--w:real^3`) (MP_TAC o SPEC `v:real^3`)) THEN
    DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP LINEAR_NEG) THEN
    DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP LINEAR_NEG) THEN
    ASM_REWRITE_TAC[VECTOR_NEG_NEG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_ricci] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]) THEN
  REWRITE_TAC[DROP_NEG] THEN REAL_ARITH_TAC);;

(* The spatial derivative of the chart scalar curvature transforms with the *)
(* chart Jacobian (LSCALAR_CHART_TRANS and the chain rule).                 *)

let P2AU_DSCALAR_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x X.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
     ==> frechet_derivative (\y. lift(lscalar (metric_local atlas (U,phi) g) y))
                            (at (phi x)) X =
         frechet_derivative (\y. lift(lscalar (metric_local atlas (V,psi) g) y))
                            (at (psi x)) (chart_jac (U,phi) (V,psi) x X)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `fV = \y. lift(lscalar (metric_local atlas ((V:A->bool),(psi:A->real^N))
                                      (g:A->real^N^N)) y)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (psi:A->real^N) V)
                  (metric_local atlas ((V:A->bool),psi) (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool),(psi:A->real^N)`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->real^N) x IN IMAGE psi V /\ x IN (V:A->bool) /\ x IN (U:A->bool)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((fV:real^N->real^1) has_derivative
                 frechet_derivative fV (at ((psi:A->real^N) x))) (at (psi x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN EXPAND_TAC "fV" THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
                CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_trans ((U:A->bool),(phi:A->real^N)) ((V:A->bool),(psi:A->real^N))
                  (phi x) = psi x` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`chart_trans ((U:A->bool),(phi:A->real^N)) ((V:A->bool),(psi:A->real^N))`;
                 `fV:real^N->real^1`;
                 `chart_jac ((U:A->bool),(phi:A->real^N)) ((V:A->bool),(psi:A->real^N)) x`;
                 `frechet_derivative (fV:real^N->real^1) (at ((psi:A->real^N) x))`;
                 `(phi:A->real^N) x`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\y. lift(lscalar (metric_local atlas ((U:A->bool),(phi:A->real^N)) (g:A->real^N^N)) y))
     has_derivative
     (frechet_derivative (fV:real^N->real^1) (at ((psi:A->real^N) x)) o
      chart_jac (U,phi) (V,psi) x)) (at (phi x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `(fV:real^N->real^1) o chart_trans ((U:A->bool),(phi:A->real^N)) (V,psi)` THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN ASM_MESON_TAC[];
      ASM SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `chart_trans ((U:A->bool),(phi:A->real^N)) ((V:A->bool),(psi:A->real^N))
                      (phi z) = psi z` SUBST1_TAC THENL
       [MATCH_MP_TAC CHART_TRANS_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "fV" THEN REWRITE_TAC[LIFT_EQ] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LSCALAR_CHART_TRANS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`] THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_THM]);;

(* The Harnack inequality in an arbitrary chart of the atlas. *)

let P2AU_HARNACK_CHART = prove
 (`!(w:A->bool) top atlas a b (g:real->A->real^3^3).
     P2B_REQ_RFA_HARNACK_STATEMENT w /\ p2a_cbflow (top,atlas) a b g /\
     (!t x v1 v2. a <= t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                  ==> &0 <= mfd_sectional atlas (g t) x v1 v2)
     ==> !t U phi x dR X.
           a < t /\ t < b /\ (U,phi) IN atlas /\ x IN U /\
           ((\s. mfd_scalar atlas (g s) x) has_real_derivative dR) (atreal t)
           ==> &0 <= dR + mfd_scalar atlas (g t) x / (t - a) -
                     &2 * drop(frechet_derivative
                                (\y. lift(lscalar (metric_local atlas (U,phi) (g t)) y))
                                (at (phi x)) X) +
                     &2 * lricci (metric_local atlas (U,phi) (g t)) (phi x) X X`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AU_HARNACK_FLOW) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(LABEL_TAC "H") THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `U:A->bool`; `phi:A->real^3`; `x:A`; `dR:real`; `X:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?(V:A->bool) (psi:A->real^3). chart_at atlas x = V,psi`
  (X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^3` ASSUME_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `((V:A->bool),(psi:A->real^3)) IN atlas /\ (x:A) IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FST]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "H" (MP_TAC o SPECL [`t:real`; `x:A`; `dR:real`;
    `chart_jac ((U:A->bool),(phi:A->real^3)) ((V:A->bool),(psi:A->real^3)) x X`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_ricci] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`; `(g:real->A->real^3^3) t`;
                 `x:A`; `X:real^3`] P2AU_DSCALAR_CHART_TRANS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`; `V:A->bool`; `psi:A->real^3`; `(g:real->A->real^3^3) t`;
                 `x:A`; `X:real^3`; `X:real^3`] LRG_LRICCI_CHART_TRANS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The integrated energy inequality (real analysis).  If f is continuous on *)
(* [0,S], differentiable on (0,S) and s f'(s) <= 2 k f(s), then             *)
(* g(s) = (s/2) f(s) has g' <= (1/2 + k) f, so by the mean value            *)
(* theorem applied to (1/2 + k) int_0^s f - g(s):                           *)
(*   (S/2) f(S) <= (1/2 + k) int_0^S f.                                      *)
(* ------------------------------------------------------------------------- *)

let P2AU_ENERGY_INTEGRAL = prove
 (`!(f:real->real) f' k S.
     &0 < S /\
     f real_continuous_on real_interval[&0,S] /\
     (!s. &0 < s /\ s < S ==> (f has_real_derivative f' s) (atreal s)) /\
     (!s. &0 < s /\ s < S ==> s * f' s <= &2 * k * f s)
     ==> S / &2 * f S <= (inv(&2) + k) * real_integral (real_interval[&0,S]) f`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ff = \s. (inv(&2) + k) * real_integral (real_interval[&0,s]) f -
                       s / &2 * (f:real->real) s` THEN
  SUBGOAL_THEN
   `!x. x IN real_interval[&0,S]
        ==> ((\u. real_integral(real_interval[&0,u]) f) has_real_derivative f x)
            (atreal x within real_interval[&0,S])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_HAS_REAL_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:real->real`;
                 `\s. (inv(&2) + k) * (f:real->real) s -
                      (inv(&2) * f s + s / &2 * f' s)`;
                 `&0`; `S:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "ff" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
        EXISTS_TAC `(f:real->real) x` THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_ID]];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "ff" THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        MP_TAC(ISPECL [`\u. real_integral(real_interval[&0,u]) (f:real->real)`;
                       `(f:real->real) x`; `x:real`; `real_interval(&0,S)`]
                      HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
        REWRITE_TAC[IN_REAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `real_interval[&0,S]` THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
          ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        SUBGOAL_THEN `inv(&2) * (f:real->real) x + x / &2 * f' x =
                      inv(&2) * f x + x / &2 * f' x` SUBST1_TAC THENL
         [REFL_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`\s:real. s / &2`; `inv(&2)`; `f:real->real`; `(f':real->real) x`;
                       `x:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[real_div] THEN
            MP_TAC(ISPECL [`\s:real. s`; `&1`; `inv(&2)`; `x:real`]
                          HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
            REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID];
            FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
          MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(ff:real->real)(&0) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[] THEN
    SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (ff:real->real) S` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `ff:real->real`)) (concl th) &&
      can (find_term (fun t -> t = `S:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `k:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "ff" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the L-Lagrangian along a chart L-geodesic              *)
(* (s = sqrt tau, A = dy/ds):                                               *)
(*   d/ds llag = 4 s R - 4 s^3 R_t + 4 s^2 dR(A) - 2 s Ric(A,A)              *)
(* (P2AL_ENERGY_CURVE for the kinetic part; the chain rule for              *)
(* R(tt - s^2, y(s)) with the joint smoothness LRG_LSMOOTH_LSCALAR).         *)
(* ------------------------------------------------------------------------- *)

(* The two partial derivatives of a jointly differentiable function of      *)
(* (t,y) (time first) and the chain rule along a curve.                      *)

let P2AU_JOINT_PARTIALS = prove
 (`!(Fj:real^(1,N)finite_sum->real^1) D t0 (y0:real^N).
     (Fj has_derivative D) (at (pastecart (lift t0) y0))
     ==> ((\t. drop(Fj(pastecart (lift t) y0))) has_real_derivative
          drop(D(pastecart (lift(&1)) (vec 0)))) (atreal t0) /\
         ((\z. Fj(pastecart (lift t0) z)) has_derivative (\v. D(pastecart (vec 0) v))) (at y0) /\
         !(P:real^1->real^(1,N)finite_sum) P' x.
           (P has_vector_derivative P') (at x) /\ P x = pastecart (lift t0) y0
           ==> ((\u. Fj(P u)) has_vector_derivative D P') (at x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(D:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(P:real^1->real^(1,N)finite_sum) P' x.
      (P has_vector_derivative P') (at x) /\ P x = pastecart (lift t0) y0
      ==> ((\u. (Fj:real^(1,N)finite_sum->real^1)(P u)) has_vector_derivative D P') (at x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`P:real^1->real^(1,N)finite_sum`; `Fj:real^(1,N)finite_sum->real^1`;
                   `\h:real^1. drop h % (P':real^(1,N)finite_sum)`;
                   `D:real^(1,N)finite_sum->real^1`; `x:real^1`] DIFF_CHAIN_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM has_vector_derivative]; ALL_TAC] THEN
    REWRITE_TAC[has_vector_derivative; o_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    MP_TAC(ISPECL [`at (lift t0)`; `\u:real^1. u`; `\u:real^1. (y0:real^N)`;
                   `\h:real^1. h`; `\h:real^1. vec 0:real^N`] HAS_DERIVATIVE_PASTECART) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM PASTECART_CMUL; VECTOR_MUL_RZERO] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. pastecart (lift t0) z`; `Fj:real^(1,N)finite_sum->real^1`;
                 `\v:real^N. pastecart (vec 0:real^1) v`;
                 `D:real^(1,N)finite_sum->real^1`; `y0:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`at (y0:real^N)`; `\z:real^N. lift t0`; `\z:real^N. z`;
                 `\h:real^N. vec 0:real^1`; `\h:real^N. h`] HAS_DERIVATIVE_PASTECART) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

(* The scalar curvature along a chart curve s |-> (tt - s^2, y(s)). *)

let P2AU_LSCALAR_CURVE_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt s (y:real^1->real^N) A dR.
     lrg_lsmooth U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A) (at (lift s)) /\
     ((\t. lscalar (Gt t) (y(lift s))) has_real_derivative dR) (atreal (tt - s pow 2))
     ==> ((\r. lscalar (Gt(tt - r pow 2)) (y(lift r))) has_real_derivative
          (--(&2 * s) * dR +
           drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                   (at (y(lift s))) A)))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z:real^(1,N)finite_sum. lift(lscalar ((Gt:real->real^N->real^N^N)(drop(fstcart z)))
                                            (sndcart z))) has_derivative
     frechet_derivative
       (\z:real^(1,N)finite_sum. lift(lscalar ((Gt:real->real^N->real^N^N)(drop(fstcart z)))
                                            (sndcart z)))
       (at (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))))
    (at (pastecart (lift(tt - s pow 2)) (y(lift s))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      ASM_MESON_TAC[lrg_lsmooth];
      MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = frechet_derivative
          (\z:real^(1,N)finite_sum. lift(lscalar ((Gt:real->real^N->real^N^N)
                                                 (drop(fstcart z))) (sndcart z)))
          (at (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s))))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_JOINT_PARTIALS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]) THEN
  SUBGOAL_THEN `drop((D:real^(1,N)finite_sum->real^1) (pastecart (lift(&1)) (vec 0))) = dR`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\t. lscalar ((Gt:real->real^N->real^N^N) t) ((y:real^1->real^N)(lift s))`;
      `tt - s pow 2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2)) z))
                       (at ((y:real^1->real^N)(lift s))) =
    (\v. (D:real^(1,N)finite_sum->real^1) (pastecart (vec 0) v))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\r. lscalar ((Gt:real->real^N->real^N^N)(tt - r pow 2)) ((y:real^1->real^N)(lift r)))
     o drop) =
    (\u. lift(lscalar (Gt(drop(fstcart(pastecart (lift(tt - drop u pow 2)) (y u)))))
                      (sndcart(pastecart (lift(tt - drop u pow 2)) (y u)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lift(--(&2 * s) * dR + drop((D:real^(1,N)finite_sum->real^1) (pastecart (vec 0) A))) =
    D(pastecart (lift(--(&2 * s))) A)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `linear(D:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (lift(--(&2 * s))) (A:real^N) =
                  (--(&2 * s)) % pastecart (lift(&1)) (vec 0) + pastecart (vec 0) A`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; GSYM LIFT_CMUL; VECTOR_MUL_RZERO;
                  VECTOR_ADD_LID; VECTOR_ADD_RID; REAL_MUL_RID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    p2au_mentions "has_vector_derivative" th)) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL [`at (lift s)`; `\u:real^1. lift(tt - drop u pow 2)`; `y:real^1->real^N`;
                 `\h:real^1. drop h % lift(--(&2 * s))`; `\h:real^1. drop h % (A:real^N)`]
                HAS_DERIVATIVE_PASTECART) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM has_vector_derivative] THEN
      SUBGOAL_THEN `(\u:real^1. lift(tt - drop u pow 2)) = lift o (\r. tt - r pow 2) o drop`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
      REAL_DIFF_TAC THEN REWRITE_TAC[ARITH_RULE `2 - 1 = 1`; REAL_POW_1] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM has_vector_derivative]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; PASTECART_CMUL]);;

(* The derivative of the L-Lagrangian along a chart L-geodesic. *)

let P2AU_LLAG_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt s (y:real^1->real^N) (A:real^1->real^N) dR.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)) /\
     ((\t. lscalar (Gt t) (y(lift s))) has_real_derivative dR) (atreal (tt - s pow 2))
     ==> ((\r. p2a_llag Gt tt r (y(lift r)) (A(lift r))) has_real_derivative
          (&4 * s * lscalar (Gt(tt - s pow 2)) (y(lift s)) - &4 * s pow 3 * dR +
           &4 * s pow 2 * drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                                  (at (y(lift s))) (A(lift s))) -
           &2 * s * lricci (Gt(tt - s pow 2)) (y(lift s)) (A(lift s)) (A(lift s))))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `s:real`; `y:real^1->real^N`; `A:real^1->real^N`]
                P2AL_ENERGY_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `s:real`; `y:real^1->real^N`; `(A:real^1->real^N)(lift s)`;
                 `dR:real`] P2AU_LSCALAR_CURVE_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[lrg_lsmooth] THEN ASM_MESON_TAC[lricci_flow];
    DISCH_TAC] THEN
  ABBREV_TAC `DRA = drop(frechet_derivative
                     (\z. lift(lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2)) z))
                     (at ((y:real^1->real^N)(lift s))) ((A:real^1->real^N)(lift s)))` THEN
  ABBREV_TAC `Ric = lricci ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                           ((y:real^1->real^N)(lift s)) ((A:real^1->real^N)(lift s))
                           (A(lift s))` THEN
  ABBREV_TAC `R0 = lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                           ((y:real^1->real^N)(lift s))` THEN
  SUBGOAL_THEN
   `(\r. p2a_llag (Gt:real->real^N->real^N^N) tt r ((y:real^1->real^N)(lift r))
                  ((A:real^1->real^N)(lift r))) =
    (\r. inv(&2) * (A(lift r) dot (Gt(tt - r pow 2) (y(lift r)) ** A(lift r))) +
         &2 * (r pow 2 * lscalar (Gt(tt - r pow 2)) (y(lift r))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2a_llag]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * s * R0 - &4 * s pow 3 * dR + &4 * s pow 2 * DRA - &2 * s * Ric =
    inv(&2) * (&4 * s pow 2 * DRA - &4 * s * Ric) +
    &2 * (s pow 2 * (--(&2 * s) * dR + DRA) + (&2 * s) * R0)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. inv(&2) * ((A:real^1->real^N)(lift r) dot
                    ((Gt:real->real^N->real^N^N)(tt - r pow 2) ((y:real^1->real^N)(lift r)) **
                     A(lift r)))`;
    `inv(&2) * (&4 * s pow 2 * DRA - &4 * s * Ric)`;
    `\r. &2 * (r pow 2 * lscalar ((Gt:real->real^N->real^N^N)(tt - r pow 2))
                                 ((y:real^1->real^N)(lift r)))`;
    `&2 * (s pow 2 * (--(&2 * s) * dR + DRA) + (&2 * s) * R0)`;
    `atreal s`] HAS_REAL_DERIVATIVE_ADD) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\s'. (A:real^1->real^N)(lift s') dot
            ((Gt:real->real^N->real^N^N)(tt - s' pow 2) ((y:real^1->real^N)(lift s')) **
             A(lift s'))`;
      `&4 * s pow 2 * DRA - &4 * s * Ric`; `inv(&2)`; `s:real`]
     HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL
     [`\r. r pow 2 * lscalar ((Gt:real->real^N->real^N^N)(tt - r pow 2))
                             ((y:real^1->real^N)(lift r))`;
      `s pow 2 * (--(&2 * s) * dR + DRA) + (&2 * s) * R0`; `&2`; `s:real`]
     HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL
     [`\r:real. r pow 2`; `&2 * s`;
      `\r. lscalar ((Gt:real->real^N->real^N^N)(tt - r pow 2)) ((y:real^1->real^N)(lift r))`;
      `--(&2 * s) * dR + DRA`; `s:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REAL_DIFF_TAC THEN REWRITE_TAC[ARITH_RULE `2 - 1 = 1`; REAL_POW_1] THEN REAL_ARITH_TAC;
      REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Nonnegative sectional curvature gives nonnegative scalar curvature.  The *)
(* two lemmas below are copies of P2BX_FRAME_TERM_NONNEG and                *)
(* P2BX_LSCALAR_NONNEG of pc_p2b_c910, renamed, on top of pc_p2b_scalpos,   *)
(* to avoid the load closure of pc_p2b_c910.                                *)
(* ------------------------------------------------------------------------- *)

let P2AU_FRAME_TERM_NONNEG = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N) i j.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v) /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> &0 <= (matrix_inv M ** basis i) dot
               (G y ** lriemann G y (matrix_inv M ** basis i)
                                    (matrix_inv M ** basis j) (matrix_inv M ** basis j))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sect") STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `fi = matrix_inv(M:real^N^N) ** basis i` THEN
  ABBREV_TAC `fj = matrix_inv(M:real^N^N) ** basis j` THEN
  SUBGOAL_THEN `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1 /\
                (fj:real^N) dot (G y ** fj) = &1 /\
                (fi:real^N) dot (G y ** fj) = (if (i:num) = j then &1 else &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `i:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `j:num`; `j:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `j:num`]
                    P2B_FRAME_ORTHO)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(G:real^N->real^N^N) y = transp(M:real^N^N) ** M` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(fi:real^N) = fj` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `fj:real^N`;
                   `fj:real^N`; `fj:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x:real^N) = --x <=> x = vec 0`] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) =
               (if (i:num) = j then &1 else &0)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~collinear {vec 0,fi:real^N,fj}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) = &0` THEN
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `c * c = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sect" (fun th -> MP_TAC(MATCH_MP (SPECL [`fi:real^N`; `fj:real^N`] th)
                                        (ASSUME `~collinear {vec 0,fi:real^N,fj}`))) THEN
  REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1]);;
let P2AU_LSCALAR_NONNEG = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v)
     ==> &0 <= lscalar G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`]
                P2B_LSCALAR_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `matrix_inv(M:real^N^N) ** basis j`] P2B_LRICCI_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P2AU_FRAME_TERM_NONNEG THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Harnack bound for the derivative of the L-Lagrangian along a chart   *)
(* L-geodesic of the flow (chart (U,phi) of the atlas):                     *)
(*   s f'(s) <= (2/c) f(s)   for 0 < s, s^2 <= (1 - c)(b - a), R >= 0.      *)
(* With X = A/(2s): s f' = 4 s^2 R - 4 s^4 (R_t - 2 dR(X) + 2 Ric(X,X))     *)
(* <= 4 s^2 R + 4 s^4 R/(t - a) <= 4 s^2 R / c <= (2/c) f.                   *)
(* ------------------------------------------------------------------------- *)

let P2AU_LLAG_BOUND_CHART = prove
 (`!(w:A->bool) top atlas a b (g:real->A->real^3^3) c U (phi:A->real^3) s
    (y:real^1->real^3) (A:real^1->real^3).
     P2B_REQ_RFA_HARNACK_STATEMENT w /\ p2a_cbflow (top,atlas) a b g /\
     (!t x v1 v2. a <= t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                  ==> &0 <= mfd_sectional atlas (g t) x v1 v2) /\
     &0 < c /\ c < &1 /\ (U,phi) IN atlas /\ &0 < s /\ s pow 2 <= (&1 - c) * (b - a) /\
     y(lift s) IN IMAGE phi U /\
     &0 <= lscalar (metric_local atlas (U,phi) (g(b - s pow 2))) (y(lift s)) /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative
        p2a_lacc (\t. metric_local atlas (U,phi) (g t)) b s (y(lift s)) (A(lift s)))
     (at (lift s))
     ==> ?f'. ((\r. p2a_llag (\t. metric_local atlas (U,phi) (g t)) b r (y(lift r)) (A(lift r)))
               has_real_derivative f') (atreal s) /\
              s * f' <= &2 * inv c *
                        p2a_llag (\t. metric_local atlas (U,phi) (g t)) b s (y(lift s))
                                 (A(lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN `lricci_flow (IMAGE (phi:A->real^3) U) a b
                  (\t. metric_local atlas ((U:A->bool),phi) ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `(U:A->bool),(phi:A->real^3)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < b - s pow 2 /\ b - s pow 2 < b /\ c * (b - a) <= (b - s pow 2) - a`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?x:A. x IN U /\ (phi:A->real^3) x = (y:real^1->real^3)(lift s)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* the time derivative of the chart scalar curvature at y(s) *)
  SUBGOAL_THEN
   `?dR. ((\t. lscalar ((\t. metric_local atlas ((U:A->bool),(phi:A->real^3))
                                ((g:real->A->real^3^3) t)) t)
                       ((y:real^1->real^3)(lift s))) has_real_derivative dR)
         (atreal (b - s pow 2))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                   `\t. metric_local atlas ((U:A->bool),(phi:A->real^3))
                         ((g:real->A->real^3^3) t)`] LRG_LSMOOTH_LSCALAR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[lrg_lsmooth] THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[lricci_flow] o check (fun th ->
        p2au_mentions "lricci_flow" th)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`interval(lift a,lift b) PCROSS IMAGE (phi:A->real^3) U`;
      `\z:real^(1,3)finite_sum. lift(lscalar ((\t. metric_local atlas ((U:A->bool),
          (phi:A->real^3)) ((g:real->A->real^3^3) t)) (drop(fstcart z))) (sndcart z))`;
      `pastecart (lift(b - s pow 2)) ((y:real^1->real^3)(lift s))`]
     SMOOTH_MAP_ON_DIFFERENTIABLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[lricci_flow] o check (fun th ->
        p2au_mentions "lricci_flow" th)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP P2AU_JOINT_PARTIALS) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                 `\t. metric_local atlas ((U:A->bool),(phi:A->real^3))
                       ((g:real->A->real^3^3) t)`;
                 `b:real`; `s:real`; `y:real^1->real^3`; `A:real^1->real^3`; `dR:real`]
                P2AU_LLAG_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  (* the Harnack inequality at (b - s^2, x) in the direction A/(2s) *)
  MP_TAC(SPECL [`w:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `a:real`; `b:real`; `g:real->A->real^3^3`] P2AU_HARNACK_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`b - s pow 2`; `U:A->bool`; `phi:A->real^3`; `x:A`; `dR:real`;
                            `inv(&2 * s) % (A:real^1->real^3)(lift s)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\t. lscalar ((\t. metric_local atlas ((U:A->bool),(phi:A->real^3))
                                   ((g:real->A->real^3^3) t)) t)
                            ((y:real^1->real^3)(lift s))` THEN
    EXISTS_TAC `min ((b - s pow 2) - a) (b - (b - s pow 2))` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t':real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:A->real^3) x = (y:real^1->real^3)(lift s)`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_SCALAR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3)(b - s pow 2)) x =
                lscalar (metric_local atlas ((U:A->bool),(phi:A->real^3)) (g(b - s pow 2)))
                        ((y:real^1->real^3)(lift s))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:A->real^3) x = (y:real^1->real^3)(lift s)`)) THEN
    MATCH_MP_TAC MFD_SCALAR_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^3) U)
                  (metric_local atlas ((U:A->bool),phi) ((g:real->A->real^3^3)(b - s pow 2)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3)(b - s pow 2))` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `(U:A->bool),(phi:A->real^3)`) THEN
      ASM_REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  ABBREV_TAC `G0 = metric_local atlas ((U:A->bool),(phi:A->real^3))
                     ((g:real->A->real^3^3)(b - s pow 2))` THEN
  ABBREV_TAC `y0 = (y:real^1->real^3)(lift s)` THEN
  ABBREV_TAC `A0 = (A:real^1->real^3)(lift s)` THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. lift(lscalar (G0:real^3->real^3^3) z)) (at y0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lricci (G0:real^3->real^3^3) y0 (inv(&2 * s) % A0) (inv(&2 * s) % A0) =
                inv(&2 * s) * inv(&2 * s) * lricci G0 y0 A0 A0`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LIFT_EQ; LIFT_CMUL] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `G0:real^3->real^3^3`; `y0:real^3`]
                  LRG_LRICCI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `inv(&2 * s) % (A0:real^3)`)
                               (MP_TAC o SPEC `A0:real^3`)) THEN
    DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP LINEAR_CMUL) THEN
    DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_CMUL; p2a_llag] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `DRA = drop(frechet_derivative (\z. lift(lscalar (G0:real^3->real^3^3) z)) (at y0) A0)` THEN
  ABBREV_TAC `Ric = lricci (G0:real^3->real^3^3) y0 A0 A0` THEN
  ABBREV_TAC `R0 = lscalar (G0:real^3->real^3^3) y0` THEN
  ABBREV_TAC `kin = (A0:real^3) dot ((G0:real^3->real^3^3) y0 ** A0)` THEN
  ABBREV_TAC `q = R0 / ((b - s pow 2) - a)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= kin` ASSUME_TAC THENL
   [SUBGOAL_THEN `!v:real^3. ~(v = vec 0) ==> &0 < v dot ((G0:real^3->real^3^3) y0 ** v)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `metric_field (IMAGE (phi:A->real^3) U) (G0:real^3->real^3^3)` THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `y0:real^3` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "kin" THEN ASM_CASES_TAC `A0:real^3 = vec 0` THENL
     [POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * s pow 4 * dR + &4 * s pow 4 * q - &4 * s pow 3 * DRA +
                &2 * s pow 2 * Ric` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 * s pow 4 * dR + &4 * s pow 4 * q - &4 * s pow 3 * DRA +
                  &2 * s pow 2 * Ric =
                  (&4 * s pow 4) * (dR + q - &2 * (inv(&2 * s) * DRA) +
                                    &2 * (inv(&2 * s) * inv(&2 * s) * Ric))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 * q <= R0 * ((&1 - c) / c)` ASSUME_TAC THENL
   [SUBGOAL_THEN `s pow 2 / ((b - s pow 2) - a) <= (&1 - c) / c` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < (b - s pow 2) - a` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - c) / c * (c * (b - a))` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(&1 - c) / c * (c * (b - a)) = (&1 - c) * (b - a)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN
    SUBGOAL_THEN `s pow 2 * R0 / ((b - s pow 2) - a) = R0 * (s pow 2 / ((b - s pow 2) - a))`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "R0" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * s pow 2 * (s pow 2 * q) <= &4 * s pow 2 * (R0 * ((&1 - c) / c))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * s pow 2 * R0 + &4 * s pow 2 * (R0 * ((&1 - c) / c)) =
                &4 * s pow 2 * R0 * inv c` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv c * kin` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The energy inequality in derivative form.  If Lam(0) = 0, Lam' = f       *)
(* and s f' <= 2 k f on (0,S), s f(s) -> 0 at 0+, and Lam, f are left       *)
(* continuous at S, then psi = (1/2 + k) Lam - (s/2) f is increasing        *)
(* on (0,S] with psi(0+) = 0, so (S/2) f(S) <= (1/2 + k) Lam(S).            *)
(* ------------------------------------------------------------------------- *)

let P2AU_ENERGY_MONO = prove
 (`!(Lam:real->real) (f:real->real) f' k S.
     &0 < S /\ &0 <= k /\
     Lam real_continuous (atreal (&0) within {s | &0 <= s}) /\ Lam(&0) = &0 /\
     ((\s. s * f s) ---> &0) (atreal (&0) within {s | &0 < s}) /\
     f real_continuous (atreal S within real_interval[&0,S]) /\
     Lam real_continuous (atreal S within real_interval[&0,S]) /\
     (!s. &0 < s /\ s < S ==> (Lam has_real_derivative f s) (atreal s)) /\
     (!s. &0 < s /\ s < S ==> (f has_real_derivative f' s) (atreal s)) /\
     (!s. &0 < s /\ s < S ==> s * f' s <= &2 * k * f s)
     ==> S / &2 * f S <= (inv(&2) + k) * Lam S`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `psi = \s. (inv(&2) + k) * (Lam:real->real) s - s / &2 * (f:real->real) s` THEN
  SUBGOAL_THEN `!e. &0 < e /\ e < S ==> (psi:real->real) e <= psi S` ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`psi:real->real`;
                   `\s. (inv(&2) + k) * (f:real->real) s - (inv(&2) * f s + s / &2 * f' s)`;
                   `e:real`; `S:real`] REAL_MVT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `x:real` THEN STRIP_TAC THEN EXPAND_TAC "psi" THEN
        SUBGOAL_THEN `(Lam:real->real) real_continuous (atreal x within real_interval[e,S]) /\
                      (f:real->real) real_continuous (atreal x within real_interval[e,S])`
        STRIP_ASSUME_TAC THENL
         [ASM_CASES_TAC `x:real = S` THENL
           [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THEN
            MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
            EXISTS_TAC `real_interval[&0,S]` THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
            CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
            MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
            ASM_MESON_TAC[REAL_ARITH `&0 < e /\ e <= x /\ x <= S /\ ~(x = S) ==> &0 < x /\ x < S`]];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
          REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID]];
        X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        EXPAND_TAC "psi" THEN
        SUBGOAL_THEN `&0 < x /\ x < S` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[];
          MP_TAC(ISPECL [`\s:real. s / &2`; `inv(&2)`; `f:real->real`; `(f':real->real) x`;
                         `x:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
          REWRITE_TAC[] THEN ANTS_TAC THENL
           [CONJ_TAC THENL
             [REWRITE_TAC[real_div] THEN
              MP_TAC(ISPECL [`\s:real. s`; `&1`; `inv(&2)`; `x:real`]
                            HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
              REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID];
              ASM_SIMP_TAC[]];
            MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `psi:real->real`)) (concl th))) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `k:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (psi:real->real) S` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `P = --((psi:real->real) S)` THEN
    SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `((\s. s * (f:real->real) s) ---> &0) (atreal (&0) within {s | &0 < s})` THEN
    REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `P / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(Lam:real->real) real_continuous (atreal (&0) within {s | &0 <= s})` THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL; IN_ELIM_THM;
                    REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `P / (&2 * (inv(&2) + k))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `x = min (min d1 d2) S / &2` THEN
    SUBGOAL_THEN `&0 < x /\ x < S /\ x < d1 /\ x < d2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `psi:real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `d1:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `d2:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&2) + k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(inv(&2) + k) * P / (&2 * (inv(&2) + k)) = P / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < inv(&2) + k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs((inv(&2) + k) * (Lam:real->real) x) < P / &2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(inv(&2) + k) = inv(&2) + k` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(inv(&2) + k) * P / (&2 * (inv(&2) + k))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `abs((inv(&2) + k) * (Lam:real->real) x) < P / &2` THEN
    UNDISCH_TAC `abs(x * (f:real->real) x) < P / &2` THEN
    EXPAND_TAC "P" THEN EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* If Lam is continuous at 0 and Lam' = f on (0,S), then s f(s) is small    *)
(* for arbitrarily small s (otherwise Lam would grow like log).              *)

let P2AU_SMALL_EPS = prove
 (`!(Lam:real->real) (f:real->real) S.
     &0 < S /\
     Lam real_continuous (atreal (&0) within {s | &0 <= s}) /\
     (!s. &0 < s /\ s < S ==> (Lam has_real_derivative f s) (atreal s))
     ==> !del eta. &0 < del /\ &0 < eta ==> ?e. &0 < e /\ e < eta /\ e * f e < del`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(Lam:real->real) real_continuous (atreal (&0) within {s | &0 <= s})` THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = min (min eta (S / &2)) (d1 / &2)` THEN
  SUBGOAL_THEN `&0 < h /\ h <= eta /\ h < S /\ h < d1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_MIN_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e = h * exp(--(&3 / del)) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ e < h` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < exp(--(&3 / del)) /\ exp(--(&3 / del)) <= &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < h * exp(--(&3 / del)) /\ h * exp(--(&3 / del)) <= h * &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the MVT for Lam - del log on [e,h] *)
  MP_TAC(ISPECL [`\s. (Lam:real->real) s - del * log s`;
                 `\s. (f:real->real) s - del * inv s`; `e:real`; `h:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(f:real->real) x - del * inv x` THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o BETA_RULE))) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (f:real->real) x - del * inv x` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `del <= x * (f:real->real) x` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `del:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `d1:real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) x - del * inv x = (x * f x - del) / x` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((Lam:real->real) h - Lam(&0)) < &1 /\ abs(Lam e - Lam(&0)) < &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log h - log e = log(&2) + &3 / del` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    SUBGOAL_THEN `log(h * exp(--(&3 / del)) / &2) = log h + --(&3 / del) - log(&2)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < exp(--(&3 / del)) / &2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL; LOG_DIV; REAL_EXP_POS_LT; REAL_ARITH `&0 < &2`; LOG_EXP] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `del * (&3 / del) = &3` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < del` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((f:real->real) x - del * inv x) * (h - e)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < del * log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `del * (log h - log e) = del * log(&2) + &3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The energy inequality without a hypothesis at 0 on s f(s) (P2AU_SMALL_EPS). *)

let P2AU_ENERGY_MONO2 = prove
 (`!(Lam:real->real) (f:real->real) f' k S.
     &0 < S /\ &0 <= k /\
     Lam real_continuous (atreal (&0) within {s | &0 <= s}) /\ Lam(&0) = &0 /\
     f real_continuous (atreal S within real_interval[&0,S]) /\
     Lam real_continuous (atreal S within real_interval[&0,S]) /\
     (!s. &0 < s /\ s < S ==> (Lam has_real_derivative f s) (atreal s)) /\
     (!s. &0 < s /\ s < S ==> (f has_real_derivative f' s) (atreal s)) /\
     (!s. &0 < s /\ s < S ==> s * f' s <= &2 * k * f s)
     ==> S / &2 * f S <= (inv(&2) + k) * Lam S`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `psi = \s. (inv(&2) + k) * (Lam:real->real) s - s / &2 * (f:real->real) s` THEN
  SUBGOAL_THEN `!e. &0 < e /\ e < S ==> (psi:real->real) e <= psi S` ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`psi:real->real`;
                   `\s. (inv(&2) + k) * (f:real->real) s - (inv(&2) * f s + s / &2 * f' s)`;
                   `e:real`; `S:real`] REAL_MVT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `x:real` THEN STRIP_TAC THEN EXPAND_TAC "psi" THEN
        SUBGOAL_THEN `(Lam:real->real) real_continuous (atreal x within real_interval[e,S]) /\
                      (f:real->real) real_continuous (atreal x within real_interval[e,S])`
        STRIP_ASSUME_TAC THENL
         [ASM_CASES_TAC `x:real = S` THENL
           [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THEN
            MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
            EXISTS_TAC `real_interval[&0,S]` THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
            CONJ_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
            MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
            ASM_MESON_TAC[REAL_ARITH `&0 < e /\ e <= x /\ x <= S /\ ~(x = S) ==> &0 < x /\ x < S`]];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
          REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID]];
        X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        EXPAND_TAC "psi" THEN
        SUBGOAL_THEN `&0 < x /\ x < S` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[];
          MP_TAC(ISPECL [`\s:real. s / &2`; `inv(&2)`; `f:real->real`; `(f':real->real) x`;
                         `x:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
          REWRITE_TAC[] THEN ANTS_TAC THENL
           [CONJ_TAC THENL
             [REWRITE_TAC[real_div] THEN
              MP_TAC(ISPECL [`\s:real. s`; `&1`; `inv(&2)`; `x:real`]
                            HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
              REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID];
              ASM_SIMP_TAC[]];
            MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `psi:real->real`)) (concl th))) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `k:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (psi:real->real) S` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `P = --((psi:real->real) S)` THEN
    SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`Lam:real->real`; `f:real->real`; `S:real`] P2AU_SMALL_EPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `(Lam:real->real) real_continuous (atreal (&0) within {s | &0 <= s})` THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL; IN_ELIM_THM;
                    REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `P / (&2 * (inv(&2) + k))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P / &2`; `min d1 S`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `eta:real`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `psi:real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `d1:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x * (f:real->real) x < P / &2` THEN
    EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&2) + k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(inv(&2) + k) * P / (&2 * (inv(&2) + k)) = P / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < inv(&2) + k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs((inv(&2) + k) * (Lam:real->real) x) < P / &2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(inv(&2) + k) = inv(&2) + k` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(inv(&2) + k) * P / (&2 * (inv(&2) + k))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `abs((inv(&2) + k) * (Lam:real->real) x) < P / &2` THEN
    UNDISCH_TAC `x * (f:real->real) x < P / &2` THEN
    EXPAND_TAC "P" THEN EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Locality.  The L-geodesic field p2a_lacc and the L-Lagrangian at (s,y)   *)
(* depend only on the metric family at time tt - s^2 near y                 *)
(* (CHRISTOFFEL_LOCAL, LSCALAR_LOCAL, LRICCI_LOCAL).                        *)
(* ------------------------------------------------------------------------- *)

(* Frechet derivatives at y depend only on the function near y. *)

let P2AU_FRECHET_LOCAL = prove
 (`!(f1:real^M->real^N) f2 O y.
     open O /\ y IN O /\ (!z. z IN O ==> f1 z = f2 z)
     ==> frechet_derivative f1 (at y) = frechet_derivative f2 (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN EQ_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THENL
   [EXISTS_TAC `f1:real^M->real^N`; EXISTS_TAC `f2:real^M->real^N`] THEN
  EXISTS_TAC `O:real^M->bool` THEN ASM_SIMP_TAC[]);;

let P2AU_LACC_LOCAL = prove
 (`!(Gt1:real->real^N->real^N^N) Gt2 O tt s y A.
     open O /\ y IN O /\ (!z. z IN O ==> Gt1 (tt - s pow 2) z = Gt2 (tt - s pow 2) z)
     ==> p2a_lacc Gt1 tt s y A = p2a_lacc Gt2 tt s y A /\
         p2a_llag Gt1 tt s y A = p2a_llag Gt2 tt s y A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN O ==> lscalar ((Gt1:real->real^N->real^N^N) (tt - s pow 2)) z =
                               lscalar (Gt2 (tt - s pow 2)) z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSCALAR_LOCAL THEN
    EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\z. lift(lscalar ((Gt1:real->real^N->real^N^N)
                                                       (tt - s pow 2)) z)) (at y) =
                frechet_derivative (\z. lift(lscalar (Gt2 (tt - s pow 2)) z)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_FRECHET_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lacc; p2a_llag; p2a_lgradR; p2a_lricop] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `christoffel ((Gt1:real->real^N->real^N^N) (tt - s pow 2)) y A A =
                christoffel (Gt2 (tt - s pow 2)) y A A /\
                (!k. lricci ((Gt1:real->real^N->real^N^N) (tt - s pow 2)) y A (basis k) =
                     lricci (Gt2 (tt - s pow 2)) y A (basis k))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; GEN_TAC] THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL; MATCH_MP_TAC LRICCI_LOCAL] THEN
    EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The local metric of the region U of a chart (U,phi) of a flow is the     *)
(* chart metric (the region form used by P2AW_FLOW_MIN_CHART).               *)

let P2AU_RLOCAL_CHART = prove
 (`!top atlas a b (g:real->A->real^3^3) (U:A->bool) (phi:A->real^3) t y.
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas /\ a < t /\ t <= b /\
     y IN IMAGE phi U
     ==> p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U INTER U,phi) t y =
         metric_local atlas (U,phi) (g t) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(U:A->bool),(phi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                  (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `(y:real^3) IN IMAGE (phi:A->real^3) U` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`;
                 `t:real`; `(U:A->bool),(phi:A->real^3)`; `x:A`] P2A_RLOCAL_SLICE) THEN
  SUBGOAL_THEN `t IN real_interval[a,b] /\ b IN real_interval[a,b]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS; FST] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2CF_MPULLBACK_LOCAL_ID THEN
  EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[chart_trans; SND; INTER_IDEMPOT] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A minimizer of a flow near an interior point s of (0, sqrt tau), in a    *)
(* chart (U,phi) of the atlas: its chart curve is C^1 with velocity A, A    *)
(* solves the L-geodesic equation of the chart metric family, and           *)
(* Lam(r) = L(gamma, r^2) has derivative the chart L-Lagrangian             *)
(* (P2AW_FLOW_MIN_CHART, P2AW_FLOW_CUT, P2A_MIN_RESTRICT_GEN).              *)
(* ------------------------------------------------------------------------- *)

let P2AU_VD_WITHIN_INTERIOR = prove
 (`!(f:real^1->real^N) f' a b x.
     (f has_vector_derivative f') (at x within interval[a,b]) /\ x IN interval(a,b)
     ==> (f has_vector_derivative f') (at x)`,
  REWRITE_TAC[has_vector_derivative] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `\h:real^1. drop h % (f':real^N)`; `x:real^1`;
                 `interval(a:real^1,b)`] HAS_DERIVATIVE_WITHIN_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `interval[a:real^1,b]` THEN ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let P2AU_MIN_INTERIOR = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) (U:A->bool) (phi:A->real^3) s.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s /\ s < sqrt tau /\ gamma(s pow 2) IN U
     ==> ?d A. &0 < d /\ d < s /\ s + d < sqrt tau /\
               A continuous_on interval[lift(s - d),lift(s + d)] /\
               !r. s - d < r /\ r < s + d
                   ==> gamma(r pow 2) IN U /\
                       ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift r))
                         (at (lift r)) /\
                       (A has_vector_derivative
                          p2a_lacc (\t. metric_local atlas (U,phi) (g t)) b r
                                   (phi(gamma(r pow 2))) (A(lift r))) (at (lift r)) /\
                       ((\rho. p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                            b gamma (rho pow 2))
                        has_real_derivative
                        p2a_llag (\t. metric_local atlas (U,phi) (g t)) b r
                                 (phi(gamma(r pow 2))) (A(lift r)))
                       (atreal r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(U:A->bool),(phi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < s /\ s < sqrt tau /\ (&0 < tau \/ tau <= &0) /\
                             (tau <= &0 ==> sqrt tau <= &0) ==> &0 < tau`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&0)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
                    REWRITE_TAC[SQRT_0; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 < tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `s pow 2 < sqrt tau pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  (* continuity of gamma at s^2: the curve stays in U *)
  SUBGOAL_THEN `?del. &0 < del /\ !t'. &0 <= t' /\ t' <= tau /\ abs(t' - s pow 2) < del
                                       ==> (gamma:real->A) t' IN U`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (b - s pow 2) = top` ASSUME_TAC THENL
     [SUBGOAL_THEN `b - s pow 2 IN real_interval[a,b]` ASSUME_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "V" THEN ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS];
      ALL_TAC] THEN
    UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_min; p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPECL [`s pow 2`; `U:A->bool`] o CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      MESON_TAC[]];
    ALL_TAC] THEN
  (* the radius d: on [s - 2d, s + 2d] the curve stays in U *)
  ABBREV_TAC `d = min (min (s / &4) ((sqrt tau - s) / &4)) (del / (&12 * s))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= s / &4 /\ d <= (sqrt tau - s) / &4 /\ &12 * s * d <= del`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &12 * s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d /\ d <= s / &4 /\ d <= (sqrt tau - s) / &4 /\ d <= del / (&12 * s)`
    MP_TAC THENL
     [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LT_DIV] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. s - &2 * d <= r /\ r <= s + &2 * d ==> (gamma:real->A)(r pow 2) IN U`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `del:real`)) (concl th))) THEN
    SUBGOAL_THEN `&0 < r /\ r < sqrt tau` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `r pow 2 < sqrt tau pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `abs(r pow 2 - s pow 2) = abs(r - s) * abs(r + s)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&2 * d) * (&3 * s)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = s + &2 * d` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < sqrt tau /\ s1 pow 2 < tau /\ sqrt(s1 pow 2) = s1 /\
                &0 < s - &2 * d /\ s - &2 * d < s1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < s1 /\ s1 < sqrt tau` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `s1 pow 2 < sqrt tau pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b p (s1 pow 2) gamma` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `tau:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `s1 pow 2`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s - &2 * d`] P2AW_FLOW_MIN_CHART) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^1->real^3` (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `sqrt(s1 pow 2) = s1`])) THEN
  (* the chart curve and its L-Lagrangian along it *)
  ABBREV_TAC `y = \v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))` THEN
  ABBREV_TAC `F0 = \rho. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#
                     (A->real^3))->bool)#(real->A->real^3^3)) U b ((U:A->bool),(phi:A->real^3)))
                     b rho ((y:real^1->real^3)(lift rho))
                     (vector_derivative y (at (lift rho)))` THEN
  ABBREV_TAC `c0 = s - &3 / &2 * d` THEN
  ABBREV_TAC `c1 = s + &3 / &2 * d` THEN
  SUBGOAL_THEN `s - &2 * d < c0 /\ c0 < s - d /\ s + d < c1 /\ c1 < s1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c0"; "c1"; "s1"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Lam(rho) = Lam(c0) + int_c0^rho F0 (P2AW_FLOW_CUT at the time rho^2) *)
  SUBGOAL_THEN
   `!rho. c0 < rho /\ rho < s1
          ==> p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) b gamma (rho pow 2) =
              p2a_L_length V b gamma (c0 pow 2) + real_integral (real_interval[c0,rho]) F0`
  ASSUME_TAC THENL
   [X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < rho /\ rho pow 2 < s1 pow 2 /\ sqrt(rho pow 2) = rho`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `p:A`; `rho pow 2`; `gamma:real->A`;
                   `U:A->bool`; `phi:A->real^3`; `s - &2 * d`; `c0:real`;
                   `A:real^1->real^3`] P2AW_FLOW_CUT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN EXISTS_TAC `s1 pow 2` THEN
        ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE];
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `s - &2 * d`)) (concl th) &&
          p2au_mentions "IN" th && not (p2au_mentions "has_vector_derivative" th))) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[lift(s - &2 * d),lift s1]` THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          p2au_mentions "has_vector_derivative" th &&
          not (p2au_mentions "p2a_lacc" th) && not (p2au_mentions "within" th))) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          p2au_mentions "has_vector_derivative" th &&
          not (p2au_mentions "p2a_lacc" th) && not (p2au_mentions "within" th))) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "F0" THEN EXPAND_TAC "y" THEN
    REWRITE_TAC[p2a_cL];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN EXISTS_TAC `A:real^1->real^3` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[lift(s - &2 * d),lift s1]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s - &2 * d < r /\ r < s1 /\ c0 < r /\ r < c1 /\ &0 < r`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!rho. s - &2 * d < rho /\ rho < s1
                      ==> ((y:real^1->real^3) has_vector_derivative A(lift rho)) (at (lift rho))`
  ASSUME_TAC THENL
   [X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2au_mentions "has_vector_derivative" th &&
      not (p2au_mentions "p2a_lacc" th) && not (p2au_mentions "within" th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!rho. s - &2 * d < rho /\ rho < s1 ==> (gamma:real->A)(rho pow 2) IN U`
  ASSUME_TAC THENL
   [X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `s - &2 * d`)) (concl th) &&
      p2au_mentions "IN" th && not (p2au_mentions "has_vector_derivative" th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(r pow 2) IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the two families agree on the chart image *)
  SUBGOAL_THEN
   `!rho z. s - &2 * d < rho /\ rho < s1 /\ z IN IMAGE (phi:A->real^3) U
            ==> p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) U b (U INTER U,phi) (b - rho pow 2) z =
                (\t. metric_local atlas ((U:A->bool),phi) ((g:real->A->real^3^3) t))
                  (b - rho pow 2) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
    MATCH_MP_TAC P2AU_RLOCAL_CHART THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < rho pow 2 /\ rho pow 2 < s1 pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2au_mentions "has_vector_derivative" th &&
      not (p2au_mentions "p2a_lacc" th) && not (p2au_mentions "within" th) &&
      can (find_term (fun t -> t = `y:real^1->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL
     [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) U b ((U:A->bool) INTER U,(phi:A->real^3))`;
      `\t. metric_local atlas ((U:A->bool),(phi:A->real^3)) ((g:real->A->real^3^3) t)`;
      `IMAGE (phi:A->real^3) U`; `b:real`; `r:real`;
      `(phi:A->real^3)((gamma:real->A)(r pow 2))`; `(A:real^1->real^3)(lift r)`]
     P2AU_LACC_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    MATCH_MP_TAC P2AU_VD_WITHIN_INTERIOR THEN
    MAP_EVERY EXISTS_TAC [`lift(s - &2 * d)`; `lift s1`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2au_mentions "p2a_lacc" th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the derivative of Lam at r *)
  SUBGOAL_THEN `(F0:real->real) real_continuous_on real_interval[c0,c1]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\rho. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) U b ((U:A->bool) INTER U,
                  (phi:A->real^3))) b rho ((y:real^1->real^3)(lift rho))
                  ((A:real^1->real^3)(lift rho))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `rho:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "F0" THEN REWRITE_TAC[INTER_IDEMPOT] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        p2au_mentions "has_vector_derivative" th &&
        can (find_term (fun t -> t = `y:real^1->real^3`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^3) (U INTER U)`; `s - &2 * d`; `s1:real`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a:real` THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
        ASM_REWRITE_TAC[REAL_LE_REFL];
        EXPAND_TAC "V" THEN ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS];
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `&0 < rho pow 2 /\ rho pow 2 < s1 pow 2` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^1. drop h % (A:real^1->real^3)(lift rho)` THEN
      REWRITE_TAC[GSYM has_vector_derivative] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        p2au_mentions "has_vector_derivative" th &&
        can (find_term (fun t -> t = `y:real^1->real^3`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[lift(s - &2 * d),lift s1]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN EXPAND_TAC "y" THEN
      REWRITE_TAC[LIFT_DROP; INTER_IDEMPOT] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `s - &2 * d`)) (concl th) &&
        p2au_mentions "IN" th && not (p2au_mentions "has_vector_derivative" th) &&
        not (p2au_mentions "p2a_rlocal" th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\rho. real_integral (real_interval[c0,rho]) F0) has_real_derivative
                 (F0:real->real) r) (atreal r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`F0:real->real`; `c0:real`; `c1:real`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`\rho. real_integral (real_interval[c0,rho]) (F0:real->real)`;
                   `(F0:real->real) r`; `r:real`; `real_interval(c0,c1)`]
                  HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[c0,c1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(F0:real->real) r =
    p2a_llag (\t. metric_local atlas ((U:A->bool),(phi:A->real^3)) ((g:real->A->real^3^3) t))
             b r (phi((gamma:real->A)(r pow 2))) ((A:real^1->real^3)(lift r))`
  ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN EXPAND_TAC "y" THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `vector_derivative (\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2)))
                    (at (lift r)) = (A:real^1->real^3)(lift r)` SUBST1_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        p2au_mentions "has_vector_derivative" th &&
        can (find_term (fun t -> t = `y:real^1->real^3`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "y" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) U b ((U:A->bool) INTER U,(phi:A->real^3))`;
      `\t. metric_local atlas ((U:A->bool),(phi:A->real^3)) ((g:real->A->real^3^3) t)`;
      `IMAGE (phi:A->real^3) U`; `b:real`; `r:real`;
      `(phi:A->real^3)((gamma:real->A)(r pow 2))`; `(A:real^1->real^3)(lift r)`]
     P2AU_LACC_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN REWRITE_TAC[INTER_IDEMPOT]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\rho. p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) b gamma (c0 pow 2) +
                    real_integral (real_interval[c0,rho]) F0` THEN
  EXISTS_TAC `min (r - c0) (s1 - r)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `rho:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2au_mentions "p2a_L_length" th && p2au_mentions "real_integral" th)) THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      p2au_mentions "p2a_llag" th && can (find_term (fun t -> t = `F0:real->real`)) (concl th))) THEN
    MP_TAC(ISPECL
     [`\rho:real. p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) b gamma (c0 pow 2)`; `&0`;
      `\rho. real_integral (real_interval[c0,rho]) (F0:real->real)`;
      `(F0:real->real) r`; `atreal r`] HAS_REAL_DERIVATIVE_ADD) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_LID]]);;
(* ------------------------------------------------------------------------- *)
(* One interior step along a minimizer.  Near an interior s, in the chart  *)
(* at gamma(s^2): Lam(r) = L(gamma, r^2) has derivative the chart          *)
(* L-Lagrangian F1(r), and F1 has a derivative F1' at s with s             *)
(* F1' <= (2/c) F1(s) (P2AU_MIN_INTERIOR, P2AU_LLAG_BOUND_CHART,           *)
(* P2AU_LSCALAR_NONNEG for R >= 0).                                        *)
(* ------------------------------------------------------------------------- *)

let P2AU_MIN_STEP = prove
 (`!(w:A->bool) top atlas a b (g:real->A->real^3^3) p c tau (gamma:real->A) s.
     P2B_REQ_RFA_HARNACK_STATEMENT w /\ p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\
     (!t x v1 v2. a <= t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                  ==> &0 <= mfd_sectional atlas (g t) x v1 v2) /\
     &0 < c /\ c < &1 /\ tau <= (&1 - c) * (b - a) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     &0 < s /\ s < sqrt tau
     ==> ?d F1 F1'. &0 < d /\ d < s /\ s + d < sqrt tau /\
                    (!r. s - d < r /\ r < s + d
                         ==> ((\rho. p2a_L_length (p2a_flow_view (top,atlas)
                                                      (real_interval[a,b]) g)
                                                   b gamma (rho pow 2))
                              has_real_derivative F1 r) (atreal r)) /\
                    (F1 has_real_derivative F1') (atreal s) /\
                    s * F1' <= &2 * inv c * F1 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN `&0 < c * (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tau < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau /\ s pow 2 < tau` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b])
                   (g:real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_min; p2a_adm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s pow 2 < sqrt tau pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b])
                   (g:real->A->real^3^3)) b p tau gamma` THEN
    REWRITE_TAC[p2a_min; p2a_adm] THEN
    DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 < s pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `b - s pow 2 IN real_interval[a,b]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(gamma:real->A)(s pow 2)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?(U:A->bool) (phi:A->real^3). chart_at atlas ((gamma:real->A)(s pow 2)) = U,phi`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` ASSUME_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `((U:A->bool),(phi:A->real^3)) IN atlas /\ (gamma:real->A)(s pow 2) IN U`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s:real`] P2AU_MIN_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    p2au_mentions "p2a_L_length" th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* R >= 0 at gamma(s^2) *)
  SUBGOAL_THEN `&0 <= lscalar (metric_local atlas ((U:A->bool),(phi:A->real^3))
                                ((g:real->A->real^3^3)(b - s pow 2)))
                              (phi((gamma:real->A)(s pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_LSCALAR_NONNEG THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3)(b - s pow 2))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && p2au_mentions "riemannian_metric" th)) THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[riemannian_metric] THEN
        DISCH_THEN(MP_TAC o SPEC `(U:A->bool),(phi:A->real^3)`) THEN ASM_REWRITE_TAC[FST; SND]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`v1:real^3`; `v2:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`b - s pow 2`; `(gamma:real->A)(s pow 2)`;
        `v1:real^3`; `v2:real^3`] o check (fun th ->
        is_forall(concl th) && p2au_mentions "mfd_sectional" th)) THEN
      ASM_REWRITE_TAC[mfd_sectional] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^3^3`; `c:real`; `U:A->bool`;
                 `phi:A->real^3`; `s:real`; `\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A:real^1->real^3`] P2AU_LLAG_BOUND_CHART) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F1':real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`d:real`;
    `\r. p2a_llag (\t. metric_local atlas ((U:A->bool),(phi:A->real^3))
                         ((g:real->A->real^3^3) t)) b r (phi((gamma:real->A)(r pow 2)))
                  ((A:real^1->real^3)(lift r))`;
    `F1':real`] THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
    p2au_mentions "p2a_L_length" th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* The energy bound for a minimizer to q at tau <= (1 - c)(b - a), with an  *)
(* end chart (U,phi) of the atlas (the data of P2AW_FLOW_MIN_CHART):         *)
(*   (sqrt tau / 2) llag(sqrt tau) = tau^(3/2) (R + |X|^2) <= (1/2 + 1/c) L. *)

let P2AU_MIN_ENERGY = prove
 (`!(w:A->bool) top atlas a b (g:real->A->real^3^3) p c tau (gamma:real->A)
    (U:A->bool) (phi:A->real^3) s0 A.
     P2B_REQ_RFA_HARNACK_STATEMENT w /\ p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\
     (!t x v1 v2. a <= t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                  ==> &0 <= mfd_sectional atlas (g t) x v1 v2) /\
     &0 < c /\ c < &1 /\ tau <= (&1 - c) * (b - a) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     (U,phi) IN atlas /\ &0 < s0 /\ s0 < sqrt tau /\
     (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift(sqrt tau)] /\
     (!s. s0 < s /\ s < sqrt tau
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
       (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)])
     ==> sqrt tau / &2 *
         p2a_llag (\t. metric_local atlas (U,phi) (g t)) b (sqrt tau) (phi(gamma tau))
                  (A(lift(sqrt tau))) <=
         (inv(&2) + inv c) *
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(U:A->bool),(phi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  SUBGOAL_THEN `&0 < c * (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau /\ tau < b - a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b p tau gamma` THEN
    SIMP_TAC[p2a_min; p2a_adm];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt tau` THEN
  SUBGOAL_THEN `&0 < S /\ S pow 2 = tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `Lam = \rho. p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->
                     bool)#(real->A->real^3^3)) b gamma (rho pow 2)` THEN
  ABBREV_TAC `Fe = \r. p2a_llag (\t. metric_local atlas ((U:A->bool),(phi:A->real^3))
                         ((g:real->A->real^3^3) t)) b r (phi((gamma:real->A)(r pow 2)))
                         ((A:real^1->real^3)(lift r))` THEN
  ABBREV_TAC `f = \r. if r = S then (Fe:real->real) S
                      else @d. ((Lam:real->real) has_real_derivative d) (atreal r)` THEN
  ABBREV_TAC `f' = \r. @d. ((f:real->real) has_real_derivative d) (atreal r)` THEN
  (* A. the interior facts *)
  SUBGOAL_THEN
   `!r. &0 < r /\ r < S
        ==> ((Lam:real->real) has_real_derivative f r) (atreal r) /\
            ((f:real->real) has_real_derivative f' r) (atreal r) /\
            r * f' r <= &2 * inv c * f r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `c:real`; `tau:real`;
                   `gamma:real->A`; `r:real`] P2AU_MIN_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `F1:real->real`
      (X_CHOOSE_THEN `F1':real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `!x. r - d < x /\ x < r + d ==> (f:real->real) x = F1 x` ASSUME_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN EXPAND_TAC "f" THEN
      SUBGOAL_THEN `~(x:real = S)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`Lam:real->real`; `x:real`] THEN
      CONJ_TAC THENL
       [CONV_TAC SELECT_CONV THEN EXISTS_TAC `(F1:real->real) x` THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `((f:real->real) has_real_derivative F1') (atreal r)` ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`F1:real->real`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f':real->real) r = F1'` ASSUME_TAC THENL
     [EXPAND_TAC "f'" THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`f:real->real`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SELECT_CONV THEN EXISTS_TAC `F1':real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) r = F1 r` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2au_mentions "has_real_derivative" th)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* B. Lam(rho) = J(0) - J(rho^2) on [0,S], continuity of Lam *)
  ABBREV_TAC `J = \x. real_integral (real_interval[x,tau])
                    (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^3))->
                     bool)#(real->A->real^3^3)) b gamma tau)` THEN
  SUBGOAL_THEN `(J:real->real) real_continuous_on real_interval[&0,tau]` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC REAL_INDEFINITE_INTEGRAL_CONTINUOUS_LEFT THEN
    UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b p tau gamma` THEN
    SIMP_TAC[p2a_min; p2a_adm];
    ALL_TAC] THEN
  SUBGOAL_THEN `!rho. &0 <= rho /\ rho <= S ==> (Lam:real->real) rho = J(&0) - J(rho pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `rho:real` THEN STRIP_TAC THEN EXPAND_TAC "Lam" THEN EXPAND_TAC "J" THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `rho = &0` THENL
     [ASM_REWRITE_TAC[p2a_L_length; REAL_POW_ZERO; ARITH_EQ; REAL_SUB_REFL] THEN
      SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho pow 2 /\ rho pow 2 <= tau` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `S pow 2 = tau`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `b:real`; `p:A`; `gamma:real->A`; `tau:real`;
                   `rho pow 2`] P2A_LENGTH_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b p tau gamma` THEN
      SIMP_TAC[p2a_min];
      ALL_TAC] THEN
    REWRITE_TAC[p2a_L_length] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Lam:real->real) real_continuous_on real_interval[&0,S]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\rho. (J:real->real)(&0) - J(rho pow 2)` THEN CONJ_TAC THENL
     [X_GEN_TAC `rho:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\rho. (J:real->real)(rho pow 2)) = J o (\rho. rho pow 2)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real. x`; `2`; `real_interval[&0,S]`] REAL_CONTINUOUS_ON_POW) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,tau]` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `S pow 2 = tau`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* C. f = Fe on (s0,S] *)
  SUBGOAL_THEN `!r. s0 < r /\ r <= S ==> (f:real->real) r = Fe r` ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_CASES_TAC `r:real = S` THENL
     [EXPAND_TAC "f" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r < S /\ &0 < r` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                   `phi:A->real^3`; `r:real`] P2AU_MIN_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `s0:real`)) (concl th) && p2au_mentions "IN" th &&
        not (p2au_mentions "has_vector_derivative" th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `A':real^1->real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      p2au_mentions "has_real_derivative" th &&
      can (find_term (fun t -> t = `A':real^1->real^3`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(A':real^1->real^3)(lift r) = A(lift r)` ASSUME_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
      MAP_EVERY EXISTS_TAC [`\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                            `lift r`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "f" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`Lam:real->real`; `r:real`] THEN CONJ_TAC THENL
     [CONV_TAC SELECT_CONV THEN EXISTS_TAC `(Fe:real->real) r`; ALL_TAC] THEN
    EXPAND_TAC "Fe" THEN EXPAND_TAC "Lam" THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `A':real^1->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* D. Fe is continuous on [s1,S], s1 = (s0 + S)/2 *)
  ABBREV_TAC `s1 = (s0 + S) / &2` THEN
  SUBGOAL_THEN `s0 < s1 /\ s1 < S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Fe:real->real) real_continuous_on real_interval[s1,S]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\rho. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#
                  (A->real^3))->bool)#(real->A->real^3^3)) U b ((U:A->bool) INTER U,
                  (phi:A->real^3))) b rho
                  ((\v:real^1. phi((gamma:real->A)(drop v pow 2))) (lift rho))
                  ((A:real^1->real^3)(lift rho))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `rho:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; LIFT_DROP] THEN STRIP_TAC THEN
      EXPAND_TAC "Fe" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < rho /\ rho pow 2 <= tau` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `S pow 2 = tau`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) U b ((U:A->bool) INTER U,(phi:A->real^3))`;
        `\t. metric_local atlas ((U:A->bool),(phi:A->real^3)) ((g:real->A->real^3^3) t)`;
        `IMAGE (phi:A->real^3) U`; `b:real`; `rho:real`;
        `(phi:A->real^3)((gamma:real->A)(rho pow 2))`; `(A:real^1->real^3)(lift rho)`]
       P2AU_LACC_LOCAL) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC FUN_IN_IMAGE THEN
          FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `s0:real`)) (concl th) && p2au_mentions "IN" th &&
            not (p2au_mentions "has_vector_derivative" th))) THEN ASM_REAL_ARITH_TAC;
          X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
          MATCH_MP_TAC P2AU_RLOCAL_CHART THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `&0 < rho pow 2` MP_TAC THENL
           [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^3) (U INTER U)`; `s0:real`; `sqrt(b - a)`] THEN
    SUBGOAL_THEN `S < sqrt(b - a)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a:real` THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "V" THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[MFDM_CHART; FST];
        EXPAND_TAC "V" THEN ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS];
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `&0 < rho pow 2 /\ rho pow 2 < b - a` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `rho pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
           [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
            ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT]];
          ASM_REAL_ARITH_TAC]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN ASM_CASES_TAC `rho:real = S` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
        EXISTS_TAC `interval[lift s0,lift S]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
          REWRITE_TAC[differentiable] THEN
          EXISTS_TAC `\h:real^1. drop h % (A:real^1->real^3)(lift S)` THEN
          ASM_REWRITE_TAC[GSYM has_vector_derivative];
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `\h:real^1. drop h % (A:real^1->real^3)(lift rho)` THEN
        REWRITE_TAC[GSYM has_vector_derivative] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift s0,lift S]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; INTER_IDEMPOT] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `s0:real`)) (concl th) && p2au_mentions "IN" th &&
        not (p2au_mentions "has_vector_derivative" th))) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* E. continuity of f and Lam at S, of Lam at 0 *)
  SUBGOAL_THEN `(f:real->real) real_continuous (atreal S within real_interval[&0,S])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_WITHINREAL_SET_IMP THEN
    EXISTS_TAC `real_interval[s1,S]` THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_ATREAL; IN_REAL_INTERVAL] THEN EXISTS_TAC `S - s1` THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_WITHINREAL THEN
    MAP_EVERY EXISTS_TAC [`Fe:real->real`; `S - s1`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(Fe:real->real) real_continuous_on real_interval[s1,S]` THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Lam:real->real) real_continuous (atreal S within real_interval[&0,S]) /\
                Lam real_continuous (atreal (&0) within {s | &0 <= s}) /\ Lam(&0) = &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(Lam:real->real) real_continuous_on real_interval[&0,S]` THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_WITHINREAL_SET_IMP THEN
      EXISTS_TAC `real_interval[&0,S]` THEN CONJ_TAC THENL
       [REWRITE_TAC[EVENTUALLY_ATREAL; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        EXISTS_TAC `S:real` THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(Lam:real->real) real_continuous_on real_interval[&0,S]` THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `J:real->real`)) (concl th) &&
        can (find_term (fun t -> t = `Lam:real->real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_REFL]];
    ALL_TAC] THEN
  (* F. the energy inequality *)
  MP_TAC(ISPECL [`Lam:real->real`; `f:real->real`; `f':real->real`; `inv c`; `S:real`]
                P2AU_ENERGY_MONO2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `f':real->real`)) (concl th) &&
      p2au_mentions "has_real_derivative" th)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) S = Fe S /\ (Lam:real->real) S =
                p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b gamma tau`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[];
      EXPAND_TAC "Lam" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "Fe" THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The conversions between the FL8 form (time first, has_derivative d1,     *)
(* lgrad2) and the LX_DERIV form (space first, wan_xder / wan_tder of       *)
(* p2bw_cfun).                                                              *)
(* ------------------------------------------------------------------------- *)

(* |grad f|^2 = X.G X when the partial derivatives of f are G X. *)

let P2AU_LGRAD2_GX = prove
 (`!(G:real^N->real^N^N) (f:real^N->real) y X.
     invertible(G y) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> drop(frechet_derivative (\z. lift(f z)) (at y) (basis i)) = (G y ** X)$i)
     ==> lgrad2 G f y = X dot (G y ** X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lgrad2] THEN
  SUBGOAL_THEN `X dot ((G:real^N->real^N^N) y ** X) =
                (G y ** X) dot (matrix_inv(G y) ** (G y ** X))` SUBST1_TAC THENL
   [SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
             ASSUME `invertible((G:real^N->real^N^N) y)`] THEN
    REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  ABBREV_TAC `pv = (G:real^N->real^N^N) y ** X` THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN REWRITE_TAC[dot; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* A function of (t,x) (time first) differentiable at (t0,x0) and its       *)
(* space-first form: derivative, time partial and space partials.           *)

let P2AU_SWAP_DERIV = prove
 (`!(Fj:real^(1,N)finite_sum->real^1) d1 t0 (x0:real^N).
     (Fj has_derivative d1) (at (pastecart (lift t0) x0))
     ==> (\w:real^(N,1)finite_sum. Fj(pastecart (sndcart w) (fstcart w)))
         differentiable (at (pastecart x0 (lift t0))) /\
         frechet_derivative (\w:real^(N,1)finite_sum. Fj(pastecart (sndcart w) (fstcart w)))
                            (at (pastecart x0 (lift t0))) =
         (\h. d1(pastecart (sndcart h) (fstcart h))) /\
         ((\z. Fj(pastecart (lift t0) z)) has_derivative (\v. d1(pastecart (vec 0) v)))
           (at x0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(\w:real^(N,1)finite_sum. pastecart (sndcart w) (fstcart w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w:real^(N,1)finite_sum. (Fj:real^(1,N)finite_sum->real^1)
        (pastecart (sndcart w) (fstcart w))) has_derivative
     (\h. d1(pastecart (sndcart h) (fstcart h)))) (at (pastecart x0 (lift t0)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^(N,1)finite_sum. pastecart (sndcart w) (fstcart w)`;
                   `Fj:real^(1,N)finite_sum->real^1`;
                   `\w:real^(N,1)finite_sum. pastecart (sndcart w) (fstcart w)`;
                   `d1:real^(1,N)finite_sum->real^1`; `pastecart (x0:real^N) (lift t0)`]
                  DIFF_CHAIN_AT) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; FSTCART_PASTECART; SNDCART_PASTECART; o_DEF];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`Fj:real^(1,N)finite_sum->real^1`; `d1:real^(1,N)finite_sum->real^1`;
                   `t0:real`; `x0:real^N`] P2AU_JOINT_PARTIALS) THEN
    ASM_SIMP_TAC[]]);;

(* The chart metric is positive definite (as P2AU_METRIC_LOCAL_PD of        *)
(* pc_p2a_frv, which is not in the load closure of this file).              *)

let P2AU_ML_POSDEF = prove
 (`!atlas (g:A->real^N^N) c y.
     riemannian_metric atlas g /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> positive_definite(metric_local atlas c g y)`,
  REWRITE_TAC[riemannian_metric; metric_field; positive_definite; symmetric_matrix] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* FL8 (MT Prop 9.9 on a finite interval).  At a point where l is           *)
(* differentiable, LX_DERIV gives grad l = G X and                          *)
(* l_tau = (R - X.G X)/2 - l/(2 tau) with X the end velocity of a           *)
(* minimizer (FL2); MIN_END gives the end chart data; the energy bound      *)
(* tau (R + X.G X) <= (1 + 2/c) l (P2AU_MIN_ENERGY,                         *)
(* L = 2 sqrt(tau) l) gives both inequalities.  P2AU_FLOW_PROP_9_9:         *)
(* LX_DERIV, MIN_END, Harnack and FL2 imply FL8.                            *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_PROP_9_9 = prove
 (`!(u:A->bool) (n:3->bool).
     P2AW_FLOW_LX_DERIV_STATEMENT u /\ P2AW_FLOW_MIN_END_STATEMENT u /\
     P2B_REQ_RFA_HARNACK_STATEMENT u /\ P2A_FLOW_MIN_EXISTS_STATEMENT u n
     ==> P2A_FLOW_PROP_9_9_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2AW_FLOW_LX_DERIV_STATEMENT; P2AW_FLOW_MIN_END_STATEMENT;
              P2A_FLOW_MIN_EXISTS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LXD") (CONJUNCTS_THEN2 (LABEL_TAC "MEND")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FL2")))) THEN
  REWRITE_TAC[P2A_FLOW_PROP_9_9_STATEMENT; DIMINDEX_3; LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `c:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `q:A`; `d1:real^(1,3)finite_sum->real^1`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN `&0 < c * (b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tau < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the chart at q *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `q:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?(U:A->bool) (phi:A->real^3). chart_at atlas (q:A) = U,phi`
  (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` ASSUME_TAC)) THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `((U:A->bool),(phi:A->real^3)) IN atlas /\ (q:A) IN U` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FST]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->A->real^3^3)(b - tau)) q =
                lscalar (metric_local atlas ((U:A->bool),(phi:A->real^3)) (g(b - tau)))
                        (phi q)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_scalar]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> p2au_mentions "has_derivative" th)) THEN
  ASM_REWRITE_TAC[SND] THEN DISCH_TAC THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)` THEN
  (* a minimizer to q *)
  USE_THEN "FL2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `q:A`; `tau:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  (* the space-first form of l *)
  MP_TAC(ISPECL [`\z:real^(1,3)finite_sum. lift(p2a_lx (V:(real->A topology)#(real->((A->bool)#
                    (A->real^3))->bool)#(real->A->real^3^3)) b p (drop(fstcart z))
                    (chart_inv ((U:A->bool),(phi:A->real^3)) (sndcart z)))`;
                 `d1:real^(1,3)finite_sum->real^1`; `tau:real`; `(phi:A->real^3) q`]
                P2AU_SWAP_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN STRIP_TAC THEN
  (* LX_DERIV at (phi q, tau) *)
  USE_THEN "LXD" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `(U:A->bool),(phi:A->real^3)`;
    `(phi:A->real^3) q`; `tau:real`; `gamma:real->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FST; SND; p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `phi:A->real^3`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `chart_inv ((U:A->bool),(phi:A->real^3)) (phi q) = q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                   `phi:A->real^3`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `G0 = metric_local atlas ((U:A->bool),(phi:A->real^3))
                     ((g:real->A->real^3^3)(b - tau))` THEN
  ABBREV_TAC `R0 = lscalar (G0:real^3->real^3^3) ((phi:A->real^3) q)` THEN
  ABBREV_TAC `l0 = p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b p tau q` THEN
  (* the spatial partials and the time partial in terms of X *)
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3
                    ==> drop((d1:real^(1,3)finite_sum->real^1)(pastecart (vec 0) (basis i))) =
                        ((G0:real^3->real^3^3) ((phi:A->real^3) q) ** X)$i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      p2au_mentions "wan_xder" th)) THEN
    ASM_REWRITE_TAC[wan_xder; p2bw_cfun; p2bw_cmet; FSTCART_PASTECART; SNDCART_PASTECART;
                    LIFT_DROP] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop((d1:real^(1,3)finite_sum->real^1)(pastecart (lift(&1)) (vec 0))) =
                (R0 - X dot ((G0:real^3->real^3^3) ((phi:A->real^3) q) ** X)) / &2 -
                l0 / (&2 * tau)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> p2au_mentions "wan_tder" th)) THEN
    ASM_REWRITE_TAC[wan_tder; p2bw_cfun; p2bw_cmet; p2bw_cscal; FSTCART_PASTECART;
                    SNDCART_PASTECART; LIFT_DROP] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  (* |grad l|^2 = X.G0 X *)
  SUBGOAL_THEN
   `lgrad2 (G0:real^3->real^3^3)
           (\y. p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b p tau (chart_inv ((U:A->bool),(phi:A->real^3)) y))
           (phi q) =
    X dot ((G0:real^3->real^3^3) (phi q) ** X)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2AU_LGRAD2_GX THEN CONJ_TAC THENL
     [MATCH_MP_TAC POSITIVE_DEFINITE_IMP_INVERTIBLE THEN EXPAND_TAC "G0" THEN
      MATCH_MP_TAC P2AU_ML_POSDEF THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          p2au_mentions "riemannian_metric" th)) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `i:num` THEN REWRITE_TAC[DIMINDEX_3] THEN STRIP_TAC THEN
      SUBGOAL_THEN `frechet_derivative (\z. lift(p2a_lx (V:(real->A topology)#(real->((A->bool)#
                      (A->real^3))->bool)#(real->A->real^3^3)) b p tau
                      (chart_inv ((U:A->bool),(phi:A->real^3)) z))) (at (phi q)) =
                    (\v. (d1:real^(1,3)finite_sum->real^1)(pastecart (vec 0) v))`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the end chart data of the minimizer *)
  USE_THEN "MEND" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`;
    `(U:A->bool),(phi:A->real^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FST]; ALL_TAC] THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `interval[lift s0,lift(sqrt tau)] SUBSET {v | &0 <= drop v /\ drop v pow 2 <= tau}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt tau pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^1->real^3)(lift(sqrt tau)) = (&2 * sqrt tau) % X` ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                          `lift s0`; `lift(sqrt tau)`; `lift(sqrt tau)`] THEN
    REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= tau}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the energy bound *)
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^3^3`; `p:A`; `c:real`; `tau:real`;
                 `gamma:real->A`; `U:A->bool`; `phi:A->real^3`; `s0:real`;
                 `A:real^1->real^3`] P2AU_MIN_ENERGY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= tau}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_llag] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) b gamma tau = &2 * sqrt tau * l0` SUBST1_TAC THENL
   [EXPAND_TAC "l0" THEN REWRITE_TAC[p2a_lx] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2A_MIN_LX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `&0 < sqrt tau` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `Q = X dot ((G0:real^3->real^3^3) ((phi:A->real^3) q) ** X)` THEN
  ABBREV_TAC `r = sqrt tau` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `tau * (Q + R0) <= (&1 + &2 / c) * l0` ASSUME_TAC THENL
   [SUBGOAL_THEN `r / &2 * (inv(&2) * ((&2 * r) * (&2 * r) * Q) + &2 * tau * R0) =
                  r * (tau * (Q + R0)) /\
                  (inv(&2) + inv c) * &2 * r * l0 = r * ((&1 + &2 / c) * l0)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `r pow 2 = tau` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONJ_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
      UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = l0 / tau` THEN
  SUBGOAL_THEN `Q + R0 <= (&1 + &2 / c) * m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `l0 = tau * m` (fun th ->
      UNDISCH_TAC `tau * (Q + R0) <= (&1 + &2 / c) * l0` THEN REWRITE_TAC[th]) THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `l0 / (&2 * tau) = m / &2` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `Q + R0 <= (&1 + &2 / c) * m` THEN REWRITE_TAC[real_div] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The hypotheses of FL8 discharged.  pc_p2a_wk3 proves                     *)
(* P2AW_FLOW_LX_DERIV_THM and P2AW_FLOW_MIN_END_THM, so FL8 follows from    *)
(* Hamilton's Harnack inequality and FL2 (P2AU_FLOW_PROP_9_9_HFL2);         *)
(* pc_p2a_l72f proves FL2 (P2AK_FLOW_MIN_EXISTS_3), so FL8 needs only the   *)
(* Harnack inequality (P2AU_FLOW_PROP_9_9_H).                               *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_PROP_9_9_HFL2 = prove
 (`!(u:A->bool) (n:3->bool).
     P2B_REQ_RFA_HARNACK_STATEMENT u /\ P2A_FLOW_MIN_EXISTS_STATEMENT u n
     ==> P2A_FLOW_PROP_9_9_STATEMENT u n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AU_FLOW_PROP_9_9 THEN
  ASM_REWRITE_TAC[P2AW_FLOW_LX_DERIV_THM; P2AW_FLOW_MIN_END_THM]);;

(* FL8 at N = 3 from the Harnack inequality alone. *)

let P2AU_FLOW_PROP_9_9_H = prove
 (`!(u:A->bool) (n:3->bool).
     P2B_REQ_RFA_HARNACK_STATEMENT u ==> P2A_FLOW_PROP_9_9_STATEMENT u n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AU_FLOW_PROP_9_9_HFL2 THEN
  ASM_REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]);;

