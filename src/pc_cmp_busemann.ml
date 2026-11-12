(* ========================================================================= *)
(* Unit pc_cmp_busemann (comparison-geometry layer CMP): Busemann functions  *)
(* of rays.  A ray is a curve on [0,inf) realizing the distance between any  *)
(* two of its points; its Busemann function is the supremum (a monotone      *)
(* limit) of t - d(x, gamma t).  General facts: monotonicity, the bound d(x, *)
(* gamma 0), 1-Lipschitz, value s on the ray; on a complete manifold with    *)
(* sec >= 0 it is convex along geodesics (the d^2 Calabi barriers of         *)
(* CMPE_BARRIER give semiconvexity of t - d(., gamma t) with constant of     *)
(* order 1/t); and from every point there is an asymptotic ray along which   *)
(* it grows with unit rate.                                                  *)
(* ========================================================================= *)

needs "src/pc_cmp_tpg.ml";;

prioritize_real();;
type_invention_error := true;;

let cmp_ray = new_definition
 `cmp_ray (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
          (gamma:real->A) <=>
    (!t. &0 <= t ==> gamma t IN topspace top) /\
    (!s t. &0 <= s /\ &0 <= t
           ==> mfd_joinable (top,atlas) (gamma s) (gamma t) /\
               mfd_dist (top,atlas) g (gamma s) (gamma t) = abs(t - s))`;;

let cmp_busemann = new_definition
 `cmp_busemann (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
               (gamma:real->A) (x:A) =
    sup {t - mfd_dist (top,atlas) g x (gamma t) | t | &0 <= t}`;;

(* ========================================================================= *)
(* Elementary properties.  For x joinable to the ray: t - d(x, gamma t) is   *)
(* non-decreasing in t and at most d(x, gamma 0), so the Busemann function   *)
(* is its limit; it is 1-Lipschitz and equals s at gamma s.                  *)
(* ========================================================================= *)

let CMPB_LE_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN
  REAL_ARITH_TAC);;

let CMPB_MONO = prove
 (`!top atlas (g:A->real^N^N) gamma x s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0)) /\
        &0 <= s /\ s <= t
        ==> s - mfd_dist (top,atlas) g x (gamma s) <= t - mfd_dist (top,atlas) g x (gamma t)`,
  REWRITE_TAC[cmp_ray] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) ((gamma:real->A) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(gamma:real->A) s`; `(gamma:real->A) t`]
    MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CMPB_BOUND = prove
 (`!top atlas (g:A->real^N^N) gamma x t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0)) /\
        &0 <= t
        ==> t - mfd_dist (top,atlas) g x (gamma t) <= mfd_dist (top,atlas) g x (gamma(&0))`,
  REWRITE_TAC[cmp_ray] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A)(&0)`; `x:A`; `(gamma:real->A) t`]
    MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_SYM];
      MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
      ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `t:real`]) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A)(&0)`; `x:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

let CMPB_SUP = prove
 (`!top atlas (g:A->real^N^N) gamma x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0))
        ==> (!t. &0 <= t
                 ==> t - mfd_dist (top,atlas) g x (gamma t) <= cmp_busemann (top,atlas) g gamma x) /\
            (!e. &0 < e
                 ==> ?T0. &0 <= T0 /\
                          !t. T0 <= t
                              ==> cmp_busemann (top,atlas) g gamma x - e <
                                  t - mfd_dist (top,atlas) g x (gamma t)) /\
            cmp_busemann (top,atlas) g gamma x <= mfd_dist (top,atlas) g x (gamma(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = {t - mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A) t) | t | &0 <= t}` THEN
  SUBGOAL_THEN `!y. y IN S <=> ?t. &0 <= t /\
                     y = t - mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A) t)`
  (LABEL_TAC "S") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cmp_busemann (top,atlas) (g:A->real^N^N) gamma x = sup S` SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[cmp_busemann]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `&0 - mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A)(&0))` THEN
      USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[REAL_LE_REFL];
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A)(&0))` THEN
      USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPB_BOUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ub" MATCH_MP_TAC THEN
    USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?t0. &0 <= t0 /\
                       sup S - e < t0 - mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A) t0)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
        TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `sup S <= sup S - e` MP_TAC THENL
       [USE_THEN "lub" MATCH_MP_TAC THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `x:A`; `t0:real`; `t:real`] CMPB_MONO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "lub" MATCH_MP_TAC THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPB_BOUND THEN
    ASM_REWRITE_TAC[]]);;

let CMPB_LIPSCHITZ = prove
 (`!top atlas (g:A->real^N^N) gamma x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0)) /\
        mfd_joinable (top,atlas) x y
        ==> abs(cmp_busemann (top,atlas) g gamma x - cmp_busemann (top,atlas) g gamma y) <=
            mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (y:A) ((gamma:real->A)(&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x' y'. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x' ((gamma:real->A)(&0)) /\
            mfd_joinable (top,atlas) y' (gamma(&0)) /\ mfd_joinable (top,atlas) x' y'
            ==> cmp_busemann (top,atlas) (g:A->real^N^N) gamma x' <=
                cmp_busemann (top,atlas) g gamma y' + mfd_dist (top,atlas) g x' y'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMPB_LE_EPS THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `x':A`] CMPB_SUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `T0:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `T0:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `y':A`] CMPB_SUP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `T0:real` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y':A`; `x':A`; `(gamma:real->A) T0`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MFD_JOINABLE_SYM];
        MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
        ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[cmp_ray]) THEN
        ASM_SIMP_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y':A`; `x':A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b + d /\ b <= a + d ==> abs(a - b) <= d`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MFD_JOINABLE_SYM]]);;

let CMPB_ON_RAY = prove
 (`!top atlas (g:A->real^N^N) gamma s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma /\ &0 <= s
        ==> cmp_busemann (top,atlas) g gamma (gamma s) = s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_ray]) THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s) (gamma(&0))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `(gamma:real->A) s`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPB_LE_EPS THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `T0:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `T0:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `T0:real`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "cmp_busemann"
                               with Failure _ -> false)) (concl th) &&
      not(can (find_term ((=) `e:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) s`] MFD_DIST_REFL) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* From a barrier of d^2 - s^2 to a barrier of d.  If bf has derivative bf'  *)
(* near t0, bf' has derivative bf2 at t0 and bf(t0) + t0^2 > 0, then sqrt(bf *)
(* s + s^2) is differentiable near t0 and its derivative has a derivative D2 *)
(* <= (bf2 + 2) / (2 sqrt(bf t0 + t0^2)) at t0.                              *)
(* ========================================================================= *)

let CMPB_SQ_DERIV = prove
 (`!bf bf' s. (bf has_real_derivative bf') (atreal s)
              ==> ((\s. bf s + s pow 2) has_real_derivative bf' + &2 * s) (atreal s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\s:real. s`; `&1`; `s:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_1; REAL_MUL_RID]);;

let CMPB_SQRT_COMP = prove
 (`!Fn Fn' s. (Fn has_real_derivative Fn') (atreal s) /\ &0 < Fn s
            ==> ((\s. sqrt(Fn s)) has_real_derivative Fn' * inv(&2 * sqrt(Fn s))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Fn:real->real`; `sqrt`; `Fn':real`; `inv(&2 * sqrt((Fn:real->real) s))`; `s:real`]
    REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT] THEN
  REWRITE_TAC[o_DEF; REAL_MUL_SYM]);;

let CMPB_SQRT_BARRIER = prove
 (`!bf bf' bf2 t0 e.
        &0 < e /\
        (!s. abs(s - t0) < e ==> (bf has_real_derivative bf' s) (atreal s)) /\
        (bf' has_real_derivative bf2) (atreal t0) /\
        &0 < bf t0 + t0 pow 2
        ==> ?d D'. &0 < d /\
                   (!s. abs(s - t0) < d
                        ==> ((\s. sqrt(bf s + s pow 2)) has_real_derivative D' s) (atreal s)) /\
                   D' t0 = (bf' t0 + &2 * t0) / (&2 * sqrt(bf t0 + t0 pow 2)) /\
                   ?D2. (D' has_real_derivative D2) (atreal t0) /\
                        D2 <= (bf2 + &2) / (&2 * sqrt(bf t0 + t0 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `F0 = bf t0 + t0 pow 2` THEN
  SUBGOAL_THEN `((\s. bf s + s pow 2) has_real_derivative bf' t0 + &2 * t0) (atreal t0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPB_SQ_DERIV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\ !s. abs(s - t0) < d1 ==> &0 < bf s + s pow 2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `F0 / &2`) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real = t0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = sqrt F0` THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min e d1` THEN
  EXISTS_TAC `\s. (bf' s + &2 * s) * inv(&2 * sqrt(bf s + s pow 2))` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\s. bf s + s pow 2`; `bf' (s:real) + &2 * s`; `s:real`]
      CMPB_SQRT_COMP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC CMPB_SQ_DERIV THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    REWRITE_TAC[real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. &2 * sqrt(bf s + s pow 2)) has_real_derivative
     &2 * ((bf' t0 + &2 * t0) * inv(&2 * S))) (atreal t0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MP_TAC(ISPECL [`\s. bf s + s pow 2`; `bf' (t0:real) + &2 * t0`; `t0:real`]
      CMPB_SQRT_COMP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(bf' t0 + &2 * t0) *
              (--(&2 * ((bf' t0 + &2 * t0) * inv(&2 * S))) / (&2 * S) pow 2) +
              (bf2 + &2) * inv(&2 * S)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\s. bf' s + &2 * s`; `bf2 + &2`;
                   `\s. inv(&2 * sqrt(bf s + s pow 2))`;
                   `--(&2 * ((bf' t0 + &2 * t0) * inv(&2 * S))) / (&2 * S) pow 2`;
                   `t0:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`\s:real. s`; `&1`; `&2`; `t0:real`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID];
        MP_TAC(ISPECL [`\s. &2 * sqrt(bf s + s pow 2)`;
                       `&2 * ((bf' t0 + &2 * t0) * inv(&2 * S))`; `t0:real`]
          HAS_REAL_DERIVATIVE_INV_ATREAL) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> x + y <= y`) THEN
  SUBGOAL_THEN
   `!x. x * --(&2 * x / (&2 * S)) / (&2 * S) pow 2 = --(x pow 2 / (&4 * S pow 3))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN UNDISCH_TAC `&0 < S` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_DIV THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* An upper barrier of the distance itself.  On a complete manifold with sec *)
(* >= 0, for a unit-speed geodesic sigma = geo(p,u) and q with L = d(sigma   *)
(* t0, q) > 0: a function D >= d(q, sigma .) near t0, equal at t0,           *)
(* differentiable near t0, whose derivative has a derivative at most 2/L at  *)
(* t0 (CMPE_BARRIER with delta = L/2 and CMPB_SQRT_BARRIER).                 *)
(* ========================================================================= *)

let CMPB_DIST_BARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) u t0 (q:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ mfd_tnorm g p u = &1 /\
        mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u t0) q /\
        &0 < mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q
        ==> ?d D D' D2.
              &0 < d /\
              (!s. abs(s - t0) < d ==> (D has_real_derivative D' s) (atreal s)) /\
              (D' has_real_derivative D2) (atreal t0) /\
              D2 <= &2 / mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q /\
              D t0 = mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u t0) q /\
              (!s. abs(s - t0) < d
                   ==> mfd_dist (top,atlas) g q (mfd_geo (top,atlas) g p u s) <= D s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z = mfd_geo (top,atlas) (g:A->real^N^N) p u t0` THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) z q` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `q:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `z:A`; `w:real^N`; `q:A`;
                 `L / &2`] CMPE_BARRIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `bf:real->real`
    (X_CHOOSE_THEN `bf':real->real` (X_CHOOSE_THEN `bf2:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`bf:real->real`; `bf':real->real`; `bf2:real`; `t0:real`; `e:real`]
    CMPB_SQRT_BARRIER) THEN
  ASM_REWRITE_TAC[REAL_SUB_ADD] THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `D':real->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `sqrt(L pow 2) = L` ASSUME_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min d e`; `\s. sqrt(bf s + s pow 2)`; `D':real->real`; `D2:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_ADD] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    UNDISCH_TAC `D2 <= (bf2 + &2) / (&2 * sqrt(L pow 2))` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(bf2 + &2) / (&2 * L)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `bf2 <= &2` ASSUME_TAC THENL
     [UNDISCH_TAC `bf2 <= &2 * L / &2 / (L - L / &2)` THEN
      SUBGOAL_THEN `&2 * L / &2 / (L - L / &2) = &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 / L = &4 / (&2 * L)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < L ==> &0 < &2 * L`] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th) &&
      can (find_term ((=) `bf:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u s`]
      MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Convexity along geodesics (complete, sec >= 0).  For a unit-speed         *)
(* geodesic sigma and Tm beyond C = d(sigma a, gamma 0) + (c - a), t -       *)
(* d(sigma s, gamma Tm) is semiconvex on [a,c] with the error (x - a)(c -    *)
(* x)/(Tm - C) (Calabi's lemma CMPA_CALABI applied to the barriers of        *)
(* CMPB_DIST_BARRIER); letting Tm go to infinity gives the convexity of the  *)
(* Busemann function along sigma.                                            *)
(* ========================================================================= *)

let CMPB_SHIFT_DERIV1 = prove
 (`!D D' Tm K s. (D has_real_derivative D') (atreal s)
                ==> ((\s. D s - Tm - K / &2 * s pow 2) has_real_derivative D' - K * s) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s. D s - Tm - K / &2 * s pow 2) has_real_derivative
                 (D' - &0) - K / &2 * (&2 * s)) (atreal s)` MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MP_TAC(ISPECL [`\s:real. s`; `&1`; `s:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_POW_1; REAL_MUL_RID]];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let CMPB_SHIFT_DERIV2 = prove
 (`!D' D2 K t0. (D' has_real_derivative D2) (atreal t0)
                ==> ((\s. D' s - K * s) has_real_derivative D2 - K) (atreal t0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\s:real. s`; `&1`; `K:real`; `t0:real`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID]);;

let CMPB_SEMICONVEX = prove
 (`!top atlas (g:A->real^N^N) gamma (p:A) u a c Tm.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        cmp_ray (top,atlas) g gamma /\ p IN topspace top /\ mfd_tnorm g p u = &1 /\
        mfd_joinable (top,atlas) p (gamma(&0)) /\ a < c /\ &0 <= Tm /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (gamma(&0)) + (c - a) < Tm
        ==> !x. a <= x /\ x <= c
                ==> Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u x) (gamma Tm) <=
                    (Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (gamma Tm)) +
                    (x - a) / (c - a) *
                    ((Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u c) (gamma Tm)) -
                     (Tm - mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (gamma Tm))) +
                    inv(Tm - (mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (gamma(&0)) +
                             (c - a))) * (x - a) * (c - x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_ray]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) p u = (:real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN STRIP_TAC THEN
  ABBREV_TAC `C = mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) a) (gamma(&0)) + (c - a)` THEN
  SUBGOAL_THEN `!s. (sigma:real->A) s IN topspace top /\
                    mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p (sigma s) /\
                    mfd_joinable (top,atlas) (sigma s) ((gamma:real->A)(&0))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `&0`; `s:real`]
      GEOH_GEO_SEG_DIST) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(sigma:real->A) s IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `(:real)`] THEN ASM_REWRITE_TAC[IN_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. mfd_tnorm (g:A->real^N^N) ((sigma:real->A) s) (mfd_vel atlas sigma s) = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= c
                    ==> Tm - C <= mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm) ((sigma:real->A) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `a:real`; `s:real`]
      GEOH_GEO_SEG_DIST) THEN
    ASM_REWRITE_TAC[IN_UNIV; REAL_MUL_RID] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                    ((gamma:real->A)(&0)) ((gamma:real->A) Tm) /\
                  mfd_dist (top,atlas) (g:A->real^N^N) (gamma(&0)) (gamma Tm) = Tm`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `Tm:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_dist"
                                 with Failure _ -> false)) (concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        not(can (find_term ((=) `sigma:real->A`)) (concl th)))) THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_SUB_RZERO; REAL_ABS_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(&0)`; `(sigma:real->A) a`; `(sigma:real->A) s`]
      MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(&0)`; `(sigma:real->A) s`; `(gamma:real->A) Tm`]
      MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MFD_JOINABLE_SYM];
        MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
        ASM_MESON_TAC[MFD_JOINABLE_SYM]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(&0)`; `(sigma:real->A) a`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(sigma:real->A) s`; `(gamma:real->A) Tm`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs(s - a) <= c - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Tm - C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = &2 / (Tm - C)` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm) ((sigma:real->A) s) -
                      Tm - K / &2 * s pow 2`; `a:real`; `c:real`] CMPA_CALABI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                       `sigma:real->A`; `(:real)`] GEOL_GEODESIC_BASIC) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `(:real)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN
        SUBGOAL_THEN `(\s. mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm) ((sigma:real->A) s)) =
                      (\y. mfd_dist (top,atlas) g (gamma Tm) y) o sigma`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_ID]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t0:real`; `e:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) t0) ((gamma:real->A) Tm)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(sigma:real->A) t0`; `(gamma:real->A) Tm`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `u:real^N`; `t0:real`; `(gamma:real->A) Tm`]
      CMPB_DIST_BARRIER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:real`; `D:real->real`; `D':real->real`; `D2:real`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `\s. (D:real->real) s - Tm - K / &2 * s pow 2`;
                          `\s. (D':real->real) s - K * s`; `D2 - K`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMPB_SHIFT_DERIV1 THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CMPB_SHIFT_DERIV2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `D2 <= K /\ &0 < e ==> D2 - K <= e`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 / mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) t0) ((gamma:real->A) Tm)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(sigma:real->A) t0`; `(gamma:real->A) Tm`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(sigma:real->A) t0`; `(gamma:real->A) Tm`] MFD_DIST_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - Tm - k <= y - Tm - k`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "cal") THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  USE_THEN "cal" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `a <= x`) (ASSUME `x <= c`)))) THEN
  REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; v; `(gamma:real->A) Tm`] MFD_DIST_SYM))
   [`(sigma:real->A) a`; `(sigma:real->A) c`; `(sigma:real->A) x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ABBREV_TAC `l = (x - a) / (c - a)` THEN
  SUBGOAL_THEN `l * (c pow 2 - a pow 2) = (x - a) * (c + a)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN UNDISCH_TAC `a < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `inv(Tm - C) = K / &2` SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN UNDISCH_TAC `&0 < Tm - C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `da = mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm) ((sigma:real->A) a)` THEN
  ABBREV_TAC `dc = mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm) ((sigma:real->A) c)` THEN
  ABBREV_TAC `dx = mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) Tm) ((sigma:real->A) x)` THEN
  SUBGOAL_THEN `K / &2 * (x - a) * (c - x) = K / &2 * (a pow 2 + (x - a) * (c + a) - x pow 2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `l * (c pow 2 - a pow 2)`)) THEN
  REAL_ARITH_TAC);;

let CMPB_GEO_JOIN = prove
 (`!top atlas (g:A->real^N^N) (p:A) u (y:A) s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        mfd_joinable (top,atlas) p y
        ==> mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u s) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`p:A`; `u:real^N`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`;
                 `&0`; `s:real`] GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM]);;

let CMPB_CONVEX = prove
 (`!top atlas (g:A->real^N^N) gamma (p:A) u a c x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        cmp_ray (top,atlas) g gamma /\ p IN topspace top /\ mfd_tnorm g p u = &1 /\
        mfd_joinable (top,atlas) p (gamma(&0)) /\ a < c /\ a <= x /\ x <= c
        ==> cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g p u x) <=
            cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g p u a) +
            (x - a) / (c - a) *
            (cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g p u c) -
             cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g p u a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN
  SUBGOAL_THEN `!s. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                      ((sigma:real->A) s) ((gamma:real->A)(&0))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "sigma" THEN MATCH_MP_TAC CMPB_GEO_JOIN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `B = cmp_busemann (top,atlas) (g:A->real^N^N) gamma` THEN
  ABBREV_TAC `l = (x - a) / (c - a)` THEN
  SUBGOAL_THEN `&0 <= l /\ l <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN
    SUBGOAL_THEN `&0 < c - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `(sigma:real->A) x`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `C = mfd_dist (top,atlas) (g:A->real^N^N) ((sigma:real->A) a) ((gamma:real->A)(&0)) +
                  (c - a)` THEN
  ABBREV_TAC `Y = (c - a) pow 2 / e` THEN
  SUBGOAL_THEN `&0 <= Y /\ Y * e = (c - a) pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  ABBREV_TAC `Tm = max T1 (C + &1 + &2 * Y)` THEN
  SUBGOAL_THEN `T1 <= Tm /\ &0 <= Tm /\ C < Tm /\ &2 * Y <= Tm - C`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `p:A`; `u:real^N`; `a:real`; `c:real`;
                 `Tm:real`] CMPB_SEMICONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `(sigma:real->A) a`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `Tm:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `(sigma:real->A) c`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `Tm:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Tm:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `T1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(Tm - C) * (x - a) * (c - x) <= e / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Tm - C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(Tm - C) * (c - a) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `&0 <= e * ((Tm - C) - &2 * Y)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `Y * e = (c - a) pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - l) * (B((sigma:real->A) a) - (Tm - mfd_dist (top,atlas) (g:A->real^N^N) (sigma a) ((gamma:real->A) Tm))) /\
                &0 <= l * (B((sigma:real->A) c) - (Tm - mfd_dist (top,atlas) (g:A->real^N^N) (sigma c) ((gamma:real->A) Tm)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Asymptotic rays.  On a complete manifold, through every point x joinable  *)
(* to a ray gamma there is a unit geodesic from x along which the Busemann   *)
(* function grows with unit rate (the limit of the minimizing segments from  *)
(* x to gamma(t)); it is again a ray.                                        *)
(* ------------------------------------------------------------------------- *)

let CMPB_GEO_FACTS = prove
 (`!top atlas (g:A->real^N^N) (p:A) u.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        p IN topspace top /\ mfd_tnorm g p u = &1
        ==> mfd_geo (top,atlas) g p u (&0) = p /\
            (!s. mfd_geo (top,atlas) g p u s IN topspace top) /\
            (!s. mfd_exp (top,atlas) g p (s % u) = mfd_geo (top,atlas) g p u s) /\
            (!s t. mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u s)
                                            (mfd_geo (top,atlas) g p u t) /\
                   mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s)
                            (mfd_geo (top,atlas) g p u t) <= abs(t - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`p:A`; `u:real^N`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) p u` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. mfd_tnorm (g:A->real^N^N) ((sigma:real->A) s) (mfd_vel atlas sigma s) = &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `(:real)`] THEN ASM_REWRITE_TAC[IN_UNIV];
    GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `u:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `sigma:real->A`; `(:real)`; `s:real`; `t:real`]
      GEOH_GEO_SEG_DIST) THEN
    ASM_REWRITE_TAC[IN_UNIV; REAL_MUL_RID] THEN MESON_TAC[]]);;

let CMPB_DIR_SUBSEQ = prove
 (`!top atlas (g:A->real^N^N) (x:A) (un:num->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        x IN topspace top /\ (!n. mfd_tnorm g x (un n) = &1)
        ==> ?u (sub:num->num). mfd_tnorm g x u = &1 /\ (!m n. m < n ==> sub m < sub n) /\
                    !r d. &0 < d
                          ==> ?N. !n. N <= n
                                  ==> mfd_dist (top,atlas) g
                                        (mfd_exp (top,atlas) g x (r % u))
                                        (mfd_exp (top,atlas) g x (r % un(sub n))) < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. mfd_exp (top,atlas) (g:A->real^N^N) x w IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_UNIV] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  ABBREV_TAC `e = \n. matrix_inv(E:real^N^N) ** (un:num->real^N) n` THEN
  SUBGOAL_THEN `!n. (E:real^N^N) ** (e:num->real^N) n = (un:num->real^N) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "e" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. norm((e:num->real^N) n) = &1` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `E:real^N^N`; `(e:num->real^N) n`]
      CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `&1`] COMPACT_SPHERE) THEN
  REWRITE_TAC[compact] THEN DISCH_THEN(MP_TAC o SPEC `e:num->real^N`) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`l:real^N`; `sub:num->num`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(E:real^N^N) ** (l:real^N)`; `sub:num->num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `E:real^N^N`; `l:real^N`] CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `d:real`] THEN DISCH_TAC THEN
  ABBREV_TAC `y0 = mfd_exp (top,atlas) (g:A->real^N^N) x (r % ((E:real^N^N) ** (l:real^N)))` THEN
  SUBGOAL_THEN `(y0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h = \w. mfd_dist (top,atlas) (g:A->real^N^N) (y0:A)
                        (mfd_exp (top,atlas) g x (r % ((E:real^N^N) ** (w:real^N))))` THEN
  SUBGOAL_THEN `continuous_map (euclidean,euclideanreal) (h:real^N->real)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SUBGOAL_THEN
     `(\w. mfd_dist (top,atlas) (g:A->real^N^N) (y0:A)
             (mfd_exp (top,atlas) g x (r % ((E:real^N^N) ** (w:real^N))))) =
      (\y. mfd_dist (top,atlas) g y0 y) o
      (\w. mfd_exp (top,atlas) g x ((r %% E) ** w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIX_VECTOR_LMUL]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `r %% (E:real^N^N)`; `(:real^N)`]
        CMPQ_EXPF_CONT) THEN
      ASM_REWRITE_TAC[IN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real) l = &0` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`; `euclidean:(real^N)topology`; `euclideanreal`;
                 `(e:num->real^N) o (sub:num->num)`; `h:real^N->real`; `l:real^N`]
    CONTINUOUS_MAP_LIMIT) THEN
  ASM_REWRITE_TAC[LIMIT_EUCLIDEAN; GSYM tendsto_real_def; REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[o_THM] THEN
  EXPAND_TAC "h" THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN REAL_ARITH_TAC);;

let CMPB_ASYM_LIMIT = prove
 (`!top atlas (g:A->real^N^N) gamma (x:A) (un:num->real^N) (tt:num->real).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0)) /\
        (!n. mfd_tnorm g x (un n) = &1) /\ (!n. &n <= tt n) /\
        (!n r. &0 <= r /\ r <= &n
               ==> mfd_joinable (top,atlas) (mfd_exp (top,atlas) g x (r % un n))
                                            (gamma(tt n)) /\
                   mfd_dist (top,atlas) g (mfd_exp (top,atlas) g x (r % un n)) (gamma(tt n)) =
                   mfd_dist (top,atlas) g x (gamma(tt n)) - r)
        ==> ?u. mfd_tnorm g x u = &1 /\
                !r. &0 <= r
                    ==> cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g x u r) =
                        cmp_busemann (top,atlas) g gamma x + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmp_ray]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rtop") (LABEL_TAC "ray")) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `un:num->real^N`] CMPB_DIR_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) x u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g0") (CONJUNCTS_THEN2 (LABEL_TAC "gtop")
    (CONJUNCTS_THEN2 (LABEL_TAC "expgeo") (LABEL_TAC "seg")))) THEN
  ABBREV_TAC `B = cmp_busemann (top,atlas) (g:A->real^N^N) gamma` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x ((sigma:real->A) r) /\
                mfd_dist (top,atlas) (g:A->real^N^N) x (sigma r) <= r`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "seg" (MP_TAC o SPECL [`&0`; `r:real`]) THEN
    USE_THEN "g0" (fun th -> REWRITE_TAC[th; REAL_SUB_RZERO]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((sigma:real->A) r) ((gamma:real->A)(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `x:A`; `(sigma:real->A) r`] CMPB_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `x:A`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `e / &2`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `sub:num->num`)) (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_dist" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  MP_TAC(SPEC `max T0 r` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
  USE_THEN "N1" (MP_TAC o SPEC `N1 + N2:num`) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = (sub:num->num)(N1 + N2)` THEN
  USE_THEN "expgeo" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `N1 + N2 <= (m:num)` ASSUME_TAC THENL
   [MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `N1 + N2:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `T0 <= (tt:num->real) m /\ r <= &m /\ &0 <= tt m` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&N2 <= &m` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `m:num` (ASSUME `!n. &n <= (tt:num->real) n`)) THEN
    MP_TAC(SPEC `m:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = mfd_exp (top,atlas) (g:A->real^N^N) x (r % (un:num->real^N) m)` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `r:real`] o check (fun th ->
    can (find_term ((=) `un:num->real^N`)) (concl th) &&
    can (find_term ((=) `tt:num->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((gamma:real->A)((tt:num->real) m)) (gamma(&0))` ASSUME_TAC THENL
   [USE_THEN "ray" (MP_TAC o SPECL [`(tt:num->real) m`; `&0`]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (y:A)
                  ((gamma:real->A)(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
    EXISTS_TAC `(gamma:real->A)((tt:num->real) m)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((sigma:real->A) r) (y:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `y:A`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(tt:num->real) m` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(tt:num->real) m` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `T0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `(sigma:real->A) r`; `y:A`] CMPB_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REAL_ARITH_TAC);;

let CMPB_ASYMPTOTE = prove
 (`!top atlas (g:A->real^N^N) gamma (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0))
        ==> ?u. mfd_tnorm g x u = &1 /\
                !r. &0 <= r
                    ==> cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g x u r) =
                        cmp_busemann (top,atlas) g gamma x + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmp_ray]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rtop") (LABEL_TAC "ray")) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  ABBREV_TAC `D0 = mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A)(&0))` THEN
  SUBGOAL_THEN `&0 <= D0` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x
                      ((gamma:real->A)(&n + D0 + &1)) /\
                    &n + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) x (gamma(&n + D0 + &1))`
  (LABEL_TAC "far") THENL
   [GEN_TAC THEN
    USE_THEN "ray" (MP_TAC o SPECL [`&0`; `&n + D0 + &1`]) THEN
    ANTS_TAC THENL [MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x
                    ((gamma:real->A)(&n + D0 + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A)(&0)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(&0)`; `x:A`;
                   `(gamma:real->A)(&n + D0 + &1)`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A)(&0)`; `x:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?w. mfd_exp (top,atlas) (g:A->real^N^N) x w = (gamma:real->A)(&n + D0 + &1) /\
            mfd_tnorm g x w = mfd_dist (top,atlas) g x (gamma(&n + D0 + &1))`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(gamma:real->A)(&n + D0 + &1)`]
      MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    USE_THEN "far" (fun th -> ASM_REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `wv:num->real^N` (LABEL_TAC "wv")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `x:A`;
                 `\n. inv(mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A)(&n + D0 + &1))) %
                      (wv:num->real^N) n`;
                 `\n. &n + D0 + &1`] CMPB_ASYM_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "wv" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `n:num` th)]) THEN
    SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A)(&n + D0 + &1))`
    ASSUME_TAC THENL
     [USE_THEN "far" (MP_TAC o CONJUNCT2 o SPEC `n:num`) THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  CONJ_TAC THENL [GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `r:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `dd = mfd_dist (top,atlas) (g:A->real^N^N) x ((gamma:real->A)(&n + D0 + &1))` THEN
  SUBGOAL_THEN `&n + &1 <= dd` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN USE_THEN "far" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "wv" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `&0 <= r * inv dd /\ r * inv dd <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(wv:num->real^N) n`; `r * inv dd`; `&1`]
    CMPS_RAY_DIST) THEN
  ASM_REWRITE_TAC[IN_UNIV; VECTOR_MUL_LID; REAL_LE_REFL] THEN
  SUBGOAL_THEN `(&1 - r * inv dd) * dd = dd - r` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID];
    ALL_TAC] THEN
  SIMP_TAC[]);;

(* The asymptotic geodesic of CMPB_ASYMPTOTE is itself a ray. *)

let CMPB_ASYMPTOTE_RAY = prove
 (`!top atlas (g:A->real^N^N) gamma (x:A) u.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        cmp_ray (top,atlas) g gamma /\ mfd_joinable (top,atlas) x (gamma(&0)) /\
        mfd_tnorm g x u = &1 /\
        (!r. &0 <= r
             ==> cmp_busemann (top,atlas) g gamma (mfd_geo (top,atlas) g x u r) =
                 cmp_busemann (top,atlas) g gamma x + r)
        ==> cmp_ray (top,atlas) g (mfd_geo (top,atlas) g x u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sigma = mfd_geo (top,atlas) (g:A->real^N^N) x u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g0") (CONJUNCTS_THEN2 (LABEL_TAC "gtop")
    (CONJUNCTS_THEN2 (LABEL_TAC "expgeo") (LABEL_TAC "seg")))) THEN
  REWRITE_TAC[cmp_ray] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  USE_THEN "seg" (STRIP_ASSUME_TAC o SPECL [`s:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                      ((sigma:real->A) z) ((gamma:real->A)(&0))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "seg" (MP_TAC o SPECL [`z:real`; `&0`]) THEN
    USE_THEN "g0" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `(sigma:real->A) s`; `(sigma:real->A) t`]
    CMPB_LIPSCHITZ) THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Two rays going off in opposite directions (as the halves of a line):    *)
(* the sum of their Busemann functions is at most 0.                       *)

let CMPB_OPPOSITE_SUM = prove
 (`!top atlas (g:A->real^N^N) gamma1 gamma2 (x:A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_ray (top,atlas) g gamma1 /\ cmp_ray (top,atlas) g gamma2 /\
        (!s t. &0 <= s /\ &0 <= t
               ==> s + t <= mfd_dist (top,atlas) g (gamma1 s) (gamma2 t)) /\
        mfd_joinable (top,atlas) x (gamma1(&0)) /\ mfd_joinable (top,atlas) x (gamma2(&0))
        ==> cmp_busemann (top,atlas) g gamma1 x + cmp_busemann (top,atlas) g gamma2 x <= &0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMPB_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma1:real->A`; `x:A`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `T1:real`))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma2:real->A`; `x:A`] CMPB_SUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `T2:real`))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmp_ray] o check (fun th ->
    concl th = `cmp_ray (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) gamma1`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `T1:real`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x
                  ((gamma1:real->A) T1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma1:real->A)(&0)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmp_ray] o check (fun th ->
    concl th = `cmp_ray (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) gamma2`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `T2:real`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x
                  ((gamma2:real->A) T2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma2:real->A)(&0)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma1:real->A) T1`; `x:A`; `(gamma2:real->A) T2`]
    MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma1:real->A) T1`; `x:A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`T1:real`; `T2:real`] o check (fun th ->
    can (find_term ((=) `gamma1:real->A`)) (concl th) &&
    can (find_term ((=) `gamma2:real->A`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

