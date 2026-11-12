(* ========================================================================= *)
(* pc_apx_neck: the neck layer N0-N8 of the Appendix (MT Appendix A).        *)
(* Distances in necks (N2, MT Lemma A.4 and Cor A.5) from the C^0 part of    *)
(* the eps-closeness, the cylinder model and the curve lemmas of             *)
(* pc_grg_dist / pc_grg_dist2.                                               *)
(* ========================================================================= *)

needs "src/pc_apx_local.ml";;
needs "src/pc_grg_dist2.ml";;
needs "src/pc_apx_scal.ml";;
needs "src/pc_lrg_constcurv.ml";;
needs "src/pc_smt_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The cylinder model.  The quadratic form of cylinder_flow 0,               *)
(* the s-coordinate along curves (s = sqrt 2 log |y|, so ds/dt is at most   *)
(* the G0-speed) and the lower bound |s(c b) - s(c a)| <= G0-length of c.    *)
(* ------------------------------------------------------------------------- *)

let APX_CYL0_QUAD = prove
 (`!y w:real^3. w dot (cylinder_flow (&0) y ** w) = &2 / norm y pow 2 * (w dot w)`,
  REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL]);;

let APX_SVAL_LOGSQ = prove
 (`!y:real^3. ~(y = vec 0) ==> apx_sval y = sqrt(&2) / &2 * log(y dot y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval; GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC);;

let APX_LOGSQ_DERIV = prove
 (`!(c:real->real^N) v t s.
        ~(c t = vec 0) /\
        ((\r. c(drop r)) has_vector_derivative v) (at (lift t) within IMAGE lift s)
        ==> ((\t. sqrt(&2) / &2 * log(c t dot c t)) has_real_derivative
             (sqrt(&2) * (c t dot v) / (c t dot c t))) (atreal t within s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\t. (c:real->real^N) t dot c t) has_real_derivative (&2 * (c t dot v)))
    (atreal t within s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN] THEN
    MP_TAC(ISPECL [`\x y:real^N. lift(x dot y)`; `\r. (c:real->real^N)(drop r)`;
                   `\r. (c:real->real^N)(drop r)`; `v:real^N`; `v:real^N`;
                   `lift t`; `IMAGE lift (s:real->bool)`]
                  HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c:real->real^N) t dot c t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (c:real->real^N) t dot c t`; `log`;
                 `&2 * ((c:real->real^N) t dot v)`; `inv((c:real->real^N) t dot c t)`;
                 `t:real`; `s:real->bool`] REAL_DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sqrt(&2) / &2` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_WITHIN) THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let APX_SVAL_SPEED_INEQ = prove
 (`!y v:real^3.
        ~(y = vec 0)
        ==> abs(sqrt(&2) * (y dot v) / (y dot y)) <=
            sqrt(&2 / norm y pow 2 * (v dot v))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  REWRITE_TAC[REAL_POW2_ABS; GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^3`; `v:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPEC `v:real^3` NORM_POS_LE) THEN
  SPEC_TAC(`(y:real^3) dot v`,`d:real`) THEN
  SPEC_TAC(`norm(v:real^3)`,`m:real`) THEN
  UNDISCH_TAC `&0 < norm(y:real^3)` THEN
  SPEC_TAC(`norm(y:real^3)`,`n:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d pow 2 <= (n * m) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `n * m:real` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(sqrt(&2) * d / n pow 2) pow 2 = (&2 * d pow 2) / n pow 4 /\
    &2 / n pow 2 * m pow 2 = (&2 * (n * m) pow 2) / n pow 4`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
    SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
    REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `~(n = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC);;

(* The G0-length of a C^1 curve of an open set avoiding 0 bounds the change *)
(* of s along it (the model version of MT Lemma A.4).                        *)

let APX_SVAL_LENGTH_LOWER = prove
 (`!s (c:real->real^3) a b.
        open s /\ (!y. y IN s ==> ~(y = vec 0)) /\
        mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b
        ==> abs(apx_sval(c b) - apx_sval(c a)) <=
            mfd_length (open_set_atlas s) (cylinder_flow (&0)) c a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL; REAL_SUB_REFL; REAL_ABS_0;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (c:real->real^3) t IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^3->bool)`;
                   `open_set_atlas (s:real^3->bool)`;
                   `c:real->real^3`; `a:real`; `b:real`; `t:real`]
                  MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[a,b]
        ==> ((\r. (c:real->real^3)(drop r)) has_vector_derivative
             vector_derivative (\r. c(drop r)) (at (lift t) within interval[lift a,lift b]))
            (at (lift t) within interval[lift a,lift b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (s:real^3->bool)`;
                   `open_set_atlas (s:real^3->bool)`;
                   `c:real->real^3`; `a:real`; `b:real`;
                   `(s:real^3->bool,(\x:real^3. x))`; `t:real`] GRGD_C1_CHART_HAS_VD) THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES; FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. sqrt(&2) *
          ((c:real->real^3) t dot
           vector_derivative (\r. c(drop r)) (at (lift t) within interval[lift a,lift b])) /
          (c t dot c t)) has_real_integral
     ((\t. sqrt(&2) / &2 * log(c t dot c t)) b -
      (\t. sqrt(&2) / &2 * log(c t dot c t)) a)) (real_interval[a,b])`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC APX_LOGSQ_DERIV THEN
    ASM_SIMP_TAC[IMAGE_LIFT_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a IN real_interval[a,b] /\ b IN real_interval[a,b]` STRIP_ASSUME_TAC
  THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((c:real->real^3) a = vec 0) /\ ~(c b = vec 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&2) / &2 * log((c:real->real^3) b dot c b) = apx_sval(c b) /\
    sqrt(&2) / &2 * log((c:real->real^3) a dot c a) = apx_sval(c a)`
  (fun th -> BETA_TAC THEN REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_SVAL_LOGSQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
    EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS] THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[GRGD_OPEN_SET_SPEED; APX_CYL0_QUAD] THEN
    MATCH_MP_TAC APX_SVAL_SPEED_INEQ THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The C^0 part of the eps-closeness of a neck (from                         *)
(* LCK_DIST_C0 of pc_lrg_stab) and the resulting comparison of lengths of    *)
(* curves in the neck with their G0-lengths in the model, at the scale       *)
(* h = R(x)^(-1/2).                                                          *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_DOM_OPEN = prove
 (`!eps. open(rfs_neck_dom eps)`,
  REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]);;

let APX_NECK_CYL_FIELD = prove
 (`!eps. metric_field (rfs_neck_dom eps) (cylinder_flow (&0))`,
  GEN_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; APX_NECK_DOM_NONZERO;
           APX_NECK_DOM_OPEN]);;

let APX_NECK_FIELDS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A).
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e
        ==> metric_field (rfs_neck_dom eps) (rfs_pullback atlas e g) /\
            metric_field (rfs_neck_dom eps)
              (\y. mfd_scalar atlas g x %% rfs_pullback atlas e g y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (rfs_pullback atlas (e:real^3->A) g)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let APX_NECK_C0 = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y w.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps
        ==> abs(w dot ((mfd_scalar atlas g x %% rfs_pullback atlas e g y) ** w) -
                w dot (cylinder_flow (&0) y ** w))
            <= eps * (w dot (cylinder_flow (&0) y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_kreg eps`; `rfs_neck_dom eps`; `cylinder_flow (&0)`;
                 `\y. mfd_scalar atlas (g:A->real^3^3) x %%
                      rfs_pullback atlas (e:real^3->A) g y`;
                 `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
       [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    REWRITE_TAC[APX_CYL0_QUAD] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[DOT_POS_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2]]);;

let APX_NECK_C0_BOUNDS = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y w.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps
        ==> (&1 - eps) * (w dot (cylinder_flow (&0) y ** w)) <=
            w dot ((mfd_scalar atlas g x %% rfs_pullback atlas e g y) ** w) /\
            w dot ((mfd_scalar atlas g x %% rfs_pullback atlas e g y) ** w) <=
            (&1 + eps) * (w dot (cylinder_flow (&0) y ** w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                `y:real^3`; `w:real^3`] APX_NECK_C0) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let APX_LENGTH_ARITH = prove
 (`!r p q L0 LG LR.
        &0 < r /\ &0 < p /\ LR = r * LG /\ L0 <= inv p * LR /\ LR <= q * L0
        ==> p * inv r * L0 <= LG /\ LG <= q * inv r * L0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LG = inv r * LR` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv r` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH `p * ir * l:real = ir * (p * l)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `L0 <= inv p * LR` THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `q * ir * l:real = ir * (q * l)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* Lengths of curves in the neck domain: e o c is C^1 and its g-length is    *)
(* within the factors sqrt(1 -+ eps) of h times the G0-length of c.          *)

let APX_NECK_CURVE_LENGTH = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) c a b.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
        mfd_c1_curve (subtopology euclidean (rfs_neck_dom eps),
                      open_set_atlas (rfs_neck_dom eps)) c a b
        ==> mfd_c1_curve (top,atlas) (e o c) a b /\
            sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0)) c a b
            <= mfd_length atlas g (e o c) a b /\
            mfd_length atlas g (e o c) a b <=
            sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0)) c a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `D = rfs_neck_dom eps` THEN
  SUBGOAL_THEN `open(D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[APX_NECK_DOM_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (D:real^3->bool)) (open_set_atlas D)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_SET_ATLAS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `D:real^3->bool`; `e:real^3->A`;
                 `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `c:real->real^3`; `a:real`; `b:real`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[rfs_pullback] THEN
  REWRITE_TAC[GSYM rfs_pullback] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                 `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `c:real->real^3`; `a:real`; `b:real`; `R:real`] MFD_LENGTH_SCALE) THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN; REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> (c:real->real^3) t IN D` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`;
                   `open_set_atlas (D:real^3->bool)`;
                   `c:real->real^3`; `a:real`; `b:real`; `t:real`]
                  MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas D) (cylinder_flow (&0)) /\
                riemannian_metric (open_set_atlas D)
                  (\y. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[APX_NECK_CYL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                 `cylinder_flow (&0)`;
                 `\y. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y`;
                 `&1 + eps`; `c:real->real^3`; `a:real`; `b:real`]
                MFD_LENGTH_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                   `(c:real->real^3) t`; `v:real^3`] APX_NECK_C0_BOUNDS) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                 `\y. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y`;
                 `cylinder_flow (&0)`;
                 `inv(&1 - eps)`; `c:real->real^3`; `a:real`; `b:real`]
                MFD_LENGTH_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                   `(c:real->real^3) t`; `v:real^3`] APX_NECK_C0_BOUNDS) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 < &1 - eps` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`&1 - eps`,`p:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC APX_LENGTH_ARITH THEN
  EXISTS_TAC `mfd_length (open_set_atlas D)
                (\y. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y)
                (c:real->real^3) a b` THEN
  REWRITE_TAC[GSYM SQRT_INV] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An explicit model path.  Between y and z (both nonzero) the               *)
(* curve t -> exp((1-t) log|y| + t log|z|) (cos(th t) u + sin(th t) q),     *)
(* u = y/|y|, z/|z| = cos th u + sin th q, has constant G0-speed            *)
(* sqrt 2 sqrt(dl^2 + th^2), so G0-length <= |s y - s z| + sqrt 2 pi.        *)
(* ------------------------------------------------------------------------- *)

let apx_mpath = new_definition
 `apx_mpath (l0:real) (dl:real) (th:real) (u:real^3) (q:real^3) (t:real) =
    (exp(l0 + t * dl) * cos(th * t)) % u + (exp(l0 + t * dl) * sin(th * t)) % q`;;

let APX_REAL_VMUL_VD = prove
 (`!f f' t (u:real^N).
        (f has_real_derivative f') (atreal t)
        ==> ((\r. f(drop r) % u) has_vector_derivative (f' % u)) (at (lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative] THEN
  DISCH_THEN(MP_TAC o ISPEC `u:real^N` o MATCH_MP HAS_DERIVATIVE_VMUL_DROP) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; DROP_CMUL; VECTOR_MUL_ASSOC]);;

let APX_C1_FROM_VD = prove
 (`!(q:real^1->real^N) V S.
        (!x. x IN S ==> (q has_vector_derivative V x) (at x)) /\ V continuous_on S
        ==> continuously_differentiable 1 S q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ONE; continuously_differentiable] THEN
  EXISTS_TAC `\x:real^1 h:real^1. drop h % (V:real^1->real^N) x` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN ASM_SIMP_TAC[];
    GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let APX_MPATH_VD = prove
 (`!l0 dl th u q t.
        ((\r. apx_mpath l0 dl th u q (drop r)) has_vector_derivative
         (dl % apx_mpath l0 dl th u q t + th % apx_mpath l0 dl th q (--u) t))
        (at (lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_mpath] THEN
  MP_TAC(ISPECL [`\t. exp(l0 + t * dl) * cos(th * t)`;
                 `exp(l0 + t * dl) * (dl * cos(th * t) - th * sin(th * t))`;
                 `t:real`; `u:real^3`] APX_REAL_VMUL_VD) THEN
  MP_TAC(ISPECL [`\t. exp(l0 + t * dl) * sin(th * t)`;
                 `exp(l0 + t * dl) * (dl * sin(th * t) + th * cos(th * t))`;
                 `t:real`; `q:real^3`] APX_REAL_VMUL_VD) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [REAL_DIFF_TAC THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [REAL_DIFF_TAC THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `dl % ((exp(l0 + t * dl) * cos(th * t)) % u + (exp(l0 + t * dl) * sin(th * t)) % q) +
    th % ((exp(l0 + t * dl) * cos(th * t)) % q +
          (exp(l0 + t * dl) * sin(th * t)) % --u) =
    (exp(l0 + t * dl) * (dl * cos(th * t) - th * sin(th * t))) % (u:real^3) +
    (exp(l0 + t * dl) * (dl * sin(th * t) + th * cos(th * t))) % q`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[]);;

let APX_MPATH_CONT = prove
 (`!l0 dl th u q x.
        (\r. apx_mpath l0 dl th u q (drop r)) continuous (at x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  MP_TAC(SPECL [`l0:real`; `dl:real`; `th:real`; `u:real^3`; `q:real^3`; `drop x`]
               APX_MPATH_VD) THEN
  REWRITE_TAC[LIFT_DROP; has_vector_derivative; differentiable] THEN MESON_TAC[]);;

let APX_MPATH_DOT = prove
 (`!l0 dl th (u:real^3) q t.
        u dot u = &1 /\ q dot q = &1 /\ u dot q = &0
        ==> apx_mpath l0 dl th u q t dot apx_mpath l0 dl th u q t =
            exp(l0 + t * dl) pow 2 /\
            apx_mpath l0 dl th q (--u) t dot apx_mpath l0 dl th q (--u) t =
            exp(l0 + t * dl) pow 2 /\
            apx_mpath l0 dl th u q t dot apx_mpath l0 dl th q (--u) t = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^3) dot u = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[apx_mpath; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LNEG; DOT_RNEG] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `th * t:real` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

(* Unit vectors u, w: w = cos th u + sin th q with q a unit vector         *)
(* orthogonal to u and 0 <= th <= pi.                                        *)

let APX_UNIT_ORTHO = prove
 (`!u r:real^3.
        u dot r = &0 ==> ?q. norm q = &1 /\ u dot q = &0 /\ norm r % q = r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r:real^3 = vec 0` THENL
   [MP_TAC(ISPEC `u:real^3` ORTHOGONAL_TO_VECTOR_EXISTS) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; orthogonal] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv(norm y) % (y:real^3)` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_LZERO; DOT_RMUL; REAL_MUL_RZERO] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
    EXISTS_TAC `inv(norm r) % (r:real^3)` THEN
    ASM_REWRITE_TAC[DOT_RMUL; REAL_MUL_RZERO; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                    VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]]);;

let APX_GREAT_CIRCLE = prove
 (`!u w:real^3.
        norm u = &1 /\ norm w = &1
        ==> ?q th. norm q = &1 /\ u dot q = &0 /\ &0 <= th /\ th <= pi /\
                   w = cos th % u + sin th % q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_EQ_1] THEN STRIP_TAC THEN
  ABBREV_TAC `d = (u:real^3) dot w` THEN
  SUBGOAL_THEN `abs d <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(ISPECL [`u:real^3`; `w:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    ASM_REWRITE_TAC[NORM_EQ_1; REAL_MUL_LID] THEN
    SUBGOAL_THEN `norm(u:real^3) = &1 /\ norm(w:real^3) = &1` (fun th -> REWRITE_TAC[th])
    THENL [ASM_REWRITE_TAC[NORM_EQ_1]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3`; `w - d % u:real^3`] APX_UNIT_ORTHO) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`q:real^3`; `acs d`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `--(&1) <= d /\ d <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ACS_BOUNDS; COS_ACS; SIN_ACS] THEN
  SUBGOAL_THEN `sqrt(&1 - d pow 2) = norm(w - d % u:real^3)` SUBST1_TAC THENL
   [REWRITE_TAC[vector_norm] THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `(w:real^3) dot u = d` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM NORM_EQ_1] THEN VECTOR_ARITH_TAC);;

let APX_AFFINE_BETWEEN = prove
 (`!a b t. &0 <= t /\ t <= &1
           ==> (a <= a + t * (b - a) \/ b <= a + t * (b - a)) /\
               (a + t * (b - a) <= a \/ a + t * (b - a) <= b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `a <= b \/ b <= a`) THENL
   [SUBGOAL_THEN `&0 <= t * (b - a) /\ t * (b - a) <= b - a` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `t * x <= &1 * x ==> t * x <= x`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 <= t * (a - b) /\ t * (a - b) <= a - b` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `t * x <= &1 * x ==> t * x <= x`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The model path as a C^1 curve of an open set containing the               *)
(* shell between |y| and |z|, with G0-length <= |s y - s z| + sqrt 2 pi.     *)
(* ------------------------------------------------------------------------- *)

let APX_MPATH_NORM = prove
 (`!l0 dl th (u:real^3) q t.
        u dot u = &1 /\ q dot q = &1 /\ u dot q = &0
        ==> norm(apx_mpath l0 dl th u q t) = exp(l0 + t * dl)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_norm] THEN
  MP_TAC(SPECL [`l0:real`; `dl:real`; `th:real`; `u:real^3`; `q:real^3`; `t:real`]
               APX_MPATH_DOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE]);;

let APX_MPATH_SPEED = prove
 (`!l0 dl th (u:real^3) q t.
        u dot u = &1 /\ q dot q = &1 /\ u dot q = &0
        ==> (dl % apx_mpath l0 dl th u q t + th % apx_mpath l0 dl th q (--u) t) dot
            (cylinder_flow (&0) (apx_mpath l0 dl th u q t) **
             (dl % apx_mpath l0 dl th u q t + th % apx_mpath l0 dl th q (--u) t)) =
            &2 * (dl pow 2 + th pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l0:real`; `dl:real`; `th:real`; `u:real^3`; `q:real^3`; `t:real`]
               APX_MPATH_DOT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[APX_CYL0_QUAD] THEN
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `l0 + t * dl` REAL_EXP_POS_LT) THEN
  SPEC_TAC(`exp(l0 + t * dl)`,`E:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(E pow 2 = &0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let APX_SQRT_PATH_BOUND = prove
 (`!dl th. &0 <= th /\ th <= pi
           ==> sqrt(&2 * (dl pow 2 + th pow 2)) <= sqrt(&2) * abs dl + sqrt(&2) * pi`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&2) * (abs dl + th)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MP_TAC(SPEC `dl:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MP_TAC(SPEC `dl:real` REAL_POW2_ABS) THEN
      SUBGOAL_THEN `&0 <= abs dl * th` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN ASM_REAL_ARITH_TAC]);;

let APX_MODEL_PATH = prove
 (`!s y z:real^3.
        open s /\ ~(y = vec 0) /\ ~(z = vec 0) /\
        (!v. (norm y <= norm v \/ norm z <= norm v) /\
             (norm v <= norm y \/ norm v <= norm z) ==> v IN s)
        ==> ?c. mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c (&0) (&1) /\
                c(&0) = y /\ c(&1) = z /\
                mfd_length (open_set_atlas s) (cylinder_flow (&0)) c (&0) (&1)
                <= abs(apx_sval y - apx_sval z) + sqrt(&2) * pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ &0 < norm(z:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`inv(norm y) % (y:real^3)`; `inv(norm z) % (z:real^3)`]
                APX_GREAT_CIRCLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `u = inv(norm y) % (y:real^3)` THEN
  SUBGOAL_THEN `(u:real^3) dot u = &1 /\ (q:real^3) dot q = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_1] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `l0 = log(norm(y:real^3))` THEN ABBREV_TAC `l1 = log(norm(z:real^3))` THEN
  SUBGOAL_THEN `exp l0 = norm(y:real^3) /\ exp l1 = norm(z:real^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l0"; "l1"] THEN ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  ABBREV_TAC `P = apx_mpath l0 (l1 - l0) th u q` THEN
  ABBREV_TAC `V = \t. (l1 - l0) % apx_mpath l0 (l1 - l0) th u q t +
                      th % apx_mpath l0 (l1 - l0) th q (--u) t` THEN
  SUBGOAL_THEN `!t. ((\r. (P:real->real^3)(drop r)) has_vector_derivative V t) (at (lift t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "V"] THEN BETA_TAC THEN
    REWRITE_TAC[APX_MPATH_VD];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. norm((P:real->real^3) t) = exp(l0 + t * (l1 - l0))` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "P" THEN MATCH_MP_TAC APX_MPATH_NORM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (P:real->real^3) t IN s` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
      check (fun th -> can (find_term (fun t -> t = `s:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`l0:real`; `l1:real`; `t:real`] APX_AFFINE_BETWEEN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `exp l0 = norm(y:real^3)` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN `exp l1 = norm(z:real^3)` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\r. (V:real->real^3)(drop r)) continuous_on (:real^1) /\
                (\r. (P:real->real^3)(drop r)) continuous_on (:real^1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THENL
     [EXPAND_TAC "V" THEN BETA_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[APX_MPATH_CONT];
      EXPAND_TAC "P" THEN REWRITE_TAC[APX_MPATH_CONT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (P:real->real^3)
                             (&0) (&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_c1_curve; REAL_POS] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `ch:(real^3->bool)#(real^3->real^3)` THEN
      REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN
      MATCH_MP_TAC APX_C1_FROM_VD THEN EXISTS_TAC `\r. (V:real->real^3)(drop r)` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `drop x` o check (is_forall o concl) o
          check (fun th -> can (find_term (fun t -> t = `V:real->real^3`)) (concl th) &&
                           can (find_term is_abs) (concl th))) THEN
        REWRITE_TAC[LIFT_DROP];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]]];
    ALL_TAC] THEN
  EXISTS_TAC `P:real->real^3` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[apx_mpath; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; COS_0; SIN_0;
                REAL_MUL_RID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    EXPAND_TAC "P" THEN
    REWRITE_TAC[apx_mpath; REAL_MUL_LID; REAL_MUL_RID;
                REAL_ARITH `l0 + (l1 - l0) = l1:real`] THEN
    ASM_REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (find_term (fun t -> t = `cos th`)) (concl th))) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MFD_LENGTH_OPEN_SET_ATLAS] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[&0,&1])
      (\t. sqrt(vector_derivative (\r. (P:real->real^3)(drop r))
                  (at (lift t) within interval[lift(&0),lift(&1)]) dot
                (cylinder_flow (&0) (P t) **
                 vector_derivative (\r. P(drop r))
                  (at (lift t) within interval[lift(&0),lift(&1)])))) =
    real_integral (real_interval[&0,&1])
      (\t. sqrt(&2 * ((l1 - l0) pow 2 + th pow 2)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN
     `vector_derivative (\r. (P:real->real^3)(drop r))
        (at (lift t) within interval[lift(&0),lift(&1)]) = V t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
      ASM_SIMP_TAC[LIFT_DROP; REAL_LT_01; GRGD_IN_INTERVAL_LIFT;
                   HAS_VECTOR_DERIVATIVE_AT_WITHIN];
      ALL_TAC] THEN
    AP_TERM_TAC THEN MAP_EVERY EXPAND_TAC ["P"; "V"] THEN BETA_TAC THEN
    MATCH_MP_TAC APX_MPATH_SPEED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  SUBGOAL_THEN `abs(apx_sval y - apx_sval z) = sqrt(&2) * abs(l1 - l0)` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["l0"; "l1"] THEN
    REWRITE_TAC[apx_sval; GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(sqrt(&2)) = sqrt(&2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN SIMP_TAC[SQRT_POS_LE; REAL_POS]; ALL_TAC] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC APX_SQRT_PATH_BOUND THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* N2 (MT Lemma A.4 and Cor A.5).  The s-coordinate on slabs,                *)
(* compact sub-slabs, lifts of curves that stay in the neck, the exit bound  *)
(* (first exit time), the two distance bounds and APX_NECK_DIST.             *)
(* ------------------------------------------------------------------------- *)

let APX_EXP_LT_NORM = prove
 (`!p y:real^3.
        ~(y = vec 0)
        ==> (exp p < norm y <=> p < log(norm y)) /\
            (norm y < exp p <=> log(norm y) < p) /\
            (exp p <= norm y <=> p <= log(norm y)) /\
            (norm y <= exp p <=> log(norm y) <= p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM LOG_MONO_LT; GSYM LOG_MONO_LE; REAL_EXP_POS_LT; LOG_EXP]);;

let APX_SLAB_SVAL = prove
 (`!a b y:real^3.
        y IN apx_slab a b <=> ~(y = vec 0) /\ a < apx_sval y /\ apx_sval y < b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THENL
   [MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_EXP_LT_NORM; apx_sval] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let APX_SVAL_NECK_DOM = prove
 (`!eps y. y IN rfs_neck_dom eps ==> ~(y = vec 0) /\ abs(apx_sval y) < inv eps`,
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_SUBSLAB = prove
 (`!eps m.
        m < inv eps
        ==> compact(cball(vec 0:real^3,exp(m / sqrt(&2))) DIFF
                    ball(vec 0,exp(--m / sqrt(&2)))) /\
            cball(vec 0:real^3,exp(m / sqrt(&2))) DIFF ball(vec 0,exp(--m / sqrt(&2)))
            SUBSET rfs_neck_dom eps /\
            (!v:real^3. ~(v = vec 0) /\ abs(apx_sval v) <= m
                        ==> v IN cball(vec 0,exp(m / sqrt(&2))) DIFF
                                 ball(vec 0,exp(--m / sqrt(&2))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT;
                APX_SLAB_NECK_DOM; apx_slab; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < exp(--m / sqrt(&2)) /\
                  exp(m / sqrt(&2)) < exp(inv eps / sqrt(&2))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    ASM_SIMP_TAC[APX_EXP_LT_NORM] THEN UNDISCH_TAC `abs(apx_sval v) <= m` THEN
    REWRITE_TAC[apx_sval] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    REAL_ARITH_TAC]);;

let APX_LENGTH_PREFIX_LE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a c /\ a <= b /\ b <= c
        ==> mfd_length atlas g gamma a b <= mfd_length atlas g gamma a c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `c:real`]
                MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* A curve from e y that stays in the neck ends at some e v, and its length  *)
(* is at least sqrt(1 - eps) h |s v - s y|.                                  *)

let APX_NECK_LIFT_SVAL = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y gamma b.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
        y IN rfs_neck_dom eps /\
        mfd_c1_curve (top,atlas) gamma (&0) b /\ gamma(&0) = e y /\
        (!t. &0 <= t /\ t <= b ==> gamma t IN IMAGE e (rfs_neck_dom eps))
        ==> ?v. v IN rfs_neck_dom eps /\ gamma b = e v /\
                sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) *
                abs(apx_sval v - apx_sval y) <= mfd_length atlas g gamma (&0) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `gamma:real->A`; `&0`; `b:real`]
                MFD_PARAM_C1_CURVE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(c:real->real^3)(&0) IN rfs_neck_dom eps /\ (gamma:real->A)(&0) = e(c(&0)) /\
    c b IN rfs_neck_dom eps /\ gamma b = e(c b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->real^3)(&0) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(c:real->real^3) b` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                 `c:real->real^3`; `&0`; `b:real`] APX_NECK_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `c:real->real^3`; `&0`; `b:real`]
                APX_SVAL_LENGTH_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:A->real^3^3) gamma (&0) b =
    mfd_length atlas g ((e:real^3->A) o c) (&0) b`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                         (c:real->real^3) (&0) b` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let APX_EXIT_ARITH = prove
 (`(!p h L i a. &0 < p /\ &0 < h /\ L < p * h * (i - a) ==> a + L / (p * h) < i) /\
   (!p h L Ls d. &0 < p /\ &0 < h /\ p * h * d <= Ls /\ Ls <= L ==> d <= L / (p * h))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < p * h` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC]) THENL
   [MATCH_MP_TAC(REAL_ARITH `L / k < i - a ==> a + L / k < i`) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* The exit bound on [0,1] (first exit time; a compact sub-slab is closed in *)
(* the Hausdorff space and the curve stays in its image before the exit).    *)

let APX_NECK_EXIT01 = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y gamma.
        hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ eps < &1 /\ y IN rfs_neck_dom eps /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = e y /\
        ~(gamma(&1) IN IMAGE e (rfs_neck_dom eps))
        ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) *
            (inv eps - abs(apx_sval y))
            <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt(&1 - eps) /\ &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas (g:A->real^3^3) gamma (&0) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `m = abs(apx_sval y) +
                  mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) /
                  (sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)))` THEN
  SUBGOAL_THEN `m < inv eps` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC(CONJUNCT1 APX_EXIT_ARITH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `m:real`] APX_SUBSLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = cball(vec 0:real^3,exp(m / sqrt(&2))) DIFF
                  ball(vec 0,exp(--m / sqrt(&2)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e:real^3->A) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (K:real^3->bool)` THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `IMAGE (e:real^3->A) (rfs_neck_dom eps)`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < t1 ==> (gamma:real->A) s IN IMAGE (e:real^3->A) K`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                   `gamma:real->A`; `s:real`] APX_NECK_LIFT_SVAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `!v:real^3. ~(v = vec 0) /\ abs(apx_sval v) <= m ==> v IN K` THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `gamma:real->A`; `&0`; `s:real`; `&1`]
                  APX_LENGTH_PREFIX_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`sqrt(&1 - eps)`; `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))`;
                   `mfd_length atlas (g:A->real^3^3) gamma (&0) (&1)`;
                   `mfd_length atlas (g:A->real^3^3) gamma (&0) s`;
                   `abs(apx_sval v - apx_sval y)`] (CONJUNCT2 APX_EXIT_ARITH)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
                    ALL_TAC] THEN
    EXPAND_TAC "m" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `IMAGE (e:real^3->A) K`; `t1:real`]
                GRGD_CLOSED_LEFT_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_c1_curve]; DISCH_TAC] THEN
  UNDISCH_TAC `~((gamma:real->A) t1 IN IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
  REWRITE_TAC[] THEN UNDISCH_TAC `(gamma:real->A) t1 IN IMAGE (e:real^3->A) K` THEN
  UNDISCH_TAC `(K:real^3->bool) SUBSET rfs_neck_dom eps` THEN SET_TAC[]);;

let APX_NECK_EXIT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y gamma a b.
        hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ eps < &1 /\ y IN rfs_neck_dom eps /\
        mfd_c1_curve (top,atlas) gamma a b /\ gamma a = e y /\
        ~(gamma b IN IMAGE e (rfs_neck_dom eps))
        ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) *
            (inv eps - abs(apx_sval y))
            <= mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `a:real`; `b:real`]
                GRGD_AFFINE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`] GRGD_AFFINE_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC APX_NECK_EXIT01 THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `e:real^3->A`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The distance bounds in a neck and N2 (APX_NECK_DIST).                     *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_DIST_UPPER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y z.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
        y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps
        ==> mfd_joinable (top,atlas) (e y) (e z) /\
            mfd_dist (top,atlas) g (e y) (e z) <=
            sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) *
            (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `y:real^3`; `z:real^3`] APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[APX_NECK_DOM_OPEN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
    UNDISCH_TAC `(z:real^3) IN rfs_neck_dom eps` THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                 `c:real->real^3`; `&0`; `&1`] APX_NECK_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) y = (e o c) (&0) /\ e z = (e o c) (&1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g:A->real^3^3) ((e:real^3->A) o c) (&0) (&1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                         (c:real->real^3) (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let APX_NECK_DIST_LOWER = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y z.
        hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
        y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps
        ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x)) *
            min (abs(apx_sval y - apx_sval z))
                (&2 * inv eps - abs(apx_sval y) - abs(apx_sval z))
            <= mfd_dist (top,atlas) g (e y) (e z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 - eps) /\ &0 <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                  `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                  `y:real^3`; `z:real^3`] APX_NECK_DIST_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[mfd_joinable; GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GRGD_IN_LENGTHS] THEN X_GEN_TAC `l:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `!t. t IN real_interval[&0,&1]
        ==> (gamma:real->A) t IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                   `gamma:real->A`; `&1`] APX_NECK_LIFT_SVAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `v:real^3 = z` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                abs(apx_sval z - apx_sval y)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `t IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&0`; `t:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                 `gamma:real->A`; `&0`; `t:real`] APX_NECK_EXIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `t:real`; `&1`]
                MFD_LENGTH_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `z:real^3`;
                 `\u. (gamma:real->A)(t + &1 - u)`; `t:real`; `&1`] APX_NECK_EXIT) THEN
  ASM_REWRITE_TAC[REAL_ARITH `t + &1 - t = &1 /\ t + &1 - &1 = t`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              (&2 * inv eps - abs(apx_sval y) - abs(apx_sval z))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* N2: the statement form.  eps1 = min alpha (1/2) gives                     *)
(* sqrt(1 + eps) <= 1 + alpha and 1 - alpha <= sqrt(1 - eps).                *)

let APX_NECK_DIST_FACTORS = prove
 (`!alpha eps. &0 < alpha /\ &0 < eps /\ eps <= min alpha (&1 / &2)
               ==> sqrt(&1 + eps) <= &1 + alpha /\ &1 - alpha <= sqrt(&1 - eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `alpha:real` REAL_LE_SQUARE) THEN REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ASM_CASES_TAC `&1 <= alpha` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RSQRT THEN
      SUBGOAL_THEN `alpha * alpha <= alpha * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC]]);;

let APX_NECK_DIST = prove
 (`!w:A->bool. APX_NECK_DIST_STATEMENT w`,
  REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min alpha (&1 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`alpha:real`; `eps:real`] APX_NECK_DIST_FACTORS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval y) < inv eps /\ abs(apx_sval z) < inv eps`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                 `y:real^3`; `z:real^3`] APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                 `y:real^3`; `z:real^3`] APX_NECK_DIST_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                min (abs(apx_sval y - apx_sval z))
                    (&2 * inv eps - abs(apx_sval y) - abs(apx_sval z))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                (inv eps - abs(apx_sval y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                     `gamma:real->A`; `a:real`; `b:real`] APX_NECK_EXIT) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* N1 (MT Lemma A.2 in model coordinates) from the curvature                 *)
(* stability LCK_CURVATURE_STABILITY of pc_lrg_stab.  The curvature norm of  *)
(* the cylinder metric G0 is bounded (it is dilation invariant, continuous,  *)
(* and the unit sphere is compact); a neck with eps <= 1/2 has              *)
(* rfs_kreg eps >= 2, so its C^2 distance to G0 is below eps.                *)
(* ------------------------------------------------------------------------- *)

let APX_CYL0_DILATION = prove
 (`!c y:real^3.
        &0 < c /\ ~(y = vec 0)
        ==> mpullback (\x:real^3. c % x) (cylinder_flow (&0)) y = cylinder_flow (&0) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^3. c % x) (at y) = (\x. (c %% mat 1) ** x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; LRG_CYL0_EQ; TRANSP_MATRIX_CMUL; TRANSP_MAT;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID; MATRIX_MUL_RID;
              MATRIX_CMUL_ASSOC; NORM_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `abs c = c /\ ~(norm(y:real^3) = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(norm(y:real^3) = &0)` THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

let APX_CYL0_RM_CONST = prove
 (`!y:real^3.
        ~(y = vec 0)
        ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y =
            lrm_deriv_norm2 0 (cylinder_flow (&0)) (inv(norm y) % y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `c = inv(norm(y:real^3))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:3`,`:N`]
   (ISPECL [`c:real`; `norm(y:real^3) / &2`; `&2 * norm(y:real^3)`]
           SMT_DIFFEO_SCALING_ANNULUS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN annulus (norm y / &2) (&2 * norm y)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN annulus (norm(y:real^3) / &2) (&2 * norm y) ==> ~(z = vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (annulus (c * norm(y:real^3) / &2) (c * &2 * norm y))
                 (cylinder_flow (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; OPEN_ANNULUS] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `c * norm(y:real^3) / &2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `annulus (c * norm(y:real^3) / &2) (c * &2 * norm y):real^3->bool`;
                 `annulus (norm(y:real^3) / &2) (&2 * norm y):real^3->bool`; `\x:real^3. c % x`;
                 `\x:real^3. inv c % x`; `cylinder_flow (&0)`; `y:real^3`]
                LRM_DERIV_NORM2_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c * norm(y:real^3) / &2 = c * (norm y / &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `annulus (norm(y:real^3) / &2) (&2 * norm y):real^3->bool` THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_CYL0_DILATION THEN ASM_SIMP_TAC[]);;

let APX_CYL0_RM_BOUND = prove
 (`?K0. !y:real^3. ~(y = vec 0)
                   ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2`,
  MP_TAC(ISPECL [`0`; `(:real^3) DELETE vec 0`; `cylinder_flow (&0)`]
                LRM_DERIV_NORM2_CONTINUOUS) THEN
  SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. lift(lrm_deriv_norm2 0 (cylinder_flow (&0)) y)`;
                 `sphere(vec 0:real^3,&1)`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_DELETE; IN_UNIV] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sqrt B` THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP APX_CYL0_RM_CONST) THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> x <= b`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0]);;

let APX_KREG_TWO = prove
 (`!eps. &0 < eps /\ eps <= &1 / &2 ==> 2 <= rfs_kreg eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[RFS_KREG; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]);;

let APX_NECK_CURV = prove
 (`!w:A->bool. APX_NECK_CURV_STATEMENT w`,
  REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  MP_TAC(INST_TYPE [`:3`,`:N`]
   (ISPECL [`K0:real`; `alpha:real`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))) THEN
  EXISTS_TAC `min eta (&1 / &2)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 2 (cylinder_flow (&0))
      (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z) y
    < eta pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
        (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z)
        y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN MATCH_MP_TAC APX_KREG_TWO THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "stab" (MP_TAC o ISPECL
   [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
    `\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z`;
    `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[APX_NECK_CYL_FIELD]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_CYL_SCALAR; REAL_ARITH `&0 < &1`; REAL_SUB_RZERO; REAL_DIV_1]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for N8.  A Lipschitz form of the scalar part of the               *)
(* curvature stability (assembled from the perturbation lemmas of            *)
(* pc_lrg_stab exactly as in the proof of LCK_CURVATURE_STABILITY, keeping   *)
(* the linear dependence on the C^2 distance), and an elementary bound       *)
(* (1 + x)^n <= 2 for n x <= 1/2.                                            *)
(* ------------------------------------------------------------------------- *)

let APX_SCALAR_STABILITY_LIP = prove
 (`!K0 s (G0:real^N->real^N^N) G y.
      metric_field s G0 /\ metric_field s G /\ y IN s /\
      lrm_deriv_norm2 0 G0 y <= K0 pow 2 /\
      sqrt(lck_dist2 2 G0 G y) <= &1 / &10
      ==> abs(lscalar G y - lscalar G0 y) <=
          &8 * &(dimindex(:N)) pow 2 * (&1 + abs K0) * sqrt(lck_dist2 2 G0 G y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `delta = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= lck_dist2 2 (G0:real^N->real^N^N) G y` ASSUME_TAC THENL
   [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
         LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 2 (G0:real^N->real^N^N)
                    (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. abs(a dot ((G:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
          delta * norm((M:real^N^N) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`2`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[PRODUCT_2; lmetric2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 2 (G0:real^N->real^N^N)
              (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 2 (G0:real^N->real^N^N)
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 3 (G0:real^N->real^N^N)
              (lnabla 2 G0
                (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u)) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u))`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lrm4 (G0:real^N->real^N^N) y u) <=
        abs K0 * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lrm4 (G0:real^N->real^N^N)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `K0 pow 2`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4; POW_2_SQRT_ABS] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G0:real^N->real^N^N) y <= K0 pow 2` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta <= &1 / &10` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `abs(K0:real)`] LRG_RICCI0_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`; `abs(K0:real)`]
         LRG_PERT_SCALAR) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `&0 <= delta * (&1 + abs K0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  MP_TAC(SPECL [`&(dimindex(:N)) * &(dimindex(:N))`; `delta * (&1 + abs K0)`]
               REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let APX_POW_BOUND = prove
 (`!x n. &0 <= x /\ &n * x <= &1 / &2 ==> (&1 + x) pow n <= &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(x) pow n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_N] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(&1 / &2)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_MONO_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `&1 / &2` REAL_EXP_BOUND_LEMMA) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* N8 (strong necks are K delta-necks at slightly earlier                    *)
(* times, K universal).  At time s = t + sg/R the rescaled pullback H is     *)
(* delta-close to cylinder_flow sg; for |sg| small the base change           *)
(* LCK_DIST_CYLINDER_BASE costs a factor 2, the scalar curvature ratio lam   *)
(* = R(y,s)/R(y,t) = lscalar H y0 is 1 + O(delta) by the Lipschitz          *)
(* stability, and LCK_DIST_RESCALE moves from H to lam H.                     *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_CYL_FIELD_GEN = prove
 (`!eps s. s < &1 ==> metric_field (rfs_neck_dom eps) (cylinder_flow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; APX_NECK_DOM_NONZERO; APX_NECK_DOM_OPEN]);;

let APX_LCK_DIST2_POS = prove
 (`!k s (G0:real^N->real^N^N) G y.
        metric_field s G0 /\ metric_field s G /\ y IN s ==> &0 <= lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* The model estimate at one point: base change from cylinder_flow sg to   *)
(* cylinder_flow 0, then rescaling by lam.                                  *)

let APX_NECK_EARLIER_POINT = prove
 (`!dl sg d0 lam (H:real^3->real^3^3) z k.
        &0 < dl /\ dl <= &1 / &2 /\ abs sg <= dl / &2 /\
        &(rfs_kreg dl + 2) * abs sg <= &1 / &2 /\ d0 < dl pow 2 /\
        metric_field (rfs_neck_dom dl) H /\ z IN rfs_neck_dom dl /\
        lck_dist2 (rfs_kreg dl) (cylinder_flow sg) H z <= d0 /\ &0 < lam /\
        k <= rfs_kreg dl
        ==> sqrt(lck_dist2 k (cylinder_flow (&0)) (\w. lam %% H w) z) <=
            lam * &2 * (sqrt d0 + dl) + abs(lam - &1) * &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs sg <= &1 / &2 /\ sg < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (cylinder_flow sg) /\
                metric_field (rfs_neck_dom dl) (cylinder_flow (&0)) /\
                metric_field (rfs_neck_dom dl) (\w. lam %% (H:real^3->real^3^3) w)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_NECK_CYL_FIELD_GEN; REAL_ARITH `&0 < &1`] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow sg) (H:real^3->real^3^3) z` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `rfs_neck_dom dl` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                     (\w. lam %% (H:real^3->real^3^3) w) z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
    EXISTS_TAC `rfs_neck_dom dl` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg dl`; `rfs_neck_dom dl`; `cylinder_flow (&0)`;
                 `H:real^3->real^3^3`; `lam:real`; `z:real^3`] LCK_DIST_RESCALE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL [`rfs_kreg dl`; `sg:real`; `rfs_neck_dom dl`;
                   `H:real^3->real^3^3`; `z:real^3`] LCK_DIST_CYLINDER_BASE) THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_POW_BOUND THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
        EXISTS_TAC `rfs_neck_dom dl` THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ &2 * c <= dl ==> a + &2 * c <= b + dl`) THEN
      ASM_REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* The scalar curvature ratio at the centre: |lscalar H y0 - 1| = O(dl).    *)

let APX_NECK_EARLIER_SCALAR = prove
 (`!K0 dl sg d0 (H:real^3->real^3^3) y0.
        (!y:real^3. ~(y = vec 0)
                    ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2) /\
        &0 < dl /\ &40 * dl <= &1 /\ abs sg <= dl / &2 /\ &4 * abs sg <= &1 / &2 /\
        d0 < dl pow 2 /\ metric_field (rfs_neck_dom dl) H /\ y0 IN rfs_neck_dom dl /\
        lck_dist2 (rfs_kreg dl) (cylinder_flow sg) H y0 <= d0
        ==> abs(lscalar H y0 - &1) <= (&288 * (&1 + abs K0)) * dl`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs sg <= &1 / &2 /\ sg < &1 /\ dl <= &1 / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (cylinder_flow sg) /\
                metric_field (rfs_neck_dom dl) (cylinder_flow (&0))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_NECK_CYL_FIELD_GEN; REAL_ARITH `&0 < &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (cylinder_flow (&0)) (H:real^3->real^3^3) y0) <= &4 * dl`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `sg:real`; `rfs_neck_dom dl`;
                   `H:real^3->real^3^3`; `y0:real^3`] LCK_DIST_CYLINDER_BASE) THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (dl + dl)` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC APX_POW_BOUND THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
        EXISTS_TAC `rfs_neck_dom dl` THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ &2 * c <= dl ==> a + &2 * c <= b + dl`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(lck_dist2 (rfs_kreg dl) (cylinder_flow sg)
                         (H:real^3->real^3^3) y0)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
        EXISTS_TAC `rfs_neck_dom dl` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC APX_KREG_TWO THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(dl pow 2)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `rfs_neck_dom dl`; `cylinder_flow (&0)`;
                 `H:real^3->real^3^3`; `y0:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_CYL_SCALAR; REAL_ARITH `&0 < &1`; DIMINDEX_3] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MP_TAC(SPECL [`&72 * (&1 + abs K0)`;
                `sqrt(lck_dist2 2 (cylinder_flow (&0)) (H:real^3->real^3^3) y0)`;
                `&4 * dl`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let APX_EARLIER_ARITH = prove
 (`!lam sd dl c1 K.
        &0 < dl /\ &0 <= sd /\ sd < dl /\ abs(lam - &1) <= c1 * dl /\
        c1 * dl <= &1 / &4 /\ &28 + &2 * c1 = K
        ==> &0 <= lam * &2 * (sd + dl) + abs(lam - &1) * &2 /\
            lam * &2 * (sd + dl) + abs(lam - &1) * &2 < K * dl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 / &4 <= lam /\ lam <= &5 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lam * &2 * (sd + dl) <= &5 / &4 * &2 * (sd + dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lam * &2 * (sd + dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&28 + &2 * c1 = K` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_STRONG_NECK_EARLIER_GEN = prove
 (`!K0. (!y:real^3. ~(y = vec 0)
                    ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2)
        ==> !TM AT G dl y t (e:real^3->A) top atlas t0.
              &0 < dl /\ (&28 + &576 * (&1 + abs K0)) * dl <= &1 / &2 /\ t0 < t /\
              rfs_strong_neck (TM,AT,G) dl y t e /\
              (!s. t0 < s /\ s < t
                   ==> TM s = top /\ AT s = atlas /\ riemannian_metric atlas (G s) /\
                       mfd_param top atlas (rfs_neck_dom dl) e)
              ==> ?d. &0 < d /\
                      !s. t - d < s /\ s < t
                          ==> rfs_neck (top,atlas) (G s)
                                ((&28 + &576 * (&1 + abs K0)) * dl) y e`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `K = &28 + &576 * (&1 + abs K0)` THEN
  ABBREV_TAC `c1 = &288 * (&1 + abs K0)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&28 + &2 * c1 = K /\ &0 < c1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "c1"] THEN MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1 * dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&40 * dl <= &1 /\ dl <= &1 / &2 /\ dl <= K * dl /\ c1 * dl <= &1 / &4 /\
                &0 < K * dl`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `K * dl = &28 * dl + &2 * (c1 * dl)` MP_TAC THENL
     [UNDISCH_TAC `&28 + &2 * c1 = K` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ASSUME `rfs_strong_neck (TM,AT,G) dl (y:A) t (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_strong_neck; rfs_evolving_neck; rfs_persists; rfs_close_fam] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC MP_TAC) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                            ((G:real->A->real^3^3) t) (y:A)` THEN
  UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL; apx_sval] THEN
    ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO; GSYM NORM_EQ_0] THEN
    SUBGOAL_THEN `&0 < inv dl` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sg1 = min (dl / &2) (inv(&2 * &(rfs_kreg dl + 2)))` THEN
  SUBGOAL_THEN `&0 < sg1` ASSUME_TAC THENL
   [EXPAND_TAC "sg1" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg1 <= dl / &2 /\ sg1 <= inv(&2 * &(rfs_kreg dl + 2))` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "sg1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (t - t0) (sg1 / R)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ABBREV_TAC `sg = (s - t) * R` THEN
  SUBGOAL_THEN `t + sg / R = s` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `t0 < s /\ (t - s) * R < sg1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t - min (t - t0) (sg1 / R) < s` THEN
    ASM_SIMP_TAC[REAL_ARITH `t - min a b < s <=> t - a < s /\ t - s < b`;
                 REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (t - s) * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs sg < sg1 /\ sg <= &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs sg <= dl / &2 /\ &(rfs_kreg dl + 2) * abs sg <= &1 / &2 /\
    &4 * abs sg <= &1 / &2 /\ --(&1) < sg /\ t - &1 / R < s`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `abs sg <= dl / &2 /\ abs sg <= inv(&2 * &(rfs_kreg dl + 2))`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(rfs_kreg dl + 2) * abs sg <= &1 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(rfs_kreg dl + 2) * inv(&2 * &(rfs_kreg dl + 2))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        SUBGOAL_THEN `~(&(rfs_kreg dl + 2) = &0)` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ARITH_TAC; CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    SUBGOAL_THEN `2 <= rfs_kreg dl` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_KREG_TWO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * abs sg <= &(rfs_kreg dl + 2) * abs sg` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t - s < &1 / R` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
    can (find_term (fun t -> t = `top:A topology`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H = \z. R %% rfs_pullback atlas (e:real^3->A) ((G:real->A->real^3^3) s) z` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (H:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN rfs_neck_dom dl
        ==> lck_dist2 (rfs_kreg dl) (cylinder_flow sg) (H:real^3->real^3^3) z <= d`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`sg:real`; `z:real^3`] o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "H" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `lam = lscalar (H:real^3->real^3^3) y0` THEN
  MP_TAC(ISPECL [`K0:real`; `dl:real`; `sg:real`; `d:real`; `H:real^3->real^3^3`;
                 `y0:real^3`] APX_NECK_EARLIER_SCALAR) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas ((G:real->A->real^3^3) s) ((e:real^3->A) y0) = R * lam`
  ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN EXPAND_TAC "H" THEN
    MP_TAC(ISPECL [`rfs_neck_dom dl`; `rfs_pullback atlas (e:real^3->A)
                                          ((G:real->A->real^3^3) s)`;
                   `R:real`; `y0:real^3`] LSCALAR_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(G:real->A->real^3^3) s`; `rfs_neck_dom dl`; `e:real^3->A`;
                   `y0:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN MATCH_MP_TAC APX_NECK_DOM_MONO THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (R * lam) %% rfs_pullback atlas (e:real^3->A) ((G:real->A->real^3^3) s) z) =
    (\z. lam %% (H:real^3->real^3^3) z)`
  SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow sg) (H:real^3->real^3^3) y0` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_SIMP_TAC[APX_NECK_CYL_FIELD_GEN; REAL_ARITH `sg <= &0 ==> sg < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d < dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(dl pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LT_EQ; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `sqrt d`; `dl:real`; `c1:real`; `K:real`]
                APX_EARLIER_ARITH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; STRIP_TAC] THEN
  EXISTS_TAC `(lam * &2 * (sqrt d + dl) + abs(lam - &1) * &2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `K * dl`] APX_NECK_DOM_MONO) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dl:real`; `sg:real`; `d:real`; `lam:real`; `H:real^3->real^3^3`;
                 `z:real^3`; `rfs_kreg(K * dl)`] APX_NECK_EARLIER_POINT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 (rfs_kreg(K * dl)) (cylinder_flow (&0))
                     (\w. lam %% (H:real^3->real^3^3) w) z) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
    MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_SIMP_TAC[APX_NECK_CYL_FIELD_GEN; REAL_ARITH `&0 < &1`] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_SIMP_TAC[APX_NECK_CYL_FIELD_GEN; REAL_ARITH `&0 < &1`] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]]);;

let APX_STRONG_NECK_EARLIER = prove
 (`!w:A->bool. APX_STRONG_NECK_EARLIER_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[APX_STRONG_NECK_EARLIER_STATEMENT] THEN
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  EXISTS_TAC `&28 + &576 * (&1 + abs K0)` THEN CONJ_TAC THENL
   [MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC APX_STRONG_NECK_EARLIER_GEN THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Algebra of sectional curvature for N7: scaling.  The                      *)
(* positivity of the denominator (APX_SECT_DEN_POS) and the curvature tensor *)
(* of a metric with constant sectional curvature (APX_CONST_CURV_RIEMANN)    *)
(* live in pc_lrg_constcurv.ml (loaded first), so that the geodesics units   *)
(* can use them without the Appendix closure.                                *)
(* ------------------------------------------------------------------------- *)

let APX_LSECTIONAL_SCALE = prove
 (`!U (G:real^N->real^N^N) c y u v.
        metric_field U G /\ y IN U /\ &0 < c
        ==> lsectional (\z. c %% G z) y u v = lsectional G y u v / c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `c:real`; `y:real^N`;
                 `u:real^N`; `v:real^N`; `v:real^N`] LRIEMANN_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  SPEC_TAC(`u dot ((G:real^N->real^N^N) y ** lriemann G y u v v)`,`a:real`) THEN
  SPEC_TAC(`u dot ((G:real^N->real^N^N) y ** u)`,`p:real`) THEN
  SPEC_TAC(`v dot ((G:real^N->real^N^N) y ** v)`,`q:real`) THEN
  SPEC_TAC(`u dot ((G:real^N->real^N^N) y ** v)`,`r:real`) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(c * p) * (c * q) - (c * r) pow 2 = c pow 2 * (p * q - r pow 2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  SPEC_TAC(`inv(p * q - r pow 2)`,`d:real`) THEN GEN_TAC THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* N7 (needed in the proof of MT Prop 15.3).  At the centre of a delta-neck  *)
(* there is a plane with sectional curvature about 0 and one with about R/2  *)
(* (from N1 and the cylinder model).  A C-component has all sectional        *)
(* curvatures above R(x)/C (sup R over the compact component is at least     *)
(* R(x), by MFD_SCALAR_CONTINUOUS); an eps-round component has q-rescaled    *)
(* sectional curvatures within 24 eps of 1 (Lipschitz sectional stability    *)
(* against the constant curvature metric, APX_CONST_CURV_RIEMANN).           *)
(* ------------------------------------------------------------------------- *)

let APX_ORTHO_FRAME3 = prove
 (`!y0:real^3. norm y0 = &1
        ==> ?w1 w2. norm w1 = &1 /\ norm w2 = &1 /\ y0 dot w1 = &0 /\
                    y0 dot w2 = &0 /\ w1 dot w2 = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y0:real^3`; `vec 0:real^3`] APX_UNIT_ORTHO) THEN
  REWRITE_TAC[DOT_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `{y0:real^3,w1}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD {y0:real^3,w1}` THEN
    SIMP_TAC[DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `2` THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; DIMINDEX_3] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; orthogonal] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`w1:real^3`; `inv(norm z) % (z:real^3)`] THEN
  ASM_REWRITE_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0]);;

let APX_ORTHO_NOT_COLLINEAR = prove
 (`!u v:real^N. norm u = &1 /\ norm v = &1 /\ u dot v = &0
                ==> ~collinear {vec 0,u,v}`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `collinear {vec 0:real^N,u,v}` THEN
  REWRITE_TAC[COLLINEAR_LEMMA_ALT] THEN STRIP_TAC THENL
   [UNDISCH_TAC `norm(u:real^N) = &1` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `(u:real^N) dot v = &0` THEN
    ASM_REWRITE_TAC[DOT_RMUL; GSYM NORM_POW_2] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(v:real^N) = &1` THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `c = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `c * &1 pow 2 = &0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

(* The two planes at the centre of a neck (N1 and the cylinder model). *)

let APX_NECK_PLANES = prove
 (`!alpha. &0 < alpha
     ==> ?eps1. &0 < eps1 /\
           !top atlas (g:A->real^3^3) eps x e.
              &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
              rfs_neck (top,atlas) g eps x (e:real^3->A)
              ==> ?u1 v1 u2 v2.
                    ~collinear {vec 0,u1,v1} /\ ~collinear {vec 0,u2,v2} /\
                    abs(mfd_sectional atlas g x u1 v1) <= alpha * mfd_scalar atlas g x /\
                    abs(mfd_sectional atlas g x u2 v2 - mfd_scalar atlas g x / &2)
                    <= alpha * mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(\x:A. T)` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `alpha:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL; apx_sval] THEN
    ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO; GSYM NORM_EQ_0] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) (e(y0:real^3))` THEN
  MP_TAC(SPEC `y0:real^3` APX_ORTHO_FRAME3) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `e(y0:real^3):A`; `e:real^3->A`]
               APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the derivative D of the chart representation of e at y0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y0:real^3`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
    (X_CHOOSE_THEN `h':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`N':real^3->bool`; `N:real^3->bool`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y0)) o e`;
                 `h':real^3->real^3`;
                 `y0:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative
                    (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y0)) o e)
                    (at y0)` THEN
  SUBGOAL_THEN
   `!p q:real^3. ~collinear {vec 0,p,q} ==> ~collinear {vec 0,(D:real^3->real^3) p,D q}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0,(D:real^3->real^3) p,D q} = IMAGE D {vec 0,p,q}` SUBST1_TAC THENL
     [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (D:real^3->real^3)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D:real^3->real^3`; `{vec 0:real^3,p,q}`]
                  COLLINEAR_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. mfd_sectional atlas (g:A->real^3^3) (e(y0:real^3)) (D p) (D q) =
          R * lsectional (\z. R %% rfs_pullback atlas (e:real^3->A) g z) y0 p q`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                   `R:real`; `y0:real^3`; `p:real^3`; `q:real^3`] APX_LSECTIONAL_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y0:real^3`;
                   `p:real^3`; `q:real^3`] APX_PULLBACK_SECTIONAL_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vec 0,y0:real^3,w1} /\ ~collinear {vec 0,w1:real^3,w2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_ORTHO_NOT_COLLINEAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(D:real^3->real^3) y0`; `(D:real^3->real^3) w1`;
                        `(D:real^3->real^3) w1`; `(D:real^3->real^3) w2`] THEN
  ASM_SIMP_TAC[] THEN
  USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `e(y0:real^3):A`; `e:real^3->A`; `y0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `mfd_scalar atlas (g:A->real^3^3) (e(y0:real^3)) = R`] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`y0:real^3`; `w1:real^3`] th) THEN
                       MP_TAC(SPECL [`w1:real^3`; `w2:real^3`] th)) THEN
  ASM_SIMP_TAC[LSECTIONAL_CYLINDER] THEN
  SUBGOAL_THEN `(y0:real^3) dot y0 = &1 /\ (w1:real^3) dot w1 = &1 /\ (w2:real^3) dot w2 = &1`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM NORM_EQ_1]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&0 < R` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`lsectional (\z. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) z)
              y0 y0 w1`,`a1:real`) THEN
  SPEC_TAC(`lsectional (\z. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) z)
              y0 w1 w2`,`a2:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `R * a2 - R / &2 = R * (a2 - &1 / &2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC]);;
let APX_SECTIONAL_STABILITY_LIP = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) K.
      metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
      &0 <= K /\
      (!u v w. norm(M ** lriemann G0 y u v w) <=
               K * norm(M ** u) * norm(M ** v) * norm(M ** w)) /\
      sqrt(lck_dist2 2 G0 G y) <= &1 / &10
      ==> !u v. abs(lsectional G y u v - lsectional G0 y u v) <=
                &8 * (&1 + K) * sqrt(lck_dist2 2 G0 G y)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(G0:real^N->real^N^N) y = transp (M:real^N^N) ** M` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `delta = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= lck_dist2 2 (G0:real^N->real^N^N) G y` ASSUME_TAC THENL
   [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 2 (G0:real^N->real^N^N)
                    (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. abs(a dot ((G:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
          delta * norm((M:real^N^N) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`2`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[PRODUCT_2; lmetric2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 2 (G0:real^N->real^N^N)
              (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 2 (G0:real^N->real^N^N)
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 3 (G0:real^N->real^N^N)
              (lnabla 2 G0
                (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u)) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u))`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta <= &1 / &10` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`; `K:real`; `u:real^N`;
                 `v:real^N`] LRG_PERT_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* N7.  Round components (rescaled sectional curvatures near                 *)
(* 1), C-components (sectional curvatures above R(x)/C), and the exclusion. *)
(* ------------------------------------------------------------------------- *)

let APX_CONST1_FRAME_BOUND = prove
 (`!(G:real^N->real^N^N) y (M:real^N^N).
        G y = transp M ** M /\
        (!u v w. lriemann G y u v w =
                 &1 % ((v dot (G y ** w)) % u - (u dot (G y ** w)) % v))
        ==> !u v w. norm(M ** lriemann G y u v w) <=
                    &2 * norm(M ** u) * norm(M ** v) * norm(M ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_MUL_LID; MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  SUBGOAL_THEN `!a b. a dot ((transp M ** M) ** b) = (M ** a) dot ((M:real^N^N) ** b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LRG_FRAME_DOT THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(((M:real^N^N) ** v) dot (M ** w)) * norm(M ** u) +
              abs((M ** u) dot (M ** w)) * norm(M ** v)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_SUB; GSYM NORM_MUL] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM NORM_NEG] THEN
    REWRITE_TAC[NORM_TRIANGLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(M:real^N^N) ** v`; `(M:real^N^N) ** w`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPECL [`(M:real^N^N) ** u`; `(M:real^N^N) ** w`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t NORM_POS_LE))
   [`(M:real^N^N) ** u`; `(M:real^N^N) ** v`; `(M:real^N^N) ** w`] THEN
  SPEC_TAC(`norm((M:real^N^N) ** u)`,`nu:real`) THEN
  SPEC_TAC(`norm((M:real^N^N) ** v)`,`nv:real`) THEN
  SPEC_TAC(`norm((M:real^N^N) ** w)`,`nw:real`) THEN
  SPEC_TAC(`abs(((M:real^N^N) ** v) dot (M ** w))`,`p:real`) THEN
  SPEC_TAC(`abs(((M:real^N^N) ** u) dot (M ** w))`,`r:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `p * nu <= (nv * nw) * nu /\ r * nv <= (nu * nw) * nv` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let APX_ROUND_SECTIONAL = prove
 (`!top atlas (g:A->real^3^3) eps W x.
        &0 < eps /\ eps <= &1 / &40 /\ riemannian_metric atlas g /\
        rfs_round_component (top,atlas) g eps W /\ x IN W
        ==> ?q. &0 < q /\
                !u v. ~collinear {vec 0,u,v}
                      ==> abs(mfd_sectional atlas g x u v / q - &1) <= &24 * eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_round_component; rfs_mclose] THEN STRIP_TAC THEN
  EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `yc = SND (c:(A->bool)#(A->real^3)) x` THEN
  ABBREV_TAC `S = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `(yc:real^3) IN S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["yc"; "S"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas c (g1:A->real^3^3)) /\
                metric_field S (metric_local atlas c (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas c (\x. q %% (g:A->real^3^3) x) =
                (\z. q %% metric_local atlas c g z)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[metric_local; FUN_EQ_THM; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]; ALL_TAC] THEN
  ABBREV_TAC `G1 = metric_local atlas c (g1:A->real^3^3)` THEN
  ABBREV_TAC `Gg = metric_local atlas c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field S (\z. q %% (Gg:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v} ==> lsectional (G1:real^3->real^3^3) yc u v = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional"))
          (concl th))) THEN
    ASM_REWRITE_TAC[mfd_sectional];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`; `&1`]
                APX_CONST_CURV_RIEMANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G1:real^3->real^3^3`; `yc:real^3`; `M:real^3^3`]
                APX_CONST1_FRAME_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg eps) (G1:real^3->real^3^3) (\z. q %% Gg z) yc` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN
      ASM_SIMP_TAC[SQRT_MONO_LT_EQ; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `\z. q %% (Gg:real^3->real^3^3) z`;
                 `yc:real^3`; `M:real^3^3`; `&2`] APX_SECTIONAL_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `u:real^3` THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th) &&
    can (find_term (fun t -> t = `&8`)) (concl th))) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Gg:real^3->real^3^3`; `q:real`; `yc:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `lsectional (Gg:real^3->real^3^3) yc u v =
                mfd_sectional (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (x:A) u v`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Gg"; "yc"; "c"] THEN REWRITE_TAC[mfd_sectional]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps` THEN
  REAL_ARITH_TAC);;

let APX_C_COMPONENT_SECTIONAL = prove
 (`!top atlas (g:A->real^3^3) C W x.
        &0 < C /\ riemannian_metric atlas g /\
        rfs_c_component (top,atlas) g C W /\ x IN W
        ==> ?d. inv C * mfd_scalar atlas g x < d /\
                !u v. ~collinear {vec 0,u,v} ==> d <= mfd_sectional atlas g x u v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `?b. !r. r IN IMAGE (mfd_scalar atlas (g:A->real^3^3)) W ==> r <= b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `euclideanreal`;
                   `mfd_scalar atlas (g:A->real^3^3)`; `W:A->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded] THEN
    MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x <= sup(IMAGE (mfd_scalar atlas g) W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_inf_gt")) (concl th))) THEN
  REWRITE_TAC[rfs_inf_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d0:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `inv C * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) W)` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* N7: the statement form, eps0 = 1/48 and alpha = min (1/10) (1/(2C)). *)

let APX_EXCLUDE = prove
 (`!w:A->bool. APX_EXCLUDE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[APX_EXCLUDE_STATEMENT] THEN
  EXISTS_TAC `&1 / &48` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `alpha = min (&1 / &10) (inv(&2 * C))` THEN
  SUBGOAL_THEN `&0 < inv(&2 * C)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < alpha /\ alpha <= &1 / &10 /\ alpha <= inv(&2 * C)` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "alpha" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `alpha:real` APX_NECK_PLANES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pl"))) THEN
  EXISTS_TAC `dl1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "pl" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3`
    (X_CHOOSE_THEN `u2:real^3` (X_CHOOSE_THEN `v2:real^3` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `W:A->bool`; `x:A`]
                  APX_C_COMPONENT_SECTIONAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u1:real^3`; `v1:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `alpha * R <= inv C * R / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * C) * R` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv C * R` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    UNDISCH_TAC `abs(mfd_sectional atlas (g:A->real^3^3) x u1 v1) <= alpha * R` THEN
    UNDISCH_TAC `inv C * R < d` THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `W:A->bool`; `x:A`]
                  APX_ROUND_SECTIONAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`u1:real^3`; `v1:real^3`] th) THEN
                         MP_TAC(SPECL [`u2:real^3`; `v2:real^3`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(mfd_sectional atlas (g:A->real^3^3) x u1 v1) <= alpha * R` THEN
    UNDISCH_TAC `abs(mfd_sectional atlas (g:A->real^3^3) x u2 v2 - R / &2) <= alpha * R` THEN
    SPEC_TAC(`mfd_sectional atlas (g:A->real^3^3) x u1 v1`,`s1:real`) THEN
    SPEC_TAC(`mfd_sectional atlas (g:A->real^3^3) x u2 v2`,`s2:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 <= s1 / q /\ s2 / q <= &3 / &2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `alpha * R <= R / &10` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `alpha * R <= &1 / &10 * R ==> alpha * R <= R / &10`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for N3.  The differential of s = apx_sval, the                    *)
(* Ricci form of the cylinder in terms of ds, and the rank-one comparison:   *)
(* two covectors whose squares agree up to delta in a metric agree up to a   *)
(* sign up to sqrt(2 delta) in the dual metric.                              *)
(* ------------------------------------------------------------------------- *)

let APX_SVAL_DERIV = prove
 (`!y:real^3.
        ~(y = vec 0)
        ==> ((\z. lift(apx_sval z)) has_derivative
             (\w. lift(sqrt(&2) * (y dot w) / (y dot y)))) (at y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\z:real^3. lift(sqrt(&2) / &2 * log(z dot z))` THEN
  EXISTS_TAC `norm(y:real^3)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_SVAL_LOGSQ THEN DISCH_TAC THEN
    UNDISCH_TAC `dist(z:real^3,y) < norm y` THEN
    ASM_REWRITE_TAC[DIST_0; REAL_LT_REFL] THEN
    REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPEC `y:real^3` HAS_DERIVATIVE_SQNORM_AT) THEN
  REWRITE_TAC[NORM_POW_2] THEN DISCH_TAC THEN
  MP_TAC(SPEC `(y:real^3) dot y` HAS_REAL_DERIVATIVE_LOG) THEN
  ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. lift(z dot z)`; `lift o log o drop`;
                 `\x:real^3. &2 % lift(y dot x)`; `\x:real^1. inv((y:real^3) dot y) % x`;
                 `y:real^3`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `sqrt(&2) / &2` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; GSYM LIFT_CMUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; LIFT_CMUL; LIFT_EQ] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN CONV_TAC REAL_FIELD);;

(* The Ricci form of the cylinder: Ric0(w,w) = (G0(w,w) - ds(w)^2) / 2. *)

let APX_CYL0_RICCI_DS = prove
 (`!y w:real^3.
        ~(y = vec 0)
        ==> lricci (cylinder_flow (&0)) y w w =
            (w dot (cylinder_flow (&0) y ** w) -
             (sqrt(&2) * (y dot w) / (y dot y)) pow 2) / &2`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`; APX_CYL0_QUAD] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  SPEC_TAC(`norm(y:real^3)`,`n:real`) THEN GEN_TAC THEN
  REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_FIELD);;

let APX_SQ_LE_LIN = prove
 (`!x d. &0 <= x /\ x * x <= d * x ==> x <= d \/ x = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LE_RMUL_EQ]);;

(* Rank one comparison in an orthonormal frame: if the squares of a.v and   *)
(* b.v agree up to delta |v|^2, then a - sg b is small for a sign sg.        *)

let APX_RANK_ONE_EUCLID = prove
 (`!a b:real^N delta.
        (!v. abs((a dot v) pow 2 - (b dot v) pow 2) <= delta * (v dot v))
        ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                 (a - sg % b) dot (a - sg % b) <= &2 * delta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^N`) THEN
    SIMP_TAC[DOT_BASIS_BASIS; LE_REFL; DIMINDEX_GE_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = a - b:real^N` THEN ABBREV_TAC `t = a + b:real^N` THEN
  SUBGOAL_THEN `!v:real^N. abs((u dot v) * (t dot v)) <= delta * (v dot v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["u"; "t"] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
    REWRITE_TAC[DOT_LADD; DOT_LSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `nu = norm(u:real^N)` THEN ABBREV_TAC `nt = norm(t:real^N)` THEN
  ABBREV_TAC `c = (u:real^N) dot t` THEN
  SUBGOAL_THEN `(u:real^N) dot u = nu pow 2 /\ (t:real^N) dot t = nt pow 2 /\
                (t:real^N) dot u = c /\ &0 <= nu /\ &0 <= nt`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["nu"; "nt"; "c"] THEN
    REWRITE_TAC[NORM_POW_2; NORM_POS_LE] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs c <= nu * nt` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^N`; `t:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nu * nt <= &2 * delta` ASSUME_TAC THENL
   [ABBREV_TAC `P = nu * nt` THEN
    SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `P = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `nt % u + nu % t:real^N` th) THEN
                             MP_TAC(SPEC `nt % u - nu % t:real^N` th)) o
      check (fun th -> length(fst(strip_forall(concl th))) = 1 &&
                       can (find_term (fun x -> x = `t:real^N`)) (concl th))) THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(nt * nu pow 2 - nu * c) * (nt * c - nu * nt pow 2) = --(P * (P - c) pow 2) /\
      nt * (nt * nu pow 2 - nu * c) - nu * (nt * c - nu * nt pow 2) =
      &2 * P * (P - c) /\
      (nt * nu pow 2 + nu * c) * (nt * c + nu * nt pow 2) = P * (P + c) pow 2 /\
      nt * (nt * nu pow 2 + nu * c) + nu * (nt * c + nu * nt pow 2) =
      &2 * P * (P + c)`
    (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_POW] THEN
    SUBGOAL_THEN `&0 <= P - c /\ &0 <= P + c` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_ARITH `d * &2 * P * q = P * ((&2 * d) * q)`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REWRITE_TAC[REAL_POW_2] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`P - c:real`; `&2 * delta`] APX_SQ_LE_LIN) THEN
    MP_TAC(SPECL [`P + c:real`; `&2 * delta`] APX_SQ_LE_LIN) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `nu <= nt` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `nu * nt` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `-- &1` THEN
    REWRITE_TAC[VECTOR_ARITH `a - --(&1) % b:real^N = a + b`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `nu * nt` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

(* The same in a metric G = transp M ** M, with the dual norm of G. *)

let APX_RANK_ONE_METRIC = prove
 (`!(G:real^N^N) (M:real^N^N) a b delta.
        G = transp M ** M /\ invertible M /\
        (!w. abs((a dot w) pow 2 - (b dot w) pow 2) <= delta * (w dot (G ** w)))
        ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                 (a - sg % b) dot (matrix_inv G ** (a - sg % b)) <= &2 * delta`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `Mi = matrix_inv(M:real^N^N)` THEN
  SUBGOAL_THEN `(M:real^N^N) ** Mi = mat 1 /\ Mi ** M = mat 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Mi" THEN ASM_SIMP_TAC[MATRIX_INV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`transp(Mi:real^N^N) ** (a:real^N)`; `transp(Mi:real^N^N) ** (b:real^N)`;
                 `delta:real`] APX_RANK_ONE_EUCLID) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `v:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(Mi:real^N^N) ** (v:real^N)` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
    REWRITE_TAC[TRANSP_TRANSP; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sg:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `matrix_inv(transp M ** M:real^N^N) = (Mi:real^N^N) ** transp Mi`
  SUBST1_TAC THENL
   [EXPAND_TAC "Mi" THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL]);;

(* lgrad2 as the dual-metric norm of the gradient covector. *)

let APX_LGRAD2_FORM = prove
 (`!(G:real^N->real^N^N) (ff:real^N->real) z L.
        ((\x. lift(ff x)) has_derivative L) (at z)
        ==> lgrad2 G ff z =
            ((lambda i. drop(L(basis i))):real^N) dot
            (matrix_inv(G z) ** ((lambda i. drop(L(basis i))):real^N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lgrad2] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let APX_LINEAR_FUNCTIONAL_DOT = prove
 (`!(L:real^N->real^1) W.
        linear L ==> drop(L W) = ((lambda i. drop(L(basis i))):real^N) dot W`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`W:real^N`; `1`] o MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* The model estimate at a point y of a neck: with gp = w.Gp w (Gp the      *)
(* pulled-back metric), Q = Ric(Gp)(w,w) and d = ds_y(w)^2,                   *)
(* |d - (R gp - 2 Q)| <= c1 R gp and |Q| <= c2 R gp.                          *)

let APX_NECK_DS_ESTIMATE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y alpha1.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps /\ eps < &1 /\ &0 <= alpha1 /\
        (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                 lricci (cylinder_flow (&0)) y w w)
             <= alpha1 * (w dot (cylinder_flow (&0) y ** w)))
        ==> !w. abs((sqrt(&2) * (y dot w) / (y dot y)) pow 2 -
                    (mfd_scalar atlas g x * (w dot (rfs_pullback atlas e g y ** w)) -
                     &2 * lricci (rfs_pullback atlas e g) y w w))
                <= (eps + &2 * alpha1) / (&1 - eps) *
                   (mfd_scalar atlas g x * (w dot (rfs_pullback atlas e g y ** w))) /\
                abs(lricci (rfs_pullback atlas e g) y w w)
                <= (&1 / &2 + alpha1) / (&1 - eps) *
                   (mfd_scalar atlas g x * (w dot (rfs_pullback atlas e g y ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^3` THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x /\ &0 < eps` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `w:real^3`]
               APX_NECK_C0) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci")) (concl th) &&
    is_forall (concl th))) THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`; `w:real^3`; `w:real^3`]
                LRICCI_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[APX_CYL0_RICCI_DS] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN
   `(sqrt(&2) * ((y:real^3) dot w) / (y dot y)) pow 2 <= w dot (cylinder_flow (&0) y ** w) /\
    &0 <= (sqrt(&2) * ((y:real^3) dot w) / (y dot y)) pow 2`
  MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC(SPECL [`y:real^3`; `w:real^3`] APX_CYL0_RICCI_DS) THEN
    ASM_SIMP_TAC[RFB_CYL_RICCI; REAL_ARITH `&0 < &1`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= r ==> r = (a - d) / &2 ==> d <= a`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b / n = (a * b) / n`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MP_TAC(ISPECL [`w:real^3`; `y:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    REWRITE_TAC[GSYM NORM_POW_2] THEN
    MP_TAC(ISPEC `w:real^3` NORM_POS_LE) THEN MP_TAC(ISPEC `y:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(w:real^3)`,`nw:real`) THEN SPEC_TAC(`norm(y:real^3)`,`ny:real`) THEN
    SPEC_TAC(`(w:real^3) dot y`,`c:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `c pow 2 <= (nw * ny) pow 2` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `nw * ny:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = (sqrt(&2) * ((y:real^3) dot w) / (y dot y)) pow 2` THEN
  ABBREV_TAC `A = w dot (cylinder_flow (&0) (y:real^3) ** w)` THEN
  ABBREV_TAC `gp = w dot (rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) y ** w)` THEN
  ABBREV_TAC `Q = lricci (rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)) y w w` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `A <= (R * gp) / (&1 - eps)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps + &2 * alpha1) * A` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * c = a * (c * b)`] THEN
    REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2 + alpha1) * A` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_ARITH `(a * b) * c = a * (c * b)`] THEN
    REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* N3.  The chart data of a neck at a point p = e y: the                     *)
(* inverse k of the chart representation near SND c p, its derivative, and  *)
(* the pulled-back metric in terms of the chart metric.                      *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_CHART_DATA = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps
        ==> ?O k.
              open O /\ SND(chart_at atlas (e y)) (e y) IN O /\
              (!z. z IN O ==> k z IN rfs_neck_dom eps /\
                              chart_inv (chart_at atlas (e y)) z = e(k z)) /\
              k(SND(chart_at atlas (e y)) (e y)) = y /\
              (k has_derivative frechet_derivative k (at (SND(chart_at atlas (e y)) (e y))))
                (at (SND(chart_at atlas (e y)) (e y))) /\
              linear(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y)) /\
              (!w. frechet_derivative k (at (SND(chart_at atlas (e y)) (e y)))
                     (frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) w) = w) /\
              (!W. frechet_derivative (SND(chart_at atlas (e y)) o e) (at y)
                     (frechet_derivative k (at (SND(chart_at atlas (e y)) (e y))) W) = W) /\
              (!w. w dot (rfs_pullback atlas e g y ** w) =
                   frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) w dot
                   (metric_local atlas (chart_at atlas (e y)) g
                      (SND(chart_at atlas (e y)) (e y)) **
                    frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:real^3->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[rfs_pullback] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)`,
           `c:(A->bool)#(A->real^3)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `V:A->bool`; `psi:A->real^3`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(V:A->bool,psi:A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (psi:A->real^3) (V INTER IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
  EXISTS_TAC `(e':A->real^3) o chart_inv (V:A->bool,psi:A->real^3)` THEN
  SUBGOAL_THEN `(y:real^3) IN {z | z IN rfs_neck_dom eps /\ (e:real^3->A) z IN V}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (psi:A->real^3) (V INTER IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
                 `{z | z IN rfs_neck_dom eps /\ (e:real^3->A) z IN V}`;
                 `(psi:A->real^3) o (e:real^3->A)`;
                 `(e':A->real^3) o chart_inv (V:A->bool,psi:A->real^3)`; `y:real^3`]
                LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (psi:A->real^3) (V INTER IMAGE (e:real^3->A) (rfs_neck_dom eps))) /\
                smooth_map_on (IMAGE psi (V INTER IMAGE e (rfs_neck_dom eps)))
                  ((e':A->real^3) o chart_inv (V:A->bool,psi))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `v:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[o_THM] THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`IMAGE (psi:A->real^3) (V INTER IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
                   `(e':A->real^3) o chart_inv (V:A->bool,psi:A->real^3)`;
                   `(psi:A->real^3) ((e:real^3->A) y)`; `vec 0:real^3`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `(e:real^3->A) y` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[FRECHET_DERIVATIVE_WORKS]];
    X_GEN_TAC `w:real^3` THEN REWRITE_TAC[mpullback] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_SIMP_TAC[MATRIX_WORKS; o_THM]]);;

let APX_SFUN_AT = prove
 (`!s (e:real^3->A) y.
        y IN s /\ (!u v. u IN s /\ v IN s /\ e u = e v ==> u = v)
        ==> apx_sfun s e (e y) = apx_sval y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sfun] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

let APX_OVERLAP_ARITH = prove
 (`!d1 d2 R R' GW QW c1 c2.
        &0 < R /\ &0 < R' /\ &0 <= GW /\ &0 <= c1 /\ &0 <= c2 /\
        abs(d1 - (R * GW - &2 * QW)) <= c1 * (R * GW) /\ abs QW <= c2 * (R * GW) /\
        abs(d2 - (R' * GW - &2 * QW)) <= c1 * (R' * GW)
        ==> abs(d1 / R - d2 / R') <= (&2 * c1 + &2 * c2 * abs(R / R' - &1)) * GW`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(d1 / R - (GW - &2 * (QW / R))) <= c1 * GW /\
                abs(d2 / R' - (GW - &2 * (QW / R'))) <= c1 * GW /\
                abs(QW / R) <= c2 * GW`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `d1 / R - (GW - &2 * (QW / R)) = (d1 - (R * GW - &2 * QW)) / R`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < R ==> abs R = R`; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `d2 / R' - (GW - &2 * (QW / R')) = (d2 - (R' * GW - &2 * QW)) / R'`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < R'` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < R ==> abs R = R`; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < R ==> abs R = R`; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `QW / R' = (QW / R) * (R / R')` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < R` THEN UNDISCH_TAC `&0 < R'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(QW / R) * abs(R / R' - &1) <= (c2 * GW) * abs(R / R' - &1)`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs((QW / R) * (R / R' - &1)) = abs(QW / R) * abs(R / R' - &1)` MP_TAC
  THENL [REWRITE_TAC[REAL_ABS_MUL]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* N3 (MT Prop A.11(1),(3)): overlapping necks have comparable               *)
(* scales, and their normalized s-differentials agree up to sign.            *)
(* ------------------------------------------------------------------------- *)

let APX_RATIO_ARITH = prove
 (`!R R' l l' a.
        &0 < R /\ &0 < R' /\ R * l = R' * l' /\ abs(l - &1) <= a /\ abs(l' - &1) <= a /\
        a <= &1 / &4
        ==> abs(R' / R - &1) <= &4 * a /\ abs(R / R' - &1) <= &4 * a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < l /\ &0 < l'` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R' / R = l / l' /\ R / R' = l' / l` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `R * l = R' * l'` THEN UNDISCH_TAC `&0 < R` THEN UNDISCH_TAC `&0 < R'` THEN
    UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&0 < l'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `l / l' - &1 = (l - l') / l' /\ l' / l - &1 = (l' - l) / l`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&0 < l'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a * (&3 / &4) <= a * l /\ a * (&3 / &4) <= a * l'` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* At a point e y of a neck: the s-function in the chart at e y, its      *)
(* derivative L, and the rank one estimate for drop(L W)^2 in chart terms.   *)

let APX_NECK_COVECTOR = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y alpha1.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps /\ eps < &1 /\ &0 <= alpha1 /\
        (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                 lricci (cylinder_flow (&0)) y w w)
             <= alpha1 * (w dot (cylinder_flow (&0) y ** w)))
        ==> ?O sf L.
              open O /\ SND(chart_at atlas (e y)) (e y) IN O /\
              (!z. z IN O
                   ==> apx_sfun (rfs_neck_dom eps) e (chart_inv (chart_at atlas (e y)) z) =
                       sf z) /\
              ((\z. lift(sf z)) has_derivative L) (at (SND(chart_at atlas (e y)) (e y))) /\
              linear L /\
              (!v. drop(L(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) v)) =
                   sqrt(&2) * (y dot v) / (y dot y)) /\
              (!W. abs(drop(L W) pow 2 -
                       (mfd_scalar atlas g x *
                        (W dot (metric_local atlas (chart_at atlas (e y)) g
                                  (SND(chart_at atlas (e y)) (e y)) ** W)) -
                        &2 * lricci (metric_local atlas (chart_at atlas (e y)) g)
                                    (SND(chart_at atlas (e y)) (e y)) W W))
                   <= (eps + &2 * alpha1) / (&1 - eps) *
                      (mfd_scalar atlas g x *
                       (W dot (metric_local atlas (chart_at atlas (e y)) g
                                 (SND(chart_at atlas (e y)) (e y)) ** W)))) /\
              (!W. abs(lricci (metric_local atlas (chart_at atlas (e y)) g)
                              (SND(chart_at atlas (e y)) (e y)) W W)
                   <= (&1 / &2 + alpha1) / (&1 - eps) *
                      (mfd_scalar atlas g x *
                       (W dot (metric_local atlas (chart_at atlas (e y)) g
                                 (SND(chart_at atlas (e y)) (e y)) ** W))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]
               APX_NECK_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` (X_CHOOSE_THEN `k:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                `alpha1:real`] APX_NECK_DS_ESTIMATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `zc = SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y))
                      (e y)` THEN
  ABBREV_TAC `Dk = frechet_derivative (k:real^3->real^3) (at zc)` THEN
  ABBREV_TAC `D1 = frechet_derivative
                     (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)) o e)
                     (at y)` THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(Dk:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`O:real^3->bool`; `\z:real^3. apx_sval((k:real^3->real^3) z)`;
    `\W:real^3. lift(sqrt(&2) * (y dot (Dk:real^3->real^3) W) / (y dot y))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(k:real^3->real^3) z IN rfs_neck_dom eps /\
                  chart_inv (chart_at atlas ((e:real^3->A) y)) z = e(k z)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SFUN_AT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`k:real^3->real^3`; `\u:real^3. lift(apx_sval u)`; `Dk:real^3->real^3`;
                   `\w:real^3. lift(sqrt(&2) * (y dot w) / (y dot y))`; `zc:real^3`]
                  DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPEC `y:real^3` APX_SVAL_DERIV) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[linear; LIFT_ADD; LIFT_CMUL; GSYM LIFT_ADD] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REPEAT GEN_TAC THEN REAL_ARITH_TAC;
    X_GEN_TAC `v:real^3` THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `W:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(Dk:real^3->real^3) W` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `alpha1:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "cylinder_flow"))
               (concl th)))) THEN
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `(D1:real^3->real^3)(Dk W) = W` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`;
                   `(Dk:real^3->real^3) W`; `(Dk:real^3->real^3) W`] APX_PULLBACK_RICCI_GEN) THEN
    ASM_REWRITE_TAC[mfd_ricci] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[];
    X_GEN_TAC `W:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(Dk:real^3->real^3) W` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `alpha1:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "cylinder_flow"))
               (concl th)))) THEN
    SUBGOAL_THEN `(D1:real^3->real^3)(Dk W) = W` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`;
                   `(Dk:real^3->real^3) W`; `(Dk:real^3->real^3) W`] APX_PULLBACK_RICCI_GEN) THEN
    ASM_REWRITE_TAC[mfd_ricci] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[]]);;

let APX_NECK_OVERLAP_GEN = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' p.
           &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
           rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
           p IN IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
           ==> abs(mfd_scalar atlas g x' / mfd_scalar atlas g x - &1) <= &4 * alpha1 /\
               ?sg. (sg = &1 \/ sg = -- &1) /\
                    apx_dnorm2 atlas g
                      (\q. inv(sqrt(mfd_scalar atlas g x)) *
                           apx_sfun (rfs_neck_dom eps) e q -
                           sg * inv(sqrt(mfd_scalar atlas g x')) *
                           apx_sfun (rfs_neck_dom eps) e' q) p
                    <= &32 * alpha1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(p:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps) INTER
                        IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(p:A) = e(y:real^3)`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `(e:real^3->A) y = (e':real^3->A) y'`)) THEN
  SUBGOAL_THEN `eps < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (n,xx,ee,yy) ->
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
       `g:A->real^3^3`; `eps:real`; xx; ee; yy]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC n)))
   [("ric1",`x:A`,`e:real^3->A`,`y:real^3`); ("ric2",`x':A`,`e':real^3->A`,`y':real^3`)] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) x *
    lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas (e:real^3->A) g z) y =
    mfd_scalar atlas (g:A->real^3^3) x' *
    lscalar (\z. mfd_scalar atlas g x' %% rfs_pullback atlas (e':real^3->A) g z) y'`
  ASSUME_TAC THENL
   [
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                     `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
                    APX_PULLBACK_SCALAR_GEN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                    `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`] APX_NECK_FIELDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e':real^3->A) (g:A->real^3^3)`;
                     `mfd_scalar atlas (g:A->real^3^3) x'`; `y':real^3`] LSCALAR_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `rfs_neck_dom eps`; `e':real^3->A`; `y':real^3`]
                    APX_PULLBACK_SCALAR_GEN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3) x`; `mfd_scalar atlas (g:A->real^3^3) x'`;
    `lscalar (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z) y`;
    `lscalar (\z. mfd_scalar atlas (g:A->real^3^3) x' %% rfs_pullback atlas (e':real^3->A) g z) y'`;
    `alpha1:real`] APX_RATIO_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                `alpha1:real`] APX_NECK_COVECTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:real^3->bool` (X_CHOOSE_THEN `sf1:real^3->real`
    (X_CHOOSE_THEN `L1:real^3->real^1` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`; `y':real^3`;
                `alpha1:real`] APX_NECK_COVECTOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(e':real^3->A) y' = (e:real^3->A) y`] THEN
  DISCH_THEN(X_CHOOSE_THEN `O2:real^3->bool` (X_CHOOSE_THEN `sf2:real^3->real`
    (X_CHOOSE_THEN `L2:real^3->real^1` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:real^3->A) y`] CHART_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)` THEN
  ABBREV_TAC `zc = SND (c:(A->bool)#(A->real^3)) ((e:real^3->A) y)` THEN
  ABBREV_TAC `Gcf = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `R' = mfd_scalar atlas (g:A->real^3^3) x'` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)) Gcf /\
                zc IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Gcf" THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "zc" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!W:real^3. &0 <= W dot ((Gcf:real^3->real^3^3) zc ** W)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `a = inv(sqrt R) % ((lambda i. drop((L1:real^3->real^1)(basis i))):real^3)` THEN
  ABBREV_TAC `b = inv(sqrt R') % ((lambda i. drop((L2:real^3->real^1)(basis i))):real^3)` THEN
  SUBGOAL_THEN `!W:real^3. a dot W = inv(sqrt R) * drop((L1:real^3->real^1) W) /\
                           b dot W = inv(sqrt R') * drop((L2:real^3->real^1) W)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[DOT_LMUL] THEN
    ASM_SIMP_TAC[GSYM APX_LINEAR_FUNCTIONAL_DOT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eps + &2 * alpha1) / (&1 - eps) <= &4 * alpha1 /\
                (&1 / &2 + alpha1) / (&1 - eps) <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 - eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `alpha1 * eps <= alpha1 * (&1 / &4)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!W:real^3. abs((a dot W) pow 2 - (b dot W) pow 2) <=
               (&16 * alpha1) * (W dot ((Gcf:real^3->real^3^3) zc ** W))`
  ASSUME_TAC THENL
   [X_GEN_TAC `W:real^3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM real_div; REAL_ARITH `inv a * b = b / a`] THEN
    MP_TAC(ISPECL [`drop((L1:real^3->real^1) W) pow 2`; `drop((L2:real^3->real^1) W) pow 2`;
                   `R:real`; `R':real`; `W dot ((Gcf:real^3->real^3^3) zc ** W)`;
                   `lricci (Gcf:real^3->real^3^3) zc W W`; `&4 * alpha1`; `&1`]
                  APX_OVERLAP_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= R * (W dot ((Gcf:real^3->real^3^3) zc ** W)) /\
                    &0 <= R' * (W dot ((Gcf:real^3->real^3^3) zc ** W))` STRIP_ASSUME_TAC
      THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(eps + &2 * alpha1) / (&1 - eps) *
                    (R * (W dot ((Gcf:real^3->real^3^3) zc ** W)))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&1 / &2 + alpha1) / (&1 - eps) *
                    (R * (W dot ((Gcf:real^3->real^3^3) zc ** W)))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(eps + &2 * alpha1) / (&1 - eps) *
                    (R' * (W dot ((Gcf:real^3->real^3^3) zc ** W)))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `Gcf:real^3->real^3^3`;
                 `zc:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`(Gcf:real^3->real^3^3) zc`; `M:real^3^3`; `a:real^3`; `b:real^3`;
                 `&16 * alpha1`] APX_RANK_ONE_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(a - sg % b:real^3) dot (matrix_inv((Gcf:real^3->real^3^3) zc) ** (a - sg % b))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  REWRITE_TAC[apx_dnorm2] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lgrad2 (Gcf:real^3->real^3^3)
                (\z. inv(sqrt R) * (sf1:real^3->real) z - sg * inv(sqrt R') * (sf2:real^3->real) z) zc` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `(O1:real^3->bool) INTER O2` THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gcf:real^3->real^3^3`;
                 `\z. inv(sqrt R) * (sf1:real^3->real) z - sg * inv(sqrt R') * (sf2:real^3->real) z`;
                 `zc:real^3`;
                 `\W. inv(sqrt R) % (L1:real^3->real^1) W - (sg * inv(sqrt R')) % (L2:real^3->real^1) W`]
                APX_LGRAD2_FORM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUB; LIFT_CMUL; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `((lambda i. drop((\W. inv(sqrt R) % (L1:real^3->real^1) W -
                          (sg * inv(sqrt R')) % (L2:real^3->real^1) W) (basis i))):real^3) =
    a - sg % b`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
             DROP_SUB; DROP_CMUL] THEN
    REAL_ARITH_TAC;
    REFL_TAC]);;

(* N3: the statement form, alpha1 = min (min (1/4) (alpha/4)) (alpha^2/32). *)

let APX_NECK_OVERLAP = prove
 (`!w:A->bool. APX_NECK_OVERLAP_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[APX_NECK_OVERLAP_STATEMENT] THEN
  X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  ABBREV_TAC `a1 = min (min (&1 / &4) (alpha / &4)) (alpha pow 2 / &32)` THEN
  SUBGOAL_THEN `&0 < alpha pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a1 /\ a1 <= &1 / &4 /\ &4 * a1 <= alpha /\ &32 * a1 <= alpha pow 2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "a1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `(\x:A. T)` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `a1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  EXISTS_TAC `min e1 a1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a1:real`; `min e1 a1`] APX_NECK_OVERLAP_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `x:A`;
      `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "gen") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "gen" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`; `p:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `sg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helpers for N4.  The pair estimate at a common point of two               *)
(* necks (the core of N3, with the model form of the two covectors).         *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_PAIR_ESTIMATE = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' y y'.
           &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
           rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
           y IN rfs_neck_dom eps /\ y' IN rfs_neck_dom eps /\ e' y' = e y
           ==> ?L1 L2.
                 linear L1 /\ linear L2 /\
                 (!v. drop(L1(frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) v)) =
                      sqrt(&2) * (y dot v) / (y dot y)) /\
                 (!v. drop(L2(frechet_derivative (SND(chart_at atlas (e y)) o e') (at y') v)) =
                      sqrt(&2) * (y' dot v) / (y' dot y')) /\
                 (!W. abs(drop(L1 W) pow 2 / mfd_scalar atlas g x -
                          drop(L2 W) pow 2 / mfd_scalar atlas g x')
                      <= (&16 * alpha1) *
                         (W dot (metric_local atlas (chart_at atlas (e y)) g
                                   (SND(chart_at atlas (e y)) (e y)) ** W)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (n,xx,ee,yy) ->
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
       `g:A->real^3^3`; `eps:real`; xx; ee; yy]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC n)))
   [("ric1",`x:A`,`e:real^3->A`,`y:real^3`); ("ric2",`x':A`,`e':real^3->A`,`y':real^3`)] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) x *
    lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas (e:real^3->A) g z) y =
    mfd_scalar atlas (g:A->real^3^3) x' *
    lscalar (\z. mfd_scalar atlas g x' %% rfs_pullback atlas (e':real^3->A) g z) y'`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                  `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                   `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
                  APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                  `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`] APX_NECK_FIELDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e':real^3->A) (g:A->real^3^3)`;
                   `mfd_scalar atlas (g:A->real^3^3) x'`; `y':real^3`] LSCALAR_SCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom eps`; `e':real^3->A`; `y':real^3`]
                  APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3) x`; `mfd_scalar atlas (g:A->real^3^3) x'`;
    `lscalar (\z. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g z) y`;
    `lscalar (\z. mfd_scalar atlas (g:A->real^3^3) x' %% rfs_pullback atlas (e':real^3->A) g z) y'`;
    `alpha1:real`] APX_RATIO_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`;
                `alpha1:real`] APX_NECK_COVECTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:real^3->bool` (X_CHOOSE_THEN `sf1:real^3->real`
    (X_CHOOSE_THEN `L1:real^3->real^1` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`; `y':real^3`;
                `alpha1:real`] APX_NECK_COVECTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(e':real^3->A) y' = (e:real^3->A) y`] THEN
  DISCH_THEN(X_CHOOSE_THEN `O2:real^3->bool` (X_CHOOSE_THEN `sf2:real^3->real`
    (X_CHOOSE_THEN `L2:real^3->real^1` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`L1:real^3->real^1`; `L2:real^3->real^1`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:real^3->A) y`] CHART_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)` THEN
  ABBREV_TAC `zc = SND (c:(A->bool)#(A->real^3)) ((e:real^3->A) y)` THEN
  ABBREV_TAC `Gcf = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `R' = mfd_scalar atlas (g:A->real^3^3) x'` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)) Gcf /\
                zc IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Gcf" THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "zc" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!W:real^3. &0 <= W dot ((Gcf:real^3->real^3^3) zc ** W)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eps + &2 * alpha1) / (&1 - eps) <= &4 * alpha1 /\
                (&1 / &2 + alpha1) / (&1 - eps) <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 - eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `alpha1 * eps <= alpha1 * (&1 / &4)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `W:real^3` THEN
  MP_TAC(ISPECL [`drop((L1:real^3->real^1) W) pow 2`; `drop((L2:real^3->real^1) W) pow 2`;
                 `R:real`; `R':real`; `W dot ((Gcf:real^3->real^3^3) zc ** W)`;
                 `lricci (Gcf:real^3->real^3^3) zc W W`; `&4 * alpha1`; `&1`]
                APX_OVERLAP_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= R * (W dot ((Gcf:real^3->real^3^3) zc ** W)) /\
                  &0 <= R' * (W dot ((Gcf:real^3->real^3^3) zc ** W))` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(eps + &2 * alpha1) / (&1 - eps) *
                  (R * (W dot ((Gcf:real^3->real^3^3) zc ** W)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 / &2 + alpha1) / (&1 - eps) *
                  (R * (W dot ((Gcf:real^3->real^3^3) zc ** W)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(eps + &2 * alpha1) / (&1 - eps) *
                  (R' * (W dot ((Gcf:real^3->real^3^3) zc ** W)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Helpers for N4.  The transition map ei o e1 between two                   *)
(* smooth parametrizations (smooth on the open overlap, with the chain rule  *)
(* in a chart), and the kernel of the derivative of a normalized map.        *)
(* ------------------------------------------------------------------------- *)

let APX_PARAM_TRANSITION = prove
 (`!top atlas s s1 (e:real^N->A) e1 ei.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        mfd_param top atlas s1 e1 /\ (!x. x IN s ==> ei(e x) = x)
        ==> open {v | v IN s1 /\ e1 v IN IMAGE e s} /\
            smooth_map_on {v | v IN s1 /\ e1 v IN IMAGE e s} (ei o e1) /\
            (!v. v IN s1 /\ e1 v IN IMAGE e s
                 ==> ei(e1 v) IN s /\ e(ei(e1 v)) = e1 v /\
                     (!k. frechet_derivative (SND(chart_at atlas (e1 v)) o e)
                            (at (ei(e1 v))) (frechet_derivative (ei o e1) (at v) k) =
                          frechet_derivative (SND(chart_at atlas (e1 v)) o e1) (at v) k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s1:real^N->bool`; `e1:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e10:A->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `U = {v | v IN s1 /\ (e1:real^N->A) v IN IMAGE (e:real^N->A) s}` THEN
  SUBGOAL_THEN `!v. v IN U <=> v IN s1 /\ (e1:real^N->A) v IN IMAGE (e:real^N->A) s`
  (LABEL_TAC "Ueq") THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN U ==> (ei:A->real^N)((e1:real^N->A) v) IN s /\ e(ei(e1 v)) = e1 v`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    UNDISCH_TAC `continuous_map (subtopology euclidean s1,top) (e1:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (e:real^N->A) s` o CONJUNCT2) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN U
        ==> ?t. open t /\ v IN t /\ t SUBSET U /\ smooth_map_on t ((ei:A->real^N) o e1) /\
                open {z | z IN s /\
                          (e:real^N->A) z IN
                          FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e1:real^N->A) v))} /\
                smooth_map_on {z | z IN s /\ e z IN FST(chart_at atlas (e1 v))}
                              (SND(chart_at atlas (e1 v)) o e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN s1 /\ (e1:real^N->A) v IN IMAGE (e:real^N->A) s`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN U` THEN USE_THEN "Ueq" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(e1:real^N->A) v IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (e1:real^N->A) s1 SUBSET topspace top` THEN
      UNDISCH_TAC `(v:real^N) IN s1` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(e1:real^N->A) v`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e1:real^N->A) v)`,
             `c:(A->bool)#(A->real^N)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                  APX_PARAM_CHART_REP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e2:A->real^N`
      (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s1:real^N->bool`; `e1:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                  APX_PARAM_CHART_REP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e3:A->real^N`
      (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(V:A->bool,psi:A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    EXISTS_TAC `{w | w IN s1 /\ (e1:real^N->A) w IN V} INTER U` THEN
    ASM_SIMP_TAC[OPEN_INTER; INTER_SUBSET] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `((e2:A->real^N) o chart_inv(V:A->bool,psi:A->real^N)) o
                ((psi:A->real^N) o (e1:real^N->A))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(e2:A->real^N)((e1:real^N->A) w) = ei(e1 w)` ASSUME_TAC THENL
       [SUBGOAL_THEN `(ei:A->real^N)((e1:real^N->A) w) IN s /\ e(ei(e1 w)) = e1 w` MP_TAC
        THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP
          (ASSUME `!z. z IN s ==> (e2:A->real^N)((e:real^N->A) z) = z`)) SUBST1_TAC) THEN
        DISCH_THEN ACCEPT_TAC;
        ASM_SIMP_TAC[o_THM]];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER IMAGE (e:real^N->A) s)` THEN
      ASM_SIMP_TAC[OPEN_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
        X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(w:real^N) IN U` THEN USE_THEN "Ueq" (fun th -> SIMP_TAC[th]);
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `{w | w IN s1 /\ (e1:real^N->A) w IN V}` THEN
        ASM_REWRITE_TAC[INTER_SUBSET]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN U` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `k:real^N` THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e1:real^N->A) v IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e1:real^N->A) s1 SUBSET topspace top` THEN
    UNDISCH_TAC `(v:real^N) IN s1` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e1:real^N->A) v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e1:real^N->A) v)` THEN
  SUBGOAL_THEN
   `(((SND (c:(A->bool)#(A->real^N)) o (e:real^N->A)) o ((ei:A->real^N) o (e1:real^N->A)))
     has_derivative
     (frechet_derivative (SND c o e) (at (ei(e1 v))) o frechet_derivative (ei o e1) (at v)))
    (at v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
      ASM_SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((SND (c:(A->bool)#(A->real^N)) o (e1:real^N->A)) has_derivative
     (frechet_derivative (SND c o (e:real^N->A)) (at ((ei:A->real^N)(e1 v))) o
      frechet_derivative (ei o e1) (at v))) (at v)`
  MP_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC
     [`(SND (c:(A->bool)#(A->real^N)) o (e:real^N->A)) o ((ei:A->real^N) o (e1:real^N->A))`;
      `d:real`] THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN U` (fun th -> ASM_SIMP_TAC[th]) THEN
    SUBGOAL_THEN `(w:real^N) IN ball(v,d)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(v:real^N,d) SUBSET t` THEN UNDISCH_TAC `(t:real^N->bool) SUBSET U` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; o_THM]));;

(* The derivative of a normalized map x/|x| o q kills h only along q. *)

let APX_NORMALIZE_KERNEL = prove
 (`!(q:real^M->real^N) w h.
        q differentiable (at w) /\ ~(q w = vec 0) /\
        ((\x. inv(norm x) % x) o q) differentiable (at w) /\
        frechet_derivative ((\x. inv(norm x) % x) o q) (at w) h = vec 0
        ==> ?c. frechet_derivative q (at w) h = c % q w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = (\x:real^N. inv(norm x) % x) o (q:real^M->real^N)` THEN
  SUBGOAL_THEN `(\x:real^M. lift(norm((q:real^M->real^N) x))) differentiable (at w)`
  MP_TAC THENL
   [SUBGOAL_THEN `(\x:real^M. lift(norm((q:real^M->real^N) x))) = (\x. lift(norm x)) o q`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_SIMP_TAC[DIFFERENTIABLE_NORM_AT];
    ALL_TAC] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
  ABBREV_TAC `L = frechet_derivative (\x:real^M. lift(norm((q:real^M->real^N) x))) (at w)` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^M. norm((q:real^M->real^N) x)`; `\k:real^M. drop((L:real^M->real^1) k)`;
                 `P:real^M->real^N`; `frechet_derivative (P:real^M->real^N) (at w)`; `w:real^M`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    BETA_TAC] THEN
  SUBGOAL_THEN `!x:real^M. (P:real^M->real^N) x = inv(norm((q:real^M->real^N) x)) % q x`
  ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^M. norm((q:real^M->real^N) x) % (P:real^M->real^N) x) = q`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC] THEN X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(q:real^M->real^N) x = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; VECTOR_MUL_ASSOC] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* N4, the geometric kernel lemma.  At a common point e y =                  *)
(* e' y' of two eps-necks, if the chart derivative of e' maps a vector k     *)
(* tangent to the level sphere of y' (y'.k = 0) to the chart derivative of e *)
(* of a radial vector c y, then k = 0: the pair estimate gives               *)
(* 2 c^2 / R <= 16 alpha1 c^2 (y.P y) and the C^0 bound R (y.P y) <= 2(1+eps)*)
(* forces c = 0.                                                             *)
(* ------------------------------------------------------------------------- *)

let APX_KERNEL_ARITH = prove
 (`!c R R' Q a eps.
     &0 < R /\ &0 <= a /\ &32 * a <= &1 /\ &0 <= eps /\ eps <= &1 / &32 /\
     abs((sqrt(&2) * c) pow 2 / R - &0 pow 2 / R') <= (&16 * a) * (c pow 2 * Q) /\
     R * Q <= &2 * (&1 + eps)
     ==> c = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(sqrt(&2) * c) pow 2 = &2 * c pow 2 /\ &0 pow 2 / R' = &0`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[REAL_POW_MUL; real_div] THEN SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * c pow 2 <= ((&16 * a) * (c pow 2 * Q)) * R` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&16 * a) * (c pow 2 * Q)) * R <= ((&16 * a) * c pow 2) * (&2 * (&1 + eps))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((&16 * a) * (c pow 2 * Q)) * R = ((&16 * a) * c pow 2) * (R * Q)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((&16 * a) * c pow 2) * (&2 * (&1 + eps)) <= (&33 / &32) * c pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((&16 * a) * c pow 2) * (&2 * (&1 + eps)) =
                  ((&32 * a) * (&1 + eps)) * c pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * (&1 + eps)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c pow 2 = &0` MP_TAC THENL
   [MP_TAC(SPEC `c:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ]]);;

let APX_NECK_SECTION_KERNEL = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &32 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' y y' k c.
           &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
           rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
           y IN rfs_neck_dom eps /\ y' IN rfs_neck_dom eps /\ e' y' = e y /\
           y' dot k = &0 /\
           frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) (c % y) =
           frechet_derivative (SND(chart_at atlas (e y)) o e') (at y') k
           ==> k = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_NECK_PAIR_ESTIMATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "pair") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "pair" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
    `y:real^3`; `y':real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real^3->real^1` (X_CHOOSE_THEN `L2:real^3->real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]
               APX_NECK_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O1:real^3->bool` (X_CHOOSE_THEN `k1:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`; `y':real^3`]
               APX_NECK_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(e':real^3->A) y' = (e:real^3->A) y`] THEN
  DISCH_THEN(X_CHOOSE_THEN `O2:real^3->bool` (X_CHOOSE_THEN `k2:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`; `y:real^3`]
               APX_NECK_C0_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; APX_CYL0_QUAD; GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
  ABBREV_TAC `D1 = frechet_derivative (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                     ((e:real^3->A) y)) o e) (at y)` THEN
  ABBREV_TAC `D2 = frechet_derivative (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                     ((e:real^3->A) y)) o (e':real^3->A)) (at y')` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool)
                     (chart_at atlas ((e:real^3->A) y)) (g:A->real^3^3)
                     (SND(chart_at atlas (e y)) (e y))` THEN
  SUBGOAL_THEN `!b z. (D1:real^3->real^3) (b % z) = b % D1 z` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LINEAR_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KERNEL_ARITH THEN
    MAP_EVERY EXISTS_TAC [`mfd_scalar atlas (g:A->real^3^3) x`;
                          `mfd_scalar atlas (g:A->real^3^3) x'`;
                          `(D1:real^3->real^3) y dot ((Gc:real^3^3) ** D1 y)`;
                          `alpha1:real`; `eps:real`] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(D2:real^3->real^3) k` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `L2:real^3->real^1`)) (concl th) &&
      can (find_term (fun t -> t = `L1:real^3->real^1`)) (concl th))) THEN
    REWRITE_TAC[ASSUME `!v. drop((L2:real^3->real^1)((D2:real^3->real^3) v)) =
                            sqrt(&2) * ((y':real^3) dot v) / (y' dot y')`;
                ASSUME `(y':real^3) dot k = &0`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(D1:real^3->real^3) (c % y) = (D2:real^3->real^3) k`)) THEN
    REWRITE_TAC[ASSUME `!v. drop((L1:real^3->real^1)((D1:real^3->real^3) v)) =
                            sqrt(&2) * ((y:real^3) dot v) / (y dot y)`] THEN
    REWRITE_TAC[ASSUME `!b z. (D1:real^3->real^3) (b % z) = b % D1 z`] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `sqrt(&2) * (c * ((y:real^3) dot y)) / (y dot y) = sqrt(&2) * c /\
                  sqrt(&2) * &0 / ((y':real^3) dot y') = &0`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
      SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[DOT_EQ_0]; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    AP_TERM_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(D2:real^3->real^3) k = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(D1:real^3->real^3) (c % y) = (D2:real^3->real^3) k`)) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO;
                    MATCH_MP LINEAR_0 (ASSUME `linear (D1:real^3->real^3)`)];
    ALL_TAC] THEN
  ASSUME_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (D2:real^3->real^3)`)) THEN
  ABBREV_TAC `Dk2 = frechet_derivative (k2:real^3->real^3)
                      (at (SND (chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                 ((e:real^3->A) y)) (e y)))` THEN
  MP_TAC(SPEC `k:real^3` (ASSUME `!w. (Dk2:real^3->real^3) ((D2:real^3->real^3) w) = w`)) THEN
  MP_TAC(SPEC `vec 0:real^3`
    (ASSUME `!w. (Dk2:real^3->real^3) ((D2:real^3->real^3) w) = w`)) THEN
  REWRITE_TAC[ASSUME `(D2:real^3->real^3) (vec 0) = vec 0`;
              ASSUME `(D2:real^3->real^3) k = vec 0`] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* N4 assembly.  A map q near the unit sphere whose                          *)
(* normalization f = q/|q| is a sphere diffeomorphism gives the section      *)
(* u(x) = |q(psi x)| (psi the inverse of f); for two necks q(w) = ei(e'(r w))*)
(* and f satisfies the hypotheses of SMT_SPHERE_COVERING_STATEMENT by the    *)
(* kernel lemma.                                                             *)
(* ------------------------------------------------------------------------- *)

let APX_NORMALIZE_INV = prove
 (`!v x:real^N. ~(v = vec 0) /\ inv(norm v) % v = x ==> norm v % x = v`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID]);;

let APX_SECTION_FROM_DIFFEO = prove
 (`!(e:real^3->A) (e':real^3->A) r r1 r2 O (q:real^3->real^3) psi.
        &0 < r /\ open O /\ sphere(vec 0,&1) SUBSET O /\ smooth_map_on O q /\
        (!w. w IN O ==> ~(q w = vec 0)) /\
        sphere_diffeo ((\x. inv(norm x) % x) o q) psi /\
        (!w. w IN sphere(vec 0,&1)
             ==> r1 < norm(q w) /\ norm(q w) < r2 /\ e(q w) = e'(r % w))
        ==> apx_section e r1 r2 (IMAGE e' (sphere(vec 0,r)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sphere_diffeo; smooth_near; o_THM] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `O2:real^3->bool` STRIP_ASSUME_TAC o check (fun th ->
    is_exists(concl th) &&
    can (find_term (fun t -> t = `psi:real^3->real^3`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "inv" o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `psi:real^3->real^3`)) (concl th))) THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                  ==> (psi:real^3->real^3) x IN sphere(vec 0,&1) /\ psi x IN O /\
                      ~((q:real^3->real^3)(psi x) = vec 0) /\
                      inv(norm(q(psi x))) % q(psi x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "inv" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `x:real^3` th)
      (ASSUME `(x:real^3) IN sphere(vec 0,&1)`))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^3->real^3) x IN O` (fun th -> ASM_SIMP_TAC[th]) THEN
    UNDISCH_TAC `sphere(vec 0,&1) SUBSET (O:real^3->bool)` THEN
    UNDISCH_TAC `(psi:real^3->real^3) x IN sphere(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | x IN O2 /\ (psi:real^3->real^3) x IN O}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[apx_section] THEN
  EXISTS_TAC `\x:real^3. norm((q:real^3->real^3)((psi:real^3->real^3) x))` THEN
  REWRITE_TAC[smooth_near] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{x:real^3 | x IN O2 /\ (psi:real^3->real^3) x IN O}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `sphere(vec 0,&1) SUBSET (O2:real^3->bool)` THEN
      UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^3. lift(norm((q:real^3->real^3)((psi:real^3->real^3) x)))) =
                  (\x:real^3. lift(norm x)) o (q o psi)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(psi:real^3->real^3) x` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `r1:real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                  ==> (e:real^3->A)(norm((q:real^3->real^3)((psi:real^3->real^3) x)) % x) =
                      (e':real^3->A)(r % psi x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm((q:real^3->real^3)((psi:real^3->real^3) x)) % x = q(psi x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC APX_NORMALIZE_INV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(psi:real^3->real^3) x` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `r1:real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `inv r % (z:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN sphere(vec 0,r)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    USE_THEN "inv" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `inv r % (z:real^3)` th)
      (ASSUME `inv r % (z:real^3) IN sphere(vec 0,&1)`))) THEN
    EXISTS_TAC `inv(norm((q:real^3->real^3)(inv r % z))) % q(inv r % z)` THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r % (psi:real^3->real^3) x` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN
    SUBGOAL_THEN `norm((psi:real^3->real^3) x) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IN_SPHERE_0] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* N4 in general form, from SMT_SPHERE_COVERING_STATEMENT.                   *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_SECTION_GEN = prove
 (`SMT_SPHERE_COVERING_STATEMENT
   ==> !alpha1 eps1.
         &0 < alpha1 /\ alpha1 <= &1 / &32 /\ &0 < eps1 /\ eps1 <= alpha1 /\
         (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
            &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
            rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
            ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
                <= alpha1 /\
                (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                         lricci (cylinder_flow (&0)) y w w)
                     <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
         ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' r.
               &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
               rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
               &0 < r /\ sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
               IMAGE e' (sphere(vec 0,r)) SUBSET IMAGE e (rfs_neck_dom eps)
               ==> apx_section e (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
                               (IMAGE e' (sphere(vec 0,r)))`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "hyp") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x' (e':real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `e:real^3->A`; `e':real^3->A`;
                 `ei:A->real^3`] APX_PARAM_TRANSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `U = {v | v IN rfs_neck_dom eps /\
                       (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  SUBGOAL_THEN `!v. v IN U <=> v IN rfs_neck_dom eps /\
                              (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  (LABEL_TAC "Ueq") THENL [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN sphere(vec 0,&1) ==> r % w IN sphere(vec 0,r)` ASSUME_TAC
  THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID];
    ALL_TAC] THEN
  ABBREV_TAC `O = {w:real^3 | r % w IN U}` THEN
  SUBGOAL_THEN `!w:real^3. w IN O <=> r % w IN U` (LABEL_TAC "Oeq") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open (O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[LINEAR_SCALING];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0,&1) SUBSET (O:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "Oeq" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Ueq" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `r % (w:real^3) IN sphere(vec 0,r)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `sphere(vec 0,r) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `r % (w:real^3) IN sphere(vec 0,r)` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (e':real^3->A) (sphere(vec 0,r)) SUBSET
                   IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `r % (w:real^3) IN sphere(vec 0,r)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `q = ((ei:A->real^3) o (e':real^3->A)) o (\w:real^3. r % w)` THEN
  SUBGOAL_THEN `!w:real^3. w IN O
                  ==> (q:real^3->real^3) w IN rfs_neck_dom eps /\
                      (e:real^3->A)(q w) = e'(r % w) /\ ~(q w = vec 0)`
  (LABEL_TAC "qf") THENL
   [X_GEN_TAC `w:real^3` THEN USE_THEN "Oeq" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    USE_THEN "tr" (MP_TAC o SPEC `r % w:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `r % (w:real^3) IN U` THEN USE_THEN "Ueq" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN
    UNDISCH_TAC `(ei:A->real^3)((e':real^3->A)(r % w)) IN rfs_neck_dom eps` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (q:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN USE_THEN "Oeq" (fun th -> REWRITE_TAC[th]);
      MP_TAC(ISPECL [`O:real^3->bool`; `r:real`; `\x:real^3. x`] SMOOTH_MAP_ON_CMUL_OPEN) THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O ((\x:real^3. inv(norm x) % x) o (q:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(\x:real^3. inv(norm x) % x) o (q:real^3->real^3)` o
    REWRITE_RULE[SMT_SPHERE_COVERING_STATEMENT] o
    check (fun th -> concl th = `SMT_SPHERE_COVERING_STATEMENT`)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[smooth_near] THEN EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN REWRITE_TAC[NORM_EQ_0] THEN
      USE_THEN "qf" (MP_TAC o SPEC `w:real^3`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `sphere(vec 0,&1) SUBSET (O:real^3->bool)` THEN
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`w:real^3`; `h:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN O` ASSUME_TAC THENL
     [UNDISCH_TAC `sphere(vec 0,&1) SUBSET (O:real^3->bool)` THEN
      UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `r % (w:real^3) IN U` ASSUME_TAC THENL
     [USE_THEN "Oeq" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r % (w:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [UNDISCH_TAC `r % (w:real^3) IN U` THEN USE_THEN "Ueq" (fun th -> SIMP_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "qf" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`q:real^3->real^3`; `w:real^3`; `h:real^3`] APX_NORMALIZE_KERNEL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `c:real`)] THEN
    SUBGOAL_THEN `frechet_derivative (q:real^3->real^3) (at w) h =
                  frechet_derivative ((ei:A->real^3) o (e':real^3->A)) (at (r % w)) (r % h)`
    ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN
      MP_TAC(ISPECL [`\w:real^3. r % w`; `(ei:A->real^3) o (e':real^3->A)`;
                     `\h:real^3. r % h`;
                     `frechet_derivative ((ei:A->real^3) o (e':real^3->A)) (at (r % w))`;
                     `w:real^3`] DIFF_CHAIN_AT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
          BETA_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
          ASM_REWRITE_TAC[]];
        DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
        REWRITE_TAC[o_THM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3->real^3) w = (ei:A->real^3)((e':real^3->A)(r % w))` ASSUME_TAC
    THENL [EXPAND_TAC "q" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative ((ei:A->real^3) o (e':real^3->A)) (at (r % w)) (r % h) =
                  c % ei(e'(r % w))`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `frechet_derivative (q:real^3->real^3) (at w) h =
         frechet_derivative ((ei:A->real^3) o (e':real^3->A)) (at (r % w)) (r % h)`)] THEN
      REWRITE_TAC[ASSUME `frechet_derivative (q:real^3->real^3) (at w) h = c % q w`] THEN
      REWRITE_TAC[ASSUME `(q:real^3->real^3) w = (ei:A->real^3)((e':real^3->A)(r % w))`];
      ALL_TAC] THEN
    USE_THEN "tr" (MP_TAC o SPEC `r % w:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `r % (w:real^3) IN U` THEN USE_THEN "Ueq" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(w:real^3) dot h = &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM orthogonal]; ALL_TAC] THEN
    USE_THEN "hyp" (MP_TAC o MATCH_MP
      (SPECL [`alpha1:real`; `eps1:real`] APX_NECK_SECTION_KERNEL)) THEN
    DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
      `(ei:A->real^3)((e':real^3->A)(r % w))`; `r % w:real^3`; `r % h:real^3`; `c:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO] THEN
      REWRITE_TAC[GSYM(ASSUME `frechet_derivative ((ei:A->real^3) o (e':real^3->A))
                                 (at (r % w)) (r % h) = c % ei(e'(r % w))`)] THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    DISCH_THEN(X_CHOOSE_TAC `psi:real^3->real^3`)] THEN
  MATCH_MP_TAC APX_SECTION_FROM_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`O:real^3->bool`; `q:real^3->real^3`; `psi:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN USE_THEN "qf" (MP_TAC o SPEC `w:real^3`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN O` ASSUME_TAC THENL
   [UNDISCH_TAC `sphere(vec 0,&1) SUBSET (O:real^3->bool)` THEN
    UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "qf" (MP_TAC o SPEC `w:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* N4 in the statement form (alpha1 = 1/32 in N1).                           *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_SECTION = prove
 (`SMT_SPHERE_COVERING_STATEMENT ==> !w:A->bool. APX_NECK_SECTION_STATEMENT w`,
  DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  MP_TAC(ISPEC `(\x:A. T)` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &32`) THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &32`] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  EXISTS_TAC `min e1 (&1 / &32)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 / &32`; `min e1 (&1 / &32)`]
    (MP (INST_TYPE [`:A`,`:A`] APX_NECK_SECTION_GEN)
        (ASSUME `SMT_SPHERE_COVERING_STATEMENT`))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "gen") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "gen" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `x:A`; `x':A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The core of a cap (for N5b and N6).  Its closure is compact               *)
(* and lies in the chart image, the core is open and nonempty, the boundary  *)
(* sphere lies in the closure, and the frontier of the closure lies in the   *)
(* boundary sphere.  Ball charts and twisted charts (RP^3 minus a ball).     *)
(* ------------------------------------------------------------------------- *)

let APX_CORE_FRONTIER = prove
 (`!top (Y:A->bool) K S.
        open_in top Y /\ top closure_of Y SUBSET K /\ K DIFF Y SUBSET S
        ==> top frontier_of (top closure_of Y) SUBSET S`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of; CLOSURE_OF_CLOSURE_OF] THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET top interior_of (top closure_of Y)` MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM SET_TAC[]]);;

let APX_ANNULUS_SPHERE_CLOSURE = prove
 (`!a b. &0 < a /\ a < b ==> sphere(vec 0:real^N,b) SUBSET closure(annulus a b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_SPHERE_0; CLOSURE_APPROACHABLE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = min d (b - a)` THEN
  SUBGOAL_THEN `&0 < m /\ m <= d /\ m <= b - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(&1 - m / (&2 * b)) % u:real^N` THEN
  ASM_REWRITE_TAC[NORM_MUL; dist; VECTOR_ARITH `(&1 - c) % u - u:real^N = --(c % u)`;
                  NORM_NEG] THEN
  SUBGOAL_THEN `m / (&2 * b) * b = m / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m / (&2 * b) /\ m / (&2 * b) < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t /\ t < &1 ==> abs(&1 - t) = &1 - t`;
               REAL_ARITH `&0 < t ==> abs t = t`] THEN
  ASM_REWRITE_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC);;

let APX_BALL_CORE_TOP = prove
 (`!top atlas (b:real^3->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_param top atlas (ball(vec 0,&2)) b
        ==> compact_in top (top closure_of (IMAGE b (ball(vec 0,&1)))) /\
            top closure_of (IMAGE b (ball(vec 0,&1))) SUBSET IMAGE b (ball(vec 0,&2)) /\
            open_in top (IMAGE b (ball(vec 0,&1))) /\
            ~(IMAGE b (ball(vec 0,&1)) = {}) /\
            IMAGE b (sphere(vec 0,&1)) SUBSET top closure_of (IMAGE b (ball(vec 0,&1))) /\
            top frontier_of (top closure_of (IMAGE b (ball(vec 0,&1))))
            SUBSET IMAGE b (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `ball(vec 0:real^3,&2)`; `b:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `bi:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN CONJ_TAC THEN GEN_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (b:real^3->A) (cball(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (b:real^3->A) (ball(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (b:real^3->A) (ball(vec 0,&1))) SUBSET
                IMAGE b (cball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,&2))`; `top:A topology`;
                   `b:real^3->A`; `ball(vec 0:real^3,&1)`]
                  CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`;
                 CLOSURE_BALL; REAL_LT_01] THEN
    MATCH_MP_TAC(SET_RULE `(t:A->bool) SUBSET s ==> s SUBSET u ==> t SUBSET u`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SPHERE_SUBSET_CBALL];
    MATCH_MP_TAC APX_CORE_FRONTIER THEN
    EXISTS_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,&2)`; `cball(vec 0:real^3,&1)`;
                   `ball(vec 0:real^3,&1)`; `b:real^3->A`] APX_PARAM_IMAGE_DIFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CBALL_DIFF_BALL; SUBSET_REFL]]);;

let APX_TWIST_SPHERE = prove
 (`!y:real^3. norm y = &1 / &2 ==> norm(rfs_twist y) = &2`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV;
    REAL_ABS_POW; REAL_ABS_NORM] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let APX_TWISTED_CORE_TOP = prove
 (`!top atlas (p:real^3->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        rfs_twisted_chart top atlas p
        ==> compact_in top (top closure_of (IMAGE p (annulus (&1 / &2) (&2)))) /\
            top closure_of (IMAGE p (annulus (&1 / &2) (&2))) SUBSET
            IMAGE p (annulus (&1 / &4) (&4)) /\
            open_in top (IMAGE p (annulus (&1 / &2) (&2))) /\
            ~(IMAGE p (annulus (&1 / &2) (&2)) = {}) /\
            IMAGE p (sphere(vec 0,&2)) SUBSET
            top closure_of (IMAGE p (annulus (&1 / &2) (&2))) /\
            top frontier_of (top closure_of (IMAGE p (annulus (&1 / &2) (&2))))
            SUBSET IMAGE p (sphere(vec 0,&2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_twisted_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "id") (LABEL_TAC "loc")))) THEN
  ABBREV_TAC `CA = cball(vec 0:real^3,&2) DIFF ball(vec 0,&1 / &2)` THEN
  SUBGOAL_THEN
   `(CA:real^3->bool) SUBSET annulus (&1 / &4) (&4) /\
    annulus (&1 / &2) (&2) SUBSET (CA:real^3->bool) /\
    (annulus (&1 / &2) (&2):real^3->bool) SUBSET annulus (&1 / &4) (&4) /\
    sphere(vec 0:real^3,&2) SUBSET CA /\ sphere(vec 0:real^3,&2) SUBSET annulus (&1 / &4) (&4) /\
    CA DIFF annulus (&1 / &2) (&2) SUBSET sphere(vec 0,&1 / &2) UNION sphere(vec 0,&2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "CA" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0; annulus;
                IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (annulus (&1 / &4) (&4)),top)
                               (p:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_ANNULUS; OPEN_BALL; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(y:real^3,r)`; `p:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->A) CA)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &4) (&4):real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    EXPAND_TAC "CA" THEN MATCH_MP_TAC COMPACT_DIFF THEN
    REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (p:real^3->A) (annulus (&1 / &2) (&2)))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (p:real^3->A) (ball(y,r) INTER annulus (&1 / &2) (&2))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(y:real^3,r)`] THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_ANNULUS; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))) SUBSET
                IMAGE p CA` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `IMAGE (p:real^3->A) CA` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (p:real^3->A) CA` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `basis 1:real^3` THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MP_TAC(ISPECL [`subtopology euclidean (annulus (&1 / &4) (&4):real^3->bool)`;
                   `top:A topology`; `p:real^3->A`; `annulus (&1 / &2) (&2):real^3->bool`]
                  CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`] THEN
    MATCH_MP_TAC(SET_RULE `(t:A->bool) SUBSET s ==> s SUBSET u ==> t SUBSET u`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPECL [`&1 / &2`; `&2`] (INST_TYPE [`:3`,`:N`] APX_ANNULUS_SPHERE_CLOSURE)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM SET_TAC[];
    MATCH_MP_TAC APX_CORE_FRONTIER THEN EXISTS_TAC `IMAGE (p:real^3->A) CA` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE] THEN X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN sphere(vec 0,&1 / &2) \/ y IN sphere(vec 0,&2)` MP_TAC THENL
     [UNDISCH_TAC `(q:A) = p(y:real^3)` THEN DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `~((y:real^3) IN annulus (&1 / &2) (&2))` MP_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC `~(?x. (p:real^3->A) y = p x /\ x IN annulus (&1 / &2) (&2))` THEN
        REWRITE_TAC[] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:real^3) IN CA` THEN
        UNDISCH_TAC `CA DIFF annulus (&1 / &2) (&2) SUBSET
                     sphere(vec 0:real^3,&1 / &2) UNION sphere(vec 0,&2)` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `rfs_twist y` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "id" (MP_TAC o SPECL [`y:real^3`; `rfs_twist y`]) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [ASM SET_TAC[];
            UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1 / &2)` THEN
            REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
            DISCH_THEN(MP_TAC o MATCH_MP APX_TWIST_SPHERE) THEN REAL_ARITH_TAC];
          SIMP_TAC[]];
        UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1 / &2)` THEN
        REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[APX_TWIST_SPHERE]];
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* N5b.  The core of a (C,eps)-cap, with its                                 *)
(* boundary eps-neck e', and the closed core never inside an eps-neck: the  *)
(* boundary sphere would be a section (N4) bounding a compact region with   *)
(* nonempty interior, against N5.                                            *)
(* ------------------------------------------------------------------------- *)

let APX_CAP_CORE = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
        hausdorff_space top /\ rfs_cap (top,atlas) g C eps U Y
        ==> ?z' e'. rfs_neck (top,atlas) g eps z' e' /\
                    compact_in top (top closure_of Y) /\
                    top closure_of Y SUBSET U /\
                    open_in top Y /\ ~(Y = {}) /\
                    IMAGE e' (sphere(vec 0,&1)) SUBSET top closure_of Y /\
                    top frontier_of (top closure_of Y) SUBSET IMAGE e' (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`z':A`; `e':real^3->A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`]
                  APX_BALL_CORE_TOP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_ball_chart top (atlas:((A->bool)#(A->real^3))->bool) (b:real^3->A)` THEN
      REWRITE_TAC[mfd_ball_chart];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`z':A`; `e':real^3->A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`]
                  APX_TWISTED_CORE_TOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
    ASM_REWRITE_TAC[]]);;

let APX_UNIT_SPHERE_NECK_DOM = prove
 (`!eps. &0 < eps ==> sphere(vec 0,&1) SUBSET rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN X_GEN_TAC `y:real^3` THEN
  DISCH_TAC THEN
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL; apx_sval] THEN
  ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO; GSYM NORM_EQ_0] THEN
  SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC]);;

(* N5b in the statement form. *)

let APX_NO_CAP_IN_NECK = prove
 (`SMT_SPHERE_COVERING_STATEMENT ==> !w:A->bool. APX_NO_CAP_IN_NECK_STATEMENT w`,
  DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[APX_NO_CAP_IN_NECK_STATEMENT] THEN
  MP_TAC(SPEC `w:A->bool` (MP APX_NECK_SECTION (ASSUME `SMT_SPHERE_COVERING_STATEMENT`))) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                APX_CAP_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':A` (X_CHOOSE_THEN `e':real^3->A` STRIP_ASSUME_TAC)) THEN
  USE_THEN "sec" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_01; APX_UNIT_SPHERE_NECK_DOM] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (Y:A->bool)` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[GSYM rfs_neck_dom]
   (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
            `exp(--(inv(sqrt(&2) * eps)))`; `exp(inv(sqrt(&2) * eps))`;
            `IMAGE (e':real^3->A) (sphere(vec 0,&1))`; `top closure_of (Y:A->bool)`]
           APX_SECTION_NOT_BOUNDING_POS)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET top interior_of (top closure_of Y)` MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Joinability inside a cap (for N6).  Points of the image of                *)
(* a connected open set under a smooth map (a parametrization, or a map that *)
(* is locally a parametrization, as twisted charts are) are joined by C^1    *)
(* curves inside the image; hence any two points of a cap U are joined       *)
(* inside U (through an anchor point in the collar).                         *)
(* ------------------------------------------------------------------------- *)

let APX_SMOOTH_JOINABLE_IN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A) TT.
        smooth_manifold_atlas top atlas /\ open s /\ connected s /\
        continuous_map (subtopology euclidean s,top) p /\
        mfd_smooth_map (open_set_atlas s) atlas s p /\ IMAGE p s SUBSET TT
        ==> !v w. v IN s /\ w IN s ==> mfd_joinable_in (top,atlas) TT (p v) (p w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (s:real^N->bool)`; `open_set_atlas (s:real^N->bool)`;
                 `v:real^N`; `w:real^N`] MFD_JOINABLE_CONNECTED) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY;
               TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[mfd_joinable] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (c:real->real^N) t IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (subtopology euclidean s,open_set_atlas s)
                   (c:real->real^N) (&0) (&1)` THEN
    REWRITE_TAC[mfd_c1_curve; continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_joinable_in] THEN EXISTS_TAC `(p:real^N->A) o (c:real->real^N)` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (s:real^N->bool)`;
                          `open_set_atlas (s:real^N->bool)`; `s:real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; REAL_LT_01; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[OPEN_IN_TOPSPACE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p:real^N->A) s SUBSET TT` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> IMAGE (f:real^N->A) s SUBSET t ==> f x IN t`) THEN
    ASM_SIMP_TAC[]]);;

(* Maps that are locally parametrizations are continuous and smooth. *)

let APX_LOCAL_PARAM_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (p:real^N->A).
        smooth_manifold_atlas top atlas /\ open W /\
        (!y. y IN W ==> ?r. &0 < r /\ ball(y,r) SUBSET W /\
                            mfd_param top atlas (ball(y,r)) p)
        ==> continuous_map (subtopology euclidean W,top) p /\
            mfd_smooth_map (open_set_atlas W) atlas W p`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean W,top) (p:real^N->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^N,r)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_BALL; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^N->bool) SUBSET t ==> t INTER s = s`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `ball(y:real^N,r)`; `p:real^N->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
  EXISTS_TAC `subtopology euclidean (W:real^N->bool)` THEN EXISTS_TAC `top:A topology` THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MESON_TAC[OPEN_IN_TOPSPACE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(y:real^N,r)` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_BALL; CENTRE_IN_BALL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `ball(y:real^N,r)`; `p:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_smooth_map (open_set_atlas (ball(y:real^N,r)))
                 (atlas:((A->bool)#(A->real^N))->bool) (ball(y,r)) (p:real^N->A)` THEN
  REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `c:(real^N->bool)#(real^N->real^N)` THEN
    X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    MP_TAC(SPECL [`(ball(y:real^N,r),(\x:real^N. x))`; `c':(A->bool)#(A->real^N)`] th)) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID] THEN
  ASM_SIMP_TAC[SET_RULE `(s:real^N->bool) SUBSET t ==> t INTER s = s`; INTER_IDEMPOT] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (W:real^N->bool)`; `open_set_atlas (W:real^N->bool)`;
                 `(W:real^N->bool,(\x:real^N. x))`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(y:real^N,r))`;
                 `open_set_atlas (ball(y:real^N,r))`;
                 `(ball(y:real^N,r),(\x:real^N. x))`] MFDM_CHART) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_BALL; RFB_OPEN_SET_ATLAS_CASES; FST; SND; IMAGE_ID] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let APX_PARAM_JOINABLE_IN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (p:real^N->A) TT.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s p /\ connected s /\
        IMAGE p s SUBSET TT
        ==> !v w. v IN s /\ w IN s ==> mfd_joinable_in (top,atlas) TT (p v) (p w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC APX_SMOOTH_JOINABLE_IN THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `p:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let APX_CAP_JOINABLE = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
        rfs_cap (top,atlas) g C eps U Y
        ==> !y1 y2. y1 IN U /\ y2 IN U ==> mfd_joinable_in (top,atlas) U y1 y2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
  SUBGOAL_THEN `?anc:A. !y. y IN U ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U y anc` MP_TAC THENL
   [UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
    REWRITE_TAC[rfs_cap] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `ball(vec 0:real^3,&2)`; `b:real^3->A`] GRGD_PARAM_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `mfd_ball_chart top (atlas:((A->bool)#(A->real^3))->bool)
                       (b:real^3->A)` THEN REWRITE_TAC[mfd_ball_chart];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `bi:A->real^3` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `v0 = (&3 / &2) % basis 1:real^3` THEN
      SUBGOAL_THEN `norm(v0:real^3) = &3 / &2` ASSUME_TAC THENL
       [EXPAND_TAC "v0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `(v0:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_BALL_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(b:real^3->A) v0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET U` THEN
          UNDISCH_TAC `(v0:real^3) IN ball(vec 0,&2)` THEN SET_TAC[];
          REWRITE_TAC[IN_IMAGE] THEN
          DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(v0:real^3) = v` MP_TAC THENL
           [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(bi:A->real^3)((b:real^3->A) v0)` THEN
            CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
            ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
            DISCH_THEN SUBST_ALL_TAC THEN
            UNDISCH_TAC `(v:real^3) IN cball(vec 0,&1)` THEN
            ASM_REWRITE_TAC[IN_CBALL_0] THEN REAL_ARITH_TAC]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(b:real^3->A) v0` THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(y:A) IN IMAGE (b:real^3->A) (cball(vec 0,&1))` THENL
       [UNDISCH_TAC `(y:A) IN IMAGE (b:real^3->A) (cball(vec 0,&1))` THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `ball(vec 0:real^3,&2)`; `b:real^3->A`; `U:A->bool`]
                      APX_PARAM_JOINABLE_IN) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[CONNECTED_BALL] THEN
          UNDISCH_TAC `mfd_ball_chart top (atlas:((A->bool)#(A->real^3))->bool)
                         (b:real^3->A)` THEN REWRITE_TAC[mfd_ball_chart];
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        SUBGOAL_THEN `(y:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `rfs_neck_dom eps`; `e:real^3->A`; `U:A->bool`]
                      APX_PARAM_JOINABLE_IN) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3] THEN
          CONJ_TAC THENL
           [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z (e:real^3->A)` THEN
            SIMP_TAC[rfs_neck; rfs_neck_dom];
            REWRITE_TAC[GSYM rfs_neck_dom] THEN ASM SET_TAC[]];
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    (* twisted case *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus (&1 / &4) (&4):real^3->bool`; `p:real^3->A`]
                  APX_LOCAL_PARAM_SMOOTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
      UNDISCH_TAC `rfs_twisted_chart top (atlas:((A->bool)#(A->real^3))->bool)
                     (p:real^3->A)` THEN SIMP_TAC[rfs_twisted_chart];
      STRIP_TAC] THEN
    ABBREV_TAC `v0 = &3 % basis 1:real^3` THEN
    SUBGOAL_THEN `norm(v0:real^3) = &3` ASSUME_TAC THENL
     [EXPAND_TAC "v0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `(v0:real^3) IN annulus (&1 / &4) (&4)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->A) v0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4)) SUBSET U` THEN
        UNDISCH_TAC `(v0:real^3) IN annulus (&1 / &4) (&4)` THEN SET_TAC[];
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `rfs_twisted_chart top (atlas:((A->bool)#(A->real^3))->bool)
                       (p:real^3->A)` THEN
        REWRITE_TAC[rfs_twisted_chart] THEN
        DISCH_THEN(MP_TAC o SPECL [`v0:real^3`; `v:real^3`] o CONJUNCT1) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [UNDISCH_TAC `norm(v:real^3) <= &2` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          UNDISCH_TAC `&1 / &2 <= norm(v:real^3)` THEN
          ASM_REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW;
                          REAL_ABS_NORM] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(p:real^3->A) v0` THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:A) IN IMAGE (p:real^3->A) {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2}`
    THENL
     [UNDISCH_TAC `(y:A) IN IMAGE (p:real^3->A)
                     {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2}` THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `annulus (&1 / &4) (&4):real^3->bool`; `p:real^3->A`; `U:A->bool`]
                    APX_SMOOTH_JOINABLE_IN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_ANNULUS; APX_CONNECTED_ANNULUS3]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(y:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`; `U:A->bool`]
                    APX_PARAM_JOINABLE_IN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z (e:real^3->A)` THEN
          SIMP_TAC[rfs_neck; rfs_neck_dom];
          REWRITE_TAC[GSYM rfs_neck_dom] THEN ASM SET_TAC[]];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `anc:A`) THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `y1:A`; `anc:A`; `y2:A`] MFD_JOINABLE_IN_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `anc:A`; `y2:A`] MFD_JOINABLE_IN_SYM) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Re-centring a neck (for N6).  The dilation v |-> c v with                 *)
(* c = |y1| shifts the s-coordinate by s(y1) and preserves the cylinder      *)
(* metric; pulling a dl-neck back by it gives a neck centred at e y1.        *)
(* ------------------------------------------------------------------------- *)

let APX_SVAL_SCALE = prove
 (`!c v:real^3. &0 < c /\ ~(v = vec 0) ==> apx_sval(c % v) = sqrt(&2) * log c + apx_sval v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; LOG_MUL; NORM_POS_LT] THEN
  REAL_ARITH_TAC);;

let APX_DILATE_DOM = prove
 (`!dl K y1:real^3.
        &0 < dl /\ &4 <= K /\ y1 IN rfs_neck_dom dl /\ abs(apx_sval y1) <= &3 / (&4 * dl)
        ==> !v. v IN rfs_neck_dom (K * dl) ==> norm y1 % v IN rfs_neck_dom dl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y1:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y1:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; APX_SVAL_SCALE] THEN
  SUBGOAL_THEN `sqrt(&2) * log(norm(y1:real^3)) = apx_sval y1` SUBST1_TAC THENL
   [REWRITE_TAC[apx_sval]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(K * dl) <= inv(&4 * dl)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 / (&4 * dl) + inv(&4 * dl) = inv dl` MP_TAC THENL
   [UNDISCH_TAC `&0 < dl` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_MATRIX_SCALING = prove
 (`!c. matrix(\x:real^N. c % x) = c %% mat 1`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\x:real^N. c % x) = (\x. (c %% mat 1:real^N^N) ** x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]);;

let APX_MPULLBACK_DILATE = prove
 (`!(G:real^N->real^N^N) c v. mpullback (\w. c % w) G v = (c pow 2) %% G(c % v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\w:real^N. c % w) (at v) = (\w. c % w)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
    ALL_TAC] THEN
  REWRITE_TAC[APX_MATRIX_SCALING; TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_MUL_LMUL;
              MATRIX_MUL_RMUL; MATRIX_MUL_LID; MATRIX_MUL_RID; MATRIX_CMUL_ASSOC] THEN
  REWRITE_TAC[REAL_POW_2]);;

let APX_MPULLBACK_DILATE_COMPOSE = prove
 (`!(Fm:real^N->real^N) G c v.
        Fm differentiable (at (c % v))
        ==> mpullback (Fm o (\w. c % w)) G v = (c pow 2) %% mpullback Fm G (c % v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN `frechet_derivative ((Fm:real^N->real^N) o (\w. c % w)) (at v) =
                frechet_derivative Fm (at (c % v)) o (\w. c % w)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fm:real^N->real^N) (at (c % v)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_SCALING; APX_MATRIX_SCALING] THEN
  REWRITE_TAC[MATRIX_MUL_RMUL; MATRIX_MUL_RID; TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL;
              MATRIX_CMUL_ASSOC; REAL_POW_2]);;

let APX_RFS_PULLBACK_DILATE = prove
 (`!top atlas (g:A->real^N^N) s t (e:real^N->A) c.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        mfd_param top atlas t (e o (\w. c % w)) /\ (!w. w IN t ==> c % w IN s)
        ==> !v. v IN t ==> rfs_pullback atlas (e o (\w. c % w)) g v =
                          (c pow 2) %% rfs_pullback atlas e g (c % v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c % v:real^N) IN s` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->A)(c % v) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^N->A) s SUBSET topspace top` THEN
    UNDISCH_TAC `(c % v:real^N) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A)(c % v)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A)(c % v))`,
           `ch:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `t:real^N->bool`; `(e:real^N->A) o (\w. c % w)`; `V:A->bool`;
                 `psi:A->real^N`; `v:real^N`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `s:real^N->bool`; `e:real^N->A`; `V:A->bool`;
                 `psi:A->real^N`; `c % v:real^N`] APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC APX_MPULLBACK_DILATE_COMPOSE THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^N`
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on]) ASSUME_TAC)) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{z | z IN s /\ (e:real^N->A) z IN V}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let APX_RECENTRE_ARITH = prove
 (`!lam sd dl c1 K.
        &0 < dl /\ &0 <= sd /\ sd < dl /\ abs(lam - &1) <= c1 * dl /\
        c1 * dl <= &1 / &4 /\ &4 + &2 * c1 = K
        ==> &0 <= lam * sd + abs(lam - &1) * sqrt(&3) /\
            lam * sd + abs(lam - &1) * sqrt(&3) < K * dl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 / &4 <= lam /\ lam <= &5 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3) <= &2 /\ &0 <= sqrt(&3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam * sd <= &5 / &4 * sd` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(lam - &1) * sqrt(&3) <= (c1 * dl) * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lam * sd /\ &0 <= abs(lam - &1) * sqrt(&3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&4 + &2 * c1 = K` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REAL_ARITH_TAC);;

(* Re-centring: a dl-neck re-centred at a level |s0| <= 3/(4 dl) is a       *)
(* K dl-neck, K = 4 + 576(1 + |K0|) universal.                               *)

let APX_NECK_RECENTRE_GEN = prove
 (`!K0. (!y:real^3. ~(y = vec 0) ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2)
        ==> !top atlas (g:A->real^3^3) dl x (e:real^3->A) y1.
              &0 < dl /\ (&4 + &576 * (&1 + abs K0)) * dl <= &1 / &2 /\
              riemannian_metric atlas g /\ rfs_neck (top,atlas) g dl x e /\
              y1 IN rfs_neck_dom dl /\ abs(apx_sval y1) <= &3 / (&4 * dl)
              ==> rfs_neck (top,atlas) g ((&4 + &576 * (&1 + abs K0)) * dl) (e y1)
                           (e o (\w. norm y1 % w))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `K = &4 + &576 * (&1 + abs K0)` THEN
  ABBREV_TAC `c1 = &288 * (&1 + abs K0)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&4 + &2 * c1 = K /\ &288 <= c1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "c1"] THEN MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= K /\ &0 < K * dl /\ &40 * dl <= &1 /\ c1 * dl <= &1 / &4 /\
                dl <= K * dl`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `K * dl = &4 * dl + &2 * (c1 * dl)` ASSUME_TAC THENL
     [UNDISCH_TAC `&4 + &2 * c1 = K` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&288 * dl <= c1 * dl` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) dl x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck; rfs_close_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `H = \z. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) z` THEN
  SUBGOAL_THEN `~(y1:real^3 = vec 0)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `y1:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN rfs_neck_dom (K * dl) ==> norm(y1:real^3) % w IN rfs_neck_dom dl`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_DILATE_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = norm(y1:real^3)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real`; `exp(--(inv(sqrt(&2) * K * dl)))`; `exp(inv(sqrt(&2) * K * dl))`]
                (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_SCALING_ANNULUS)) THEN
  ASM_REWRITE_TAC[GSYM rfs_neck_dom] THEN
  ABBREV_TAC `T' = annulus (c * exp(--(inv(sqrt(&2) * K * dl))))
                           (c * exp(inv(sqrt(&2) * K * dl))):real^3->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(T':real^3->bool) SUBSET rfs_neck_dom dl /\ open T'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (rfs_neck_dom (K * dl)) T' (\x:real^3. c % x)
                   (\x. inv c % x)` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (\x:real^3. c % x) (rfs_neck_dom (K * dl)) = T'` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom (K * dl))
                  ((e:real^3->A) o (\w. c % w))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`rfs_neck_dom dl`; `T':real^3->bool`; `\x:real^3. inv c % x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `lam = lscalar (H:real^3->real^3^3) y1` THEN
  MP_TAC(ISPECL [`K0:real`; `dl:real`; `&0`; `d:real`; `H:real^3->real^3^3`; `y1:real^3`]
                APX_NECK_EARLIER_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_0; REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y1) = R * lam`
  ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN EXPAND_TAC "H" THEN
    MP_TAC(ISPECL [`rfs_neck_dom dl`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                   `R:real`; `y1:real^3`] LSCALAR_SCALE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom dl`; `e:real^3->A`; `y1:real^3`]
                  APX_PULLBACK_SCALAR_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; o_THM] THEN EXISTS_TAC `inv c % (y1:real^3)` THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 REAL_ARITH `&0 < c ==> abs c = c`; REAL_MUL_LINV];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0)) (H:real^3->real^3^3) y1` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `rfs_neck_dom dl` THEN ASM_REWRITE_TAC[APX_NECK_CYL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d < dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(dl pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LT_EQ; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `sqrt d`; `dl:real`; `c1:real`; `K:real`]
                APX_RECENTRE_ARITH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; STRIP_TAC] THEN
  EXISTS_TAC `(lam * sqrt d + abs(lam - &1) * sqrt(&3)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `metric_field T' (H:real^3->real^3^3) /\ metric_field T' (cylinder_flow (&0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom (K * dl)) (mpullback (\x:real^3. c % x) H)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`T':real^3->bool`; `\x:real^3. inv c % x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
      (\w. (R * lam) %% rfs_pullback atlas ((e:real^3->A) o (\w. c % w)) (g:A->real^3^3) w) v =
    lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
      (\w. lam %% mpullback (\x:real^3. c % x) (H:real^3->real^3^3) w) v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom (K * dl)` THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom dl`; `rfs_neck_dom (K * dl)`;
                   `e:real^3->A`; `c:real`] APX_RFS_PULLBACK_DILATE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `w:real^3`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[APX_MPULLBACK_DILATE] THEN EXPAND_TAC "H" THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
      (mpullback (\x:real^3. c % x) (H:real^3->real^3^3)) v <= d`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
        (mpullback (\x:real^3. c % x) (H:real^3->real^3^3)) v =
      lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0)) H (c % v)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg (K * dl))
                    (mpullback (\x:real^3. c % x) (cylinder_flow (&0)))
                    (mpullback (\x:real^3. c % x) (H:real^3->real^3^3)) v` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom (K * dl)` THEN
        ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_CYL0_DILATION THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[APX_SVAL_NECK_DOM];
        MP_TAC(ISPECL [`rfs_kreg (K * dl)`; `T':real^3->bool`; `rfs_neck_dom (K * dl)`;
                       `\x:real^3. c % x`; `\x:real^3. inv c % x`; `cylinder_flow (&0)`;
                       `H:real^3->real^3^3`; `v:real^3`] LCK_DIST2_PULLBACK) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0)) (H:real^3->real^3^3) (c % v)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom dl` THEN
      ASM_SIMP_TAC[APX_NECK_CYL_FIELD] THEN MATCH_MP_TAC APX_KREG_MONO THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg (K * dl)`; `rfs_neck_dom (K * dl)`; `cylinder_flow (&0)`;
                 `mpullback (\x:real^3. c % x) (H:real^3->real^3^3)`; `lam:real`; `v:real^3`]
                LCK_DIST_RESCALE) THEN
  ASM_REWRITE_TAC[APX_NECK_CYL_FIELD; DIMINDEX_3] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
                  (\w. lam %% mpullback (\x:real^3. c % x) (H:real^3->real^3^3) w) v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom (K * dl)` THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN
    MP_TAC(ISPECL [`rfs_neck_dom (K * dl)`; `mpullback (\x:real^3. c % x) (H:real^3->real^3^3)`;
                   `lam:real`] RFB_METRIC_FIELD_CMUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
                 (\w. lam %% mpullback (\x:real^3. c % x) (H:real^3->real^3^3) w) v) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * sqrt(lck_dist2 (rfs_kreg (K * dl)) (cylinder_flow (&0))
                   (mpullback (\x:real^3. c % x) (H:real^3->real^3^3)) v) +
                abs(lam - &1) * sqrt(&3)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_MONO_LE]]);;

(* ------------------------------------------------------------------------- *)
(* N6 helpers.  Distance lower bounds from all curves, scalar                *)
(* comparability along a neck, a cap meeting the middle half of a long neck *)
(* lies within s-distance 4C of the meeting point (diameter clause, exit    *)
(* bound), and the boundary sphere of the cap lies in the eps-slab of the   *)
(* re-centred neck (small central sphere of the boundary neck).             *)
(* ------------------------------------------------------------------------- *)

let APX_DIST_GE_CURVES = prove
 (`!top atlas (g:A->real^N^N) x y b.
        mfd_joinable (top,atlas) x y /\
        (!gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y
                 ==> b <= mfd_length atlas g gamma (&0) (&1))
        ==> b <= mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y` THEN
    REWRITE_TAC[mfd_joinable; GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN MESON_TAC[];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let APX_NECK_SCALAR_COMPARE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
        y IN rfs_neck_dom eps /\
        abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
        <= &1 / &2
        ==> mfd_scalar atlas g x / &2 <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &3 / &2 * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `rfs_pullback atlas (e:real^3->A) (g:A->real^3^3)`;
                 `mfd_scalar atlas (g:A->real^3^3) x`; `y:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`]
                APX_PULLBACK_SCALAR_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
  UNDISCH_TAC `abs(mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y) /
                   mfd_scalar atlas g x - &1) <= &1 / &2` THEN
  UNDISCH_TAC `&0 < mfd_scalar atlas (g:A->real^3^3) x` THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) y)`,`a:real`) THEN
  SPEC_TAC(`mfd_scalar atlas (g:A->real^3^3) x`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a / b - &1 = (a - b) / b` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `abs((a - b) / b) <= &1 / &2` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < b ==> abs b = b`; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let APX_SECTION_MONO = prove
 (`!(E:real^3->A) r1 r2 r1' r2' S.
        r1' <= r1 /\ r2 <= r2' /\ apx_section E r1 r2 S ==> apx_section E r1' r2' S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_section] THEN STRIP_TAC THEN
  EXISTS_TAC `u:real^3->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
    can (find_term (fun t -> t = `r1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_CAP_NEAR = prove
 (`!top atlas (g:A->real^3^3) C eps U Y dl x (e:real^3->A) yp.
        hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g dl x e /\ rfs_cap (top,atlas) g C eps U Y /\
        &0 < C /\ &0 < dl /\ &8 * C * dl <= &1 /\
        (!y z. y IN rfs_neck_dom dl /\ z IN rfs_neck_dom dl
               ==> mfd_joinable (top,atlas) (e y) (e z) /\
                   &1 / &2 * inv(sqrt(mfd_scalar atlas g x)) *
                   min (abs(apx_sval y - apx_sval z))
                       (&2 * inv dl - abs(apx_sval y) - abs(apx_sval z))
                   <= mfd_dist (top,atlas) g (e y) (e z) /\
                   (!gamma a b. mfd_c1_curve (top,atlas) gamma a b /\ gamma a = e y /\
                                ~(gamma b IN IMAGE e (rfs_neck_dom dl))
                                ==> &1 / &2 * inv(sqrt(mfd_scalar atlas g x)) *
                                    (inv dl - abs(apx_sval y))
                                    <= mfd_length atlas g gamma a b)) /\
        (!y. y IN rfs_neck_dom dl
             ==> mfd_scalar atlas g x / &2 <= mfd_scalar atlas g (e y)) /\
        yp IN rfs_neck_dom dl /\ abs(apx_sval yp) < inv(&2 * dl) /\ e yp IN U
        ==> !q. q IN U ==> ?y. y IN rfs_neck_dom dl /\ q = e y /\
                               abs(apx_sval y - apx_sval yp) < &4 * C`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "n2")
    (CONJUNCTS_THEN2 (LABEL_TAC "sc") STRIP_ASSUME_TAC))))))))) THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl x (e:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `r = inv(sqrt R)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y`) THEN
  REWRITE_TAC[rfs_cap; rfs_sup_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "rpos")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `dU:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "diam")))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `dR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ratio")))
    (K ALL_TAC))))))) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) yp)` ASSUME_TAC THENL
   [USE_THEN "rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `R / &2 <= sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) yp)` THEN
    CONJ_TAC THENL [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `dR * mfd_scalar atlas (g:A->real^3^3) ((e:real^3->A) yp)` THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y2:A` THEN DISCH_TAC THEN
      USE_THEN "ratio" (MP_TAC o SPEC
        `mfd_scalar atlas (g:A->real^3^3) y2 / mfd_scalar atlas g ((e:real^3->A) yp)`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`y2:A`; `(e:real^3->A) yp`] THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))) <= &2 * C * r`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))) <= &2 * r`
    MP_TAC THENL
     [SUBGOAL_THEN `&0 < sqrt R / &2 /\ sqrt R / &2 <=
                    sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
          MATCH_MP_TAC REAL_LE_RSQRT THEN
          REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(SPECL [`sqrt R / &2`;
                    `sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))`] REAL_LE_INV2) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
      EXPAND_TAC "r" THEN
      SUBGOAL_THEN `~(sqrt R = &0)` MP_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD];
      DISCH_TAC THEN
      MP_TAC(SPECL [`C:real`; `inv(sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)))`;
                    `&2 * r`] REAL_LE_LMUL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U ((e:real^3->A) yp) q`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                  APX_CAP_JOINABLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) yp) q < &2 * C * r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U ((e:real^3->A) yp) q` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dU:real` THEN CONJ_TAC THENL
     [USE_THEN "diam" MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(CONJ (ASSUME `(e:real^3->A) yp IN U`) (ASSUME `(q:A) IN U`)) THEN
      MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * C <= inv(&2 * dl) /\ &2 * inv(&2 * dl) = inv dl` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `inv(&2 * dl) = &1 / (&2 * dl)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &2 * dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < dl` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN IMAGE (e:real^3->A) (rfs_neck_dom dl)` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 * r * (inv dl - abs(apx_sval (yp:real^3))) <=
                  mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) yp) q` MP_TAC THENL
     [MATCH_MP_TAC APX_DIST_GE_CURVES THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_IN_IMP THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `gamma:real->A` THEN STRIP_TAC THEN
        USE_THEN "n2" (MP_TAC o SPECL [`yp:real^3`; `yp:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `r * (&4 * C) < r * (inv dl - abs(apx_sval (yp:real^3)))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) yp) q < &2 * C * r` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `yq:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `yq:real^3` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "n2" (MP_TAC o SPECL [`yp:real^3`; `yq:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) yp) q < &2 * C * r` THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = min (abs(apx_sval yp - apx_sval (yq:real^3)))
                      (&2 * inv dl - abs(apx_sval yp) - abs(apx_sval yq))` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) yp) (e yq)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `m < &4 * C` ASSUME_TAC THENL
   [SUBGOAL_THEN `r * m < r * (&4 * C)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(yq:real^3)) < inv dl` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  UNDISCH_TAC `m < &4 * C` THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC);;

let APX_SVAL_UNIT = prove
 (`!u:real^3. norm u = &1 ==> apx_sval u = &0`,
  SIMP_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]);;

let APX_SPHERE_NEAR = prove
 (`!top atlas (g:A->real^3^3) eps dl0 z' (e':real^3->A) x0 (e0:real^3->A) u0.
        &0 < eps /\ eps <= &1 / &40 /\ &0 < dl0 /\ dl0 <= eps /\
        riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps z' e' /\ rfs_neck (top,atlas) g dl0 x0 e0 /\
        (!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps
               ==> mfd_dist (top,atlas) g (e' y) (e' z)
                   <= &3 / &2 * inv(sqrt(mfd_scalar atlas g z')) *
                      (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi)) /\
        (!y z. y IN rfs_neck_dom dl0 /\ z IN rfs_neck_dom dl0
               ==> &1 / &2 * inv(sqrt(mfd_scalar atlas g x0)) *
                   min (abs(apx_sval y - apx_sval z))
                       (&2 * inv dl0 - abs(apx_sval y) - abs(apx_sval z))
                   <= mfd_dist (top,atlas) g (e0 y) (e0 z)) /\
        (!y. y IN rfs_neck_dom eps
             ==> mfd_scalar atlas g (e' y) <= &3 / &2 * mfd_scalar atlas g z') /\
        norm u0 = &1 /\ x0 = e0 u0 /\ x0 IN IMAGE e' (sphere(vec 0,&1)) /\
        IMAGE e' (sphere(vec 0,&1)) SUBSET IMAGE e0 (rfs_neck_dom dl0)
        ==> IMAGE e' (sphere(vec 0,&1)) SUBSET IMAGE e0 (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "up")
    (CONJUNCTS_THEN2 (LABEL_TAC "low") (CONJUNCTS_THEN2 (LABEL_TAC "sc")
    STRIP_ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) z' /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' (e':real^3->A)` THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl0 x0 (e0:real^3->A)` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  UNDISCH_TAC `(x0:A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `(e':real^3->A) v0 = (e0:real^3->A) u0`)) THEN
  SUBGOAL_THEN `!v:real^3. norm v = &1 ==> v IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) v0) <=
                &3 / &2 * mfd_scalar atlas g z'` ASSUME_TAC THENL
   [USE_THEN "sc" MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `a = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) v0)))` THEN
  ABBREV_TAC `b = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  SUBGOAL_THEN `&0 < a /\ &0 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `b <= &5 / &4 * a` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) v0)) <=
                  &5 / &4 * sqrt(mfd_scalar atlas g z')` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`sqrt(mfd_scalar atlas (g:A->real^3^3) ((e':real^3->A) v0))`;
                  `&5 / &4 * sqrt(mfd_scalar atlas (g:A->real^3^3) z')`] REAL_LE_INV2) THEN
    ASM_SIMP_TAC[SQRT_POS_LT] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[REAL_INV_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * pi <= &24 / &5` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ pi <= &16 / &5` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &16 / &5` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&40 <= inv eps /\ &40 <= inv dl0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `inv eps = &1 / eps /\ inv dl0 = &1 / dl0` (CONJUNCTS_THEN SUBST1_TAC)
    THENL [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e':real^3->A) v IN IMAGE (e0:real^3->A) (rfs_neck_dom dl0)` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET
                 IMAGE (e0:real^3->A) (rfs_neck_dom dl0)` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u0 IN rfs_neck_dom dl0` ASSUME_TAC THENL
   [MP_TAC(SPEC `dl0:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "up" (MP_TAC o SPECL [`v0:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "low" (MP_TAC o SPECL [`u0:real^3`; `w:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SVAL_UNIT] THEN
  SUBGOAL_THEN `(e0:real^3->A) u0 = (e':real^3->A) v0 /\ (e0:real^3->A) w = e' v` (fun th ->
    REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID; REAL_SUB_LZERO; REAL_ABS_NEG;
              REAL_SUB_RZERO] THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^3^3) ((e':real^3->A) v0) (e' v)` THEN
  ABBREV_TAC `sw = abs(apx_sval(w:real^3))` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `D <= &9 * a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * b * &24 / &5` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * b * sqrt(&2) * pi` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `min sw (&2 * inv dl0 - sw) <= &18` ASSUME_TAC THENL
   [SUBGOAL_THEN `a * min sw (&2 * inv dl0 - sw) <= a * &18` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sw < inv dl0` ASSUME_TAC THENL
   [EXPAND_TAC "sw" THEN ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sw < inv eps` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "sw" THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* N6 (CAP_FAR).  A (C,eps)-cap meeting the middle half of a                 *)
(* dl-neck (dl small relative to 1/C and eps) lies in the neck near the      *)
(* meeting point (APX_CAP_NEAR); re-centring the neck at a point of the      *)
(* cap's boundary sphere gives a K dl-neck, hence an eps-neck, whose eps-    *)
(* slab contains the boundary sphere (APX_SPHERE_NEAR); by N4 that sphere is *)
(* a section, and by N5 it bounds no compact region, but it bounds the       *)
(* closed core.  Conditional on SMT_SPHERE_COVERING_STATEMENT (through N4).  *)
(* ------------------------------------------------------------------------- *)

let APX_CAP_FAR = prove
 (`SMT_SPHERE_COVERING_STATEMENT ==> !w:A->bool. APX_CAP_FAR_STATEMENT w`,
  DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[APX_CAP_FAR_STATEMENT] THEN
  X_CHOOSE_TAC `K0:real` APX_CYL0_RM_BOUND THEN
  ABBREV_TAC `K = &4 + &576 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&4 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `w:A->bool` (MP APX_NECK_SECTION (ASSUME `SMT_SPHERE_COVERING_STATEMENT`))) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec"))) THEN
  MP_TAC(ISPEC `w:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eC:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))) THEN
  MP_TAC(ISPEC `w:A->bool` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `eD:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  EXISTS_TAC `min eS (min eC (min eD (&1 / &40)))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eS /\ eps <= eC /\ eps <= eD /\ eps <= &1 / &40` STRIP_ASSUME_TAC
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (eps / K) (inv(&16 * K * (C + &1)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`; `U:A->bool`; `Y:A->bool`] THEN
  STRIP_TAC THEN
  (* the smallness of dl *)
  SUBGOAL_THEN `K * dl <= eps /\ &16 * C * dl <= &1 /\ &8 * C * K * dl <= &1 /\
                &8 * C * dl <= &1 /\ dl <= eps /\ K * dl <= &1 / &2 /\ &0 < K * dl`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `K * dl <= eps /\ (&16 * K * (C + &1)) * dl <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `dl <= eps / K` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `dl <= inv(&16 * K * (C + &1))` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < &16 * K * (C + &1)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * dl <= K * dl /\ &16 * C * dl <= &16 * C * K * dl /\
                  &0 <= &16 * K * dl` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(&16 * C * dl) * &1 <= (&16 * C * dl) * K` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
             [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
            ASM_REAL_ARITH_TAC];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `(&16 * K * (C + &1)) * dl <= &1` THEN
    UNDISCH_TAC `&16 * C * dl <= &16 * C * K * dl` THEN
    UNDISCH_TAC `&0 <= &16 * K * dl` THEN UNDISCH_TAC `&4 * dl <= K * dl` THEN
    UNDISCH_TAC `K * dl <= eps` THEN UNDISCH_TAC `eps <= &1 / &40` THEN
    UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `DISJOINT (s:A->bool) t <=> !p. p IN s ==> ~(p IN t)`] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `yp:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(yp:real^3) IN rfs_neck_dom dl /\ abs(apx_sval yp) < inv(&2 * dl)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(yp:real^3) IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl))` THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    SUBGOAL_THEN `inv(&2 * dl) < inv dl` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* N1 and N2 for the dl-neck *)
  SUBGOAL_THEN `!y. y IN rfs_neck_dom dl
                    ==> mfd_scalar atlas (g:A->real^3^3) x / &2 <=
                        mfd_scalar atlas g ((e:real^3->A) y)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`; `y:real^3`]
                  APX_NECK_SCALAR_COMPARE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`;
                 `dl:real`; `x:A`; `e:real^3->A`; `yp:real^3`] APX_CAP_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`; `y:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "near")] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                APX_CAP_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':A` (X_CHOOSE_THEN `e':real^3->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(e':real^3->A) (basis 1) IN U` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e':real^3->A) (basis 1) IN IMAGE e' (sphere(vec 0,&1))` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `(e':real^3->A) (basis 1)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
  (* re-centre the dl-neck at y' *)
  SUBGOAL_THEN `abs(apx_sval(y':real^3)) <= &3 / (&4 * dl)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 * C <= inv(&4 * dl) /\ inv(&2 * dl) + inv(&4 * dl) = &3 / (&4 * dl)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `inv(&4 * dl) = &1 / (&4 * dl)` SUBST1_TAC THENL
         [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < &4 * dl` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < dl` THEN CONV_TAC REAL_FIELD];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `K0:real` APX_NECK_RECENTRE_GEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `dl:real`; `x:A`; `e:real^3->A`; `y':real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y':real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  ABBREV_TAC `c = norm(y':real^3)` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `e0 = (e:real^3->A) o (\w. c % w)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^3. (e0:real^3->A) (inv c % v) = e v` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "e0" THEN REWRITE_TAC[o_THM; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN U ==> ?wq. wq IN rfs_neck_dom (K * dl) /\ q = (e0:real^3->A) wq`
  (LABEL_TAC "inU") THENL
   [X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    USE_THEN "near" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yq:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv c % (yq:real^3)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(yq:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ; APX_SVAL_SCALE;
                 REAL_LT_INV; LOG_INV; REAL_MUL_RNEG] THEN
    SUBGOAL_THEN `sqrt(&2) * log c = apx_sval(y':real^3)` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[apx_sval]; ALL_TAC] THEN
    SUBGOAL_THEN `&8 * C <= inv(K * dl)` MP_TAC THENL
     [SUBGOAL_THEN `inv(K * dl) = &1 / (K * dl)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* facts for APX_SPHERE_NEAR *)
  SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET
                IMAGE (e0:real^3->A) (rfs_neck_dom (K * dl))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    USE_THEN "inU" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET top closure_of Y` THEN
      UNDISCH_TAC `top closure_of Y SUBSET (U:A->bool)` THEN
      UNDISCH_TAC `(q:A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `K * dl`; `z':A`; `e':real^3->A`;
                 `(e:real^3->A) y'`; `e0:real^3->A`; `inv c % (y':real^3)`]
                APX_SPHERE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "dist" (MP_TAC o SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `z':A`;
        `e':real^3->A`; `y:real^3`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "dist" (MP_TAC o SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `K * dl`; `(e:real^3->A) y'`;
        `e0:real^3->A`; `y:real^3`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `z':A`; `e':real^3->A`; `y:real^3`]
                    APX_NECK_SCALAR_COMPARE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "curv" (MP_TAC o SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `z':A`;
        `e':real^3->A`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `basis 1:real^3` THEN
      ASM_REWRITE_TAC[IN_SPHERE_0] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((e:real^3->A) y') e0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `K * dl` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "sec" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(e:real^3->A) y'`; `e0:real^3->A`; `z':A`;
    `e':real^3->A`; `&1`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_01; APX_UNIT_SPHERE_NECK_DOM]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`e0:real^3->A`; `exp(--(inv(sqrt(&2) * eps)))`; `exp(inv(sqrt(&2) * eps))`;
                 `exp(--(inv(sqrt(&2) * K * dl)))`; `exp(inv(sqrt(&2) * K * dl))`;
                 `IMAGE (e':real^3->A) (sphere(vec 0,&1))`] APX_SECTION_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[GSYM rfs_neck_dom]
   (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e0:real^3->A`;
            `exp(--(inv(sqrt(&2) * K * dl)))`; `exp(inv(sqrt(&2) * K * dl))`;
            `IMAGE (e':real^3->A) (sphere(vec 0,&1))`; `top closure_of (Y:A->bool)`]
           APX_SECTION_NOT_BOUNDING_POS)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) dl x (e:real^3->A)` THEN
      SIMP_TAC[rfs_neck];
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (K * dl) ((e:real^3->A) y') e0` THEN
      SIMP_TAC[rfs_neck];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      USE_THEN "inU" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL
       [UNDISCH_TAC `top closure_of Y SUBSET (U:A->bool)` THEN
        UNDISCH_TAC `(q:A) IN top closure_of Y` THEN SET_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET top interior_of (top closure_of Y)` MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* N4, N5b and N6 unconditionally, from S6 (SMT_SPHERE_COVERING in           *)
(* pc_smt_cover.ml, loaded first).  The conditional forms APX_NECK_SECTION,  *)
(* APX_NO_CAP_IN_NECK and APX_CAP_FAR are also available.                    *)
(* ------------------------------------------------------------------------- *)

let APX_NECK_SECTION_UNCOND = prove
 (`!w:A->bool. APX_NECK_SECTION_STATEMENT w`,
  MATCH_MP_TAC APX_NECK_SECTION THEN ACCEPT_TAC SMT_SPHERE_COVERING);;

let APX_NO_CAP_IN_NECK_UNCOND = prove
 (`!w:A->bool. APX_NO_CAP_IN_NECK_STATEMENT w`,
  MATCH_MP_TAC APX_NO_CAP_IN_NECK THEN ACCEPT_TAC SMT_SPHERE_COVERING);;

let APX_CAP_FAR_UNCOND = prove
 (`!w:A->bool. APX_CAP_FAR_STATEMENT w`,
  MATCH_MP_TAC APX_CAP_FAR THEN ACCEPT_TAC SMT_SPHERE_COVERING);;

