(* ========================================================================= *)
(* Unit pc_rfa_hbar: the barrier at infinity for the maximum principle on    *)
(* complete 3D Ricci flows with bounded Ricci curvature.  Main theorem:      *)
(* RFA_HARNACK_BARRIER proves the statement RFA_HARNACK_BARRIER_STATEMENT of *)
(* pc_rfa_u17iface.                                                          *)
(*                                                                           *)
(* Witness psi t x = 1 + d_g(t)(x0,x)^2.  Ingredients: the metric            *)
(* equivalence on [t1,t2] from the Ricci bound (RFA_QFORM_DERIV and          *)
(* RFA_GRONWALL_2SIDED of pc_rfa_shi), the induced distance comparison       *)
(* (RFAH_DIST_COMPARE), closed balls compact (mfd_complete), the Calabi      *)
(* barrier CMP_LAPLACIAN_BARRIER_SQ of pc_cmp_hess in the preferred chart,   *)
(* and a chart-change lemma for llap and lgrad2 (RFAH_CHART_TRANS_LAP).      *)
(* ========================================================================= *)

needs "src/pc_rfa_u17iface.ml";;
needs "src/pc_cmp_hess.ml";;
needs "src/pc_grg_distcont.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Chart change for llap and lgrad2 of a function smooth on an               *)
(* open set of the manifold, and the shift by a constant.                    *)
(* ========================================================================= *)

let RFAH_CHART_TRANS_LAP = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) c' (f:A->real) W x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ c' IN atlas /\ open_in top W /\
     mfd_smooth_on atlas W (lift o f) /\
     x IN FST c /\ x IN FST c' /\ x IN W
     ==> llap (metric_local atlas c g) (f o chart_inv c) (SND c x) =
         llap (metric_local atlas c' g) (f o chart_inv c') (SND c' x) /\
         lgrad2 (metric_local atlas c g) (f o chart_inv c) (SND c x) =
         lgrad2 (metric_local atlas c' g) (f o chart_inv c') (SND c' x)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`;
                       `V:A->bool`; `psi:A->real^N`; `f:A->real`; `W:A->bool`;
                       `x:A`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U INTER V INTER W:A->bool)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC) THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (phi:A->real^N) (U INTER V INTER W)) /\
    open (IMAGE (psi:A->real^N) (U INTER V INTER W))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
    THENL [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:A. y IN U ==> chart_trans (U,phi) (V,psi) ((phi:A->real^N) y) = psi y`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `diffeomorphism_on (IMAGE (phi:A->real^N) (U INTER V INTER W))
                      (IMAGE (psi:A->real^N) (U INTER V INTER W))
                      (chart_trans (U,phi) (V,psi)) (chart_trans (V,psi) (U,phi))`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (psi:A->real^N) (U INTER V INTER W) =
      IMAGE (chart_trans (U,phi) (V,psi)) (IMAGE (phi:A->real^N) (U INTER V INTER W))`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
      REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CMPH_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^N) (U INTER V)`;
                          `IMAGE (psi:A->real^N) (U INTER V)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (psi:A->real^N) (U INTER V INTER W))
                 (metric_local atlas (V,psi) (g:A->real^N^N))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER U)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (psi:A->real^N) (U INTER V INTER W))
                  (\z. lift(((f:A->real) o chart_inv (V,psi)) z))`
   ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool) (lift o (f:A->real))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER W)` THEN CONJ_TAC THENL
     [SET_TAC[];
      FIRST_X_ASSUM(MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (phi:A->real^N) (U INTER V INTER W)
        ==> metric_local atlas (U,phi) (g:A->real^N^N) z =
            mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g) z /\
            ((f:A->real) o chart_inv (U,phi)) z =
            ((f o chart_inv (V,psi)) o chart_trans (U,phi) (V,psi)) z`
   ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN IMAGE phi (U INTER V INTER W)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `llap (mpullback (chart_trans (U,phi) (V,psi))
                      (metric_local atlas (V,psi) (g:A->real^N^N)))
           (((f:A->real) o chart_inv (V,psi)) o chart_trans (U,phi) (V,psi))
           ((phi:A->real^N) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LLAP_LOCAL THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V INTER W)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:A->real^N) x = chart_trans (U,phi) (V,psi) (phi x)`
     SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LLAP_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (psi:A->real^N) (U INTER V INTER W)`;
      `IMAGE (phi:A->real^N) (U INTER V INTER W)`;
      `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
    ASM_REWRITE_TAC[];
    TRANS_TAC EQ_TRANS
     `lgrad2 (mpullback (chart_trans (U,phi) (V,psi))
                        (metric_local atlas (V,psi) (g:A->real^N^N)))
           (((f:A->real) o chart_inv (V,psi)) o chart_trans (U,phi) (V,psi))
           ((phi:A->real^N) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LGRAD2_LOCAL THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V INTER W)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:A->real^N) x = chart_trans (U,phi) (V,psi) (phi x)`
     SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LGRAD2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (psi:A->real^N) (U INTER V INTER W)`;
      `IMAGE (phi:A->real^N) (U INTER V INTER W)`;
      `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Metric equivalence on [t1,t2] and the distance comparison.                *)
(* ========================================================================= *)

(* The quadratic forms of g(s) and g(t), s <= t in [t1,t2], are equivalent   *)
(* with factor exp(2K(t-s)) (Gronwall; RFA_METRIC_EQUIV of pc_rfa_shi needs  *)
(* ricci_flow_from and a bound up to b, so we use its two ingredients).       *)

let RFAH_QFORM_EQUIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) t1 t2 K.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t2 < b /\
     (!t x v. t1 <= t /\ t <= t2 /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v)))
     ==> !s t x v. t1 <= s /\ s <= t /\ t <= t2 /\ x IN topspace top
                   ==> exp(--(&2 * K * (t - s))) * (v dot (g s x ** v)) <=
                       v dot (g t x ** v) /\
                       v dot (g t x ** v) <=
                       exp(&2 * K * (t - s)) * (v dot (g s x ** v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ric")))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `x:A`; `v:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = t` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0;
                    REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. s <= r /\ r <= t
        ==> ((\r. v dot ((g:real->A->real^N^N) r x ** v)) has_real_derivative
             --(&2) * mfd_ricci atlas (g r) x v v) (atreal r)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. v dot ((g:real->A->real^N^N) r x ** v)`;
                 `\r. --(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) (x:A) v v`;
                 `&2 * K`; `s:real`; `t:real`] RFA_GRONWALL_2SIDED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) (x:A) v v` THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      USE_THEN "ric" (MP_TAC o SPECL [`r:real`; `x:A`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_ASSOC]]);;

let RFAH_QFORM_EQUIV_ABS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) t1 t2 K.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t2 < b /\
     (!t x v. t1 <= t /\ t <= t2 /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v)))
     ==> !s t x v. t1 <= s /\ s <= t2 /\ t1 <= t /\ t <= t2 /\ x IN topspace top
                   ==> v dot (g s x ** v) <=
                       exp(&2 * K * abs(t - s)) * (v dot (g t x ** v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RFAH_QFORM_EQUIV) THEN
  DISCH_THEN(LABEL_TAC "eq") THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `x:A`; `v:real^N`] THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= t \/ t <= s`) THENL
   [USE_THEN "eq" (MP_TAC o SPECL [`s:real`; `t:real`; `x:A`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
      (SPEC `&2 * K * (t - s)` REAL_EXP_POS_LE) o CONJUNCT1) THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_ARITH `s <= t ==> abs(t - s) = t - s`];
    USE_THEN "eq" (MP_TAC o SPECL [`t:real`; `s:real`; `x:A`; `v:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `t <= s ==> abs(t - s) = s - t`]]);;

(* Distances under a pointwise comparison of the metrics.                   *)

let RFAH_DIST_COMPARE = prove
 (`!top atlas (g:A->real^N^N) g' c x y.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ riemannian_metric atlas g' /\ &0 < c /\
     (!z v. z IN topspace top ==> v dot (g' z ** v) <= c * (v dot (g z ** v))) /\
     mfd_joinable (top,atlas) x y
     ==> mfd_dist (top,atlas) g' x y <= sqrt c * mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y` THEN
    REWRITE_TAC[mfd_joinable] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `l:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (g':A->real^N^N) gamma (&0) (&1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g':A->real^N^N`; `gamma:real->A`; `&0`; `&1`]
      MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC MFD_LENGTH_METRIC_COMPARE THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL]]);;


(* ========================================================================= *)
(* The hypotheses of the barrier statement, their basic                      *)
(* consequences, and the clauses (1), (3), (4) of the statement.             *)
(* ========================================================================= *)

let rfah_hyp = new_definition
 `rfah_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
           (g:real->A->real^N^N) a b t1 t2 K x0 <=>
    hausdorff_space top /\
    ricci_flow_on (top,atlas) a b g /\
    a < t1 /\ t1 < t2 /\ t2 < b /\
    (!t. t1 <= t /\ t <= t2 ==> mfd_complete (top,atlas) (g t)) /\
    (!t x v. t1 <= t /\ t <= t2 /\ x IN topspace top
             ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v))) /\
    x0 IN topspace top`;;

let RFAH_HYP_BASIC = prove
 (`!top atlas (g:real->A->real^N^N) a b t1 t2 K x0.
     rfah_hyp top atlas g a b t1 t2 K x0
     ==> smooth_manifold_atlas top atlas /\
         (!t. t1 <= t /\ t <= t2 ==> riemannian_metric atlas (g t)) /\
         &0 <= K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfah_hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
    (!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t))`
   STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                   a b (g:real->A->real^N^N)` THEN
    SIMP_TAC[ricci_flow_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t1 <= t /\ t <= t2
                    ==> riemannian_metric atlas ((g:real->A->real^N^N) t)`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`a < t1`; `t2 < b`; `t1 <= t`; `t <= t2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t1`; `x0:A`] RIEMANNIAN_METRIC_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t1 < t2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^N` o CONJUNCT2) THEN
  SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t1:real`; `x0:A`; `basis 1:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `t1 < t2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:real`; `&0`;
                 `basis 1 dot ((g:real->A->real^N^N) t1 x0 ** basis 1)`]
    REAL_LT_RMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  UNDISCH_TAC `abs(mfd_ricci atlas ((g:real->A->real^N^N) t1) (x0:A)
                 (basis 1) (basis 1)) <=
               K * (basis 1 dot (g t1 x0 ** basis 1))` THEN
  REAL_ARITH_TAC);;

let RFAH_SQRT_EXP2 = prove
 (`!u. sqrt(exp(&2 * u)) = exp u`,
  GEN_TAC THEN
  SUBGOAL_THEN `exp(&2 * u) = exp u pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* Distances of g(s) and g(t), s, t in [t1,t2], differ by exp(K|t-s|).      *)

let RFAH_HYP_DIST = prove
 (`!top atlas (g:real->A->real^N^N) a b t1 t2 K x0.
     rfah_hyp top atlas g a b t1 t2 K x0
     ==> !s t x y. t1 <= s /\ s <= t2 /\ t1 <= t /\ t <= t2 /\
                   mfd_joinable (top,atlas) x y
                   ==> mfd_dist (top,atlas) (g s) x y <=
                       exp(K * abs(t - s)) * mfd_dist (top,atlas) (g t) x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFAH_HYP_BASIC) THEN
  SUBGOAL_THEN
   `!s t x v. t1 <= s /\ s <= t2 /\ t1 <= t /\ t <= t2 /\ x IN topspace top
              ==> v dot ((g:real->A->real^N^N) s x ** v) <=
                  exp(&2 * K * abs(t - s)) * (v dot (g t x ** v))`
   (LABEL_TAC "eq") THENL
   [MATCH_MP_TAC RFAH_QFORM_EQUIV_ABS THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `a:real`; `b:real`] THEN
    UNDISCH_TAC `rfah_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
                   (g:real->A->real^N^N) a b t1 t2 K x0` THEN
    SIMP_TAC[rfah_hyp];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `x:A`; `y:A`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM RFAH_SQRT_EXP2] THEN
  MATCH_MP_TAC RFAH_DIST_COMPARE THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_MUL_ASSOC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Clause (3): sublevel sets lie in a closed g(t1)-ball, compact.           *)

let RFAH_BAR_PROPER = prove
 (`!top atlas (g:real->A->real^N^N) a b t1 t2 K x0.
     rfah_hyp top atlas g a b t1 t2 K x0
     ==> !B. ?S. compact_in top S /\
                 !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
                       &1 + mfd_dist (top,atlas) (g t) x0 x pow 2 <= B
                       ==> x IN S`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFAH_HYP_BASIC) THEN
  FIRST_ASSUM(LABEL_TAC "dist" o MATCH_MP RFAH_HYP_DIST) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfah_hyp]) THEN
  X_GEN_TAC `B:real` THEN
  EXISTS_TAC `mfd_cball (top,atlas) ((g:real->A->real^N^N) t1) x0
                        (exp(K * (t2 - t1)) * sqrt(abs B))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->A->real^N^N) t1)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `t1 < t2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(K * abs(t - t1)) *
              mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 x` THEN
  CONJ_TAC THENL
   [USE_THEN "dist" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `t1 < t2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`t1 <= t`; `t <= t2`] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    UNDISCH_TAC `&1 + mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 x pow 2
                 <= B` THEN
    REAL_ARITH_TAC]);;

(* Clause (4): the backward-in-time bound, for any C >= 4K.                 *)

let RFAH_BAR_BACKWARD = prove
 (`!top atlas (g:real->A->real^N^N) a b t1 t2 K x0 C.
     rfah_hyp top atlas g a b t1 t2 K x0 /\ &4 * K <= C
     ==> !t x. t1 < t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
               ==> ?d. &0 < d /\
                       !s. t1 <= s /\ t - d < s /\ s <= t
                           ==> &1 + mfd_dist (top,atlas) (g s) x0 x pow 2 <=
                               (&1 + mfd_dist (top,atlas) (g t) x0 x pow 2) +
                               C * (t - s) *
                               (&1 + mfd_dist (top,atlas) (g t) x0 x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFAH_HYP_BASIC) THEN
  FIRST_ASSUM(LABEL_TAC "dist" o MATCH_MP RFAH_HYP_DIST) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(&4 * K + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 < t2` ASSUME_TAC THENL
   [UNDISCH_TAC `rfah_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
                   (g:real->A->real^N^N) a b t1 t2 K x0` THEN
    SIMP_TAC[rfah_hyp];
    ALL_TAC] THEN
  ABBREV_TAC `h = t - s` THEN
  SUBGOAL_THEN `&0 <= h /\ (&4 * K + &1) * h <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h <= inv(&4 * K + &1)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
      (REAL_ARITH `&0 <= K ==> &0 <= &4 * K + &1` |> UNDISCH)) THEN
    SUBGOAL_THEN `(&4 * K + &1) * inv(&4 * K + &1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 x` THEN
  ABBREV_TAC `Ds = mfd_dist (top,atlas) ((g:real->A->real^N^N) s) x0 x` THEN
  SUBGOAL_THEN `&0 <= D /\ &0 <= Ds` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "Ds"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Ds <= exp(K * h) * D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "Ds"; "h"] THEN
    SUBGOAL_THEN `t - s = abs(t - s)` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "dist" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Ds pow 2 <= (&1 + &4 * K * h) * D pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(exp(K * h) * D) pow 2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `exp(K * h) pow 2 = exp(&2 * (K * h))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_2; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * (&2 * (K * h))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN
      SUBGOAL_THEN `&0 <= K * h` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(&4 * K + &1) * h <= &1` THEN UNDISCH_TAC `&0 <= h` THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * K) * (h * D pow 2) <= C * (h * (&1 + D pow 2))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`Ds pow 2 <= (&1 + &4 * K * h) * D pow 2`;
    `(&4 * K) * (h * D pow 2) <= C * (h * (&1 + D pow 2))`] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Clause (2), joint continuity of (t,x) |-> 1 + d_t(x0,x)^2.                *)
(* ========================================================================= *)

let RFAH_CONT_ARITH = prove
 (`!K D Dty Dsy dxy e r h.
     &0 <= K /\ &0 <= D /\ &0 <= Dsy /\ &0 <= Dty /\ &0 < r /\
     abs(Dty - D) <= dxy /\ dxy < r / &3 /\ dxy < &1 /\
     Dsy <= e * Dty /\ Dty <= e * Dsy /\ &1 <= e /\ e <= &1 + &2 * (K * h) /\
     &0 <= h /\ &2 * (K + &1) * h <= &1 /\
     &12 * (K + &1) * (D + &1) * h <= r
     ==> abs(Dsy - D) < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= K * h /\ &0 <= D * h /\ &0 <= K * D * h` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e <= &2` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`e <= &1 + &2 * (K * h)`; `&2 * (K + &1) * h <= &1`;
                           `&0 <= h`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Dty <= D + &1` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`abs(Dty - D) <= dxy`; `dxy < &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e - &1) * Dty <= (&2 * (K * h)) * (D + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Dsy <= &2 * (D + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * Dty` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e - &1) * Dsy <= (&2 * (K * h)) * (&2 * (D + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(e - &1) * Dty <= (&2 * (K * h)) * (D + &1)`;
    `(e - &1) * Dsy <= (&2 * (K * h)) * (&2 * (D + &1))`;
    `Dsy <= e * Dty`; `Dty <= e * Dsy`; `abs(Dty - D) <= dxy`; `dxy < r / &3`;
    `&12 * (K + &1) * (D + &1) * h <= r`; `&0 <= K * h`; `&0 <= D * h`;
    `&0 <= K * D * h`; `&0 <= h`; `&0 < r`] THEN
  REAL_ARITH_TAC);;

let RFAH_BAR_CONT = prove
 (`!top atlas (g:real->A->real^N^N) a b t1 t2 K x0.
     rfah_hyp top atlas g a b t1 t2 K x0
     ==> continuous_map
           (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                          (subtopology top {x | mfd_joinable (top,atlas) x0 x}),
            euclideanreal)
           (\z. &1 + mfd_dist (top,atlas) (g (FST z)) x0 (SND z) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFAH_HYP_BASIC) THEN
  FIRST_ASSUM(LABEL_TAC "dist" o MATCH_MP RFAH_HYP_DIST) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o RAND_CONV)
    [GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_TO_METRIC] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; FORALL_PAIR_THM;
              IN_CROSS; IN_INTER; IN_ELIM_THM; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
              IN_MBALL; REAL_EUCLIDEAN_METRIC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 x` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x:A`; `min (r / &3) (&1)`]
    GRGD_DIST_SMALL_NBHD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nb:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `del = min (inv(&2 * (K + &1))) (r / (&12 * (K + &1) * (D + &1)))` THEN
  SUBGOAL_THEN `&0 < del` ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(real_interval(t - del,t + del) INTER real_interval[t1,t2]) CROSS
              (nb INTER {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x0 y})` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_CROSS] THEN REPEAT DISJ2_TAC THEN CONJ_TAC THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THENL
     [EXISTS_TAC `real_interval(t - del,t + del)` THEN
      REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL];
      EXISTS_TAC `nb:A->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_CROSS; IN_INTER; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_CROSS; IN_INTER; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_joinable (top,atlas) (x:A) y /\
    mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x y < min (r / &3) (&1)`
   STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h = abs(t - s)` THEN
  SUBGOAL_THEN `&0 <= h /\ h <= inv(&2 * (K + &1)) /\
                h <= r / (&12 * (K + &1) * (D + &1))`
   STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_ABS_POS] THEN
    SUBGOAL_THEN `abs(t - s) < del` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "del" THEN REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (K + &1) * h <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&2 * (K + &1)`; `h:real`; `inv(&2 * (K + &1))`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * (K + &1)) * inv(&2 * (K + &1)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&12 * (K + &1) * (D + &1) * h <= r` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real`; `r:real`; `&12 * (K + &1) * (D + &1)`]
      REAL_LE_RDIV_EQ) THEN
    ANTS_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(EQ_MP th (ASSUME
      `h <= r / (&12 * (K + &1) * (D + &1))`))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K * h /\ K * h <= inv(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&2 * (K + &1) * h <= &1` THEN UNDISCH_TAC `&0 <= h` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC RFAH_CONT_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`K:real`; `mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 y`;
    `mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x y`;
    `exp(K * h)`; `h:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_SIMP_TAC[];
    EXPAND_TAC "D" THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    MATCH_MP_TAC MFD_DIST_LIPSCHITZ_RIGHT THEN ASM_SIMP_TAC[];
    UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x y <
                 min (r / &3) (&1)` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x y <
                 min (r / &3) (&1)` THEN REAL_ARITH_TAC;
    EXPAND_TAC "h" THEN USE_THEN "dist" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "h" THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    USE_THEN "dist" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + K * h` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Clause (5), the smooth upper barriers in every atlas chart.               *)
(* ========================================================================= *)

(* Shifting by a constant changes neither llap nor lgrad2.                  *)

let RFAH_LAP_SHIFT = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) c y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> llap G (\z. c + f z) y = llap G f y /\
         lgrad2 G (\z. c + f z) y = lgrad2 G f y`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N. (c:real)`;
                   `f:real^N->real`; `y:real^N`] RFA_LLAP_ADD) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; RFA_LLAP_CONST; REAL_ADD_LID];
    REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner] THEN
    SUBGOAL_THEN `!h. rfa_d1 (\z. (c:real) + f z) (y:real^N) h = rfa_d1 f y h`
     (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN
    MP_TAC(ISPECL [`\z:real^N. (c:real)`; `f:real^N->real`; `y:real^N`;
                   `h:real^N`] RFA_D1_ADD_AT) THEN
    REWRITE_TAC[RFA_D1_CONST; REAL_ADD_LID; DIFFERENTIABLE_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let RFAH_MFD_SMOOTH_ON_SHIFT = prove
 (`!top atlas W (phi:A->real) c.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     open_in top W /\ mfd_smooth_on atlas W (lift o phi)
     ==> mfd_smooth_on atlas W (lift o (\y. c + phi y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_on] THEN STRIP_TAC THEN
  X_GEN_TAC `d:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND (d:(A->bool)#(A->real^N))) (FST d INTER W))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y. lift(drop((\y:real^N. lift c) y) +
                       drop(((lift o (phi:A->real)) o chart_inv d) y))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_ADD THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX]);;

let RFAH_BAR_ARITH = prove
 (`!s d. &0 <= s /\ &0 <= d
         ==> &2 * &3 + &2 * &2 * s * d + &1 <= (&7 + &2 * s) * (&1 + d pow 2) /\
             &4 * d pow 2 <= &4 * (&1 + d pow 2) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s * (&1 - d) pow 2 /\ &0 <= (d pow 2) pow 2`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= s * (&1 - d) pow 2`] THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `&0 <= d pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `&0 <= (d pow 2) pow 2` THEN
    SUBGOAL_THEN `&0 <= d pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let RFAH_BAR_BARRIER = prove
 (`!top atlas (g:real->A->real^3^3) a b t1 t2 K x0.
     rfah_hyp top atlas g a b t1 t2 K x0
     ==> !t x c. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
                 c IN atlas /\ x IN FST c
                 ==> ?W q. open W /\ SND c x IN W /\ W SUBSET IMAGE (SND c) (FST c) /\
                           smooth_map_on W (\y. lift(q y)) /\
                           (!y. y IN W
                                ==> &1 + mfd_dist (top,atlas) (g t) x0 (chart_inv c y)
                                         pow 2 <= q y) /\
                           q (SND c x) = &1 + mfd_dist (top,atlas) (g t) x0 x pow 2 /\
                           llap (metric_local atlas c (g t)) q (SND c x) <=
                           (&7 + &2 * sqrt(K / &2)) *
                           (&1 + mfd_dist (top,atlas) (g t) x0 x pow 2) /\
                           lgrad2 (metric_local atlas c (g t)) q (SND c x) <=
                           &4 * (&1 + mfd_dist (top,atlas) (g t) x0 x pow 2) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFAH_HYP_BASIC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfah_hyp]) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `x0:A`; `x:A`] MFD_JOINABLE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t) /\
                mfd_complete (top,atlas) ((g:real->A->real^3^3) t)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIV:A->bool`; `UNIV:3->bool`] CMP_LAPLACIAN_BARRIER_SQ) THEN
  REWRITE_TAC[CMP_LAPLACIAN_BARRIER_SQ_STATEMENT; DIMINDEX_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `(g:real->A->real^3^3) t`; `x0:A`; `K / &2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 <= K` THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
      FIRST_ASSUM(fun th -> MP_TAC(SPECL [`t:real`; `y:A`; `w:real^3`] th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `&1`]) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W0:A->bool`; `phi:A->real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) (W0:A->bool)
                  (lift o (\y. &1 + (phi:A->real) y))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC RFAH_MFD_SMOOTH_ON_SHIFT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W0)) /\
    SND c (x:A) IN IMAGE (SND c) (FST c INTER W0)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c0:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c0:(A->bool)#(A->real^3))) (FST c0 INTER W0)) /\
    SND c0 (x:A) IN IMAGE (SND c0) (FST c0 INTER W0) /\
    smooth_map_on (IMAGE (SND c0) (FST c0 INTER W0))
                  (\z. lift(((phi:A->real) o chart_inv c0) z))`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W0
                     (lift o (phi:A->real))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN
      DISCH_THEN(MP_TAC o SPEC `c0:(A->bool)#(A->real^3)`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W0)` THEN
  EXISTS_TAC `(\y:A. &1 + (phi:A->real) y) o chart_inv (c:(A->bool)#(A->real^3))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`;
                 `c0:(A->bool)#(A->real^3)`; `\y:A. &1 + (phi:A->real) y`;
                 `W0:A->bool`; `x:A`] RFAH_CHART_TRANS_LAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN
   `(\y:A. &1 + (phi:A->real) y) o chart_inv (c0:(A->bool)#(A->real^3)) =
    (\z. &1 + (phi o chart_inv c0) z)`
   SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^3))) (FST c0 INTER W0)`;
                 `metric_local atlas (c0:(A->bool)#(A->real^3))
                               ((g:real->A->real^3^3) t)`;
                 `(phi:A->real) o chart_inv (c0:(A->bool)#(A->real^3))`;
                 `&1`; `SND (c0:(A->bool)#(A->real^3)) (x:A)`] RFAH_LAP_SHIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->A->real^3^3) t) x0 x` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt(K / &2)`; `d:real`] RFAH_BAR_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `&0 <= K` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W0
                   (lift o (\y:A. &1 + (phi:A->real) y))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LADD];
    REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * &3 + &2 * &2 * sqrt(K / &2) * d + &1` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The headline, with C = 8 + 4K + 2 sqrt(K/2) and                           *)
(* psi t x = 1 + d_g(t)(x0,x)^2.                                             *)
(* ========================================================================= *)

let RFA_HARNACK_BARRIER = prove
 (`!u:A->bool. RFA_HARNACK_BARRIER_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[RFA_HARNACK_BARRIER_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:real->A->real^3^3`; `a:real`; `b:real`; `t1:real`; `t2:real`;
    `K:real`; `x0:A`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `rfah_hyp (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
                  (g:real->A->real^3^3) a b t1 t2 K x0`
   ASSUME_TAC THENL [ASM_REWRITE_TAC[rfah_hyp]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFAH_HYP_BASIC) THEN
  SUBGOAL_THEN `&0 <= sqrt(K / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN UNDISCH_TAC `&0 <= K` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&8 + &4 * K + &2 * sqrt(K / &2)` THEN
  EXISTS_TAC `\t x. &1 + mfd_dist (top,atlas) ((g:real->A->real^3^3) t) x0 x pow 2` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR; REAL_LE_POW_2];
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP RFAH_BAR_CONT);
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP RFAH_BAR_PROPER);
    MATCH_MP_TAC RFAH_BAR_BACKWARD THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `K:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`; `c:(A->bool)#(A->real^3)`] o
              MATCH_MP RFAH_BAR_BARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `W:real^3->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^3->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = &1 + mfd_dist (top,atlas) ((g:real->A->real^3^3) t) x0 x pow 2` THEN
  SUBGOAL_THEN `&0 <= p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_LE_ADD THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&7 + &2 * sqrt(K / &2)) * p` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * p pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC]);;

