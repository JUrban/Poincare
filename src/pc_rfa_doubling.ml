(* ========================================================================= *)
(* Unit pc_rfa_doubling: the doubling-time estimate for the curvature (R2,   *)
(* the statement PDE_REQ_RM_DOUBLING_STATEMENT of pc_pde_iface;              *)
(* MT Prop 4.11, CLN Lemma 6.1): the maximum principle RFA_MAXP_SCALAR of    *)
(* pc_rfa_maxp applied to |Rm|^2 with the comparison function                *)
(* H' = C H^(3/2).                                                           *)
(* ========================================================================= *)

needs "src/pc_rfa_mfd.ml";;
needs "src/pc_pde_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The comparison function: u |-> C |u|^(3/2) is Lipschitz on                *)
(* bounded sets, and H(t) = 4 H0 / (2 - C sqrt(H0) (t - a))^2 solves        *)
(* H' = C H^(3/2) with H(a) = H0.                                            *)
(* ========================================================================= *)

let RFA_POW32_LIPSCHITZ = prove
 (`!x y B. &0 <= x /\ x <= B /\ &0 <= y /\ y <= B
           ==> abs(sqrt x pow 3 - sqrt y pow 3) <= &2 * sqrt B * abs(x - y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt x /\ &0 <= sqrt y /\ sqrt x <= sqrt B /\ sqrt y <= sqrt B`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - y) = abs(sqrt x pow 2 - sqrt y pow 2)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt x` THEN ABBREV_TAC `r = sqrt y` THEN ABBREV_TAC `q = sqrt B` THEN
  SUBGOAL_THEN `s pow 2 + s * r + r pow 2 <= &2 * q * (s + r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s + r) * (s + r)` THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`s:real`; `r:real`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= (&2 * q) * (s + r) ==> x <= &2 * q * (s + r)`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s pow 2 + s * r + r pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:real`; `r:real`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s pow 3 - r pow 3 = (s - r) * (s pow 2 + s * r + r pow 2) /\
                s pow 2 - r pow 2 = (s - r) * (s + r)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`;
               REAL_ARITH `&0 <= s /\ &0 <= r ==> abs(s + r) = s + r`] THEN
  SUBGOAL_THEN `abs(s - r) * (s pow 2 + s * r + r pow 2) <= abs(s - r) * (&2 * q * (s + r))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN CONV_TAC REAL_RING);;

let RFA_PSI_LIPSCHITZ = prove
 (`!Cp B. ?L. !u v. abs u <= B /\ abs v <= B
                    ==> abs(Cp * sqrt(abs u) pow 3 - Cp * sqrt(abs v) pow 3) <=
                        L * abs(u - v)`,
  REPEAT GEN_TAC THEN EXISTS_TAC `abs Cp * &2 * sqrt(abs B)` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * sqrt(abs B) * abs(abs u - abs v)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_POW32_LIPSCHITZ THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let RFA_DOUBLING_ODE = prove
 (`!a Cp H0 t.
     &0 < Cp /\ &0 < H0 /\ Cp * sqrt H0 * (t - a) < &2
     ==> ((\s. &4 * H0 / (&2 - Cp * sqrt H0 * (s - a)) pow 2) has_real_derivative
          Cp * sqrt(abs(&4 * H0 / (&2 - Cp * sqrt H0 * (t - a)) pow 2)) pow 3)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s0 = sqrt H0` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 pow 2 = H0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\s. &4 * H0 / (&2 - Cp * s0 * (s - a)) pow 2) has_real_derivative f')
     (atreal t)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ABBREV_TAC `D = &2 - Cp * s0 * (t - a)` THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(abs(&4 * H0 / D pow 2)) = &2 * s0 / D` SUBST1_TAC THENL
   [SUBGOAL_THEN `abs(&4 * H0 / D pow 2) = (&2 * s0 / D) pow 2` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 <= &4 * H0 / D pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      UNDISCH_TAC `s0 pow 2 = H0` THEN UNDISCH_TAC `&0 < D` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  UNDISCH_TAC `s0 pow 2 = H0` THEN UNDISCH_TAC `&0 < D` THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The maximum principle for |Rm|^2: starting from |Rm|^2 <= H0              *)
(* it stays below 4 H0 for a time of order H0^(-1/2).                        *)
(* ========================================================================= *)

let RFA_RMD2_POS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) l x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> &0 <= rfa_rmd2 l atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rmd2; lrm_deriv_norm2] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at atlas (x:A))) (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MATCH_MP_TAC LTNORM2_POS THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N)`]
         LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                             (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N)`;
                 `lrm4 (metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N))`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[]);;

let RFA_CONTINUOUS_MAP_RESTRICT_TIME = prove
 (`!(X:A topology) (top':B topology) (f:real#A->B) a b b'.
        continuous_map
          (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b}) X, top') f /\
        b' <= b
        ==> continuous_map
              (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b'}) X, top') f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `prod_topology (subtopology euclideanreal {t | a <= t /\ t < b'}) (X:A topology) =
    subtopology (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b}) X)
                ({t | a <= t /\ t < b'} CROSS topspace X)`
  SUBST1_TAC THENL
   [REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; IN_INTER; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[]]);;

let RFA_RMD2_DOUBLING = prove
 (`?Cp. &0 < Cp /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
      (g:real->A->real^N^N) H0.
       compact_space top /\ ricci_flow_from (top,atlas) a b g /\ &0 < H0 /\
       (!x. x IN topspace top ==> rfa_rmd2 0 atlas (g a) x <= H0)
       ==> !t x. a <= t /\ t < b /\ Cp * sqrt H0 * (t - a) <= &1 /\
                 x IN topspace top
                 ==> rfa_rmd2 0 atlas (g t) x <= &4 * H0`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B4"))
    (INST_TYPE [`:A`,`:A`] RFA_RMD2_EVOLUTION_0) THEN
  EXISTS_TAC `C + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `H0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top:A topology,atlas) a b (g:real->A->real^N^N) /\
                smooth_manifold_atlas top atlas /\ a < b`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  ABBREV_TAC `Cp = C + &1` THEN
  SUBGOAL_THEN `&0 < Cp /\ C <= Cp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s0 = sqrt H0` THEN
  SUBGOAL_THEN `&0 < s0` ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Cp * s0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ABBREV_TAC `b' = min b (a + &3 / (&2 * Cp * s0))` THEN
  SUBGOAL_THEN `a < b' /\ b' <= b /\
                !t. a <= t /\ t < b' ==> Cp * s0 * (t - a) < &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b'" THEN
    SUBGOAL_THEN `&0 < &3 / (&2 * Cp * s0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Cp * s0) * (t - a) < (Cp * s0) * (&3 / (&2 * Cp * s0))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Cp * s0) * (&3 / (&2 * Cp * s0)) = &3 / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Cp * s0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `topspace(top:A topology)`;
    `a:real`; `b':real`; `g:real->A->real^N^N`;
    `\t x. rfa_rmd2 0 (atlas:((A->bool)#(A->real^N))->bool) ((g:real->A->real^N^N) t) x`;
    `\t:real u. Cp * sqrt(abs u) pow 3`;
    `\s. &4 * H0 / (&2 - Cp * s0 * (s - a)) pow 2`] RFA_MAXP_SCALAR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM compact_space];
      REWRITE_TAC[OPEN_IN_TOPSPACE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                                 (g:real->A->real^N^N)` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_CONTINUOUS_MAP_RESTRICT_TIME THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_RMD2_CONTINUOUS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace(top:A topology))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFA_RMD2_CHART_SMOOTH THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
      USE_THEN "B4" (MP_TAC o SPECL
        [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
         `g:real->A->real^N^N`; `t:real`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[ETA_AX] THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
       [UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                                   (g:real->A->real^N^N)` THEN
        REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) t`; `0 + 1`; `x:A`] RFA_RMD2_POS) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) t`; `0`; `x:A`] RFA_RMD2_POS) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `d <= rfa_lap atlas ((g:real->A->real^N^N) t) (rfa_rmd2 0 atlas (g t)) x -
             &2 * rfa_rmd2 (0 + 1) atlas (g t) x +
             C * sqrt(rfa_rmd2 0 atlas (g t) x) *
             sum(0..0) (\i. sqrt(rfa_rmd2 i atlas (g t) x) *
                            sqrt(rfa_rmd2 (0 - i) atlas (g t) x))` THEN
      REWRITE_TAC[SUM_SING_NUMSEG; SUB_REFL] THEN
      ABBREV_TAC `f = rfa_rmd2 0 atlas ((g:real->A->real^N^N) t) x` THEN
      ABBREV_TAC `f1 = rfa_rmd2 (0 + 1) atlas ((g:real->A->real^N^N) t) x` THEN
      ABBREV_TAC `L = rfa_lap atlas ((g:real->A->real^N^N) t) (rfa_rmd2 0 atlas (g t)) x` THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `C * sqrt f * sqrt f * sqrt f <= Cp * sqrt(abs f) pow 3` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_ARITH `&0 <= f ==> abs f = f`] THEN
        SUBGOAL_THEN `sqrt f pow 3 = sqrt f * sqrt f * sqrt f` SUBST1_TAC THENL
         [CONV_TAC REAL_RING; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]];
        ALL_TAC] THEN
      UNDISCH_TAC `&0 <= f1` THEN
      UNDISCH_TAC `d <= L - &2 * f1 + C * sqrt f * sqrt f * sqrt f` THEN
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`cc:real`; `B:real`] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`Cp:real`; `B:real`] RFA_PSI_LIPSCHITZ) THEN
      DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN EXISTS_TAC `L:real` THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(SPECL [`a:real`; `Cp:real`; `H0:real`; `t:real`] RFA_DOUBLING_ODE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&4 * H0 / (&2 - Cp * s0 * (a - a)) pow 2 = H0` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
        CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t < b'` ASSUME_TAC THENL
   [EXPAND_TAC "b'" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `t < a + x <=> t - a < x`] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
    UNDISCH_TAC `Cp * s0 * (t - a) <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  ABBREV_TAC `D = &2 - Cp * s0 * (t - a)` THEN
  SUBGOAL_THEN `&1 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= D pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D pow 2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `H0 * &1 <= H0 * d ==> H0 <= H0 * d`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* |Rm| on the manifold (largest absolute sectional curvature)               *)
(* against |Rm|^2 in a chart, and R2 (PDE_REQ_RM_DOUBLING_STATEMENT).        *)
(* ========================================================================= *)

let RFA_MFD_SECTIONAL_LE_RMD2 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ ~collinear {vec 0,u,v}
        ==> abs(mfd_sectional atlas g x u v) <= sqrt(rfa_rmd2 0 atlas g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional; rfa_rmd2] THEN
  MATCH_MP_TAC RFA_LSECTIONAL_LRM_BOUND THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  ASM_MESON_TAC[riemannian_metric]);;

let RFA_NONCOLLINEAR_BASIS = prove
 (`2 <= dimindex(:N) ==> ~collinear {vec 0:real^N, basis 1, basis 2}`,
  DISCH_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    X_GEN_TAC `c:real` THEN DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. v$2`) THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `1 <= 2 /\ 2 <= dimindex(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[BASIS_COMPONENT]] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let RFA_MFD_RM_NORM_LE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x B.
        2 <= dimindex(:N) /\
        (!u v. ~collinear {vec 0,u,v} ==> abs(mfd_sectional atlas g x u v) <= B)
        ==> mfd_rm_norm atlas g x <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`abs(mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x
                         (basis 1) (basis 2))`;
      `basis 1:real^N`; `basis 2:real^N`] THEN
    ASM_SIMP_TAC[RFA_NONCOLLINEAR_BASIS];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

let RFA_MFD_SECTIONAL_LE_NORM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ ~collinear {vec 0,u,v}
        ==> abs(mfd_sectional atlas g x u v) <= mfd_rm_norm atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN
  MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
   [EXISTS_TAC `sqrt(rfa_rmd2 0 (atlas:((A->bool)#(A->real^N))->bool)
                                (g:A->real^N^N) x)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN ASM_REWRITE_TAC[]]);;

(* R2: the doubling-time estimate (MT Prop 4.11, CLN Lemma 6.1). *)

let RFA_R2 = prove
 (`!(u:A->bool) (n:N->bool). PDE_REQ_RM_DOUBLING_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PDE_REQ_RM_DOUBLING_STATEMENT] THEN
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A14"))
    (INST_TYPE [`:N`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  X_CHOOSE_THEN `Cp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dbl"))
    (INST_TYPE [`:A`,`:A`; `:N`,`:N`] RFA_RMD2_DOUBLING) THEN
  ABBREV_TAC `C3 = C2 + &1` THEN
  SUBGOAL_THEN `&0 < C3 /\ C2 <= C3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt C3` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Cp * sqrt C3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  EXISTS_TAC `inv(Cp * sqrt C3)` THEN EXISTS_TAC `&2 * sqrt C3` THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `K:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^N^N) a)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_RICCI_FLOW_FROM_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                                 a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> rfa_rmd2 0 atlas ((g:real->A->real^N^N) a) (x:A) <= C3 * K pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C2 * K pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[rfa_rmd2] THEN USE_THEN "A14" MATCH_MP_TAC THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
             CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                       ((g:real->A->real^N^N) a)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`p:real^N`; `q:real^N`] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_rm_norm atlas ((g:real->A->real^N^N) a) (x:A)` THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM mfd_sectional] THEN
      MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C3 * K pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(C3 * K pow 2) = sqrt C3 * K` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  USE_THEN "dbl" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
    `g:real->A->real^N^N`; `C3 * K pow 2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfa_rmd2 0 atlas ((g:real->A->real^N^N) t) (x:A) <= &4 * (C3 * K pow 2)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t - a <= inv(Cp * sqrt C3) / K` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Cp * sqrt C3) * ((t - a) * K) <= (Cp * sqrt C3) * inv(Cp * sqrt C3)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= &1 ==> y <= &1`) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:real^N`; `q:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(rfa_rmd2 0 atlas ((g:real->A->real^N^N) t) (x:A))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_RMD2 THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&4 * (C3 * K pow 2))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
                  MATCH_MP_TAC RFA_RMD2_POS THEN EXISTS_TAC `top:A topology` THEN
                  ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(&4) = &2` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
  UNDISCH_TAC `sqrt(C3 * K pow 2) = sqrt C3 * K` THEN REWRITE_TAC[SQRT_MUL] THEN
  CONV_TAC REAL_RING);;

