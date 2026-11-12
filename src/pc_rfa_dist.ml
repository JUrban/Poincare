(* ========================================================================= *)
(* Unit pc_rfa_dist: MT Prop 3.21 in local form with a backward difference,  *)
(* the statement P2B_REQ_RFA_DIST_LOCAL_STATEMENT of pc_p2b_distreq.  Along  *)
(* a Ricci flow with complete slice at t, take a minimizing g(t)-geodesic    *)
(* gamma from x0 to x1 (Hopf-Rinow); the g(s)-length of gamma has derivative *)
(* -int Ric(gamma',gamma')/|gamma'| at s = t (dominated differentiation,     *)
(* curvature bounded on a compact neighbourhood in spacetime), MT Claim 3.24 *)
(* (CMP_RICCI_INTEGRAL of pc_cmp_index) bounds the integral when d >= 2 r0,  *)
(* and for d < 2 r0 the whole geodesic lies in the two end balls.  Main      *)
(* theorem RFA_P2B_REQ_RFA_DIST_LOCAL.                                       *)
(* ========================================================================= *)

needs "src/pc_p2b_distreq.ml";;
needs "src/pc_cmp_index.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_rfa_r1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Restriction of a Ricci flow to a later start                              *)
(* (RFA_DS_FLOW_FROM), a bound of |Rm|^2 on [t1,t2] times a compact curve    *)
(* (RFA_DS_RMD2_BOUND), and the pointwise Gronwall comparison of the metric  *)
(* along the flow under a pointwise Ricci bound (RFA_DS_QFORM_PT).           *)
(* ========================================================================= *)

let RFA_DS_FLOW_FROM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t1.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 < b
     ==> ricci_flow_from (top,atlas) t1 b g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ricci_flow_from] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_RICCI_FLOW_ON_EXT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`] THEN ASM_REWRITE_TAC[]]);;

let RFA_DS_RMD2_BOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    (gamma:real->A) t1 t2.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 <= t2 /\ t2 < b /\
     continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) gamma
     ==> ?D. &0 <= D /\
             !s u. t1 <= s /\ s <= t2 /\ u IN real_interval[&0,&1]
                   ==> rfa_rmd2 0 atlas (g s) (gamma u) <= D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `t1:real`; `b:real`;
                 `g:real->A->real^N^N`] RFA_RMD2_CONTINUOUS) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RFA_DS_FLOW_FROM THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `compact_in (prod_topology (subtopology euclideanreal {t | t1 <= t /\ t < b})
                              (subtopology top (topspace top)))
               (real_interval[t1,t2] CROSS IMAGE (gamma:real->A) (real_interval[&0,&1]))`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_IN_CROSS] THEN DISJ2_TAC THEN DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; GSYM real_compact_def; REAL_COMPACT_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL; GSYM real_compact_def;
                      REAL_COMPACT_INTERVAL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prod_topology (subtopology euclideanreal {t | t1 <= t /\ t < b})
                                (subtopology top (topspace (top:A topology)))`;
                 `euclideanreal`;
                 `\z:real#A. rfa_rmd2 0 atlas ((g:real->A->real^N^N) (FST z)) (SND z)`;
                 `real_interval[t1,t2] CROSS IMAGE (gamma:real->A) (real_interval[&0,&1])`]
                IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[GSYM real_compact_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `abs B` THEN
  REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(gamma:real->A) u`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

let RFA_DS_QFORM_PT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    t1 t2 x w C.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t2 < b /\ x IN topspace top /\ &0 <= C /\
     (!s. t1 <= s /\ s <= t2
          ==> abs(mfd_ricci atlas (g s) x w w) <= C * (w dot (g s x ** w)))
     ==> !s t. t1 <= s /\ s <= t2 /\ t1 <= t /\ t <= t2
               ==> w dot (g s x ** w) <= exp(&2 * C * abs(s - t)) * (w dot (g t x ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ric")))))) THEN
  SUBGOAL_THEN
   `!p q. t1 <= p /\ p <= q /\ q <= t2
          ==> exp(--(&2 * C * (q - p))) * (w dot ((g:real->A->real^N^N) p x ** w)) <=
              w dot (g q x ** w) /\
              w dot (g q x ** w) <= exp(&2 * C * (q - p)) * (w dot (g p x ** w))`
  (LABEL_TAC "gw") THENL
   [MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `p:real = q` THENL
     [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0;
                      REAL_MUL_LID; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `p < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!r. p <= r /\ r <= q
          ==> ((\r. w dot ((g:real->A->real^N^N) r x ** w)) has_real_derivative
               --(&2) * mfd_ricci atlas (g r) x w w) (atreal r)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\r. w dot ((g:real->A->real^N^N) r x ** w)`;
                   `\r. --(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) (x:A) w w`;
                   `&2 * C`; `p:real`; `q:real`] RFA_GRONWALL_2SIDED) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) r) (x:A) w w` THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        USE_THEN "ric" (MP_TAC o SPEC `r:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC];
      REWRITE_TAC[REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= t \/ t <= s:real`) THENL
   [USE_THEN "gw" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `abs(s - t) = t - s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `&2 * C * (t - s)` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 * C * (t - s)) *
                (exp(--(&2 * C * (t - s))) * (w dot ((g:real->A->real^N^N) s x ** w)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0;
                  REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    USE_THEN "gw" (MP_TAC o SPECL [`t:real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    SUBGOAL_THEN `abs(s - t) = s - t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC]);;

(* ========================================================================= *)
(* The time derivative of the g(s)-length of a fixed C^1 curve               *)
(* of positive g(t)-speed (RFA_DS_LENGTH_DERIV), by dominated               *)
(* differentiation under the integral (CMPV_HAS_REAL_DERIVATIVE_INTEGRAL_    *)
(* DOMINATED) with the bound of RFA_DS_DOM_ALG.                              *)
(* ========================================================================= *)

let RFA_DS_DOM_ALG = prove
 (`!C P P0 Rc h t1 t2.
     &0 <= C /\ abs Rc <= C * P /\ P <= exp(&2 * C * h) * P0 /\ &0 < P /\
     h <= t2 - t1
     ==> abs(--Rc / sqrt P) <= C * exp(C * (t2 - t1)) * sqrt P0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt P` ASSUME_TAC THENL [ASM_REWRITE_TAC[SQRT_LT_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!e. &0 < e /\ &0 < P /\ P <= e * P0 /\ (&0 < e * P0 ==> &0 < P0)
                             ==> &0 <= P0`) THEN
    EXISTS_TAC `exp(&2 * C * h)` THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
    SIMP_TAC[REAL_LT_MUL_EQ; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `sqrt P * sqrt P = P` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt P <= exp(C * h) * sqrt P0` ASSUME_TAC THENL
   [SUBGOAL_THEN `exp(C * h) * sqrt P0 = sqrt(exp(&2 * C * h) * P0)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_MUL; REAL_EXP_POS_LE] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `exp(&2 * C * h) = exp(C * h) pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_2; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        SIMP_TAC[POW_2_SQRT; REAL_EXP_POS_LE]];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(C * h) <= exp(C * (t2 - t1))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(C * h) * sqrt P0 <= exp(C * (t2 - t1)) * sqrt P0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `C * sqrt P <= C * exp(C * (t2 - t1)) * sqrt P0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs Rc <= (C * sqrt P) * sqrt P` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(C * sqrt P) * sqrt P <= (C * exp(C * (t2 - t1)) * sqrt P0) * sqrt P`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_DS_LENGTH_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    (gamma:real->A) t t1 t2.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 < t /\ t < t2 /\ t2 < b /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     (!u. u IN real_interval[&0,&1] ==> &0 < mfd_speed atlas (g t) gamma (&0) (&1) u)
     ==> (\u. --(mfd_ricci atlas (g t) (gamma u)
                    (mfd_velocity atlas gamma (&0) (&1) u)
                    (mfd_velocity atlas gamma (&0) (&1) u)) /
               mfd_speed atlas (g t) gamma (&0) (&1) u)
         real_integrable_on real_interval[&0,&1] /\
         ((\s. mfd_length atlas (g s) gamma (&0) (&1)) has_real_derivative
          real_integral (real_interval[&0,&1])
            (\u. --(mfd_ricci atlas (g t) (gamma u)
                      (mfd_velocity atlas gamma (&0) (&1) u)
                      (mfd_velocity atlas gamma (&0) (&1) u)) /
                 mfd_speed atlas (g t) gamma (&0) (&1) u))
         (atreal t within real_interval[t1,t2])`,
  REPEAT GEN_TAC THEN INTRO_TAC "rf at1 t1t tt2 t2b c1 pos" THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                (!s. a < s /\ s < b ==> riemannian_metric atlas ((g:real->A->real^N^N) s))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. t1 <= s /\ s <= t2 ==> riemannian_metric atlas ((g:real->A->real^N^N) s)`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                  (gamma:real->A)` ASSUME_TAC THENL
   [USE_THEN "c1" (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_c1_curve]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN real_interval[&0,&1] ==> (gamma:real->A) u IN topspace top`
  (LABEL_TAC "intop") THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                   (gamma:real->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `gamma:real->A`; `t1:real`; `t2:real`]
                RFA_DS_RMD2_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))] THEN
  ABBREV_TAC `C = &(dimindex(:N)) * sqrt D` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `vel = mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) (&0) (&1)` THEN
  SUBGOAL_THEN
   `!s u. mfd_speed atlas ((g:real->A->real^N^N) s) (gamma:real->A) (&0) (&1) u =
          sqrt((vel:real->real^N) u dot (g s (gamma u) ** vel u))`
  (LABEL_TAC "spd") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "vel" THEN REWRITE_TAC[mfd_speed]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u w. t1 <= s /\ s <= t2 /\ u IN real_interval[&0,&1]
            ==> abs(mfd_ricci atlas ((g:real->A->real^N^N) s) ((gamma:real->A) u) w w) <=
                C * (w dot (g s (gamma u) ** w))`
  (LABEL_TAC "ricb") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "C" THEN MATCH_MP_TAC RFA_R1_RIC_BOUND THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "intop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u. t1 <= s /\ s <= t2 /\ u IN real_interval[&0,&1]
          ==> (vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u) <=
              exp(&2 * C * abs(s - t)) * (vel u dot (g t (gamma u) ** vel u)) /\
              vel u dot (g t (gamma u) ** vel u) <=
              exp(&2 * C * abs(t - s)) * (vel u dot (g s (gamma u) ** vel u))`
  (LABEL_TAC "eqv") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) u IN topspace top` ASSUME_TAC THENL
     [USE_THEN "intop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!s'. t1 <= s' /\ s' <= t2
           ==> abs(mfd_ricci atlas ((g:real->A->real^N^N) s') ((gamma:real->A) u)
                     ((vel:real->real^N) u) (vel u)) <=
               C * (vel u dot (g s' (gamma u) ** vel u))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "ricb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^N^N`; `t1:real`; `t2:real`; `(gamma:real->A) u`;
                   `(vel:real->real^N) u`; `C:real`] RFA_DS_QFORM_PT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u. t1 <= s /\ s <= t2 /\ u IN real_interval[&0,&1]
          ==> &0 < (vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)`
  (LABEL_TAC "phipos") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "eqv" (MP_TAC o SPECL [`s:real`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    USE_THEN "pos" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "spd" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SQRT_LT_0] THEN
    MP_TAC(SPEC `&2 * C * abs(t - s)` REAL_EXP_POS_LT) THEN
    ABBREV_TAC `e = exp(&2 * C * abs(t - s))` THEN
    ABBREV_TAC `P = (vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)` THEN
    ABBREV_TAC `P0 = (vel:real->real^N) u dot ((g:real->A->real^N^N) t ((gamma:real->A) u) ** vel u)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 < e * P` MP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_MUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u. t1 <= s /\ s <= t2 /\ u IN real_interval[&0,&1]
          ==> ((\s. mfd_speed atlas ((g:real->A->real^N^N) s) (gamma:real->A) (&0) (&1) u)
               has_real_derivative
               --(mfd_ricci atlas (g s) (gamma u) ((vel:real->real^N) u) (vel u)) /
               mfd_speed atlas (g s) gamma (&0) (&1) u)
              (atreal s within real_interval[t1,t2])`
  (LABEL_TAC "fd") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "spd" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 < (vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)`
    ASSUME_TAC THENL [USE_THEN "phipos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^N^N`; `s:real`; `(gamma:real->A) u`;
                   `(vel:real->real^N) u`] RFA_QFORM_DERIV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "intop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      DISCH_TAC] THEN
    MP_TAC(SPEC `(vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)`
                HAS_REAL_DERIVATIVE_SQRT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. (vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)`;
                   `sqrt`;
                   `--(&2) * mfd_ricci atlas ((g:real->A->real^N^N) s) ((gamma:real->A) u)
                                   ((vel:real->real^N) u) (vel u)`;
                   `inv(&2 * sqrt((vel:real->real^N) u dot
                                   ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)))`;
                   `s:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 < sqrt((vel:real->real^N) u dot
                            ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u))`
    MP_TAC THENL [ASM_REWRITE_TAC[SQRT_LT_0]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u. t1 <= s /\ s <= t2 /\ u IN real_interval[&0,&1]
          ==> abs(--(mfd_ricci atlas ((g:real->A->real^N^N) s) ((gamma:real->A) u)
                       ((vel:real->real^N) u) (vel u)) /
                  mfd_speed atlas (g s) gamma (&0) (&1) u) <=
              C * exp(C * (t2 - t1)) * mfd_speed atlas (g t) gamma (&0) (&1) u`
  (LABEL_TAC "dom") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "spd" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ricb" (MP_TAC o SPECL [`s:real`; `u:real`; `(vel:real->real^N) u`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "eqv" (MP_TAC o SPECL [`s:real`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    USE_THEN "phipos" (MP_TAC o SPECL [`s:real`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(s - t) <= t2 - t1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `P = (vel:real->real^N) u dot ((g:real->A->real^N^N) s ((gamma:real->A) u) ** vel u)` THEN
    ABBREV_TAC `P0 = (vel:real->real^N) u dot ((g:real->A->real^N^N) t ((gamma:real->A) u) ** vel u)` THEN
    ABBREV_TAC `Rc = mfd_ricci atlas ((g:real->A->real^N^N) s) ((gamma:real->A) u)
                       ((vel:real->real^N) u) (vel u)` THEN
    ABBREV_TAC `h = abs(s - t)` THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC RFA_DS_DOM_ALG THEN EXISTS_TAC `h:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s u. mfd_speed atlas ((g:real->A->real^N^N) s) (gamma:real->A) (&0) (&1) u`;
    `\s u. --(mfd_ricci atlas ((g:real->A->real^N^N) s) ((gamma:real->A) u)
                ((vel:real->real^N) u) (vel u)) /
           mfd_speed atlas (g s) gamma (&0) (&1) u`;
    `\u. C * exp(C * (t2 - t1)) *
         mfd_speed atlas ((g:real->A->real^N^N) t) (gamma:real->A) (&0) (&1) u`;
    `real_interval[t1,t2]`; `real_interval[&0,&1]`]
   CMPV_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `u:real`] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN USE_THEN "fd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
      MAP_EVERY X_GEN_TAC [`s:real`; `u:real`] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN USE_THEN "dom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `t1:real` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "vel" THEN REWRITE_TAC[ETA_AX; mfd_length]);;

(* ========================================================================= *)
(* The lower bound -2(n-1)(K r0 + 1/r0) for the derivative                   *)
(* integrand along a minimizing geodesic (RFA_DS_DERIV_LOWER): MT Claim     *)
(* 3.24 when d >= 2 r0, the end balls otherwise.                              *)
(* ========================================================================= *)

let RFA_DS_DERIV_LOWER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x v K r0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x /\
     mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
     &0 < mfd_tnorm g x v /\ &0 < r0 /\ &0 <= K /\
     (!y w. y IN mfd_ball (top,atlas) g x r0 UNION
                 mfd_ball (top,atlas) g (mfd_exp (top,atlas) g x v) r0
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w))) /\
     (\u. --(mfd_ricci atlas g (mfd_geo (top,atlas) g x v u)
               (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)
               (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)) /
          mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) u)
       real_integrable_on real_interval[&0,&1]
     ==> --(&2 * &(dimindex(:N) - 1) * (K * r0 + inv r0)) <=
         real_integral (real_interval[&0,&1])
           (\u. --(mfd_ricci atlas g (mfd_geo (top,atlas) g x v u)
                     (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)
                     (mfd_velocity atlas (mfd_geo (top,atlas) g x v) (&0) (&1) u)) /
                mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) u)`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus sma rm xtop vdom dist dpos r0 K ric int" THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `d = mfd_tnorm (g:A->real^N^N) x v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,&1] SUBSET J` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `is_realinterval (J:real->bool)` THEN
    REWRITE_TAC[is_realinterval; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,&1]
        ==> mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) (&1) u =
            mfd_vel atlas gam u /\
            mfd_speed atlas (g:A->real^N^N) gam (&0) (&1) u = d /\
            mfd_vel atlas gam u dot (g (gam u) ** mfd_vel atlas gam u) = d pow 2 /\
            mfd_tnorm g (gam u) (mfd_vel atlas gam u) = d`
  (LABEL_TAC "vs") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) (&1) u =
                  mfd_vel atlas gam u`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GEOM_VELOCITY_EQ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gam:real->A) u IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gam:real->A) u)
                    (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam u) = d`
    ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gam:real->A`; `J:real->bool`; `u:real`; `&0`]
                    MFD_GEODESIC_SPEED) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_speed] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_tnorm (g:A->real^N^N) ((gam:real->A) u)
                     (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam u) = d` THEN
      REWRITE_TAC[mfd_tnorm];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(gam:real->A) u`] GEOD_TNORM_BASIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `R1 = \u. mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                        (mfd_vel atlas gam u) (mfd_vel atlas gam u)` THEN
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,&1]
        ==> --(mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                 (mfd_velocity atlas gam (&0) (&1) u) (mfd_velocity atlas gam (&0) (&1) u)) /
            mfd_speed atlas g gam (&0) (&1) u = --inv d * (R1:real->real) u`
  (LABEL_TAC "intg") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "vs" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R1" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 * r0 <= d` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `v:real^N`; `K:real`; `r0:real`]
           (REWRITE_RULE[CMP_RICCI_INTEGRAL_STATEMENT]
             (ISPECL [`(:A)`; `(:N)`] CMP_RICCI_INTEGRAL))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ric" ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\t. mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) t) (mfd_vel atlas gam t)
             (mfd_vel atlas gam t)) = R1` SUBST1_TAC THENL
     [EXPAND_TAC "R1" THEN REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `real_integral (real_interval[&0,&1])
        (\u. --(mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                  (mfd_velocity atlas gam (&0) (&1) u) (mfd_velocity atlas gam (&0) (&1) u)) /
             mfd_speed atlas g gam (&0) (&1) u) =
      real_integral (real_interval[&0,&1]) (\u. --inv d * (R1:real->real) u)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN BETA_TAC THEN USE_THEN "intg" ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL] THEN
    ABBREV_TAC `I1 = real_integral (real_interval[&0,&1]) (R1:real->real)` THEN
    ABBREV_TAC `N1 = &(dimindex(:N) - 1)` THEN
    SUBGOAL_THEN `&0 <= N1 * K * r0 /\ &0 <= N1 * inv r0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "N1" THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; REAL_LE_INV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv d * I1 <= &2 * N1 * (&2 / &3 * K * r0 + inv r0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv d * (d * &2 * N1 * (&2 / &3 * K * r0 + inv r0))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 <= N1 * K * r0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d < &2 * r0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval[&0,&1]
        ==> --(&(dimindex(:N) - 1) * K * d) <=
            --(mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                 (mfd_velocity atlas gam (&0) (&1) u) (mfd_velocity atlas gam (&0) (&1) u)) /
            mfd_speed atlas g gam (&0) (&1) u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "intg" (fun th -> ASM_SIMP_TAC[th]) THEN EXPAND_TAC "R1" THEN BETA_TAC THEN
    USE_THEN "vs" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `(gam:real->A) u IN mfd_ball (top,atlas) (g:A->real^N^N) x r0 UNION
                         mfd_ball (top,atlas) g (mfd_exp (top,atlas) g x v) r0`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(u:real) IN J /\ &0 IN J /\ &1 IN J` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `real_interval[&0,&1] SUBSET J` THEN
        UNDISCH_TAC `(u:real) IN real_interval[&0,&1]` THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[REAL_LE_REFL; REAL_POS];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `gam:real->A`; `J:real->bool`; `&0`; `u:real`] GEOH_GEO_SEG_DIST) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "j0") (LABEL_TAC "d0"))] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `gam:real->A`; `J:real->bool`; `&1`; `u:real`] GEOH_GEO_SEG_DIST) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "j1") (LABEL_TAC "d1"))] THEN
      SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((gam:real->A) (&0))
                      (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam (&0)) = d /\
                    mfd_tnorm (g:A->real^N^N) ((gam:real->A) (&1))
                      (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gam (&1)) = d`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "vs" (MP_TAC o SPEC `&0`); USE_THEN "vs" (MP_TAC o SPEC `&1`)] THEN
        REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN SIMP_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(u:real) IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `abs(u - &0) = u /\ abs(u - &1) = &1 - u` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `mfd_dist (top,atlas) (g:A->real^N^N) ((gam:real->A) (&0)) (gam u) <= u * d /\
        mfd_dist (top,atlas) (g:A->real^N^N) ((gam:real->A) (&1)) (gam u) <= (&1 - u) * d`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [REMOVE_THEN "d0" MP_TAC; REMOVE_THEN "d1" MP_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[mfd_ball; IN_UNION; IN_ELIM_THM; mfd_exp] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(gam:real->A) (&0) = x` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_CASES_TAC `u * d < r0` THENL
       [DISJ1_TAC THEN USE_THEN "j0" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
        DISJ2_TAC THEN USE_THEN "j1" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "ric" (MP_TAC o SPECL [`(gam:real->A) u`;
      `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) u`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `Rr = mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) u)
                       (mfd_vel atlas gam u) (mfd_vel atlas gam u)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Rr * inv d <= (&(dimindex(:N) - 1) * K * d pow 2) * inv d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&(dimindex(:N) - 1) * K * d pow 2) * inv d = &(dimindex(:N) - 1) * K * d`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1]) (\u. --(&(dimindex(:N) - 1) * K * d))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN
    ABBREV_TAC `N1 = &(dimindex(:N) - 1)` THEN
    SUBGOAL_THEN `&0 <= N1 * K * r0 /\ &0 <= N1 * inv r0 /\ N1 * K * d <= N1 * K * (&2 * r0)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "N1" THEN REPEAT CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST]]);;

(* ========================================================================= *)
(* Facts about the geodesic exp_x(tv) on [0,1]                               *)
(* (RFA_DS_GEO_FACTS) and the headline RFA_P2B_REQ_RFA_DIST_LOCAL:           *)
(* |- !u n. P2B_REQ_RFA_DIST_LOCAL_STATEMENT u n.                           *)
(* ========================================================================= *)

let RFA_DS_GEO_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x
     ==> mfd_c1_curve (top,atlas) (mfd_geo (top,atlas) g x v) (&0) (&1) /\
         mfd_geo (top,atlas) g x v (&0) = x /\
         mfd_geo (top,atlas) g x v (&1) = mfd_exp (top,atlas) g x v /\
         mfd_length atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) = mfd_tnorm g x v /\
         !u. u IN real_interval[&0,&1]
             ==> mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) u =
                 mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,&1] SUBSET J` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `is_realinterval (J:real->bool)` THEN
    REWRITE_TAC[is_realinterval; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `J:real->bool`; `&0`; `&1`] MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LT_01; REAL_SUB_RZERO; REAL_MUL_LID] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_exp] THEN
  X_GEN_TAC `u:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_speed] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `J:real->bool`; `u:real`; `&0`]
                MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[mfd_tnorm]);;

let RFA_P2B_REQ_RFA_DIST_LOCAL = prove
 (`!(u:A->bool) (n:N->bool). P2B_REQ_RFA_DIST_LOCAL_STATEMENT u n`,
  REWRITE_TAC[P2B_REQ_RFA_DIST_LOCAL_STATEMENT] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "haus rf at tb cpl x0 x1 jn r0 K ric" THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                (!s. a < s /\ s < b ==> riemannian_metric atlas ((g:real->A->real^N^N) s))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `C = &2 * &(dimindex(:N) - 1) * (K * r0 + inv r0)` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) ((g:real->A->real^N^N) t) x0 x1` THEN
  ASM_CASES_TAC `d = &0` THENL
   [SUBGOAL_THEN `(x1:A) = x0` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) t`; `x0:A`; `x1:A`] MFD_DIST_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `t - a` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) (t - s)`; `x0:A`] MFD_DIST_REFL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`; `x0:A`; `x1:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x0:A`; `x1:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x0:A`; `v:real^N`] RFA_DS_GEO_FACTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) ((g:real->A->real^N^N) t) x0 v` THEN
  ABBREV_TAC `t1 = (a + t) / &2` THEN ABBREV_TAC `t2 = (t + b) / &2` THEN
  SUBGOAL_THEN `a < t1 /\ t1 < t /\ t < t2 /\ t2 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `gam:real->A`; `t:real`; `t1:real`; `t2:real`]
                RFA_DS_LENGTH_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `I0 = real_integral (real_interval[&0,&1])
           (\u. --(mfd_ricci atlas ((g:real->A->real^N^N) t) ((gam:real->A) u)
                     (mfd_velocity atlas gam (&0) (&1) u)
                     (mfd_velocity atlas gam (&0) (&1) u)) /
                mfd_speed atlas (g t) gam (&0) (&1) u)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "der")) THEN
  SUBGOAL_THEN `--C <= I0` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN EXPAND_TAC "I0" THEN EXPAND_TAC "gam" THEN
    MATCH_MP_TAC RFA_DS_DERIV_LOWER THEN ASM_REWRITE_TAC[IN_UNIV] THEN
    UNDISCH_TAC `(\u. --(mfd_ricci atlas ((g:real->A->real^N^N) t) ((gam:real->A) u)
                     (mfd_velocity atlas gam (&0) (&1) u)
                     (mfd_velocity atlas gam (&0) (&1) u)) /
                mfd_speed atlas (g t) gam (&0) (&1) u)
                real_integrable_on real_interval[&0,&1]` THEN
    EXPAND_TAC "gam" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_length atlas ((g:real->A->real^N^N) s) (gam:real->A) (&0) (&1)`;
                 `I0:real`; `t:real`; `real_interval[t1,t2]`; `e:real`] RFA_LEFT_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  EXISTS_TAC `min d1 (t - t1)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "lb" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) (t - s)`; `gam:real->A`; `&0`; `&1`]
                MFD_DIST_LE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s * --I0 <= s * C` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

