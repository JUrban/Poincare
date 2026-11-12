(* ========================================================================= *)
(* Unit pc_p2c_stdnc2 (Part 2C): small times for the noncollapsing of        *)
(* partial standard flows.  On [0,t0], t0 < te, the curvature of G is        *)
(* bounded (p3_partial_std), so G t and g0 are equivalent with a factor L    *)
(* (PV411_QFORM_EQUIV, the Ricci bound RFA_R1_RIC_BOUND), balls of g0 sit in *)
(* balls of G t (RFAH_DIST_COMPARE), volumes compare                         *)
(* (MFD_HAS_VOLUME_COMPARE_QF), and the small g0-balls of                    *)
(* STNC_G0_SMALL_BALLS give vol >= kappa1 r^3 with no curvature hypothesis:  *)
(* the pattern of PV411_PROP_4_11_VOLUME on R^3.                             *)
(* ========================================================================= *)

needs "src/pc_p2c_stdnc1.ml";;
needs "src/pc_pv411.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Metric equivalence on [0,t0] and the small-time volume                   *)
(* bound.                                                                     *)
(* ------------------------------------------------------------------------- *)

let STNC_METRIC_EQUIV = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < t0 /\ t0 < te
     ==> ?L. &1 <= L /\
             !t x v. &0 <= t /\ t <= t0
                     ==> v dot (G t x ** v) <= L * (v dot (g0 x ** v)) /\
                         v dot (g0 x ** v) <= L * (v dot (G t x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_partial_std]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmd"))
    (INST_TYPE [`:real^3`,`:A`; `:3`,`:N`] RFA_R1_RMD0) THEN
  ABBREV_TAC `K1 = &(dimindex(:3)) * sqrt(C0 * K pow 2)` THEN
  SUBGOAL_THEN `&0 <= K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < te
                    ==> riemannian_metric (open_set_atlas (:real^3))
                          ((G:real->real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te
                   (G:real->real^3->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
    ASM_CASES_TAC `s = &0` THENL
     [ASM_SIMP_TAC[];
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s z v. &0 <= s /\ s <= t0 /\ z IN topspace euclidean
            ==> abs(mfd_ricci (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s) z v v)
                <= K1 * (v dot (G s z ** v))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) s)`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "K1" THEN MATCH_MP_TAC RFA_R1_RIC_BOUND THEN
    EXISTS_TAC `euclidean:(real^3)topology` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; P2C_EUCLID_FACTS] THEN
    USE_THEN "rmd" MATCH_MP_TAC THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
    ASM_SIMP_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `&0`; `te:real`;
                 `G:real->real^3->real^3^3`; `t0:real`; `K1:real`] PV411_QFORM_EQUIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC] THEN
  EXISTS_TAC `exp(&2 * K1 * t0)` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC PV411_EXP_EQUIV_L THEN EXISTS_TAC `exp(&2 * K1 * t)` THEN
  REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_NEG] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC PV411_QPOS THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`] THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN
    UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PV411_QPOS THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`] THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `exp`)) (concl th))) THEN
    ASM_SIMP_TAC[P2C_EUCLID_FACTS; IN_UNIV];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `exp`)) (concl th))) THEN
    ASM_SIMP_TAC[P2C_EUCLID_FACTS; IN_UNIV]]);;

let STNC_SMALL_TIME_VOL = prove
 (`!g0 A0 te (G:real->real^3->real^3^3) t0.
     p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ &0 < t0 /\ t0 < te
     ==> ?rho1 kappa1. &0 < rho1 /\ &0 < kappa1 /\
           !t x r. &0 <= t /\ t <= t0 /\ &0 < r /\ r <= rho1
                   ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) (G t)
                             (mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) x r) v /\
                           kappa1 * r pow 3 <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `G:real->real^3->real^3^3`;
                 `t0:real`] STNC_METRIC_EQUIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "eq"))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `rho0:real` (X_CHOOSE_THEN `c0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n0")))) o
    MATCH_MP STNC_G0_SMALL_BALLS) THEN
  SUBGOAL_THEN `&0 < L /\ &0 < sqrt L /\ &1 <= sqrt L` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&1 <= L ==> &0 < L`] THEN
    ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rho0:real`; `c0 / L pow 3`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `r:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_partial_std]) THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3) /\
                riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) /\
                mfd_complete (euclidean,open_set_atlas (:real^3)) (G t)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te
                     (G:real->real^3->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
      ASM_CASES_TAC `t = &0` THENL
       [ASM_SIMP_TAC[];
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / sqrt L /\ r / sqrt L <= rho0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rho0 * &1` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "n0" (MP_TAC o SPECL [`x:real^3`; `r / sqrt L`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x (r / sqrt L) SUBSET
    mfd_ball (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) x r`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sqrt L * mfd_dist (euclidean,open_set_atlas (:real^3)) g0 x y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFAH_DIST_COMPARE THEN ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN
      REPEAT STRIP_TAC THEN USE_THEN "eq" (MP_TAC o SPECL [`t:real`; `z:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(G:real->real^3->real^3^3) t`; `x:real^3`; `r:real`] MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN STRIP_TAC THEN
  EXISTS_TAC `mfd_volume (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)
                (mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) x r)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(G:real->real^3->real^3^3) t`;
                 `mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x (r / sqrt L)`;
                 `mfd_ball (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t) x r`;
                 `mfd_volume (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)
                    (mfd_ball (euclidean,open_set_atlas (:real^3)) (G t) x r)`]
    MFD_HAS_VOLUME_SUBSET) THEN
  ASM_REWRITE_TAC[P2C_EUCLID_FACTS] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`g0:real^3->real^3^3`; `\x:real^3. &1`; `v0:real`] THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume; P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  ABBREV_TAC `vt = mfd_volume (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) t)
                     (mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x (r / sqrt L))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `(G:real->real^3->real^3^3) t`;
                 `mfd_ball (euclidean,open_set_atlas (:real^3)) g0 x (r / sqrt L)`;
                 `v0:real`; `vt:real`; `L:real`] MFD_HAS_VOLUME_COMPARE_QF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2C_EUCLID_FACTS; REAL_LT_IMP_LE] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    USE_THEN "eq" (MP_TAC o SPECL [`t:real`; `y:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < L * sqrt L` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `c0 * (r / sqrt L) pow 3 <= (L * sqrt L) * vt` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 / L pow 3 * r pow 3 = (c0 * (r / sqrt L) pow 3) / (L * sqrt L)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `sqrt L pow 2 = L` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sqrt L` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `vt:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

