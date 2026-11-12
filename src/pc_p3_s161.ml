(* ========================================================================= *)
(* Unit pc_p3_s161: MT Prop 16.1 (Sec 16.6) on the Kleiner-Lott route: the   *)
(* large-scale core (MT Claims 16.27, 16.28, Lemma 11.2 and Thm 8.1 at the   *)
(* second scale rr of Props 16.4, 16.21, Cor 16.24) and the assembly with    *)
(* the small-scale statement P3N_SMALL_SCALE_STATEMENT (KL Sublemma 79.23).  *)
(* ========================================================================= *)

needs "src/pc_rfa_histc2c.ml";;
needs "src/pc_rfa_pinchrm.ml";;
needs "src/pc_p3_s13rot.ml";;
needs "src/pc_p2c_hreg.ml";;
needs "src/pc_p2a_p164.ml";;
needs "src/pc_p2a_hreg.ml";;
needs "src/pc_p3_s16small.ml";;
needs "src/pc_p2a_reach.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A standard initial metric has scalar curvature bounded below              *)
(* by a positive constant (MT Lemma 12.3 for every g0 of Def 12.1): near the *)
(* tip all sectional curvatures are 1/4; elsewhere the plane tangent to the  *)
(* SO(3)-orbit has curvature (1 - f'^2)/f^2 >= c > 0 (P3S_ROT_SEC_TAN_POS),  *)
(* and a frame through it (RFA_FRAME3) with the other sectional curvatures   *)
(* >= 0 gives R >= 2c.                                                       *)
(* ------------------------------------------------------------------------- *)

let P3L_TANGENT_PAIR = prove
 (`!x:real^3. ~(x = vec 0)
              ==> ?u v. u dot x = &0 /\ v dot x = &0 /\ u dot v = &0 /\
                        ~(u = vec 0) /\ ~(v = vec 0) /\ ~collinear {vec 0,u,v}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?w:real^3. ~(x cross w = vec 0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real^3` CROSS_BASIS_NONZERO) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x cross w:real^3`; `x cross (x cross w):real^3`] THEN
  SUBGOAL_THEN `(x cross w) dot (x:real^3) = &0 /\ (x cross (x cross w)) dot x = &0 /\
                (x cross w) dot (x cross (x cross w)) = &0 /\ x dot (x cross w) = &0`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_CROSS_SELF]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x cross (x cross w):real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN
    ONCE_REWRITE_TAC[REAL_RING `x = &0 <=> x pow 2 = &0`] THEN
    ONCE_REWRITE_TAC[NORM_CROSS] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO; REAL_ENTIRE; REAL_POW_EQ_0;
                NORM_EQ_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM CROSS_EQ_0; GSYM NORM_EQ_0] THEN
  ONCE_REWRITE_TAC[REAL_RING `x = &0 <=> x pow 2 = &0`] THEN
  ONCE_REWRITE_TAC[NORM_CROSS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO; REAL_ENTIRE; REAL_POW_EQ_0;
              NORM_EQ_0] THEN
  ASM_REWRITE_TAC[]);;

(* The plane tangent to the orbit through x has curvature sec_tan(dist x).  *)

let P3L_STD_SEC_TAN = prove
 (`!g0 A0 (x:real^3) u v.
     p3_std_initial g0 A0 /\ ~(x = vec 0) /\ u dot x = &0 /\ v dot x = &0 /\
     u dot v = &0 /\ ~(u = vec 0) /\ ~(v = vec 0) /\ ~collinear {vec 0,u,v}
     ==> lsectional g0 x u v = p3s_sec_tan g0 (p3_std_dist g0 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SECTIONAL] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
               P3S_ROT_SEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `u:real^3`]
               P3S_ROT_BIL) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`; `v:real^3`]
               P3S_ROT_BIL) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
               P3S_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_SUB_RZERO; REAL_ADD_LID;
              REAL_POW_ZERO; ARITH_EQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `&0 < u dot (u:real^3) /\ &0 < v dot (v:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3s_rad_b g0 (norm(x:real^3))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`] P3S_STD_POS) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `u:real^3`]
                 P3S_ROT_BIL) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_SUB_RZERO; REAL_ADD_LID] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&0`; `p3s_rad_b g0 (norm(x:real^3))`; `u dot (u:real^3)`]
                 REAL_LT_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < p3s_rad_b g0 (norm(x:real^3))` THEN
  UNDISCH_TAC `&0 < u dot (u:real^3)` THEN UNDISCH_TAC `&0 < v dot (v:real^3)` THEN
  CONV_TAC REAL_FIELD);;

let P3L_STD_SCALAR_POS = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> ?c. &0 < c /\ !x:real^3. c <= lscalar g0 x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[p3_std_initial] (ASSUME `p3_std_initial g0 A0`)) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0:real`] P3S_ROT_SEC_TAN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (&3 / &2) (&2 * c1)` THEN
  CONJ_TAC THENL [UNDISCH_TAC `&0 < c1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `p3_std_dist g0 (x:real^3) < r0` THENL
   [MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `x:real^3`; `basis 1:real^3`;
                   `basis 2:real^3`] RFA_FRAME3) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIV; GSYM CROSS_EQ_0; CROSS_BASIS] THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3`
      (X_CHOOSE_THEN `w1:real^3` (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `lsectional g0 (x:real^3) u1 v1 = &1 / &4 /\
                  lsectional g0 x u1 w1 = &1 / &4 /\ lsectional g0 x v1 w1 = &1 / &4`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SECTIONAL] THEN REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&1 / &4`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `lscalar g0 (x:real^3) =
                 &2 * (lsectional g0 x u1 v1 + lsectional g0 x u1 w1 + lsectional g0 x v1 w1)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(p3_std_dist g0 (x:real^3) < r0)` THEN
    ASM_REWRITE_TAC[p3_std_dist] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `vec 0:real^3`] MFD_DIST_REFL) THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) o
              MATCH_MP P3L_TANGENT_PAIR) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
               P3L_STD_SEC_TAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1 <= lsectional g0 (x:real^3) u v` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(p3_std_dist g0 (x:real^3) < r0)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `x:real^3`; `u:real^3`; `v:real^3`]
                RFA_FRAME3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `v1:real^3`
    (X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 <= lsectional g0 (x:real^3) u1 w1 /\ &0 <= lsectional g0 x v1 w1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SECTIONAL] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&0`)) (concl th) &&
      not (can (find_term ((=) `&1 / &4`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `lscalar g0 (x:real^3) =
               &2 * (lsectional g0 x u1 v1 + lsectional g0 x u1 w1 + lsectional g0 x v1 w1)` THEN
  UNDISCH_TAC `lsectional g0 (x:real^3) u1 v1 = lsectional g0 x u v` THEN
  UNDISCH_TAC `c1 <= lsectional g0 (x:real^3) u v` THEN
  UNDISCH_TAC `&0 <= lsectional g0 (x:real^3) u1 w1` THEN
  UNDISCH_TAC `&0 <= lsectional g0 (x:real^3) v1 w1` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hot surgery caps.  At an event time the scalar curvature of               *)
(* the slice on a cap core Phi(s1 >= 0) is at least c0 / (2 h^2), c0 a       *)
(* positive lower bound of R(g0) (f1), once the control dl is below md dd   *)
(* for dd small (the cap closeness of p3_cap_param, RFA_HC2_CAP_SCALAR_T).   *)
(* P3L_VIEW_AT: the view at a time of slab k is stage k (as P4_VIEW_AT of     *)
(* pc_p4_top, outside this closure).                                         *)
(* ------------------------------------------------------------------------- *)

let P3L_VIEW_AT = prove
 (`!(hs:(A)rfs_history) k s.
     rfs_history_ok hs /\ k <= hs_count hs /\ hs_time hs k <= s /\ s < hs_time hs (k + 1)
     ==> rfs_vtop (rfs_view hs) s = hs_top hs k /\
         rfs_vatlas (rfs_view hs) s = hs_atlas hs k /\
         rfs_vmetric (rfs_view hs) s = hs_metric hs k s /\
         rfs_vscalar (rfs_view hs) s = mfd_scalar (hs_atlas hs k) (hs_metric hs k s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) s /\ rfs_slab hs s = k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[rfs_live] THEN
      SUBGOAL_THEN `k <= hs_count (hs:(A)rfs_history) + 1` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `0`; `k:num`] RFS_TIME_MONO) THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k + 1`; `hs_count (hs:(A)rfs_history) + 1`]
                    RFS_TIME_MONO) THEN
      ASM_REWRITE_TAC[LE_0; LE_REFL; LE_ADD_RCANCEL] THEN
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN
      REWRITE_TAC[rfs_history_ok] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_top_at; rfs_atlas_at;
                  rfs_metric_at; FUN_EQ_THM; rfs_vscalar]);;

let P3L_HOT_ARITH = prove
 (`!c0 D dd hh R s0.
     &0 < hh /\ c0 <= s0 /\ &0 <= D /\ &144 * (&1 + D) * dd <= c0 /\
     abs(hh * R - s0) <= &72 * (&1 + abs D) * dd
     ==> c0 / (&2 * hh) <= R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < hh ==> &0 < &2 * hh`] THEN
  UNDISCH_TAC `abs(hh * R - s0) <= &72 * (&1 + abs D) * dd` THEN
  SUBGOAL_THEN `abs D = D` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `&144 * (&1 + D) * dd <= c0` THEN UNDISCH_TAC `c0 <= s0` THEN
  REAL_ARITH_TAC);;

let P3L_HOT_CAP_POINT = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k i c0 D dd c.
     rfs_history_ok hs /\ k <= hs_count hs /\ p3_std_initial g0 A0 /\
     p3_cap_ok (md,g0,A0) (dl,h) hs k i /\
     &0 < c0 /\ (!x. c0 <= lscalar g0 x) /\
     (!x. p3_std_dist g0 x <= A0 + &4 ==> lrm_deriv_norm2 0 g0 x <= D pow 2) /\
     &0 <= D /\ &0 < dd /\ dd <= &1 / &10 /\ (A0 + &4) * dd < &1 /\
     &144 * (&1 + D) * dd <= c0 /\
     &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= md dd /\ &0 < h(hs_time hs k) /\
     c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
     ==> c0 / (&2 * h(hs_time hs k) pow 2) <=
         mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_TAC `xi:real^3->real^3`) o
                REWRITE_RULE[p3_cap_ok]) THEN
  SUBGOAL_THEN `?q. &0 <= A0 + &4 - p3_std_dist g0 q /\ c = (Phi:real^3->A) q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c:A) IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (REWRITE_RULE[p3_cap_param] th)))))]) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `p3_std_dist g0 q < inv dd` ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_std_dist g0 q * dd < &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(A0 + &4) * dd` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`p3_std_dist g0 q`; `&1`; `dd:real`] REAL_LT_RDIV_EQ) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `h:real->real`; `hs:(A)rfs_history`; `k:num`; `i:num`; `Phi:real^3->A`;
                 `xi:real^3->real^3`; `dd:real`; `D:real`; `q:real^3`]
                RFA_HC2_CAP_SCALAR_T) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> --a < b`) THEN
      ASM_SIMP_TAC[REAL_LT_INV];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P3L_HOT_ARITH THEN
  MAP_EVERY EXISTS_TAC [`D:real`; `dd:real`; `lscalar g0 (q:real^3)`] THEN
  ASM_SIMP_TAC[REAL_POW_LT]);;

(* ------------------------------------------------------------------------- *)
(* MT Claims 16.27 and 16.28.  The L-integrand of an admissible              *)
(* curve is >= -6 sqrt(tau) (pinching); if R >= rho on (T1,T2) the L-length  *)
(* is at least rho (2/3)(T2^3/2 - T1^3/2) - 4 T1^3/2 - 4 (b^3/2 - T2^3/2), so *)
(* a curve with L <= 3 sqrt b meets R < rho in (T1,T2) when rho is large.     *)
(* P3L_ST_SCALAR_LOW is the slice form of P3N_ST_SCALAR_LOW (pc_p3_s1621,    *)
(* outside this closure).                                                    *)
(* ------------------------------------------------------------------------- *)

let P3L_ST_SCALAR_LOW = prove
 (`!(hs:(A)rfs_history) t x.
     rfs_pinched (rfs_view hs) /\ x IN topspace(rfs_top_at hs t)
     ==> --(&6) <= mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN topspace(rfs_top_at hs t)` THEN
    REWRITE_TAC[rfs_top_at; rfs_live] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
  REWRITE_TAC[rfs_view; rfs_pinched] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[rfs_pinched_at] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(&6) / (&4 * t + &1)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> --(&6) <= --(&6 * x)`) THEN
  MATCH_MP_TAC REAL_INV_LE_1 THEN UNDISCH_TAC `&0 <= t` THEN REAL_ARITH_TAC);;

let P3L_SQRT_INTEGRAL = prove
 (`!a b. &0 <= a /\ a <= b
         ==> (sqrt has_real_integral (&2 / &3 * (b * sqrt b - a * sqrt a)))
             (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. &2 / &3 * (t * sqrt t)`; `\t. sqrt t`; `a:real`; `b:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_SQRT];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt x` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt x = &2 / &3 * (x * inv(&2 * sqrt x) + &1 * sqrt x)` SUBST1_TAC THENL
   [MP_TAC(SPEC `x:real` SQRT_POW_2) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < sqrt x` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[]);;

let P3L_L_SPLIT_LOWER = prove
 (`!f b T1 T2 rho ex.
     FINITE ex /\ &0 <= T1 /\ T1 <= T2 /\ T2 <= b /\
     f real_integrable_on real_interval[&0,b] /\
     (!tau. &0 <= tau /\ tau <= b ==> --(&6) * sqrt tau <= f tau) /\
     (!tau. T1 < tau /\ tau < T2 /\ ~(tau IN ex) ==> rho * sqrt tau <= f tau)
     ==> rho * &2 / &3 * (T2 * sqrt T2 - T1 * sqrt T1) - &4 * T1 * sqrt T1 -
         &4 * (b * sqrt b - T2 * sqrt T2)
         <= real_integral (real_interval[&0,b]) f`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = \tau. if T1 < tau /\ tau < T2 /\ ~(tau IN ex) then rho * sqrt tau
                       else --(&6) * sqrt tau` THEN
  SUBGOAL_THEN
   `(g has_real_integral
      (--(&6) * (&2 / &3 * (T1 * sqrt T1 - &0 * sqrt(&0))) +
       rho * (&2 / &3 * (T2 * sqrt T2 - T1 * sqrt T1)) +
       --(&6) * (&2 / &3 * (b * sqrt b - T2 * sqrt T2)))) (real_interval[&0,b])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN EXISTS_TAC `T1:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
      EXISTS_TAC `\tau. --(&6) * sqrt tau` THEN CONJ_TAC THENL
       [EXPAND_TAC "g" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `~(T1 < x)` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC P3L_SQRT_INTEGRAL THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN EXISTS_TAC `T2:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_FINITE THEN
      MAP_EVERY EXISTS_TAC [`\tau. rho * sqrt tau`; `{T1:real,T2} UNION ex`] THEN
      ASM_REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_EMPTY] THEN CONJ_TAC THENL
       [EXPAND_TAC "g" THEN
        REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
                    DE_MORGAN_THM] THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `T1 < x /\ x < T2` STRIP_ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC P3L_SQRT_INTEGRAL THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
      EXISTS_TAC `\tau. --(&6) * sqrt tau` THEN CONJ_TAC THENL
       [EXPAND_TAC "g" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `~(x < T2)` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC P3L_SQRT_INTEGRAL THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real->real`; `f:real->real`; `real_interval[&0,b]`] HAS_REAL_INTEGRAL_LE) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`--(&6) * (&2 / &3 * (T1 * sqrt T1 - &0 * sqrt(&0))) +
      rho * (&2 / &3 * (T2 * sqrt T2 - T1 * sqrt T1)) +
      --(&6) * (&2 / &3 * (b * sqrt b - T2 * sqrt T2))`;
     `real_integral (real_interval[&0,b]) (f:real->real)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_0; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN REAL_ARITH_TAC);;

let P3L_CLAIM_16_27 = prove
 (`!(hs:(A)rfs_history) tt x b gamma T1 T2 rho ex.
     rfs_pinched (rfs_view hs) /\ rfs_L_adm hs tt x b gamma /\ FINITE ex /\
     &0 <= T1 /\ T1 <= T2 /\ T2 <= b /\
     rfs_L_length hs tt gamma b <
     rho * &2 / &3 * (T2 * sqrt T2 - T1 * sqrt T1) - &4 * T1 * sqrt T1 -
     &4 * (b * sqrt b - T2 * sqrt T2)
     ==> ?tau. T1 < tau /\ tau < T2 /\ ~(tau IN ex) /\
               mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                          (gamma tau) < rho`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_adm; rfs_st_curve] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `rfs_L_length hs tt (gamma:real->A) b <
    rho * &2 / &3 * (T2 * sqrt T2 - T1 * sqrt T1) - &4 * T1 * sqrt T1 -
    &4 * (b * sqrt b - T2 * sqrt T2)` THEN
  MATCH_MP_TAC(TAUT `(~p ==> ~q) ==> q ==> p`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c /\ d) <=> a /\ b /\ c ==> ~d`;
              REAL_NOT_LT] THEN
  DISCH_TAC THEN REWRITE_TAC[rfs_L_length] THEN MATCH_MP_TAC P3L_L_SPLIT_LOWER THEN
  EXISTS_TAC `ex:real->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_L_integrand] THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= s * (R + p + &6) ==> --(&6) * s <= s * (R + p)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `--(&6) <= R /\ &0 <= p ==> &0 <= R + p + &6`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC P3L_ST_SCALAR_LOW THEN ASM_SIMP_TAC[];
    SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL
     [UNDISCH_TAC `T1 < tau` THEN UNDISCH_TAC `&0 <= T1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s * (R + p - rho) ==> rho * s <= s * (R + p)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `rho <= R /\ &0 <= p ==> &0 <= R + p - rho`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P3L_16_28_POLY = prove
 (`!s u v rho e2.
     &0 <= v /\ v pow 2 <= &2 / &3 * s pow 2 /\
     &0 <= u /\ u pow 2 = s pow 2 - e2 /\ &0 <= e2 /\ e2 <= &1 / &1600 /\
     &0 <= s /\ &1 / &32 <= s pow 2 /\ &1600 <= rho
     ==> &3 * s < rho * &2 / &3 * (u pow 2 * u - v pow 2 * v) - &4 * v pow 2 * v -
                  &4 * (s pow 2 * s - u pow 2 * u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= s /\ ~(s = &0) ==> &0 < s`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `&1 / &32 <= s pow 2` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `u pow 2 = s pow 2 - e2` THEN UNDISCH_TAC `&0 <= e2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&98 / &100 * s <= u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `u pow 2 = s pow 2 - e2` THEN UNDISCH_TAC `e2 <= &1 / &1600` THEN
    UNDISCH_TAC `&1 / &32 <= s pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v <= &82 / &100 * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [UNDISCH_TAC `&0 <= s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `v pow 2 <= &2 / &3 * s pow 2` THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&98 / &100 * s) pow 3 <= u pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 <= s` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v pow 3 <= (&82 / &100 * s) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s pow 3 - u pow 3 <= &3 * s * e2` ASSUME_TAC THENL
   [SUBGOAL_THEN `e2 = s pow 2 - u pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `u pow 2 = s pow 2 - e2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (s - u) * (&2 * s pow 2 + &2 * s * u - u pow 2)
      ==> s pow 3 - u pow 3 <= &3 * s * (s pow 2 - u pow 2)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `u <= s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s * u /\ u pow 2 <= s pow 2` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s * e2 <= s * (&1 / &1600)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u pow 3 - v pow 3` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(&98 / &100 * s) pow 3 <= u pow 3`;
                           `v pow 3 <= (&82 / &100 * s) pow 3`; `&0 <= s pow 3`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1600 * (u pow 3 - v pow 3) <= rho * (u pow 3 - v pow 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s * (&1 / &32) <= s * s pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(&98 / &100 * s) pow 3 <= u pow 3`; `v pow 3 <= (&82 / &100 * s) pow 3`;
    `s pow 3 - u pow 3 <= &3 * s * e2`; `s * e2 <= s * (&1 / &1600)`;
    `&1600 * (u pow 3 - v pow 3) <= rho * (u pow 3 - v pow 3)`;
    `s * (&1 / &32) <= s * s pow 2`; `&0 < s`] THEN
  REAL_ARITH_TAC);;

let P3L_CLAIM_16_28 = prove
 (`!b T1 eps rho.
     &1 / &32 <= b /\ &0 <= T1 /\ T1 <= &2 / &3 * b /\
     eps pow 2 <= &1 / &1600 /\ &1600 <= rho
     ==> &3 * sqrt b <
         rho * &2 / &3 * ((b - eps pow 2) * sqrt(b - eps pow 2) - T1 * sqrt T1) -
         &4 * T1 * sqrt T1 - &4 * (b * sqrt b - (b - eps pow 2) * sqrt(b - eps pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b /\ &0 <= b - eps pow 2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 / &32 <= b`; `eps pow 2 <= &1 / &1600`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`sqrt b`; `sqrt(b - eps pow 2)`; `sqrt T1`; `rho:real`; `eps pow 2`]
               P3L_16_28_POLY) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE; REAL_LE_POW_2]; ASM_SIMP_TAC[SQRT_POW_2]]);;

let P3L_CLAIM_16_27_APPLY = prove
 (`!(hs:(A)rfs_history) tt x b gamma T1 eps rho ex.
     rfs_pinched (rfs_view hs) /\ rfs_L_adm hs tt x b gamma /\ FINITE ex /\
     rfs_L_length hs tt gamma b <= &3 * sqrt b /\
     &1 / &32 <= b /\ &0 <= T1 /\ T1 <= &2 / &3 * b /\
     eps pow 2 <= &1 / &1600 /\ &1600 <= rho
     ==> ?tau. T1 < tau /\ tau < b - eps pow 2 /\ ~(tau IN ex) /\
               mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                          (gamma tau) < rho`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3L_CLAIM_16_27 THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`b:real`; `T1:real`; `eps:real`; `rho:real`] P3L_CLAIM_16_28) THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `eps:real` REAL_LE_POW_2) THEN
  MAP_EVERY UNDISCH_TAC
   [`rfs_L_length hs tt (gamma:real->A) b <= &3 * sqrt b`; `T1 <= &2 / &3 * b`;
    `&1 / &32 <= b`; `eps pow 2 <= &1 / &1600`] THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* MT 16.6, the backward ball at y = gamma(tau0) (p. 392).                   *)
(* With R(y,t1) < r0^-2, W = B(y,t1,r0/2C') (C' = max C 2) persists over     *)
(* (t1 - Dl, t1] with R <= 4 r0^-2 there, if Dl <= r0^2/32C', canonical      *)
(* neighbourhoods exist for R >= r0^-2 on the window, t1 is not an event     *)
(* time and the caps of the events in the window are hotter than 4 r0^-2.    *)
(* Otherwise W is exposed at an event time T_k in the window and meets a     *)
(* cap there (RFA_HC2_EXPOSED_WINDOW); Lemma 11.2 bounds R on W after T_k,  *)
(* and right continuity at T_k (P2C_VIEW_SCALAR_CONT_FROM) contradicts the   *)
(* hot cap.                                                                  *)
(* ------------------------------------------------------------------------- *)

let P3L_L112_ARITH = prove
 (`!R r0 Cp Dl d.
     &0 < r0 /\ &0 < Cp /\ R < inv(r0 pow 2) /\ abs d <= Dl /\ Dl <= r0 pow 2 / (&32 * Cp)
     ==> r0 / (&2 * Cp) <= inv(&2 * Cp * sqrt(max R (inv(r0 pow 2)))) /\
         abs d <= inv(&16 * Cp * (max (&0) R + inv(r0 pow 2))) /\
         &2 * (max (&0) R + inv(r0 pow 2)) <= &4 * inv(r0 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `max R (inv(r0 pow 2)) = inv(r0 pow 2)` SUBST1_TAC THENL
   [UNDISCH_TAC `R < inv(r0 pow 2)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SQRT_INV] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < r0` THEN UNDISCH_TAC `&0 < Cp` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r0 pow 2 / (&32 * Cp)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `abs d <= Dl` THEN UNDISCH_TAC `Dl <= r0 pow 2 / (&32 * Cp)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r0 pow 2 / (&32 * Cp) = inv(&16 * Cp * (&2 * inv(r0 pow 2)))` SUBST1_TAC
    THENL
     [UNDISCH_TAC `&0 < r0` THEN UNDISCH_TAC `&0 < Cp` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < inv(r0 pow 2)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < Cp` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `R < inv(r0 pow 2)` THEN UNDISCH_TAC `&0 < inv(r0 pow 2)` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `R < inv(r0 pow 2)` THEN UNDISCH_TAC `&0 < inv(r0 pow 2)` THEN
    REAL_ARITH_TAC]);;

let P3L_BALL_PERSISTS = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !(hs:(A)rfs_history) C eps r0 y t1 Dl.
           rfs_history_ok hs /\ &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < r0 /\
           &0 < Dl /\ &0 <= t1 - Dl /\ t1 < rfs_horizon hs /\
           Dl <= r0 pow 2 / (&32 * max C (&2)) /\
           (!x t. t1 - Dl <= t /\ t <= t1 /\ x IN topspace(rfs_top_at hs t) /\
                  inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                  ==> p3_canon_at (rfs_view hs) C eps x t) /\
           y IN topspace(rfs_top_at hs t1) /\
           rfs_vscalar (rfs_view hs) t1 y < inv(r0 pow 2) /\
           (!k. 1 <= k /\ k <= hs_count hs ==> ~(hs_time hs k = t1)) /\
           (!k i c. 1 <= k /\ k <= hs_count hs /\ t1 - Dl < hs_time hs k /\
                    hs_time hs k < t1 /\ i IN ev_index(hs_event hs k) /\
                    c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
                    ==> &4 * inv(r0 pow 2) < rfs_vscalar (rfs_view hs) (hs_time hs k) c)
           ==> rfs_persists (rfs_view hs)
                 (rfs_vball (rfs_view hs) t1 y (r0 / (&2 * max C (&2)))) (t1 - Dl) t1 /\
               (!s w. t1 - Dl < s /\ s <= t1 /\
                      w IN rfs_vball (rfs_view hs) t1 y (r0 / (&2 * max C (&2)))
                      ==> rfs_vscalar (rfs_view hs) s w <= &4 * inv(r0 pow 2))`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_11_2_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L112"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `y:A`;
                       `t1:real`; `Dl:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "can")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "noev") (LABEL_TAC "hot")))))))))))))) THEN
  ABBREV_TAC `Cp = max C (&2)` THEN
  SUBGOAL_THEN `&2 <= Cp /\ C <= Cp /\ &0 < Cp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN UNDISCH_TAC `&1 < C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) t1 y (r0 / (&2 * Cp))` THEN
  (* canonical neighbourhoods with the constant Cp on the window *)
  SUBGOAL_THEN
   `!x t. t1 - Dl <= t /\ t <= t1 /\ x IN topspace(rfs_top_at hs t) /\
          inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
          ==> p3_canon_at (rfs_view (hs:(A)rfs_history)) Cp eps x t`
  (LABEL_TAC "canp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `(:A)` P2B_CANON_MONO_C) THEN REWRITE_TAC[P2B_CANON_MONO_C_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "can" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Lemma 11.2 from any start T in [t1 - Dl, t1) over which W persists *)
  SUBGOAL_THEN
   `!T0. t1 - Dl <= T0 /\ T0 < t1 /\ rfs_persists (rfs_view (hs:(A)rfs_history)) W T0 t1
         ==> !s w. T0 < s /\ s <= t1 /\ w IN W
                   ==> rfs_vscalar (rfs_view hs) s w <= &4 * inv(r0 pow 2)`
  (LABEL_TAC "back") THENL
   [X_GEN_TAC `T0:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vscalar (rfs_view (hs:(A)rfs_history)) t1 y`; `r0:real`; `Cp:real`;
                   `Dl:real`; `T0 - t1:real`] P3L_L112_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`t1 - Dl <= T0`; `T0 < t1`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "L112" (MP_TAC o SPECL [`hs:(A)rfs_history`; `Cp:real`; `eps:real`; `r0:real`;
      `y:A`; `t1:real`; `T0:real`; `r0 / (&2 * Cp)`]) THEN
    SUBGOAL_THEN `min t1 T0 = T0 /\ max t1 T0 = t1` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`T0 < t1`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "canp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`t1 - Dl <= T0`; `T0 <= t`] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN UNDISCH_TAC `&0 < Cp` THEN
        UNDISCH_TAC `&0 < r0` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC(SPECL [`s:real`; `w:A`] th)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&2 * (max (&0) (rfs_vscalar (rfs_view (hs:(A)rfs_history)) t1 y) +
                       inv(r0 pow 2)) <= &4 * inv(r0 pow 2)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* W is open at t1 *)
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) t1) W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `t1:real`; `y:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN STRIP_TAC THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the persistence *)
  SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W (t1 - Dl) t1` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `t1 - Dl`; `t1:real`]
                  RFA_HC2_EXPOSED_WINDOW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < Dl` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `i0:num` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k0 < t1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b /\ ~(a = b) ==> a < b`) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "noev" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER]
      (ASSUME `~DISJOINT W (IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k0) i0)
                                  (cball(vec 0,&1)))`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `Tk = hs_time (hs:(A)rfs_history) k0` THEN
    SUBGOAL_THEN `rfs_vscalar (rfs_view (hs:(A)rfs_history)) Tk c <= &4 * inv(r0 pow 2)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `mfd_diffeo (rfs_top_at (hs:(A)rfs_history) Tk) (rfs_atlas_at hs Tk) W
                   (rfs_top_at hs t1) (rfs_atlas_at hs t1) W (\y:A. y) (\y. y)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
        REWRITE_TAC[p2c_regular_view] THEN
        DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `Tk:real`; `t1:real`] o last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `Tk:real`; `t1:real`; `c:A`;
                     `(Tk + t1) / &2`] P2C_VIEW_SCALAR_CONT_FROM) THEN
      ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ANTS_TAC THENL
       [UNDISCH_TAC `Tk < t1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
      MP_TAC(ISPECL [`\u. rfs_vscalar (rfs_view (hs:(A)rfs_history)) u c`; `Tk:real`;
                     `(Tk + t1) / &2`; `&4 * inv(r0 pow 2)`] RFA_HC2_CONTON_RIGHT_LE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `Tk < t1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "back" (MP_TAC o SPEC `Tk:real`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `t1 - Dl < Tk` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`Tk < t1`; `s <= (Tk + t1) / &2`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN EXPAND_TAC "Tk" THEN USE_THEN "hot" MATCH_MP_TAC THEN
    EXISTS_TAC `i0:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "back" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `&0 < Dl` THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* MT 16.6 (p. 393), the region at y.  On W persisting over                  *)
(* (a,b] with R <= Q: abs Rm <= 2(abs Q + 6) + 2 e^4 (pinching), and for     *)
(* 8 K (b - s) <= 1 the metrics at s and b agree up to the factor 2          *)
(* (P2AP_METRIC_COMPARE).  The earlier ball B(y,t'',rho) lies in W           *)
(* (P3N_XBALL_IN), its parabolic neighbourhood exists (P3N_PERSIST_SUBOPEN)  *)
(* and noncollapsing passes from the truncation to the history before T_i.   *)
(* ------------------------------------------------------------------------- *)

let P3L_EXP_LE_2 = prove
 (`!x. &0 <= x /\ x <= &1 / &2 ==> exp x <= &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x <= &1 / &2` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `x <= &1 / &2` THEN REAL_ARITH_TAC]);;

let P3L_STEP_EQ = prove
 (`!t j. p3_T j <= t /\ t < p3_T (SUC j) ==> p3_step t = SUC j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ARITH_RULE `a <= b /\ b <= a ==> a = b:num`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P3_STEP_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3_STEP_GE THEN ASM_REWRITE_TAC[]]);;

let P3L_NONCOLL_UNTRUNC = prove
 (`!TM AT G (kp:real->real) r0 tau t x.
     p3_noncoll_all (rfs_trunc (TM:real->A topology,AT,G) tau) kp r0 /\
     &0 <= t /\ t < tau /\ x IN topspace(TM t)
     ==> p3_noncoll_at (TM,AT,G) (kp t) r0 x t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3_noncoll_all; p3_noncoll_at; rfs_trunc; rfs_vtop; rfs_vatlas;
              rfs_vmetric; rfs_parabolic_exists; rfs_persists; rfs_vball] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. s <= t ==> s < tau` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_SIMP_TAC[]);;

let P3L_REGION_QF_NONNEG = prove
 (`!(hs:(A)rfs_history) W a b s y w.
     rfs_history_ok hs /\ a < s /\ s <= b /\ rfs_persists (rfs_view hs) W a b /\ y IN W
     ==> &0 <= w dot (p2c_vfam (rfs_view hs) W b s y ** w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (rfs_view (hs:(A)rfs_history)) W a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (rfs_view (hs:(A)rfs_history)) b) W`;
                 `restrict_atlas (rfs_vatlas (rfs_view (hs:(A)rfs_history)) b) W`;
                 `a:real`; `b:real`; `p2c_vfam (rfs_view (hs:(A)rfs_history)) W b`; `s:real`]
                P2AP_UPTO_RIEM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2AP_REGION_UPTO]; STRIP_TAC] THEN
  MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
  EXISTS_TAC `subtopology (rfs_vtop (rfs_view (hs:(A)rfs_history)) b) W` THEN
  EXISTS_TAC `restrict_atlas (rfs_vatlas (rfs_view (hs:(A)rfs_history)) b) W` THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
  UNDISCH_TAC `(y:A) IN W` THEN SET_TAC[]);;

let P3L_REGION_RM = prove
 (`!(hs:(A)rfs_history) W a b Q.
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\ &0 <= a /\
     rfs_persists (rfs_view hs) W a b /\
     (!s w. a < s /\ s <= b /\ w IN W ==> rfs_vscalar (rfs_view hs) s w <= Q)
     ==> !s w. a < s /\ s <= b /\ w IN W
               ==> p3_vrm (rfs_view hs) s w <= &2 * (abs Q + &6) + &2 * exp(&4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`s:real`; `w:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A) IN topspace(rfs_top_at hs s)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    UNDISCH_TAC `(w:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`; `w:A`] P3N_HIST_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `s:real`; `w:A`] P3N_PINCHED_AT) THEN
  ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                 `rfs_metric_at (hs:(A)rfs_history) s`; `s:real`; `w:A`] RFA_PINCH_RM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`; `w:A`] P2AO_PINCHED_LOW) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `w:A`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Q:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[p3_vrm; P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN REAL_ARITH_TAC);;

let P3L_REGION_CMP = prove
 (`!(hs:(A)rfs_history) W a b K s y w.
     rfs_history_ok hs /\ a < s /\ s <= b /\ rfs_persists (rfs_view hs) W a b /\ &0 <= K /\
     (!t z. a < t /\ t <= b /\ z IN W ==> p3_vrm (rfs_view hs) t z <= K) /\
     &8 * K * (b - s) <= &1 /\ y IN W
     ==> w dot (p2c_vfam (rfs_view hs) W b s y ** w) <=
         &2 * (w dot (p2c_vfam (rfs_view hs) W b b y ** w)) /\
         w dot (p2c_vfam (rfs_view hs) W b b y ** w) <=
         &2 * (w dot (p2c_vfam (rfs_view hs) W b s y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `a:real`; `b:real`; `K:real`;
                 `s:real`; `y:A`; `w:real^3`] P2AP_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AB_SVS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[P2AB_RMETRIC_VFAM] THEN
  SUBGOAL_THEN `exp(&4 * K * (b - s)) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC P3L_EXP_LE_2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&8 * K * (b - s) <= &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`; `s:real`; `y:A`;
                 `w:real^3`] P3L_REGION_QF_NONNEG) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`; `b:real`; `y:A`;
                 `w:real^3`] P3L_REGION_QF_NONNEG) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = w dot (p2c_vfam (rfs_view (hs:(A)rfs_history)) W b s y ** w)` THEN
  ABBREV_TAC `Y = w dot (p2c_vfam (rfs_view (hs:(A)rfs_history)) W b b y ** w)` THEN
  ABBREV_TAC `e = exp(&4 * K * (b - s))` THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `e * Y`; EXISTS_TAC `e * X`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let P3L_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) x r r'.
     r <= r' ==> mfd_ball (top,atlas) g x r SUBSET mfd_ball (top,atlas) g x r'`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LTE_TRANS]);;

let P3L_Y_BALL = prove
 (`!(hs:(A)rfs_history) W a t2 t1 y rW rho K.
     rfs_history_ok hs /\ &0 <= a /\ a < t2 /\ t2 < t1 /\ t1 < rfs_horizon hs /\
     rfs_persists (rfs_view hs) W a t1 /\ &0 < rW /\
     rfs_vball (rfs_view hs) t1 y rW SUBSET W /\ y IN topspace(rfs_top_at hs t1) /\
     (!z w. z IN W
            ==> w dot (p2c_vfam (rfs_view hs) W t1 t1 z ** w) <=
                &2 * (w dot (p2c_vfam (rfs_view hs) W t1 t2 z ** w))) /\
     (!s z. a < s /\ s <= t1 /\ z IN W ==> p3_vrm (rfs_view hs) s z <= K) /\
     &0 < rho /\ rho <= rW / &2 /\ a <= t2 - rho pow 2 /\ K <= inv(rho pow 2)
     ==> rfs_vball (rfs_view hs) t2 y rho SUBSET W /\
         rfs_parabolic_exists (rfs_view hs) t2 y rho (rho pow 2) /\
         (!s z. t2 - rho pow 2 < s /\ s <= t2 /\ z IN rfs_vball (rfs_view hs) t2 y rho
                ==> p3_vrm (rfs_view hs) s z <= inv(rho pow 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Wb") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cmp") (CONJUNCTS_THEN2 (LABEL_TAC "rm")
     STRIP_ASSUME_TAC))))))))))) THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:A)` P2CY_HISTORY_REGULAR) THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL
   [USE_THEN "Wb" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    MATCH_MP_TAC P2AO_VBALL_CENTRE THEN ASM_SIMP_TAC[P2AB_SVS; P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  (* W is open in the slice at t2, so y lies in that slice *)
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) t2) W /\
                smooth_manifold_atlas (rfs_top_at hs t2) (rfs_atlas_at hs t2)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a t1` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `t2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_top_at hs t2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) t2`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t2:real`; `y:A`] P3N_HIST_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the ball at t2 inside W (P3N_XBALL_IN, lam = sqrt 2) *)
  SUBGOAL_THEN `rfs_vball (rfs_view (hs:(A)rfs_history)) t2 y rho SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop (rfs_view (hs:(A)rfs_history)) t2,
                          rfs_vatlas (rfs_view hs) t2) (rfs_vmetric (rfs_view hs) t2) y
                         (rW / sqrt(&2))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[P2C_VIEW_EXPAND] THEN MATCH_MP_TAC P3L_BALL_MONO THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rW / &2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (rfs_vtop (rfs_view (hs:(A)rfs_history)) t1,
                          rfs_vatlas (rfs_view hs) t1) (rfs_vmetric (rfs_view hs) t1) y rW` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3N_XBALL_IN THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t1:real`] P2AB_LIVE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS];
        SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
        USE_THEN "Wb" (ACCEPT_TAC o REWRITE_RULE[P2C_VIEW_EXPAND]);
        SIMP_TAC[SQRT_POW_2; REAL_POS] THEN USE_THEN "cmp" ACCEPT_TAC];
      USE_THEN "Wb" (ACCEPT_TAC o REWRITE_RULE[P2C_VIEW_EXPAND])];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_parabolic_exists] THEN MATCH_MP_TAC P3N_PERSIST_SUBOPEN THEN
    EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AH_PERSISTS_MONO THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `t1:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t`) THEN ASM_SIMP_TAC[REAL_POW_LT];
      REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rm" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Facts of the step setting.  Hot caps with explicit constants              *)
(* (d0, c0 from g0, A0, md: f1, f2, RFA_HC2_STD_BOUNDS); the setting is      *)
(* monotone in the control bound dlt; step functions on a step interval.    *)
(* ------------------------------------------------------------------------- *)

let P3L_HOT_CAPS = prove
 (`!md g0 A0.
     p3_modulus md /\ p3_std_initial g0 A0
     ==> ?d0 c0. &0 < d0 /\ &0 < c0 /\
           !C eps hf rp dl (hs:(A)rfs_history) k i c.
             p3_hfun C hf /\ p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
             1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
             c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)) /\
             dl(hs_time hs k) <= d0
             ==> c0 / (&2 * p3_hscale hf rp dl (hs_time hs k) pow 2) <=
                 rfs_vscalar (rfs_view hs) (hs_time hs k) c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`] P3L_STD_SCALAR_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &4`] RFA_HC2_STD_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `dd0 = min (&1 / &10) (min (inv(&2 * (A0 + &4))) (c1 / (&144 * (&1 + D))))` THEN
  SUBGOAL_THEN `&0 < dd0 /\ dd0 <= &1 / &10 /\ (A0 + &4) * dd0 < &1 /\
                &144 * (&1 + D) * dd0 <= c1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&2 * (A0 + &4)) /\ &0 < c1 / (&144 * (&1 + D))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN UNDISCH_TAC `&0 < A0` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&1 <= D` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "dd0" THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
      EXPAND_TAC "dd0" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(A0 + &4) * inv(&2 * (A0 + &4))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < A0` THEN REAL_ARITH_TAC; EXPAND_TAC "dd0" THEN REAL_ARITH_TAC];
        UNDISCH_TAC `&0 < A0` THEN CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&144 * (&1 + D) * c1 / (&144 * (&1 + D))` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `&1 <= D` THEN REAL_ARITH_TAC; EXPAND_TAC "dd0" THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= D` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(md:real->real) dd0`; `c1:real`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `p3_modulus md` THEN REWRITE_TAC[p3_modulus] THEN
    DISCH_THEN(MP_TAC o SPEC `dd0:real`) THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\
                p3_cap_ok (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i /\
                (!t. &0 <= t ==> &0 < rp t /\ &0 < dl t)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (rp,dl) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k < hs_time hs (k + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_HS_TIME_POS THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `hs_time (hs:(A)rfs_history) k`] P3L_VIEW_AT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3L_HOT_CAP_POINT THEN
  MAP_EVERY EXISTS_TAC [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                        `i:num`; `D:real`; `dd0:real`] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `p3_hfun C (hf:real->real->real)` THEN REWRITE_TAC[p3_hfun; p3_hscale] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(dl:real->real)(hs_time (hs:(A)rfs_history) k) * (rp:real->real)(hs_time hs k)`;
    `(dl:real->real)(hs_time (hs:(A)rfs_history) k)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; SIMP_TAC[]]);;

let P3L_STEPF_AT = prove
 (`!s t j. p3_T j <= t /\ t < p3_T (SUC j) ==> p3_stepf s t = s (SUC j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_stepf] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P3L_STEP_EQ THEN ASM_REWRITE_TAC[]);;

let P3L_P16_SETTING_MONO = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt dlt' rs' ks' dd (hs:(A)rfs_history).
     p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\ dlt <= dlt'
     ==> p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt' (rs',ks',dd) hs`,
  REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `dlt:real` THEN ASM_REWRITE_TAC[]);;

let P3L_SEQ_UPTO_LE = prove
 (`!i (s:num->real). p3_seq_upto i s ==> !j. j <= i ==> s i <= s j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_seq_upto] THEN DISCH_THEN(LABEL_TAC "S") THEN
  SUBGOAL_THEN `!d j. j + d <= i ==> (s:num->real) (j + d) <= s j` MP_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(s:num->real) (j + d)` THEN CONJ_TAC THENL
       [REWRITE_TAC[ADD_CLAUSES] THEN
        USE_THEN "S" (MP_TAC o SPEC `j + d:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i - j:num`; `j:num`]) THEN
  SUBGOAL_THEN `(j:num) + (i - j) = i` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[LE_REFL]]);;

let P3L_HSCALE_LE = prove
 (`!C hf rp dl t.
     p3_hfun C hf /\ &0 < rp t /\ &0 < dl t
     ==> &0 < p3_hscale hf rp dl t /\ p3_hscale hf rp dl t <= dl t pow 2 * rp t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_hfun; p3_hscale] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(dl:real->real) t * (rp:real->real) t`;
                                `(dl:real->real) t`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(hf:real->real->real) ((dl:real->real) t * (rp:real->real) t) (dl t) <=
               (dl t * rp t) * dl t` THEN
  REAL_ARITH_TAC);;

let P3L_HOT_ARITH2 = prove
 (`!c0 h dl rp ri eps.
     &0 < c0 /\ &0 < h /\ h <= dl pow 2 * rp /\ &0 < dl /\ dl <= &1 /\
     dl <= c0 * ri pow 2 / (&16 * eps pow 2) /\ &0 < rp /\ rp <= eps /\ &0 < ri /\ &0 < eps
     ==> &4 * inv(ri pow 2) < c0 / (&2 * h pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h pow 2 <= c0 * ri pow 2 / &16` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dl pow 2 * rp) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl pow 4 * eps pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl * eps pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      SUBGOAL_THEN `dl pow 4 = dl * dl pow 3` SUBST1_TAC THENL
       [REWRITE_TAC[num_CONV `4`; real_pow]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eps pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(c0 * ri pow 2 / (&16 * eps pow 2)) * eps pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < ri pow 2 /\ &0 < c0 * ri pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c0 * ri pow 2 - &8 * h pow 2) / (&2 * h pow 2 * ri pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`h pow 2 <= c0 * ri pow 2 / &16`; `&0 < c0 * ri pow 2`] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &2`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c0 * ri pow 2 - &8 * h pow 2) / (&2 * h pow 2 * ri pow 2) =
                c0 / (&2 * h pow 2) - &4 * inv(ri pow 2)` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < h`; `&0 < ri`] THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The core of MT 16.6 in phases, for a fixed history.                       *)
(* Phase 1 (Claims 16.27, 16.28): on the 16.4 geodesic to T_(i-1) there is   *)
(* tau0 in (max(eps^2, tt - T_i), tt - T_(i-1) - eps^2), with tt - tau0 not  *)
(* an event time, where R < ri^-2.                                           *)
(* ------------------------------------------------------------------------- *)

let P3L_T_FACTS = prove
 (`!j. p3_T (SUC j) = &2 * p3_T j /\ &1 / &32 <= p3_T j`,
  GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[p3_T; real_pow] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`0`; `j:num`] P3_T_MONO) THEN REWRITE_TAC[LE_0] THEN
    REWRITE_TAC[p3_T; real_pow] THEN REAL_ARITH_TAC]);;

let P3L_PH1 = prove
 (`!(hs:(A)rfs_history) tt x gamma i eps ri.
     rfs_pinched (rfs_view hs) /\ 1 <= i /\ p3_T i <= tt /\ tt < p3_T (SUC i) /\
     rfs_min_Lgeod hs tt x (tt - p3_T (i - 1)) gamma /\
     rfs_L_length hs tt gamma (tt - p3_T (i - 1)) <= &3 * sqrt(tt - p3_T (i - 1)) /\
     &0 < eps /\ eps <= &1 / &40 /\ &0 < ri /\ ri <= eps
     ==> ?tau0. max (eps pow 2) (tt - p3_T i) < tau0 /\
                tau0 < (tt - p3_T (i - 1)) - eps pow 2 /\
                (!k. 1 <= k /\ k <= hs_count hs ==> ~(hs_time hs k = tt - tau0)) /\
                mfd_scalar (rfs_atlas_at hs (tt - tau0)) (rfs_metric_at hs (tt - tau0))
                           (gamma tau0) < inv(ri pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?j. i = SUC j` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `i - 1` THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `SUC j - 1 = j`]) THEN
  REWRITE_TAC[ARITH_RULE `SUC j - 1 = j`] THEN
  MP_TAC(SPEC `j:num` P3L_T_FACTS) THEN MP_TAC(SPEC `SUC j` P3L_T_FACTS) THEN
  ABBREV_TAC `T0 = p3_T j` THEN
  ABBREV_TAC `T2 = p3_T (SUC j)` THEN
  ABBREV_TAC `T3 = p3_T (SUC (SUC j))` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_min_Lgeod]) THEN
  SUBGOAL_THEN `eps pow 2 <= &1 / &1600` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &40) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1600 <= inv(ri pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < ri pow 2 /\ ri pow 2 <= &1 / &1600` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &1600)` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ex = IMAGE (\k. tt - hs_time (hs:(A)rfs_history) k) (1..hs_count hs)` THEN
  SUBGOAL_THEN `FINITE (ex:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ex" THEN MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tt - T0`; `gamma:real->A`;
                 `max (eps pow 2) (tt - T2)`; `eps:real`; `inv(ri pow 2)`; `ex:real->bool`]
                P3L_CLAIM_16_27_APPLY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`T2 = &2 * T0`; `T2 <= tt`; `&1 / &32 <= T0`] THEN
      REAL_ARITH_TAC;
      MP_TAC(SPEC `eps:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`T2 = &2 * T0`; `T3 = &2 * T2`; `T2 <= tt`; `tt < T3`;
                             `&1 / &32 <= T0`; `eps pow 2 <= &1 / &1600`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~((tau:real) IN ex)` THEN EXPAND_TAC "ex" THEN
  REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `hs_time (hs:(A)rfs_history) k = tt - tau` THEN REAL_ARITH_TAC);;

(* Phase 2 (MT p. 392-393): the ball W = B(y,t1,rW), rW = ri/2C', persists  *)
(* over (t1 - Dl, t1] with R <= 4 ri^-2 and abs Rm <= K1; on [t1 - Dl1, t1]  *)
(* the metrics agree up to 2; the ball B(y,t1 - Dl1,rho) lies in W, with an  *)
(* existing parabolic neighbourhood on which abs Rm <= rho^-2.              *)

let p3l_k1 = new_definition
 `p3l_k1 (ri:real) = &2 * (abs(&4 * inv(ri pow 2)) + &6) + &2 * exp(&4)`;;

let P3L_PH2 = prove
 (`!u:A->bool.
     P2_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !(hs:(A)rfs_history) C eps ri y t1 Dl Dl1 rho.
           rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
           &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < ri /\
           &0 < Dl /\ &0 <= t1 - Dl /\ t1 < rfs_horizon hs /\
           Dl <= ri pow 2 / (&32 * max C (&2)) /\
           (!x t. t1 - Dl <= t /\ t <= t1 /\ x IN topspace(rfs_top_at hs t) /\
                  inv(ri pow 2) <= rfs_vscalar (rfs_view hs) t x
                  ==> p3_canon_at (rfs_view hs) C eps x t) /\
           y IN topspace(rfs_top_at hs t1) /\
           rfs_vscalar (rfs_view hs) t1 y < inv(ri pow 2) /\
           (!k. 1 <= k /\ k <= hs_count hs ==> ~(hs_time hs k = t1)) /\
           (!k i c. 1 <= k /\ k <= hs_count hs /\ t1 - Dl < hs_time hs k /\
                    hs_time hs k < t1 /\ i IN ev_index(hs_event hs k) /\
                    c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
                    ==> &4 * inv(ri pow 2) < rfs_vscalar (rfs_view hs) (hs_time hs k) c) /\
           &0 < Dl1 /\ &2 * Dl1 <= Dl /\
           &8 * (p3l_k1 ri) * Dl1 <= &1 /\
           &0 < rho /\ rho <= (ri / (&2 * max C (&2))) / &2 /\ rho pow 2 <= Dl1 /\
           p3l_k1 ri <= inv(rho pow 2)
           ==> rfs_persists (rfs_view hs)
                 (rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2)))) (t1 - Dl) t1 /\
               (!s w. t1 - Dl < s /\ s <= t1 /\
                      w IN rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2)))
                      ==> rfs_vscalar (rfs_view hs) s w <= &4 * inv(ri pow 2)) /\
               (!s z w. t1 - Dl1 <= s /\ s <= t1 /\
                        z IN rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2)))
                        ==> w dot (p2c_vfam (rfs_view hs)
                                     (rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2))))
                                     t1 s z ** w) <=
                            &2 * (w dot (p2c_vfam (rfs_view hs)
                                     (rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2))))
                                     t1 t1 z ** w)) /\
                            w dot (p2c_vfam (rfs_view hs)
                                     (rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2))))
                                     t1 t1 z ** w) <=
                            &2 * (w dot (p2c_vfam (rfs_view hs)
                                     (rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2))))
                                     t1 s z ** w))) /\
               rfs_vball (rfs_view hs) (t1 - Dl1) y rho SUBSET
               rfs_vball (rfs_view hs) t1 y (ri / (&2 * max C (&2))) /\
               rfs_parabolic_exists (rfs_view hs) (t1 - Dl1) y rho (rho pow 2) /\
               (!s z. (t1 - Dl1) - rho pow 2 < s /\ s <= t1 - Dl1 /\
                      z IN rfs_vball (rfs_view hs) (t1 - Dl1) y rho
                      ==> p3_vrm (rfs_view hs) s z <= inv(rho pow 2))`,
  REWRITE_TAC[p3l_k1] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3L_BALL_PERSISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `ri:real`; `y:A`;
                       `t1:real`; `Dl:real`; `Dl1:real`; `rho:real`] THEN
  STRIP_TAC THEN
  USE_THEN "BP" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `ri:real`;
                                 `y:A`; `t1:real`; `Dl:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) t1 y (ri / (&2 * max C (&2)))` THEN
  ABBREV_TAC `K1 = &2 * (abs(&4 * inv(ri pow 2)) + &6) + &2 * exp(&4)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s w. t1 - Dl < s /\ s <= t1 /\ w IN W
                      ==> p3_vrm (rfs_view (hs:(A)rfs_history)) s w <= K1`
  (LABEL_TAC "RM") THENL
   [EXPAND_TAC "K1" THEN MATCH_MP_TAC P3L_REGION_RM THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "R" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ri / (&2 * max C (&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC P2AO_VBALL_CENTRE THEN
    ASM_SIMP_TAC[P2AB_SVS; P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s z w. t1 - Dl1 <= s /\ s <= t1 /\ z IN W
            ==> w dot (p2c_vfam (rfs_view (hs:(A)rfs_history)) W t1 s z ** w) <=
                &2 * (w dot (p2c_vfam (rfs_view hs) W t1 t1 z ** w)) /\
                w dot (p2c_vfam (rfs_view hs) W t1 t1 z ** w) <=
                &2 * (w dot (p2c_vfam (rfs_view hs) W t1 s z ** w))`
  (LABEL_TAC "CMP") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `t1 - Dl < s /\ &8 * K1 * (t1 - s) <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * K1 * Dl1` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P3L_REGION_CMP THEN
    MAP_EVERY EXISTS_TAC [`t1 - Dl`; `K1:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t1 - Dl < t1 - Dl1 /\ t1 - Dl1 < t1 /\ t1 - Dl <= (t1 - Dl1) - rho pow 2 /\
    (!z w. z IN W
           ==> w dot (p2c_vfam (rfs_view (hs:(A)rfs_history)) W t1 t1 z ** w) <=
               &2 * (w dot (p2c_vfam (rfs_view hs) W t1 (t1 - Dl1) z ** w)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      USE_THEN "CMP" (MP_TAC o SPECL [`t1 - Dl1`; `z:A`; `w:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3L_Y_BALL THEN
  MAP_EVERY EXISTS_TAC [`t1 - Dl`; `t1:real`; `ri / (&2 * max C (&2))`; `K1:real`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* Phase 3 (MT p. 393-394): the L-geodesic cut at tau0 (P2AO_LADM_RESTRICT,  *)
(* and an almost minimizing competitor), then the moving-endpoint curves of  *)
(* Part 2A (the statement P2ARC_BALL_REACH_STATEMENT, a hypothesis here) to  *)
(* every point of the ball at t1 - Dl1, with L <= L(gamma) + 6 sqrt b0       *)
(* (b0 - tau0) + sqrt(tau0 + Dl1) (Q Dl1 + 4 rho^2 / Dl1) + 2.               *)

let P3L_LX_APPROX = prove
 (`!(hs:(A)rfs_history) tt x b q e.
     rfs_pinched (rfs_view hs) /\ &0 < e /\
     (?g. rfs_L_adm hs tt x b g /\ g b = q)
     ==> ?g. rfs_L_adm hs tt x b g /\ g b = q /\
             rfs_L_length hs tt g b < rfs_Lx hs tt x b q + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{rfs_L_length hs tt gamma b | gamma |
                 rfs_L_adm hs tt (x:A) b gamma /\ gamma b = q}` INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXISTS_TAC `--(abs(--(&6)) * sqrt b * b)` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_LADM_LOWER THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P3L_ST_SCALAR_LOW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rfs_Lx hs tt (x:A) b q + e` o CONJUNCT2) THEN
  REWRITE_TAC[GSYM rfs_Lx] THEN
  MATCH_MP_TAC(TAUT `(~r ==> p) /\ ~q ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`; REAL_NOT_LT;
                IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `l:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real->A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]);;

let P3L_PH3 = prove
 (`!(u:A->bool) (hs:(A)rfs_history) tt x r b0 gamma tau0 W Dl Dl1 Q rho.
     P2ARC_BALL_REACH_STATEMENT u /\
     rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
     x IN topspace(rfs_top_at hs tt) /\ &0 < r /\
     rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
     rfs_L_adm hs tt x b0 gamma /\ &0 < tau0 /\ tau0 < b0 /\ b0 < tt /\
     &0 < Dl1 /\ Dl1 < Dl /\ tau0 + Dl1 < tt /\ &0 <= Q /\ &0 < rho /\
     rfs_persists (rfs_view hs) W ((tt - tau0) - Dl) (tt - tau0) /\
     (!s w. (tt - tau0) - Dl < s /\ s <= tt - tau0 /\ w IN W
            ==> rfs_vscalar (rfs_view hs) s w <= Q) /\
     (!s z w. (tt - tau0) - Dl1 <= s /\ s <= tt - tau0 /\ z IN W
              ==> w dot (p2c_vfam (rfs_view hs) W (tt - tau0) s z ** w) <=
                  &2 * (w dot (p2c_vfam (rfs_view hs) W (tt - tau0) (tt - tau0) z ** w)) /\
                  w dot (p2c_vfam (rfs_view hs) W (tt - tau0) (tt - tau0) z ** w) <=
                  &2 * (w dot (p2c_vfam (rfs_view hs) W (tt - tau0) s z ** w))) /\
     rfs_vball (rfs_view hs) ((tt - tau0) - Dl1) (gamma tau0) rho SUBSET W
     ==> !z. z IN rfs_vball (rfs_view hs) ((tt - tau0) - Dl1) (gamma tau0) rho
             ==> ?gamma'. rfs_L_adm hs tt x (tau0 + Dl1) gamma' /\ gamma'(tau0 + Dl1) = z /\
                          rfs_L_length hs tt gamma' (tau0 + Dl1) <=
                          rfs_L_length hs tt gamma b0 + &6 * sqrt b0 * (b0 - tau0) +
                          sqrt(tau0 + Dl1) * (Q * Dl1 + &4 * rho pow 2 / Dl1) + &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "REACH") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  (* the cut curve and an almost minimizing competitor on [0,tau0] *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `b0:real`; `tau0:real`;
                 `gamma:real->A`] P2AO_LADM_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`r:real`; `r pow 2`] THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tau0:real`;
                 `(gamma:real->A) tau0`; `&1`] P3L_LX_APPROX) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->A` STRIP_ASSUME_TAC) THEN
   (* Part 2A curves from (gamma tau0, tt - tau0) to the ball at tt - tau0 - Dl1 *)
  USE_THEN "REACH" (MP_TAC o REWRITE_RULE[P2ARC_BALL_REACH_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `tau0:real`;
    `g1:real->A`; `Dl1:real`; `Dl - Dl1`; `W:A->bool`; `Q:real`; `&4`; `rho:real`]) THEN
  SUBGOAL_THEN `tt - tau0 - Dl1 - (Dl - Dl1) = (tt - tau0) - Dl` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`r:real`; `r pow 2`] THEN ASM_SIMP_TAC[REAL_POW_LT];
      UNDISCH_TAC `rfs_vball (rfs_view (hs:(A)rfs_history)) ((tt - tau0) - Dl1) (gamma tau0) rho
                   SUBSET W` THEN
      REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `Q:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`; `v:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM P2AH_VFAM] THEN
      FIRST_X_ASSUM((fun th -> MP_TAC(SPECL [`s:real`; `y:A`; `v:real^3`] th) THEN
                               MP_TAC(SPECL [`(tt - tau0) - Dl1`; `y:A`; `v:real^3`] th)) o
        check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_vfam")) (concl th))) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:A`; `&1`]) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN ANTS_TAC THENL
   [UNDISCH_TAC `(z:A) IN rfs_vball (rfs_view hs) ((tt - tau0) - Dl1) (gamma tau0) rho` THEN
    REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g2:real->A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`rfs_L_length hs tt (g2:real->A) (tau0 + Dl1) <=
     rfs_L_length hs tt g1 tau0 + sqrt(tau0 + Dl1) * (Q * Dl1 + &4 * rho pow 2 / Dl1) + &1`;
    `rfs_L_length hs tt (g1:real->A) tau0 < rfs_Lx hs tt x tau0 ((gamma:real->A) tau0) + &1`;
    `rfs_Lx hs tt (x:A) tau0 ((gamma:real->A) tau0) <=
     rfs_L_length hs tt gamma b0 + &6 * sqrt b0 * (b0 - tau0)`] THEN
  REAL_ARITH_TAC);;

(* Phase 4 (MT p. 394, Thm 8.1): minimizing L-geodesics to the points of the *)
(* ball at tt - tau1 (Cor 16.24), in the compact set K (Prop 16.21), reduced *)
(* length <= Lb / 2 eps, then Thm 8.1 at (taub, Lb / 2 eps, V0).             *)

let P3L_LX_LE = prove
 (`!(hs:(A)rfs_history) tt x b g.
     rfs_pinched (rfs_view hs) /\ rfs_L_adm hs tt x b g
     ==> rfs_Lx hs tt x b (g b) <= rfs_L_length hs tt g b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_Lx] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC [`--(abs(--(&6)) * sqrt b * b)`; `rfs_L_length hs tt (g:real->A) b`] THEN
  REWRITE_TAC[REAL_LE_REFL; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `g:real->A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `l:real` THEN DISCH_THEN(X_CHOOSE_THEN `h:real->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AB_LADM_LOWER THEN
  EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3L_ST_SCALAR_LOW THEN ASM_REWRITE_TAC[]);;

let P3L_LX_RED_ARITH = prove
 (`!L Lb eps s. L <= Lb /\ &0 < Lb /\ &0 < eps /\ eps <= s
                ==> L / (&2 * s) <= Lb / (&2 * eps)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lb / (&2 * s)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`L:real`; `Lb:real`; `&2 * s`] REAL_LE_DIV2_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let P3L_PH4 = prove
 (`!u:A->bool.
     P2_THM_8_1_STATEMENT u
     ==> !taub Lb eps V0. &0 < taub /\ &0 < Lb /\ &0 < eps /\ &0 < V0
         ==> ?kappa. &0 < kappa /\
               !(hs:(A)rfs_history) x tt r tau1 B K Tm.
                 (!tau0 gamma. &0 < tau0 /\ tau0 <= tt - Tm /\ rfs_L_adm hs tt x tau0 gamma /\
                               rfs_L_length hs tt gamma tau0 <= Lb
                               ==> ?gamma'. rfs_min_Lgeod hs tt x tau0 gamma' /\
                                            gamma' tau0 = gamma tau0) /\
                 (!tau0 gamma. &0 < tau0 /\ tau0 <= tt - Tm /\ rfs_L_adm hs tt x tau0 gamma /\
                               rfs_L_length hs tt gamma tau0 <= Lb
                               ==> !tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K (tt - tau)) /\
                 (!z. z IN B ==> ?gamma. rfs_L_adm hs tt x tau1 gamma /\ gamma tau1 = z /\
                                         rfs_L_length hs tt gamma tau1 <= Lb) /\
                 rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
                 eps pow 2 <= tau1 /\ tau1 <= taub /\ tau1 < tt /\ tau1 <= tt - Tm /\
                 &0 < r /\ r <= eps /\ x IN topspace(rfs_top_at hs tt) /\
                 rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
                 (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
                        ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
                 open_in (rfs_top_at hs (tt - tau1)) B /\
                 (?v. mfd_has_volume (rfs_top_at hs (tt - tau1),rfs_atlas_at hs (tt - tau1))
                                     (rfs_metric_at hs (tt - tau1)) B v /\ V0 <= v) /\
                 p3_st_compact hs K
                 ==> ?v. mfd_has_volume (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt)
                                        (rfs_vball (rfs_view hs) tt x r) v /\
                         kappa * r pow 3 <= v`,
  GEN_TAC THEN REWRITE_TAC[P2_THM_8_1_STATEMENT] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`taub:real`; `Lb / (&2 * eps)`; `V0:real`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kappa:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T81")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`; `tau1:real`;
                       `B:A->bool`; `K:real->A->bool`; `Tm:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1624") (CONJUNCTS_THEN2 (LABEL_TAC "c1621")
    (CONJUNCTS_THEN2 (LABEL_TAC "reach") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 < tau1 /\ r pow 2 <= tau1 /\ eps <= sqrt tau1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eps pow 2 /\ r pow 2 <= eps pow 2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "T81" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tau1:real`; `B:A->bool`; `K:real->A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  REMOVE_THEN "reach" (MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->A` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "c1624" (MP_TAC o SPECL [`tau1:real`; `g:real->A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g':real->A` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_min_Lgeod] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "rfs_min_Lgeod")) (concl th))) THEN
  SUBGOAL_THEN `rfs_Lx hs tt (x:A) tau1 q <= Lb` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rfs_L_length hs tt (g:real->A) tau1` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q:A = (g:real->A) tau1` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P3L_LX_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_lx] THEN MATCH_MP_TAC P3L_LX_RED_ARITH THEN ASM_REWRITE_TAC[];
    USE_THEN "c1621" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g':real->A) tau1 = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The step setting unfolded; canonical neighbourhoods with the               *)
(* parameter rs i on [T_(i-1), T_i); noncollapsing there from the truncation. *)
(* ------------------------------------------------------------------------- *)

let P3L_SETTING_UNFOLD = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt rs' ks' dd (hs:(A)rfs_history).
     p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\ rs 0 = eps
     ==> rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
         p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) hs /\
         rs' i = rs i /\ ks' i = ks i /\ rs' (SUC i) = r' /\
         p3_seq_ok rs' /\ p3_seq_ok ks' /\ p3_seq_ok dd /\
         dd i <= dlt /\ dd (SUC i) <= dlt /\
         p3_T i < rfs_horizon hs /\ rfs_horizon hs <= p3_T (SUC i) /\
         rfs_canonical_assumption (rfs_view hs) C eps (p3_stepf rs') /\
         p3_noncoll_all (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks') eps /\
         (!t. p3_stepf rs' t <= eps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LE_REFL] THEN
  UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history)` THEN
  REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[p3_stepf] THEN
  SUBGOAL_THEN `(rs':num->real) 0 = eps` (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `ks':num->real`)) (concl th))) THEN
    ASM_SIMP_TAC[LE_0];
    ALL_TAC] THEN
  MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_0]);;

let P3L_CANON_WINDOW = prove
 (`!(hs:(A)rfs_history) C eps rs' j ri.
     rfs_canonical_assumption (rfs_view hs) C eps (p3_stepf rs') /\ rs' (SUC j) = ri
     ==> !x t. p3_T j <= t /\ t < p3_T (SUC j) /\ x IN topspace(rfs_top_at hs t) /\
               inv(ri pow 2) <= rfs_vscalar (rfs_view hs) t x
               ==> p3_canon_at (rfs_view hs) C eps x t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `rfs_canonical_assumption (rfs_view (hs:(A)rfs_history)) C eps (p3_stepf rs')` THEN
  REWRITE_TAC[rfs_view; rfs_canonical_assumption; p3_canon_at] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`rs':num->real`; `t:real`; `j:num`] P3L_STEPF_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `inv(ri pow 2) <= rfs_vscalar (rfs_view (hs:(A)rfs_history)) t x` THEN
  REWRITE_TAC[rfs_view; rfs_vscalar] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `j:num` P3_T_POS) THEN ASM_REAL_ARITH_TAC);;

let P3L_NONCOLL_WINDOW = prove
 (`!(hs:(A)rfs_history) ks' eps i j y t.
     p3_noncoll_all (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks') eps /\ i = SUC j /\
     p3_T j <= t /\ t < p3_T i /\ y IN topspace(rfs_top_at hs t)
     ==> p3_noncoll_at (rfs_view hs) (ks' i) eps y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history)`; `rfs_atlas_at (hs:(A)rfs_history)`;
                 `rfs_metric_at (hs:(A)rfs_history)`; `p3_stepf ks'`; `eps:real`;
                 `p3_T i`; `t:real`; `y:A`] P3L_NONCOLL_UNTRUNC) THEN
  REWRITE_TAC[GSYM rfs_view] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [MP_TAC(SPEC `j:num` P3_T_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ks':num->real`; `t:real`; `j:num`] P3L_STEPF_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* The L-length bookkeeping of Phase 3: the moving-endpoint term is <= 2,   *)
(* and the total is at most 3 sqrt T3 + 6 sqrt T3 T3 + 2 sqrt T3 + 2.       *)

let P3L_X_ARITH = prove
 (`!Q ri Cp Dl1 rho.
     Q = &4 * inv(ri pow 2) /\ &0 < ri /\ &2 <= Cp /\ &0 < Dl1 /\
     &2 * Dl1 <= ri pow 2 / (&32 * Cp) /\ &0 <= rho /\ &4 * rho pow 2 <= Dl1
     ==> &0 <= Q * Dl1 + &4 * rho pow 2 / Dl1 /\ Q * Dl1 + &4 * rho pow 2 / Dl1 <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ri pow 2 /\ &0 < Q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `Dl1 <= ri pow 2 / &128` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(ri pow 2 / (&32 * Cp)) / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&64) * inv(&2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q * Dl1 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * (ri pow 2 / &128)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &1 / &32 ==> x <= &1`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < ri` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= rho pow 2 / Dl1 /\ rho pow 2 / Dl1 <= inv(&4)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q * Dl1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`Q * Dl1 <= &1`; `&0 <= rho pow 2 / Dl1`;
                         `rho pow 2 / Dl1 <= inv(&4)`] THEN
  REAL_ARITH_TAC);;

let P3L_LB_ARITH = prove
 (`!L b0 tau0 tau1 T3 X.
     L <= &3 * sqrt b0 /\ &0 <= tau0 /\ tau0 <= b0 /\ b0 <= T3 /\
     &0 <= tau1 /\ tau1 <= T3 /\ &0 <= X /\ X <= &2
     ==> L + &6 * sqrt b0 * (b0 - tau0) + sqrt tau1 * X + &2 <=
         &3 * sqrt T3 + &6 * sqrt T3 * T3 + sqrt T3 * &2 + &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b0 <= sqrt T3 /\ &0 <= sqrt b0 /\ sqrt tau1 <= sqrt T3 /\
                &0 <= sqrt tau1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b0 * (b0 - tau0) <= sqrt T3 * T3 /\ sqrt tau1 * X <= sqrt T3 * &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The large-scale core of MT Prop 16.1 (Sec 16.6) on the KL route: for r    *)
(* between the second scale rr and eps, at times tt >= T_i, the ball         *)
(* B(x,tt,r) has volume >= kL r^3, kL depending on i, rs i, ks i, C, eps     *)
(* (and g0, A0, md) but not on r' or rr; the control bound dlt depends on    *)
(* r', rr.  Inputs: the rr forms of 16.4, 16.21, 16.24, Thm 8.1, Lemma 11.2  *)
(* and the moving-endpoint statement of Part 2A.                             *)
(* ------------------------------------------------------------------------- *)

let P3L_CORE_161 = prove
 (`!u:A->bool.
     P3_PROP_16_4_STATEMENT u /\ P3_PROP_16_21_STATEMENT u /\ P3_COR_16_24_STATEMENT u /\ P2_THM_8_1_STATEMENT u /\
     P2_LEMMA_11_2_STATEMENT u /\ P2ARC_BALL_REACH_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
         !C eps hf md g0 A0.
           &1 < C /\ &0 < eps /\ eps <= eps0 /\ p3_hfun C hf /\ p3_modulus md /\
           p3_std_initial g0 A0
           ==> !i rs ks ds.
                 1 <= i /\ rs 0 = eps /\ p3_seq_upto i rs /\ p3_seq_upto i ks /\
                 p3_seq_upto i ds
                 ==> ?kL. &0 < kL /\
                       !r' rr. &0 < r' /\ r' <= (rs:num->real) i /\ &0 < rr /\ rr <= r'
                         ==> ?dlt. &0 < dlt /\
                               !rs' ks' dd (hs:(A)rfs_history) x tt r.
                                 p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt
                                                (rs',ks',dd) hs /\
                                 p3_T i <= tt /\ tt < rfs_horizon hs /\
                                 x IN topspace(rfs_top_at hs tt) /\
                                 rr <= r /\ r <= eps /\
                                 rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
                                 (!s y. tt - r pow 2 < s /\ s <= tt /\
                                        y IN rfs_vball (rfs_view hs) tt x r
                                        ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2))
                                 ==> ?v. mfd_has_volume (rfs_top_at hs tt,rfs_atlas_at hs tt)
                                                        (rfs_metric_at hs tt)
                                                        (rfs_vball (rfs_view hs) tt x r) v /\
                                         kL * r pow 3 <= v`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H164") (CONJUNCTS_THEN2 (LABEL_TAC "H1621")
    (CONJUNCTS_THEN2 (LABEL_TAC "H1624") (CONJUNCTS_THEN2 (LABEL_TAC "H81")
    (CONJUNCTS_THEN2 (LABEL_TAC "H112") (LABEL_TAC "REACH")))))) THEN
  USE_THEN "H164" (MP_TAC o REWRITE_RULE[P3_PROP_16_4_STATEMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S164"))) THEN
  USE_THEN "H1621" (MP_TAC o REWRITE_RULE[P3_PROP_16_21_STATEMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S1621"))) THEN
  USE_THEN "H1624" (MP_TAC o REWRITE_RULE[P3_COR_16_24_STATEMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S1624"))) THEN
  USE_THEN "H112" (MP_TAC o MATCH_MP P3L_PH2) THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PH2"))) THEN
  USE_THEN "H81" (LABEL_TAC "PH4" o MATCH_MP P3L_PH4) THEN
  EXISTS_TAC `min (min e1 e2) (min e3 (min e4 (&1 / &40)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  REMOVE_THEN "S164" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T164") THEN
  REMOVE_THEN "S1621" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T1621") THEN
  REMOVE_THEN "S1624" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T1624") THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`] P3L_HOT_CAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `c0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HOT"))))) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rs:num->real) i /\ rs i <= eps /\ &0 < (ks:num->real) i`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p3_seq_upto i rs` THEN REWRITE_TAC[p3_seq_upto] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[LE_REFL];
      MP_TAC(ISPECL [`i:num`; `rs:num->real`] P3L_SEQ_UPTO_LE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[LE_0];
      UNDISCH_TAC `p3_seq_upto i ks` THEN REWRITE_TAC[p3_seq_upto] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. SUC j = i` (X_CHOOSE_TAC `j:num`) THENL
   [EXISTS_TAC `i - 1` THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i - 1 = j` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* the constants: Dl, Dl1, rho2, Lb, and kL from Thm 8.1 *)
  SUBGOAL_THEN `&0 < p3l_k1 ((rs:num->real) i)` ASSUME_TAC THENL
   [REWRITE_TAC[p3l_k1] THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?Dl. &0 < Dl /\ Dl <= (rs:num->real) i pow 2 / (&32 * max C (&2)) /\ Dl <= eps pow 2`
  (X_CHOOSE_THEN `Dl:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min ((rs:num->real) i pow 2 / (&32 * max C (&2))) (eps pow 2)` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?Dl1. &0 < Dl1 /\ &2 * Dl1 <= Dl /\ &8 * p3l_k1 ((rs:num->real) i) * Dl1 <= &1`
  (X_CHOOSE_THEN `Dl1:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min (Dl / &2) (inv(&8 * p3l_k1 ((rs:num->real) i)))` THEN
    SUBGOAL_THEN `&0 < inv(&8 * p3l_k1 ((rs:num->real) i))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&8 * p3l_k1 ((rs:num->real) i)) * inv(&8 * p3l_k1 (rs i))` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?rho2. &0 < rho2 /\ rho2 <= ((rs:num->real) i / (&2 * max C (&2))) / &2 /\
           &4 * rho2 pow 2 <= Dl1 /\ p3l_k1 (rs i) <= inv(rho2 pow 2)`
  (X_CHOOSE_THEN `rho2:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min (((rs:num->real) i / (&2 * max C (&2))) / &2)
                    (min (sqrt Dl1 / &2) (inv(sqrt(p3l_k1 (rs i)))))` THEN
    SUBGOAL_THEN `&0 < ((rs:num->real) i / (&2 * max C (&2))) / &2 /\ &0 < sqrt Dl1 /\
                  &0 < sqrt(p3l_k1 (rs i))` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `m = min (((rs:num->real) i / (&2 * max C (&2))) / &2)
                        (min (sqrt Dl1 / &2) (inv(sqrt(p3l_k1 (rs i)))))` THEN
    SUBGOAL_THEN `&0 < m /\ m <= ((rs:num->real) i / (&2 * max C (&2))) / &2 /\ m <= sqrt Dl1 / &2 /\
                  m <= inv(sqrt(p3l_k1 (rs i)))` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[REAL_LT_INV; REAL_ARITH `&0 < x ==> &0 < x / &2`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (sqrt Dl1 / &2) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `m pow 2 <= inv(p3l_k1 ((rs:num->real) i))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sqrt(p3l_k1 ((rs:num->real) i))) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_POW_INV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < m pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(p3l_k1 ((rs:num->real) i)))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `T3 = p3_T (SUC i)` THEN
  SUBGOAL_THEN `&0 < T3 /\ &0 < sqrt T3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T3" THEN REWRITE_TAC[P3_T_POS] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    REWRITE_TAC[P3_T_POS];
    ALL_TAC] THEN
  ABBREV_TAC `Lb = &3 * sqrt T3 + &6 * sqrt T3 * T3 + sqrt T3 * &2 + &2` THEN
  SUBGOAL_THEN `&0 < Lb` ASSUME_TAC THENL
   [EXPAND_TAC "Lb" THEN
    SUBGOAL_THEN `&0 <= sqrt T3 * T3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sqrt T3` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "PH4" (MP_TAC o SPECL [`T3:real`; `Lb:real`; `eps:real`;
                                  `(ks:num->real) i * rho2 pow 3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kL:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K81"))) THEN
  EXISTS_TAC `kL:real` THEN ASM_REWRITE_TAC[] THEN
  (* the scales r', rr: the control bound *)
  MAP_EVERY X_GEN_TAC [`r':real`; `rr:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "T164" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`;
    `ds:num->real`; `r':real`; `rr:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D164"))) THEN
  REMOVE_THEN "T1621" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`;
    `ds:num->real`; `r':real`; `rr:real`; `Lb:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1621"))) THEN
  REMOVE_THEN "T1624" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`;
    `ds:num->real`; `r':real`; `rr:real`; `Lb:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dlt3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1624"))) THEN
  SUBGOAL_THEN `?dlt4. &0 < dlt4 /\ dlt4 <= d0 /\ dlt4 <= &1 /\
                       dlt4 <= c0 * (rs:num->real) i pow 2 / (&16 * eps pow 2)`
  (X_CHOOSE_THEN `dlt4:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `min d0 (min (&1) (c0 * (rs:num->real) i pow 2 / (&16 * eps pow 2)))` THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (min dlt1 dlt2) (min dlt3 dlt4)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`;
                       `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`] THEN
  STRIP_TAC THEN
  (* the setting unfolded; the settings at dlt1, dlt2, dlt3 *)
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `r':real`; `min (min dlt1 dlt2) (min dlt3 dlt4)`;
                 `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`]
                P3L_SETTING_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. min (min dlt1 dlt2) (min dlt3 dlt4) <= d
        ==> p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' d (rs',ks',dd)
                           (hs:(A)rfs_history)`
  (LABEL_TAC "SET") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3L_P16_SETTING_MONO THEN
    EXISTS_TAC `min (min dlt1 dlt2) (min dlt3 dlt4)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_T j /\ p3_T i = &2 * p3_T j /\ T3 = &2 * p3_T i`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T3" THEN UNDISCH_TAC `SUC j = i` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[P3_T_POS; P3L_T_FACTS];
    ALL_TAC] THEN
  (* Stage 1: the 16.4 geodesic to T_(i-1) *)
  USE_THEN "D164" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
    `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "SET" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?gamma. rfs_min_Lgeod (hs:(A)rfs_history) tt x (tt - p3_T j) gamma /\
            rfs_L_length hs tt gamma (tt - p3_T j) <= &3 * sqrt(tt - p3_T j)`
  (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `p3_T j` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_Lmin_set")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_Lx")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:A` MP_TAC) THEN
    REWRITE_TAC[p3_Lmin_set; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p3_T j`; `y0:A`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_min_Lgeod")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_min_Lgeod hs tt x (tt - p3_T j) (g:real->A)` THEN
    REWRITE_TAC[rfs_min_Lgeod] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_min_Lgeod] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "rfs_min_Lgeod")) (concl th) && not(is_forall(concl th)))) THEN
  (* Stage 2: Claims 16.27, 16.28 *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `gamma:real->A`; `i:num`; `eps:real`;
                 `(rs:num->real) i`] P3L_PH1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p3_T (i - 1) = p3_T j` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                                    ASSUME_TAC th) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 < tau0 /\ tt - p3_T i < tau0 /\ tau0 < tt - p3_T j - eps pow 2 /\
                &0 < eps pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau0 IN topspace(rfs_top_at hs (tt - tau0))` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_L_adm hs tt x (tt - p3_T j) (gamma:real->A)` THEN
    REWRITE_TAC[rfs_L_adm; rfs_st_curve] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rs':num->real) (SUC j) = (rs:num->real) i /\ p3_T (SUC j) = p3_T i`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC j = i` THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Stage 3: the region at y = gamma tau0, t1 = tt - tau0 (Phase 2) *)
  USE_THEN "PH2" (MP_TAC o SPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`;
    `(rs:num->real) i`; `(gamma:real->A) tau0`; `tt - tau0`; `Dl:real`; `Dl1:real`;
    `rho2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:A`; `t:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `C:real`; `eps:real`; `rs':num->real`; `j:num`;
                     `(rs:num->real) i`] P3L_CANON_WINDOW) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[rfs_view; rfs_vscalar] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `m:num`; `c:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `p3_T j <= hs_time (hs:(A)rfs_history) k /\ hs_time hs k < p3_T (SUC j)`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `p3_stepf dd (hs_time (hs:(A)rfs_history) k) = dd i /\
                    p3_stepf rs' (hs_time hs k) = (rs:num->real) i` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`dd:num->real`; `hs_time (hs:(A)rfs_history) k`; `j:num`]
                      P3L_STEPF_AT) THEN
        MP_TAC(ISPECL [`rs':num->real`; `hs_time (hs:(A)rfs_history) k`; `j:num`]
                      P3L_STEPF_AT) THEN
        ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `c0 / (&2 * p3_hscale hf (p3_stepf rs') (p3_stepf dd)
                                  (hs_time (hs:(A)rfs_history) k) pow 2)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`C:real`; `hf:real->real->real`; `p3_stepf rs'`; `p3_stepf dd`;
                       `hs_time (hs:(A)rfs_history) k`] P3L_HSCALE_LE) THEN
        ASM_SIMP_TAC[P3_STEPF_POS] THEN STRIP_TAC THEN
        MATCH_MP_TAC P3L_HOT_ARITH2 THEN
        MAP_EVERY EXISTS_TAC [`(dd:num->real) i`; `(rs:num->real) i`; `eps:real`] THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 < (dd:num->real) i` ASSUME_TAC THENL
         [UNDISCH_TAC `p3_seq_ok dd` THEN SIMP_TAC[p3_seq_ok]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "HOT" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `m:num`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      MP_TAC(SPEC `rho2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) (tt - tau0) ((gamma:real->A) tau0)
                            ((rs:num->real) i / (&2 * max C (&2)))` THEN
  STRIP_TAC THEN
   (* Stage 4: moving-endpoint curves to t'' = tt - tau0 - Dl1, L <= Lb (Phase 3) *)
  MP_TAC(ISPECL [`u:A->bool`; `hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`;
                 `tt - p3_T j`; `gamma:real->A`; `tau0:real`; `W:A->bool`; `Dl:real`;
                 `Dl1:real`; `&4 * inv((rs:num->real) i pow 2)`; `rho2:real`] P3L_PH3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "P3") THEN
  MP_TAC(ISPECL [`&4 * inv((rs:num->real) i pow 2)`; `(rs:num->real) i`; `max C (&2)`;
                 `Dl1:real`; `rho2:real`] P3L_X_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN rfs_vball (rfs_view hs) ((tt - tau0) - Dl1) ((gamma:real->A) tau0) rho2
        ==> ?gamma'. rfs_L_adm hs tt x (tau0 + Dl1) gamma' /\ gamma'(tau0 + Dl1) = z /\
                     rfs_L_length hs tt gamma' (tau0 + Dl1) <= Lb`
  (LABEL_TAC "RCH") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    REMOVE_THEN "P3" (MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rfs_L_length hs tt (gamma:real->A) (tt - p3_T j) +
                &6 * sqrt(tt - p3_T j) * ((tt - p3_T j) - tau0) +
                sqrt(tau0 + Dl1) * ((&4 * inv((rs:num->real) i pow 2)) * Dl1 + &4 * rho2 pow 2 / Dl1) + &2` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Lb" THEN MATCH_MP_TAC P3L_LB_ARITH THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Stage 5: 16.21, 16.24, noncollapsing at (y,t''), Thm 8.1 (Phase 4) *)
  USE_THEN "D1621" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
    `hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "SET" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K21"))) THEN
  SUBGOAL_THEN
   `!tau1 g. &0 < tau1 /\ tau1 <= tt - p3_T j /\ rfs_L_adm (hs:(A)rfs_history) tt x tau1 g /\
             rfs_L_length hs tt g tau1 <= Lb
             ==> ?g'. rfs_min_Lgeod hs tt x tau1 g' /\ g' tau1 = (g:real->A) tau1`
  (LABEL_TAC "K24") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "D1624" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "SET" MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the ball at t'' and its volume *)
  ABBREV_TAC `B = rfs_vball (rfs_view (hs:(A)rfs_history)) ((tt - tau0) - Dl1)
                            ((gamma:real->A) tau0) rho2` THEN
  SUBGOAL_THEN `(gamma:real->A) tau0 IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC P2AO_VBALL_CENTRE THEN
    ASM_SIMP_TAC[P2AB_SVS; P2C_RFS_VIEW_PARTS] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau0 IN topspace(rfs_top_at hs ((tt - tau0) - Dl1))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W ((tt - tau0) - Dl) (tt - tau0)` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `(tt - tau0) - Dl1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
    UNDISCH_TAC `(gamma:real->A) tau0 IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. mfd_has_volume (rfs_top_at (hs:(A)rfs_history) ((tt - tau0) - Dl1),
                                    rfs_atlas_at hs ((tt - tau0) - Dl1))
                                   (rfs_metric_at hs ((tt - tau0) - Dl1)) B v /\
                    (ks:num->real) i * rho2 pow 3 <= v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `ks':num->real`; `eps:real`; `i:num`; `j:num`;
                   `(gamma:real->A) tau0`; `(tt - tau0) - Dl1`] P3L_NONCOLL_WINDOW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3_noncoll_at] THEN DISCH_THEN(MP_TAC o SPEC `rho2:real`) THEN
    ASM_REWRITE_TAC[GSYM p3_vrm] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((rs:num->real) i / (&2 * max C (&2))) / &2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rs:num->real) i` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&4) * inv(&2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) ((tt - tau0) - Dl1)) B` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `(tt - tau0) - Dl1`; `(gamma:real->A) tau0`]
                  P3N_HIST_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[P2C_VIEW_EXPAND; P2C_RFS_VIEW_PARTS] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tt - (tau0 + Dl1) = (tt - tau0) - Dl1` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "K81" (MP_TAC o SPECL [`hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`;
    `tau0 + Dl1`; `B:A->bool`; `K:real->A->bool`; `p3_T j`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "K24" ACCEPT_TAC; USE_THEN "K21" ACCEPT_TAC; USE_THEN "RCH" ACCEPT_TAC;
           ASM_REAL_ARITH_TAC];
    SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* MT Prop 16.1 on the KL route.  Times before T_i: the                       *)
(* truncated noncollapsing; times tt >= T_i: scales r >= rr by the core, and  *)
(* scales r < rr by the small-scale statement P3N_SMALL_SCALE_STATEMENT       *)
(* (KL Sublemma 79.23) with Rthr = max (r'^-2) (8 e^4 C), rr = (Lam Rthr)^-1/2 *)
(* and the core at rr as its large-scale input; kappa = min (ks i)            *)
(* (min (kL/2) kS), dfun r' = min (ds i) (min (dlt of the core at (r',rr))    *)
(* (hot-cap bound)).                                                          *)
(* ------------------------------------------------------------------------- *)

let P3L_SLICES_SC = prove
 (`!hs:(A)rfs_history.
     RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\ rfs_history_ok hs /\ rfs_components_sc (hs_top hs 0)
     ==> !t. &0 <= t /\ t < rfs_horizon hs ==> rfs_components_sc (rfs_vtop (rfs_view hs) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `hs:(A)rfs_history` RFS_HISTORY_SC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P2AB_LIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[P2C_RFS_VIEW_PARTS]);;

let P3L_HOT_ARITH3 = prove
 (`!c0 h dl rp eps LR.
     &0 < c0 /\ &0 < h /\ h <= dl pow 2 * rp /\ &0 < dl /\ dl <= &1 /\
     dl <= c0 / (&2 * eps pow 2 * LR) /\ &0 < rp /\ rp <= eps /\ &0 < eps /\ &0 < LR
     ==> LR <= c0 / (&2 * h pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h pow 2 <= dl * eps pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dl pow 2 * rp) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl pow 4 * eps pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `dl pow 4 = dl * dl pow 3` SUBST1_TAC THENL
     [REWRITE_TAC[num_CONV `4`; real_pow]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < eps pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `dl * eps pow 2 <= c0 / (&2 * LR)` ASSUME_TAC THENL
   [UNDISCH_TAC `dl <= c0 / (&2 * eps pow 2 * LR)` THEN
    SUBGOAL_THEN `c0 / (&2 * eps pow 2 * LR) = (c0 / (&2 * LR)) / eps pow 2` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < eps`; `&0 < LR`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &2 * x`] THEN
  SUBGOAL_THEN `h pow 2 <= c0 / (&2 * LR)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &2 * x`] THEN REAL_ARITH_TAC);;

let P3L_RR_FACTS = prove
 (`!Lam C r'.
     &1 <= Lam /\ &1 < C /\ &0 < r'
     ==> &0 < max (inv(r' pow 2)) (&8 * exp(&4) * C) /\
         &0 < inv(sqrt(Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C))) /\
         inv(sqrt(Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C))) <= r' /\
         Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C) <=
         inv(inv(sqrt(Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C))) pow 2) /\
         inv(sqrt(Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C))) pow 2 <= &1 / &40`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = max (inv(r' pow 2)) (&8 * exp(&4) * C)` THEN
  SUBGOAL_THEN `&5 <= exp(&4)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&4` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(r' pow 2) <= R /\ &40 <= R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&40 <= y ==> &40 <= max x y`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * &5 * &1` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R /\ &0 < Lam * R /\ R <= Lam * R` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(Lam * R)) pow 2 = inv(Lam * R)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(Lam * R) <= inv(R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(R)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(r' pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_SIMP_TAC[REAL_POW_LT];
      REWRITE_TAC[REAL_INV_INV; REAL_LE_REFL]];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(R)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&40)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]]);;

let P3L_STEPF_GE_NEXT = prove
 (`!(s:num->real) i t. p3_seq_ok s /\ t < p3_T (SUC i) ==> s (SUC i) <= p3_stepf s t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_stepf] THEN
  MP_TAC(SPEC `s:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P3_STEP_LE THEN ASM_REWRITE_TAC[]);;

let P3L_PROP_16_1_PRE = prove
 (`!u:A->bool.
     P3N_SMALL_SCALE_STATEMENT u /\ P3_PROP_16_4_STATEMENT u /\ P3_PROP_16_21_STATEMENT u /\ P3_COR_16_24_STATEMENT u /\
     P2_THM_8_1_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u /\ RFS_CUTCAP_SC_STATEMENT u u /\
     P2ARC_BALL_REACH_STATEMENT u
     ==> P3_PROP_16_1_STATEMENT u`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SMALL") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SC") ASSUME_TAC))))))) THEN
  MP_TAC(SPEC `u:A->bool` P3L_CORE_161) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CORE"))) THEN
  USE_THEN "SMALL" (MP_TAC o REWRITE_RULE[P3N_SMALL_SCALE_STATEMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SS"))) THEN
  SUBGOAL_THEN `RFS_CUTCAP_SC_STATEMENT (:A) (:A)` (LABEL_TAC "SCA") THENL
   [USE_THEN "SC" MP_TAC THEN REWRITE_TAC[RFS_CUTCAP_SC_STATEMENT]; ALL_TAC] THEN
  REWRITE_TAC[P3_PROP_16_1_STATEMENT] THEN
  MAP_EVERY EXISTS_TAC [`min ec es`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  REMOVE_THEN "CORE" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CORE1") THEN
  REMOVE_THEN "SS" (MP_TAC o SPEC `C:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Lam:real` (X_CHOOSE_THEN `kS:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SS1"))))) THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`] P3L_HOT_CAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `c0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HOT"))))) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "CORE1" (MP_TAC o SPECL [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kL:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `dltf:real->real->real` (LABEL_TAC "DL") o
             GEN_REWRITE_RULE I [SKOLEM_THM] o GEN_REWRITE_RULE BINDER_CONV [SKOLEM_THM] o
             GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM]) THEN
  SUBGOAL_THEN `&0 < (rs:num->real) i /\ rs i <= eps /\ &0 < (ks:num->real) i /\
                &0 < (ds:num->real) i` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `p3_seq_upto i rs` THEN REWRITE_TAC[p3_seq_upto] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[LE_REFL];
      MP_TAC(ISPECL [`i:num`; `rs:num->real`] P3L_SEQ_UPTO_LE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[LE_0];
      UNDISCH_TAC `p3_seq_upto i ks` THEN REWRITE_TAC[p3_seq_upto] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[LE_REFL];
      UNDISCH_TAC `p3_seq_upto i ds` THEN REWRITE_TAC[p3_seq_upto] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[LE_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `min ((ks:num->real) i) (min (kL / &2) kS)` THEN
  EXISTS_TAC `\r':real. min ((ds:num->real) i)
                (min ((dltf:real->real->real) r' (inv(sqrt(Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C)))))
                     (min d0 (min (&1) (c0 / (&2 * eps pow 2 *
                        (Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C)))))))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    X_GEN_TAC `r':real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`Lam:real`; `C:real`; `r':real`] P3L_RR_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "DL" (MP_TAC o SPECL [`r':real`;
      `inv(sqrt(Lam * max (inv(r' pow 2)) (&8 * exp(&4) * C)))`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the noncollapsing of every history in the step setting *)
  REWRITE_TAC[p3_noncoll_prop] THEN
  MAP_EVERY X_GEN_TAC [`r':real`; `rs':num->real`; `ks':num->real`; `dd:num->real`;
                       `hs:(A)rfs_history`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Rth = max (inv(r' pow 2)) (&8 * exp(&4) * C)` THEN
  ABBREV_TAC `rr = inv(sqrt(Lam * Rth))` THEN
  MP_TAC(ISPECL [`Lam:real`; `C:real`; `r':real`] P3L_RR_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&8 * exp(&4) * C <= Rth /\ inv(r' pow 2) <= Rth` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Rth" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "DL" (MP_TAC o SPECL [`r':real`; `rr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CORE2")) THEN
  ABBREV_TAC `DF = min ((ds:num->real) i) (min ((dltf:real->real->real) r' rr)
                      (min d0 (min (&1) (c0 / (&2 * eps pow 2 * (Lam * Rth))))))` THEN
  SUBGOAL_THEN `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' DF (rs',ks',dd)
                               (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p3_p16_setting] THEN MATCH_MP_TAC P3_CANONV_ASSUMPTION_IMP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' ((dltf:real->real->real) r' rr)
                               (rs',ks',dd) (hs:(A)rfs_history)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3L_P16_SETTING_MONO THEN EXISTS_TAC `DF:real` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "DF" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `r':real`; `DF:real`;
                 `rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`]
                P3L_SETTING_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `DF <= d0 /\ DF <= &1 /\ DF <= c0 / (&2 * eps pow 2 * (Lam * Rth))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "DF" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?j. SUC j = i` (X_CHOOSE_TAC `j:num`) THENL
   [EXISTS_TAC `i - 1` THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_T j /\ p3_T i = &2 * p3_T j /\ &1 / &16 <= p3_T i`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC j = i` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[P3_T_POS; P3L_T_FACTS] THEN
    MP_TAC(SPECL [`1`; `SUC j`] P3_T_MONO) THEN REWRITE_TAC[ARITH_RULE `1 <= SUC j`] THEN
    REWRITE_TAC[p3_T] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3_noncoll_all] THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_top_at hs t) /\ t < rfs_horizon hs` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (rfs_view hs) t)` THEN
    REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MESON_TAC[P2A_TOPSPACE_LIVE];
    ALL_TAC] THEN
  ASM_CASES_TAC `t < p3_T i` THENL
   [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history)`; `rfs_atlas_at (hs:(A)rfs_history)`;
                   `rfs_metric_at (hs:(A)rfs_history)`; `p3_stepf ks'`; `eps:real`;
                   `p3_T i`; `t:real`; `x:A`] P3L_NONCOLL_UNTRUNC) THEN
    REWRITE_TAC[GSYM rfs_view] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* tt = t >= T_i: kp t = kappa *)
  SUBGOAL_THEN `p3_stepf ks' t = min ((ks:num->real) i) (min (kL / &2) kS)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`ks':num->real`; `t:real`; `i:num`] P3L_STEPF_AT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p3_noncoll_at] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `rr <= r` THENL
   [(* large scales: the core *)
    REMOVE_THEN "CORE2" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
      `hs:(A)rfs_history`; `x:A`; `t:real`; `r:real`]) THEN
    ASM_REWRITE_TAC[p3_vrm] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `kL * r pow 3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   (* small scales: the small-scale statement, with the core at rr as its input *)
  USE_THEN "SS1" (MP_TAC o SPECL [`hs:(A)rfs_history`; `eps:real`; `Rth:real`; `rr:real`;
    `kL:real`; `x:A`; `t:real`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3L_SLICES_SC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history)` THEN
      SIMP_TAC[p3_struct];
      (* canonical neighbourhoods with the volume clause above Rth *)
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
      UNDISCH_TAC `p3_canonv_assumption (rfs_view (hs:(A)rfs_history)) C eps (p3_stepf rs')` THEN
      REWRITE_TAC[p3_canonv_assumption] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Rth:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:A) IN topspace(rfs_vtop (rfs_view hs) s)` THEN
        REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MESON_TAC[P2A_TOPSPACE_LIVE];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`rs':num->real`; `i:num`; `s:real`] P3L_STEPF_GE_NEXT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      (* hot caps in the window [t - rr^2, t] *)
      MAP_EVERY X_GEN_TAC [`k:num`; `m:num`; `c:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `p3_T j <= hs_time (hs:(A)rfs_history) k` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `p3_stepf dd (hs_time (hs:(A)rfs_history) k) <= dd i` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p3_stepf dd (p3_T j)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC P3_STEPF_MONO THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`dd:num->real`; `p3_T j`; `j:num`] P3L_STEPF_AT) THEN
          ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c0 / (&2 * p3_hscale hf (p3_stepf rs') (p3_stepf dd)
                                  (hs_time (hs:(A)rfs_history) k) pow 2)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`C:real`; `hf:real->real->real`; `p3_stepf rs'`; `p3_stepf dd`;
                       `hs_time (hs:(A)rfs_history) k`] P3L_HSCALE_LE) THEN
        ASM_SIMP_TAC[P3_STEPF_POS] THEN STRIP_TAC THEN
        MATCH_MP_TAC P3L_HOT_ARITH3 THEN
        MAP_EVERY EXISTS_TAC [`p3_stepf dd (hs_time (hs:(A)rfs_history) k)`;
                              `p3_stepf rs' (hs_time (hs:(A)rfs_history) k)`; `eps:real`] THEN
        ASM_SIMP_TAC[P3_STEPF_POS] THEN
        SUBGOAL_THEN `&0 < Lam * Rth` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "HOT" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `m:num`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      (* rr^2 <= t *)
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      (* the large-scale input at rr: the core *)
      STRIP_TAC THEN
      REMOVE_THEN "CORE2" (MP_TAC o SPECL [`rs':num->real`; `ks':num->real`; `dd:num->real`;
        `hs:(A)rfs_history`; `x:A`; `t:real`; `rr:real`]) THEN
      ASM_REWRITE_TAC[p3_vrm; REAL_LE_REFL] THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[P2C_RFS_VIEW_PARTS]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `min (kL / &2) kS * r pow 3` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REAL_ARITH_TAC);;

(* The 16.1 route theorem (pc_p3_route): the moving-endpoint statement of Part 2A is a theorem *)
(* (P2ARC_BALL_REACH, unit pc_p2a_reach); P3_LEMMA_14_11_STATEMENT is not needed (the region   *)
(* flow comes from P2AH_HISTORY_REGION through P2AB_REGION).                                    *)

let P3L_PROP_16_1_ROUTE = prove
 (`!u:A->bool. P3_PROP_16_1_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_1_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3L_PROP_16_1_PRE THEN ASM_REWRITE_TAC[P2ARC_BALL_REACH]);;

