(* ========================================================================= *)
(* pc_pv411: MT Prop 4.11, volume part (P2_PROP_4_11_VOLUME_STATEMENT of     *)
(* pc_p3_iface): a Ricci flow on a closed 3-manifold from a normalized       *)
(* metric with abs Rm <= K on [0,tau] is noncollapsed there on scales <= 1,  *)
(* with a constant depending on (K, tau).  Route: the curvature bound bounds *)
(* the Ricci curvature, the metrics on [0,tau] are equivalent with factor    *)
(* L = exp(2 K' tau) (PV411_QFORM_EQUIV, a closed-interval form of          *)
(* RFA_METRIC_EQUIV), so B(x,0,r/sqrt L) SUBSET B(x,t,r) and the volumes are *)
(* comparable, and the normalization gives the bound at time 0 for every     *)
(* r <= 1 (no Bishop-Gromov needed).                                         *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_rfa_r1.ml";;
needs "src/pc_rfa_hbar.ml";;
needs "src/pc_grg_area.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Metric equivalence along a Ricci flow on a closed interval                *)
(* [a,t1] with t1 < b, from a Ricci bound on [a,t1] only (RFA_METRIC_EQUIV   *)
(* needs the bound up to b), and positivity of the quadratic forms.          *)
(* ------------------------------------------------------------------------- *)

let PV411_QFORM_EQUIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t1 K.
     ricci_flow_from (top,atlas) a b g /\ a < t1 /\ t1 < b /\
     (!t x v. a <= t /\ t <= t1 /\ x IN topspace top
              ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v)))
     ==> !t x v. a <= t /\ t <= t1 /\ x IN topspace top
                 ==> exp(--(&2 * K * (t - a))) * (v dot (g a x ** v)) <= v dot (g t x ** v) /\
                     v dot (g t x ** v) <= exp(&2 * K * (t - a)) * (v dot (g a x ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "ric" o check (fun th -> is_forall(concl th))) THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) a t1 (g:real->A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `t1:real`;
                 `g:real->A->real^N^N`; `K:real`] RFA_METRIC_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "ric" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN(LABEL_TAC "eq")] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t < t1` THENL
   [USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t:real = t1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `s = (a + t1) / &2` THEN
  SUBGOAL_THEN `a < s /\ s < t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "eq" (MP_TAC o SPECL [`s:real`; `x:A`; `v:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `s:real`; `t1:real`; `K:real`] RFAH_QFORM_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `ricci_flow_from (top,atlas) a b (g:real->A->real^N^N)` THEN
      SIMP_TAC[ricci_flow_from];
      REPEAT STRIP_TAC THEN USE_THEN "ric" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `t1:real`; `x:A`; `v:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `exp(&2 * K * (t1 - a)) = exp(&2 * K * (t1 - s)) * exp(&2 * K * (s - a)) /\
    exp(--(&2 * K * (t1 - a))) = exp(--(&2 * K * (t1 - s))) * exp(--(&2 * K * (s - a)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `exp(--(&2 * K * (t1 - s))) * (v dot ((g:real->A->real^N^N) s x ** v))`;
    EXISTS_TAC `exp(&2 * K * (t1 - s)) * (v dot ((g:real->A->real^N^N) s x ** v))`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]);;

let PV411_QPOS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= v dot (g x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]]);;

(* ------------------------------------------------------------------------- *)
(* The volume part of MT Prop 4.11.                                          *)
(* ------------------------------------------------------------------------- *)

let PV411_EXP_EQUIV_L = prove
 (`!q0 q E L. &0 < E /\ E <= L /\ &0 <= q0 /\ &0 <= q /\ inv E * q0 <= q /\ q <= E * q0
              ==> q <= L * q0 /\ q0 <= L * q`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E * q0` THEN ASM_SIMP_TAC[REAL_LE_RMUL];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E * q` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `q0 = E * (inv E * q0)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ASM_SIMP_TAC[REAL_LE_RMUL]]]);;

let PV411_PROP_4_11_VOLUME = prove
 (`!(u:A->bool). P2_PROP_4_11_VOLUME_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_PROP_4_11_VOLUME_STATEMENT] THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmd"))
    (INST_TYPE [`:3`,`:N`] RFA_R1_RMD0) THEN
  MAP_EVERY X_GEN_TAC [`K:real`; `tau:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `K1 = &(dimindex(:3)) * sqrt(C0 * K pow 2)` THEN
  SUBGOAL_THEN `&0 <= K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `L = exp(&2 * K1 * tau)` THEN
  SUBGOAL_THEN `&1 <= L /\ &0 < L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt L /\ &1 <= sqrt L` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN
    ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&2 / &3 * pi / L pow 3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[PI_POS; REAL_POW_LT];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real`;
                       `g:real->A->real^3^3`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `r:real`] THEN STRIP_TAC THEN
  (* the metrics on [0,tau] are Riemannian *)
  SUBGOAL_THEN `!s. &0 <= s /\ s <= tau ==> riemannian_metric atlas ((g:real->A->real^3^3) s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `ricci_flow_from (top,atlas) (&0) b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
    ASM_CASES_TAC `s = &0` THENL
     [ASM_SIMP_TAC[];
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) (&0)) /\
                riemannian_metric atlas (g t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the Ricci bound on [0,tau] *)
  SUBGOAL_THEN
   `!s z v. &0 <= s /\ s <= tau /\ z IN topspace top
            ==> abs(mfd_ricci atlas ((g:real->A->real^3^3) s) z v v) <= K1 * (v dot (g s z ** v))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K1" THEN MATCH_MP_TAC RFA_R1_RIC_BOUND THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2] THEN
    TRY(USE_THEN "rmd" MATCH_MP_TAC THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[]);
    ALL_TAC] THEN
  (* metric equivalence with factor L *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `&0`; `b:real`;
                 `g:real->A->real^3^3`; `tau:real`; `K1:real`] PV411_QFORM_EQUIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `!z v. z IN topspace top
          ==> v dot ((g:real->A->real^3^3) t z ** v) <= L * (v dot (g (&0) z ** v)) /\
              v dot (g (&0) z ** v) <= L * (v dot (g t z ** v))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:A`; `v:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC PV411_EXP_EQUIV_L THEN EXISTS_TAC `exp(&2 * K1 * t)` THEN
    REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_NEG] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC PV411_QPOS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PV411_QPOS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:A`; `v:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `exp`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `z:A`; `v:real^3`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `exp`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the ball of radius r / sqrt L at time 0 lies in the ball of radius r at time t *)
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->A->real^3^3) (&0)) x (r / sqrt L) SUBSET
    mfd_ball (top,atlas) (g t) x r`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sqrt L * mfd_dist (top,atlas) ((g:real->A->real^3^3) (&0)) x y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFAH_DIST_COMPARE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  (* volumes *)
  SUBGOAL_THEN `&0 < r / sqrt L /\ r / sqrt L <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rfs_normalized (top,atlas) ((g:real->A->real^3^3) (&0))` THEN
  REWRITE_TAC[rfs_normalized] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `r / sqrt L`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `x:A`; `r:real`] MFD_HAS_VOLUME_BALL_COMPACT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`;
                 `mfd_ball (top,atlas) ((g:real->A->real^3^3) (&0)) x (r / sqrt L)`;
                 `mfd_ball (top,atlas) ((g:real->A->real^3^3) t) x r`; `w:real`]
    MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`(g:real->A->real^3^3) (&0)`; `\x:A. &1`; `v0:real`] THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume];
    ALL_TAC] THEN
  ABBREV_TAC `vt = mfd_volume (top,atlas) ((g:real->A->real^3^3) t)
                     (mfd_ball (top,atlas) (g (&0)) x (r / sqrt L))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) (&0)`; `(g:real->A->real^3^3) t`;
                 `mfd_ball (top,atlas) ((g:real->A->real^3^3) (&0)) x (r / sqrt L)`;
                 `v0:real`; `vt:real`; `L:real`] MFD_HAS_VOLUME_COMPARE_QF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` (fun th -> ASM_SIMP_TAC[th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) (&0)`; `x:A`; `r / sqrt L`] MFD_BALL_OPEN) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(&2 / &3 * pi / L pow 3) * r pow 3 =
    (&2 / &3 * pi * (r / sqrt L) pow 3) / (L * sqrt L)`
  SUBST1_TAC THENL
   [MP_TAC(MATCH_MP SQRT_POW_2 (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < L`))) THEN
    UNDISCH_TAC `&0 < sqrt L` THEN
    SPEC_TAC(`sqrt L`,`q:real`) THEN GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L * sqrt L` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(L * sqrt L) * vt <= (L * sqrt L) * w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

