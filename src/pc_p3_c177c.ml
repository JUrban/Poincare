(* ========================================================================= *)
(* Unit pc_p3_c177c: MT Lemma 17.7, case (2b) (p. 405-406):                 *)
(* the neck of the standard solution from time 0 with normalized length     *)
(* below 1 + eps_in.  The strong neck at (x, ts) reaches back past the      *)
(* surgery time: an exactly time-matched transfer of the neck to the        *)
(* history after T_k, a strong neck at (x, T_k) re-centred from the surgery *)
(* neck (which evolves for rescaled time 2), and                            *)
(* Prop 15.2 (P3E_PROP_15_2, pc_p3e_152h) glue them.                         *)
(* ========================================================================= *)

needs "src/pc_p3_c177a.ml";;
needs "src/pc_p2b_979.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The exactly time-matched transfer of an evolving neck (the               *)
(* target length L may equal a R'/Q', the length whose time interval maps   *)
(* onto the source interval).  Adapted from P2B9_TIME_SHIFT,                *)
(* P2B9_ENECK_POINTWISE and P2B9_ENECK_CORE of pc_p2b_979: only the length  *)
(* hypothesis L < a (1 - m) is replaced by L <= a R'/Q', and the steps      *)
(* using it.                                                                *)
(* ========================================================================= *)

let P3H_TIME_SHIFT_X = prove
 (`!a L m c s.
     &0 < L /\ abs(c - &1) <= m /\ m <= &1 / &2 /\ L <= a * c /\
     --L < s /\ s <= &0
     ==> &0 < c /\ --a < s / c /\ s / c <= &0 /\ abs(s - s / c) <= &2 * L * m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= c /\ &0 < c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < a` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a * c <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    SUBGOAL_THEN `s - s / c = (s * (c - &1)) / c` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(L * m) * &1 <= (L * m) * (&2 * c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let P3H_ENECK_POINTWISE_X = prove
 (`!k1 M K0 eps eps1 a L delta d0 V x t (e:real^3->A) V' t' Q' (psi:A->B) R R' c m.
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k1 G0 G1 y <= &1 / &4
         ==> lck_dist2 k1 G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k1 G1 G2 y) /\
     &0 <= M /\ k1 = rfs_kreg eps1 /\
     &0 < eps /\ eps <= eps1 /\ &0 < L /\
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\
     rfs_vscalar V t x = R /\ rfs_vscalar V' t' (psi x) = R' /\ R' / Q' = c /\
     &72 * (&1 + abs K0) * delta = m /\ d0 <= &1 / &4 /\
     (!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                  (\z. R %% rfs_pullback (rfs_vatlas V (t + s / R)) e
                                        (rfs_vmetric V (t + s / R)) z) y <= d0) /\
     (!s. --a < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                    (rfs_vatlas V' (t' + s / Q')) /\
              riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                (rfs_vmetric V' (t' + s / Q'))) /\
     p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
       V' t' Q' psi {s | --a < s /\ s <= &0} delta /\
     &0 < delta /\ delta <= &1 / &10 /\ delta <= eps1 /\
     m <= &1 / &2 /\ &2 * L * m <= &1 / &2 /\ L <= a * c /\
     abs(c - &1) <= m
     ==> !s y. --L < s /\ s <= &0 /\ y IN rfs_neck_dom eps1
               ==> lck_dist2 k1 (cylinder_flow s)
                     (\z. R' %% rfs_pullback (rfs_vatlas V' (t' + s / R')) (psi o e)
                                             (rfs_vmetric V' (t' + s / R')) z) y
                   <= ((&1 + &2 * L * m) pow (k1 + 2) *
                       ((&1 + m) * (sqrt d0 + sqrt M * delta) + (&2 + &4 * L) * m)) pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k1 <= rfs_kreg eps /\ k1 <= rfs_kreg delta` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC APX_KREG_MONO THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `k1 = rfs_kreg eps1` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < Q'` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_view_close (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t (rfs_vscalar V t x)
                   (IMAGE e (rfs_neck_dom eps))
                   (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                       (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta` THEN
    SIMP_TAC[p3_view_close];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= c /\ &0 < c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R' = c * Q'` ASSUME_TAC THENL
   [UNDISCH_TAC `R' / Q' = c` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < Q'` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < a` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a * c <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = s / c` THEN
  SUBGOAL_THEN `s1 <= &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real`; `&0`; `c:real`] REAL_LE_LDIV_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--a < s1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`--a`; `s:real`; `c:real`] REAL_LT_RDIV_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(s - s1) <= &2 * L * m` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `s / c = s1`)) THEN
    SUBGOAL_THEN `s - s / c = (s * (c - &1)) / c` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= L * m` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(L * m) * &1 <= (L * m) * (&2 * c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t' + s / R' = t' + s1 / Q'` SUBST1_TAC THENL
   [UNDISCH_TAC `s / c = s1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `R' = c * Q'` THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < c`; `&0 < Q'`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `eps:real`; `x:A`; `t:real`; `a:real`; `e:real^3->A`;
                 `(V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))`; `t':real`; `Q':real`; `psi:A->B`; `delta:real`; `s1:real`]
                P2B9_VIEW_SLICE_DATA) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `eps:real`; `x:A`; `t:real`; `a:real`; `e:real^3->A`; `s1:real`]
                P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))))) THEN
  MP_TAC(MATCH_MP (SPEC `s1:real` (ASSUME
    `!s. --a < s /\ s <= &0
         ==> smooth_manifold_atlas (rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q'))
                                   (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q')) /\
             riemannian_metric (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q'))
                               (rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q'))`))
    (CONJ (ASSUME `--a < s1`) (ASSUME `s1 <= &0`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_neck_dom eps1 SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `G1 = \z. R %% rfs_pullback (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t + s1 / R)) (e:real^3->A)
                                          (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t + s1 / R)) z` THEN
  ABBREV_TAC `G2 = \z. Q' %% rfs_pullback (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q'))
                                           ((psi:A->B) o (e:real^3->A))
                                           (rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q')) z` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (G1:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (G2:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]]) THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 (rfs_kreg eps) (cylinder_flow s1) (G1:real^3->real^3^3) y <= d0`
  ASSUME_TAC THENL
   [EXPAND_TAC "G1" THEN MATCH_MP_TAC(ASSUME
     `!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                  (\z. R %% rfs_pullback (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t + s / R)) (e:real^3->A)
                                        (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t + s / R)) z) y <= d0`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 (rfs_kreg delta) (G1:real^3->real^3^3) G2 y <= dd` ASSUME_TAC THENL
   [USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d0 /\ &0 <= dd` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow s1) (G1:real^3->real^3^3) y`;
      EXISTS_TAC `lck_dist2 (rfs_kreg delta) (G1:real^3->real^3^3) G2 y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[APX_NECK_DOM_NONZERO; APX_NECK_DOM_OPEN] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg eps`; `k1:num`; `rfs_kreg delta`; `M:real`; `s:real`; `s1:real`;
                 `rfs_neck_dom eps`; `G1:real^3->real^3^3`; `G2:real^3->real^3^3`;
                 `c:real`; `d0:real`; `dd:real`; `y:real^3`] P2B9_NECK_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k1 + 2`; `L:real`; `m:real`; `delta:real`; `c:real`; `abs(s - s1)`;
                 `sqrt d0`; `M:real`; `dd:real`] P2B9_BND_ARITH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_POS; SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&72 * (&1 + abs K0) * delta = m` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `lck_dist2 k1 (cylinder_flow s) (\z. c %% (G2:real^3->real^3^3) z) y <= ((&1 + &2 * L * m) pow (k1 + 2) *
     ((&1 + m) * (sqrt d0 + sqrt M * delta) + (&2 + &4 * L) * m)) pow 2` MP_TAC THENL
   [SUBGOAL_THEN `&0 <= lck_dist2 k1 (cylinder_flow s) (\z. c %% (G2:real^3->real^3^3) z) y` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        REWRITE_TAC[APX_NECK_DOM_NONZERO; APX_NECK_DOM_OPEN] THEN
        MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(lck_dist2 k1 (cylinder_flow s) (\z. c %% (G2:real^3->real^3^3) z) y) <= ((&1 + &2 * L * m) pow (k1 + 2) *
     ((&1 + m) * (sqrt d0 + sqrt M * delta) + (&2 + &4 * L) * m))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th1 -> FIRST_ASSUM(fun th2 ->
        ACCEPT_TAC(MATCH_MP REAL_LE_TRANS (CONJ th1 th2))));
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(lck_dist2 k1 (cylinder_flow s) (\z. c %% (G2:real^3->real^3^3) z) y) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  UNDISCH_TAC `R' = c * Q'` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_CMUL_ASSOC] THEN EXPAND_TAC "G2" THEN REWRITE_TAC[]);;

let P3H_ENECK_CORE_X = prove
 (`!k1 M K0 eps eps1 a L delta d0 V x t (e:real^3->A) V' t' Q' (psi:A->B).
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k1 G0 G1 y <= &1 / &4
         ==> lck_dist2 k1 G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k1 G1 G2 y) /\
     &0 <= M /\ k1 = rfs_kreg eps1 /\
     &0 < eps /\ eps <= eps1 /\ &0 < L /\
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\
     &0 <= d0 /\ d0 <= &1 / &4 /\
     (!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                  (\z. rfs_vscalar V t x %%
                       rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                    (rfs_vmetric V (t + s / rfs_vscalar V t x)) z) y <= d0) /\
     (!y0. y0 IN sphere(vec 0,&1) /\ e y0 = x
           ==> lrm_deriv_norm2 0 (\z. rfs_vscalar V t x %%
                                      rfs_pullback (rfs_vatlas V t) e (rfs_vmetric V t) z) y0
               <= K0 pow 2) /\
     (!s. --a < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                    (rfs_vatlas V' (t' + s / Q')) /\
              riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                (rfs_vmetric V' (t' + s / Q'))) /\
     p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
       V' t' Q' psi {s | --a < s /\ s <= &0} delta /\
     &0 < delta /\ delta <= &1 / &10 /\ delta <= eps1 /\
     &72 * (&1 + abs K0) * delta <= &1 / &2 /\
     &2 * L * (&72 * (&1 + abs K0) * delta) <= &1 / &2 /\
     L <= a * (rfs_vscalar V' t' (psi x) / Q') /\
     (&1 + &2 * L * (&72 * (&1 + abs K0) * delta)) pow (k1 + 2) *
       ((&1 + &72 * (&1 + abs K0) * delta) * (sqrt d0 + sqrt M * delta) +
        (&2 + &4 * L) * (&72 * (&1 + abs K0) * delta)) < eps1
     ==> rfs_evolving_neck V' eps1 (psi x) t' L (psi o e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = &72 * (&1 + abs K0) * delta` THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x` THEN
  ABBREV_TAC `R' = rfs_vscalar (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                   (real->B->real^3^3)) t' ((psi:A->B) x)` THEN
  ABBREV_TAC `c = R' / Q'` THEN
  ABBREV_TAC `Bnd = (&1 + &2 * L * m) pow (k1 + 2) *
                    ((&1 + m) * (sqrt d0 + sqrt M * delta) + (&2 + &4 * L) * m)` THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN sphere(vec 0,&1) /\ (e:real^3->A) y0 = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) eps x t a (e:real^3->A)` THEN
    REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) <= m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `eps:real`; `x:A`; `t:real`; `a:real`; `e:real^3->A`;
                   `(V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))`; `t':real`; `Q':real`; `psi:A->B`; `delta:real`; `K0:real`;
                   `y0:real^3`] P2B9_SCALAR_RATIO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2"))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Q'` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_view_close (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t R (IMAGE (e:real^3->A) (rfs_neck_dom eps))
                   (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t' Q' (psi:A->B) {s | --a < s /\ s <= &0} delta` THEN
    SIMP_TAC[p3_view_close];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c /\ &0 < R'` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R' = c * Q'` SUBST1_TAC THENL
     [UNDISCH_TAC `R' / Q' = c` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `&0 < Q'` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:num`; `M:real`; `K0:real`; `eps:real`; `eps1:real`; `a:real`;
                 `L:real`; `delta:real`; `d0:real`; `(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `x:A`; `t:real`; `e:real^3->A`;
                 `(V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))`; `t':real`; `Q':real`; `psi:A->B`; `R:real`; `R':real`; `c:real`;
                 `m:real`] P3H_ENECK_POINTWISE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "base" ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pw") THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bnd` ASSUME_TAC THENL
   [EXPAND_TAC "Bnd" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN
      SUBGOAL_THEN `&0 <= L * m` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Bnd pow 2 < eps1 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `c * Q' = R'` ASSUME_TAC THENL
   [UNDISCH_TAC `R' / Q' = c` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < Q'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps1 SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps1` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps1:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1. --a < s1 /\ s1 <= &0
         ==> smooth_manifold_atlas (rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q')) (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q')) /\
             mfd_param (rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q')) (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q'))
                       (rfs_neck_dom eps1) ((psi:A->B) o (e:real^3->A)) /\
             open_in (rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s1 / Q'))
                     (IMAGE ((psi:A->B) o (e:real^3->A)) (rfs_neck_dom eps1))`
  (LABEL_TAC "sl") THENL
   [X_GEN_TAC `s1:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `eps:real`; `x:A`; `t:real`; `a:real`; `e:real^3->A`;
                   `(V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3))`; `t':real`; `Q':real`; `psi:A->B`; `delta:real`; `s1:real`]
                  P2B9_VIEW_SLICE_DATA) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "op") (K ALL_TAC))) THEN
    MP_TAC(MATCH_MP (SPEC `s1:real` (ASSUME
      `!s. --a < s /\ s <= &0
           ==> smooth_manifold_atlas (rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q'))
                                     (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q')) /\
               riemannian_metric (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q'))
                                 (rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) (t' + s / Q'))`))
      (CONJ (ASSUME `--a < s1`) (ASSUME `s1 <= &0`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[APX_NECK_DOM_OPEN];
      USE_THEN "op" MATCH_MP_TAC THEN ASM_REWRITE_TAC[APX_NECK_DOM_OPEN]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) eps x t a (e:real^3->A)` THEN
    REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; rfs_neck; rfs_close_on; rfs_close_fam] THEN
  REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  USE_THEN "sl" (fun th -> MP_TAC(REWRITE_RULE[real_div; REAL_MUL_LZERO; REAL_ADD_RID]
     (MATCH_MP (SPEC `&0` th)
        (CONJ (MATCH_MP (REAL_ARITH `&0 < a ==> --a < &0`) (ASSUME `&0 < a`))
              (SPEC `&0` REAL_LE_REFL))))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `Bnd pow 2` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    USE_THEN "pw" (fun th -> MP_TAC(REWRITE_RULE[real_div; REAL_MUL_LZERO; REAL_ADD_RID]
      (MATCH_MP (SPECL [`&0`; `y:real^3`] th)
        (CONJ (MATCH_MP (REAL_ARITH `&0 < L ==> --L < &0`) (ASSUME `&0 < L`))
              (CONJ (SPEC `&0` REAL_LE_REFL) (ASSUME `(y:real^3) IN rfs_neck_dom eps1`)))))) THEN
    REWRITE_TAC[];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real`; `L:real`; `m:real`; `c:real`; `(u - t') * R'`] P3H_TIME_SHIFT_X) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`--L`; `u - t'`; `R':real`] REAL_LT_LDIV_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
        UNDISCH_TAC `t' - L / R' < u` THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
        REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "sl" (fun th -> MP_TAC(MATCH_MP (SPEC `((u - t') * R') / c` th)
      (CONJ (ASSUME `--a < ((u - t') * R') / c`) (ASSUME `((u - t') * R') / c <= &0`)))) THEN
    SUBGOAL_THEN `t' + ((u - t') * R') / c / Q' = u` SUBST1_TAC THENL
     [UNDISCH_TAC `c * Q' = R'` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MAP_EVERY UNDISCH_TAC [`&0 < c`; `&0 < Q'`] THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[]];
    EXISTS_TAC `Bnd pow 2` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "pw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* (b1) re-centring the surgery neck.  The slices of the                    *)
(* pre-surgery view along an evolving neck; the cylinder view (the          *)
(* shrinking cylinder on R^3 minus 0 over [-3,1)) with its exact necks; the  *)
(* view closeness from the cylinder view along an evolving neck; and the     *)
(* re-centred neck N o (dilation by |u0|) at N u0 (P3H_RECENTRE_CORE, by     *)
(* P3H_ENECK_CORE_X with the exact cylinder neck as source).                 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* (b1) part 1: the slices of the pre-surgery view along an evolving neck.  *)
(* For times before T_k the preview is the history view (regular); at T_k   *)
(* it is the open set Omega of stage k-1 with the limit metric.  An evolving *)
(* neck in the preview at T_k is a parametrization of every slice it         *)
(* persists through (via a time b of slab k-1 and the identity diffeos of    *)
(* the regular history view).                                                *)
(* ========================================================================= *)

let P3H_PREVIEW_BEFORE = prove
 (`!(hs:(A)rfs_history) k t.
     t < hs_time hs k
     ==> rfs_vtop (rfs_preview hs k) t = rfs_top_at hs t /\
         rfs_vatlas (rfs_preview hs k) t = rfs_atlas_at hs t /\
         rfs_vmetric (rfs_preview hs k) t = rfs_metric_at hs t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[rfs_preview; rfs_vtop; rfs_vatlas; rfs_vmetric; REAL_LT_IMP_NE]);;

let P3H_PREVIEW_AT_TOP = prove
 (`!(hs:(A)rfs_history) k.
     rfs_vtop (rfs_preview hs k) (hs_time hs k) =
     subtopology (hs_top hs (k - 1)) (ev_omega(hs_event hs k))`,
  REWRITE_TAC[rfs_preview; rfs_vtop]);;

let P3H_PREVIEW_AT_METRIC = prove
 (`!(hs:(A)rfs_history) k.
     rfs_vatlas (rfs_preview hs k) (hs_time hs k) =
     restrict_atlas (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k)) /\
     rfs_vmetric (rfs_preview hs k) (hs_time hs k) =
     restrict_metric (hs_atlas hs (k - 1)) (ev_omega(hs_event hs k))
                     (ev_limit(hs_event hs k))`,
  REWRITE_TAC[rfs_preview; rfs_vatlas; rfs_vmetric]);;

let P3H_VSCALAR_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric]);;

let P3H_PERSISTS_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a b.
     rfs_persists V W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
             open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]);;

let P3H_PREVIEW_NECK_SLICE = prove
 (`!(hs:(A)rfs_history) k d y a (N:real^3->A) s.
     rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\ 1 <= k /\ k <= hs_count hs /\
     rfs_evolving_neck (rfs_preview hs k) d y (hs_time hs k) a N /\ --a < s /\ s <= &0
     ==> &0 < rfs_vscalar (rfs_preview hs k) (hs_time hs k) y /\
         smooth_manifold_atlas
           (rfs_vtop (rfs_preview hs k)
                     (hs_time hs k + s / rfs_vscalar (rfs_preview hs k) (hs_time hs k) y))
           (rfs_vatlas (rfs_preview hs k)
                       (hs_time hs k + s / rfs_vscalar (rfs_preview hs k) (hs_time hs k) y)) /\
         riemannian_metric
           (rfs_vatlas (rfs_preview hs k)
                       (hs_time hs k + s / rfs_vscalar (rfs_preview hs k) (hs_time hs k) y))
           (rfs_vmetric (rfs_preview hs k)
                        (hs_time hs k + s / rfs_vscalar (rfs_preview hs k) (hs_time hs k) y)) /\
         mfd_param
           (rfs_vtop (rfs_preview hs k)
                     (hs_time hs k + s / rfs_vscalar (rfs_preview hs k) (hs_time hs k) y))
           (rfs_vatlas (rfs_preview hs k)
                       (hs_time hs k + s / rfs_vscalar (rfs_preview hs k) (hs_time hs k) y))
           (rfs_neck_dom d) N`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
  ABBREV_TAC `Tk = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `R = rfs_vscalar (rfs_preview (hs:(A)rfs_history) k) Tk y` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[P3H_VSCALAR_ALT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = Tk + s / R` THEN
  SUBGOAL_THEN `Tk - a / R < u /\ u <= Tk` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SUBGOAL_THEN `--a / R < s / R /\ s / R <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
      REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (N:real^3->A) (rfs_neck_dom d) = {})` ASSUME_TAC THENL
   [MP_TAC(SPEC `d:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:A) IN IMAGE (N:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the event k and the stage k-1 *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "times")
    (CONJUNCTS_THEN2 (LABEL_TAC "stages") (LABEL_TAC "events")))) THEN
  USE_THEN "events" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (k - 1)) (ev_omega(hs_event hs k)) /\
                rfs_limit_metric (hs_top hs (k - 1),hs_atlas hs (k - 1))
                  (ev_omega(hs_event hs k)) Tk (hs_metric hs (k - 1))
                  (ev_limit(hs_event hs k))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_metric (hs:(A)rfs_history) (k - 1)) (hs_time hs k)
                   (hs_top hs k,hs_atlas hs k) (hs_metric hs k) (hs_event hs k)` THEN
    ASM_REWRITE_TAC[rfs_event_ok] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) (k - 1)) (hs_atlas hs (k - 1))
                          (rfs_neck_dom d) (N:real^3->A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `ev_omega(hs_event (hs:(A)rfs_history) k)`; `rfs_neck_dom d`;
                   `N:real^3->A`] APX_PARAM_FROM_RESTRICT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_param (rfs_vtop (rfs_preview (hs:(A)rfs_history) k) Tk)
                   (rfs_vatlas (rfs_preview hs k) Tk) (rfs_neck_dom d) (N:real^3->A)` THEN
    EXPAND_TAC "Tk" THEN REWRITE_TAC[P3H_PREVIEW_AT_TOP; P3H_PREVIEW_AT_METRIC];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real = Tk` THENL
   [(* the slice at T_k: Omega with the limit metric *)
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `u:real = Tk` THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "Tk" THEN REWRITE_TAC[P3H_PREVIEW_AT_METRIC] THEN
    MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                          `hs_metric (hs:(A)rfs_history) (k - 1)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u < Tk` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* earlier slices: the history view *)
  SUBGOAL_THEN `!v. v < Tk
                    ==> rfs_vtop (rfs_preview (hs:(A)rfs_history) k) v = rfs_top_at hs v /\
                        rfs_vatlas (rfs_preview hs k) v = rfs_atlas_at hs v /\
                        rfs_vmetric (rfs_preview hs k) v = rfs_metric_at hs v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real` THEN DISCH_TAC THEN MATCH_MP_TAC P3H_PREVIEW_BEFORE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) u) (rfs_atlas_at hs u) /\
                open_in (rfs_top_at hs u) (IMAGE (N:real^3->A) (rfs_neck_dom d))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `~(topspace(rfs_top_at (hs:(A)rfs_history) u) = {})` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
      can (find_term (fun t -> t = `u:real`)) (concl th))) THEN
    UNDISCH_TAC `~(IMAGE (N:real^3->A) (rfs_neck_dom d) = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `u:real` o CONJUNCT1 o REWRITE_RULE[p2c_regular_view] o check
      (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_regular_view"))
                     (concl th))) THEN
    REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* a time b of slab k-1 after u *)
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < Tk` ASSUME_TAC THENL
   [EXPAND_TAC "Tk" THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k = hs_time hs ((k - 1) + 1)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "times" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b = (max u (hs_time (hs:(A)rfs_history) (k - 1)) + Tk) / &2` THEN
  SUBGOAL_THEN `u < b /\ b < Tk /\ hs_time (hs:(A)rfs_history) (k - 1) <= b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `b:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  (* the identity diffeo from slice u to slice b *)
  FIRST_ASSUM(MP_TAC o SPECL [`IMAGE (N:real^3->A) (rfs_neck_dom d)`; `Tk - a / R`; `b:real`;
                              `u:real`] o el 3 o CONJUNCTS o REWRITE_RULE[p2c_regular_view] o
    check (fun th -> can (find_term (fun t -> is_const t &&
                                            fst(dest_const t) = "p2c_regular_view")) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P3H_PERSISTS_ALT] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real` THEN STRIP_TAC THEN
    REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas] THEN
    SUBGOAL_THEN `v < Tk` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
      can (find_term (fun t -> t = `a:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_top_at")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_preview")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(N:real^3->A) = (\z. z) o N` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                        `IMAGE (N:real^3->A) (rfs_neck_dom d)`;
                        `IMAGE (N:real^3->A) (rfs_neck_dom d)`; `\z:A. z`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* (b1) part 2: the cylinder view.  The shrinking cylinder flow on R^3      *)
(* minus 0 over [-3,1) as a regular view, its exact necks (dilations), and  *)
(* the view closeness to any view along an evolving neck of length <= 3.    *)
(* ========================================================================= *)

let p3h_cylview = new_definition
 `p3h_cylview =
    rfs_flow_view (subtopology euclidean ((:real^3) DELETE vec 0),
                   open_set_atlas ((:real^3) DELETE vec 0))
                  {s | --(&3) <= s /\ s < &1} cylinder_flow`;;

let P3H_RICCI_FLOW_ON_FROM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a' a b (g:real->A->real^N^N).
     ricci_flow_on (top,atlas) a' b g /\ a' < a /\ a < b
     ==> ricci_flow_from (top,atlas) a b g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a',lift b) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    EXISTS_TAC `a - a':real` THEN
    EXISTS_TAC `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas (c:(A->bool)#(A->real^N))
                       ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
    REWRITE_TAC[REAL_ARITH `a - (a - a') = a':real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

let P3H_OPEN_NONZERO = prove
 (`open ((:real^3) DELETE vec 0)`,
  MATCH_MP_TAC OPEN_DELETE THEN REWRITE_TAC[OPEN_UNIV]);;

let P3H_CYLVIEW = prove
 (`(!s. --(&3) <= s /\ s < &1
        ==> rfs_vtop p3h_cylview s = subtopology euclidean ((:real^3) DELETE vec 0)) /\
   (!s. rfs_vatlas p3h_cylview s = open_set_atlas ((:real^3) DELETE vec 0)) /\
   (!s. rfs_vmetric p3h_cylview s = cylinder_flow s)`,
  REWRITE_TAC[p3h_cylview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
  SIMP_TAC[]);;

let P3H_CYLVIEW_REGULAR = prove
 (`P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) ==> p2c_regular_view p3h_cylview`,
  REWRITE_TAC[P2C_FLOW_VIEW_REGULAR_STATEMENT; p3h_cylview] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN] THEN
  MATCH_MP_TAC P3H_RICCI_FLOW_ON_FROM THEN EXISTS_TAC `--(&4)` THEN
  SIMP_TAC[SHRINKING_CYLINDER_FLOW; REAL_ARITH `--(&4) < &1`] THEN REAL_ARITH_TAC);;


let P3H_PULLBACK_OSA_SET = prove
 (`!U (e:real^N->real^N) (g:real^N->real^N^N) y.
     open U /\ e y IN U
     ==> rfs_pullback (open_set_atlas U) e g y = mpullback e g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT; RFB_OPEN_SET_METRIC_LOCAL; o_THM] THEN
  SUBGOAL_THEN `(\x:real^N. x) o (e:real^N->real^N) = e` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; REFL_TAC]);;

let P3H_MPB_OSA_SET = prove
 (`!U (atlas:((B->bool)#(B->real^N))->bool) (e:real^N->B) (g:B->real^N^N) y.
     open U /\ y IN U
     ==> mfd_pullback_metric (open_set_atlas U) atlas e g y = rfs_pullback atlas e g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_pullback_metric; rfs_pullback] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT; SND] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative
                  (SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) ((e:real^N->B) y)) o e o
                   chart_inv (U,(\x:real^N. x))) (at y) =
                frechet_derivative (SND(chart_at atlas (e y)) o e) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BC_FRECHET_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID];
    ASM_SIMP_TAC[MFDM_CHART_INV_ID; o_THM]]);;

(* The exact necks of the cylinder view: at a point u0 <> 0 at time 0 the   *)
(* dilation by |u0| is an evolving eps-neck of any length a <= 3, with      *)
(* family distance 0 (the cylinder flow is dilation invariant).             *)

let P3H_NECK_DOM_NONZERO = prove
 (`!eps y:real^3. y IN rfs_neck_dom eps ==> ~(y = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck_dom] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`exp(--(inv(sqrt(&2) * eps)))`; `exp(inv(sqrt(&2) * eps))`]
                (INST_TYPE [`:3`,`:N`] SMT_SUBSET_NONZERO_ANNULUS)) THEN
  SIMP_TAC[REAL_EXP_POS_LE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3H_CYL_PULLBACK_DILATE = prove
 (`!(u0:real^3) s y.
     ~(u0 = vec 0) /\ ~(y = vec 0)
     ==> rfs_pullback (open_set_atlas ((:real^3) DELETE vec 0)) (\v. norm u0 % v)
                      (cylinder_flow s) y =
         cylinder_flow s y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfs_pullback (open_set_atlas ((:real^3) DELETE vec 0)) (\v. norm(u0:real^3) % v)
                             (cylinder_flow s) y =
                mpullback (\v. norm u0 % v) (cylinder_flow s) y` SUBST1_TAC THENL
   [MATCH_MP_TAC P3H_PULLBACK_OSA_SET THEN
    ASM_REWRITE_TAC[P3H_OPEN_NONZERO; IN_DELETE; IN_UNIV; VECTOR_MUL_EQ_0; NORM_EQ_0];
    MATCH_MP_TAC P3N_CYL_DILATION THEN ASM_REWRITE_TAC[NORM_POS_LT]]);;

let P3H_CYL_DILATE_DIST = prove
 (`!k (u0:real^3) s y.
     ~(u0 = vec 0) /\ ~(y = vec 0)
     ==> lck_dist2 k (cylinder_flow s)
           (\z. rfs_pullback (open_set_atlas ((:real^3) DELETE vec 0)) (\v. norm u0 % v)
                             (cylinder_flow s) z) y = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `cylinder_flow s`; `cylinder_flow s`; `cylinder_flow s`;
                 `\z. rfs_pullback (open_set_atlas ((:real^3) DELETE vec 0))
                        (\v. norm(u0:real^3) % v) (cylinder_flow s) z`;
                 `(:real^3) DELETE vec 0`; `y:real^3`] LCK_DIST2_LOCAL) THEN
  REWRITE_TAC[P3H_OPEN_NONZERO; IN_DELETE; IN_UNIV] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3H_CYL_PULLBACK_DILATE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[P2BL_LCK_DIST2_REFL]]);;

let P3H_CYL_EXACT_NECK = prove
 (`!eps a (u0:real^3).
     &0 < eps /\ &0 < a /\ a <= &3 /\ ~(u0 = vec 0)
     ==> rfs_vscalar p3h_cylview (&0) u0 = &1 /\
         rfs_evolving_neck p3h_cylview eps u0 (&0) a (\v. norm u0 % v) /\
         (!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
                ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                      (\z. rfs_vscalar p3h_cylview (&0) u0 %%
                           rfs_pullback
                             (rfs_vatlas p3h_cylview (&0 + s / rfs_vscalar p3h_cylview (&0) u0))
                             (\v. norm u0 % v)
                             (rfs_vmetric p3h_cylview (&0 + s / rfs_vscalar p3h_cylview (&0) u0))
                             z) y
                    <= &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_vscalar p3h_cylview (&0) (u0:real^3) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[P3H_VSCALAR_ALT; P3H_CYLVIEW] THEN
    MP_TAC(SPECL [`&0`; `u0:real^3`] CYLINDER_FLOW_SCALAR) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(u0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!s y. y IN rfs_neck_dom eps
                      ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                            (\z. rfs_pullback (open_set_atlas ((:real^3) DELETE vec 0))
                                   (\v. norm(u0:real^3) % v) (cylinder_flow s) z) y = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_CYL_DILATE_DIST THEN
    ASM_MESON_TAC[P3H_NECK_DOM_NONZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_DIV_1; REAL_ADD_LID; MATRIX_CMUL_LID; P3H_CYLVIEW] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LE_REFL]] THEN
  SUBGOAL_THEN `open (IMAGE (\v. norm(u0:real^3) % v) (rfs_neck_dom eps)) /\
                IMAGE (\v. norm(u0:real^3) % v) (rfs_neck_dom eps) SUBSET (:real^3) DELETE vec 0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_SCALING THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; rfs_neck_dom; OPEN_ANNULUS];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; VECTOR_MUL_EQ_0] THEN
      ASM_MESON_TAC[P3H_NECK_DOM_NONZERO; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
  SUBGOAL_THEN `rfs_vtop p3h_cylview (&0) = subtopology euclidean ((:real^3) DELETE vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 P3H_CYLVIEW) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P3H_CYLVIEW; REAL_DIV_1; REAL_SUB_LZERO] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean ((:real^3) DELETE vec 0))
                                      (open_set_atlas ((:real^3) DELETE vec 0))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_SET_ATLAS THEN REWRITE_TAC[P3H_OPEN_NONZERO]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the neck at time 0 *)
    REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar (open_set_atlas ((:real^3) DELETE vec 0)) (cylinder_flow (&0))
                             (u0:real^3) = &1` SUBST1_TAC THENL
     [MP_TAC(SPECL [`&0`; `u0:real^3`] CYLINDER_FLOW_SCALAR) THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_01; MATRIX_CMUL_LID] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[mfd_param] THEN EXISTS_TAC `\v:real^3. inv(norm(u0:real^3)) % v` THEN
      MP_TAC(ISPECL [`(:real^3)`; `(:real^3) DELETE vec 0`; `rfs_neck_dom eps`;
                     `IMAGE (\v. norm(u0:real^3) % v) (rfs_neck_dom eps)`;
                     `\v:real^3. norm(u0:real^3) % v`; `\v:real^3. inv(norm(u0:real^3)) % v`]
                    MFD_DIFFEO_OPEN_SET_ATLAS) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; OPEN_UNIV; SUBSET_UNIV; P3H_OPEN_NONZERO] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`norm(u0:real^3)`; `exp(--(inv(sqrt(&2) * eps)))`;
                     `exp(inv(sqrt(&2) * eps))`]
                    (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_SCALING_ANNULUS)) THEN
      ASM_REWRITE_TAC[GSYM rfs_neck_dom] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[diffeomorphism_on]) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      EXISTS_TAC `inv(norm(u0:real^3)) % u0` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; NORM_MUL;
                   REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV];
      REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `&0` THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_REFL]];
    (* persistence *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `rfs_vtop p3h_cylview s = subtopology euclidean ((:real^3) DELETE vec 0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 P3H_CYLVIEW) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `(:real^3) DELETE vec 0`;
                   `IMAGE (\v. norm(u0:real^3) % v) (rfs_neck_dom eps)`] OPEN_IN_OPEN_SUBTOPOLOGY) THEN
    REWRITE_TAC[GSYM OPEN_IN; P3H_OPEN_NONZERO] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[];
    (* the family *)
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM; MATRIX_CMUL_LID; REAL_ADD_LID] THEN
    EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_REFL]]);;

(* The source of a diffeo from an open set of R^3 may be read in the open  *)
(* manifold U (one identity chart) instead of R^3.                          *)

let P3H_MFD_DIFFEO_OSA_SOURCE = prove
 (`!U W (top:B topology) (atlas:((B->bool)#(B->real^N))->bool) W' (f:real^N->B) g.
     open U /\ W SUBSET U /\
     mfd_diffeo euclidean (open_set_atlas (:real^N)) W top atlas W' f g
     ==> mfd_diffeo (subtopology euclidean U) (open_set_atlas U) W top atlas W' f g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^N)topology`; `U:real^N->bool`; `W:real^N->bool`]
                  OPEN_IN_OPEN_SUBTOPOLOGY) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[OPEN_IN];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(U:real^N->bool) INTER W = W` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    UNDISCH_TAC `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((B->bool)#(B->real^N))->bool)
                   W (f:real^N->B)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN
    SUBGOAL_THEN `(U:real^N->bool) INTER W = W` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c':(B->bool)#(B->real^N)`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    UNDISCH_TAC `mfd_smooth_map (atlas:((B->bool)#(B->real^N))->bool) (open_set_atlas (:real^N))
                   W' (g:B->real^N)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[FST; SND; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(B->bool)#(B->real^N)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) {y | y IN FST c INTER W'}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* An evolving d-neck N of length a <= 3 (parametrizing its slices) gives    *)
(* the view closeness of the cylinder view at time 0 (scale 1) on any open  *)
(* W inside the neck domain to the view at its time (scale R(y)), with      *)
(* precision d, over the normalized times (-a,0].                            *)

let P3H_NECK_VIEW_CLOSE_CYL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    d y t a (N:real^3->A) W.
     rfs_evolving_neck V d y t a N /\ a <= &3 /\
     (!s. --a < s /\ s <= &0
          ==> mfd_param (rfs_vtop V (t + s / rfs_vscalar V t y))
                        (rfs_vatlas V (t + s / rfs_vscalar V t y)) (rfs_neck_dom d) N) /\
     open W /\ W SUBSET rfs_neck_dom d
     ==> p3_view_close p3h_cylview (&0) (&1) W V t (rfs_vscalar V t y) N
                       {s | --a < s /\ s <= &0} d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t y` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[P3H_VSCALAR_ALT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_close_fam] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_fam"))
                         (concl th))) THEN
  REWRITE_TAC[p3_view_close; REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_DIV_1; REAL_ADD_LID; P3H_CYLVIEW] THEN
  SUBGOAL_THEN `rfs_vtop p3h_cylview s = subtopology euclidean ((:real^3) DELETE vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1 P3H_CYLVIEW) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
    ASM_MESON_TAC[SUBSET; P3H_NECK_DOM_NONZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    ASM_REWRITE_TAC[mfd_param] THEN
    DISCH_THEN(X_CHOOSE_TAC `N':A->real^3`) THEN EXISTS_TAC `N':A->real^3` THEN
    MATCH_MP_TAC P3H_MFD_DIFFEO_OSA_SOURCE THEN ASM_REWRITE_TAC[P3H_OPEN_NONZERO] THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `rfs_neck_dom d` THEN
    EXISTS_TAC `IMAGE (N:real^3->A) (rfs_neck_dom d)` THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN (:real^3) DELETE vec 0 /\ x IN rfs_neck_dom d`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `x:real^3`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
    can (find_term (fun t -> t = `dd:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= d ==> b <= d`) THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
  ASM_REWRITE_TAC[P3H_OPEN_NONZERO] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; P3H_OPEN_NONZERO; MATRIX_CMUL_LID] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3H_MPB_OSA_SET THEN
  ASM_REWRITE_TAC[P3H_OPEN_NONZERO]);;

(* Re-centring an evolving d-neck of length 2 at a point N u0 of its domain: *)
(* the exact cylinder neck at u0 (dilation by |u0|) is carried by the view  *)
(* closeness to the view along N (P3H_NECK_VIEW_CLOSE_CYL) to an evolving    *)
(* eps1-neck N o (dilation) at N u0 of length 1 (P3H_ENECK_CORE_X, L = 1).   *)

let P3H_RECENTRE_CORE = prove
 (`!K0 M eps eps1
    (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    d y t (N:real^3->A) u0.
     P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     (!V' eps' x' t' a' (e':real^3->real^3).
        p2c_regular_view V' /\ rfs_evolving_neck V' eps' x' t' a' e' /\ eps' < &1 / &4
        ==> !y0. y0 IN sphere(vec 0,&1) /\ e' y0 = x'
                 ==> lrm_deriv_norm2 0
                       (\z. rfs_vscalar V' t' x' %%
                            rfs_pullback (rfs_vatlas V' t') e' (rfs_vmetric V' t') z) y0
                     <= K0 pow 2) /\
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 (rfs_kreg eps1) G0 G1 y <= &1 / &4
         ==> lck_dist2 (rfs_kreg eps1) G0 (\z. G0 z + G2 z - G1 z) y <=
             M * lck_dist2 (rfs_kreg eps1) G1 G2 y) /\
     &0 <= M /\ &0 < eps /\ eps <= eps1 /\ eps < &1 / &4 /\
     rfs_evolving_neck V d y t (&2) N /\
     (!s. --(&2) < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop V (t + s / rfs_vscalar V t y))
                                    (rfs_vatlas V (t + s / rfs_vscalar V t y)) /\
              riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t y))
                                (rfs_vmetric V (t + s / rfs_vscalar V t y)) /\
              mfd_param (rfs_vtop V (t + s / rfs_vscalar V t y))
                        (rfs_vatlas V (t + s / rfs_vscalar V t y)) (rfs_neck_dom d) N) /\
     ~(u0 = vec 0) /\ IMAGE (\v. norm u0 % v) (rfs_neck_dom eps) SUBSET rfs_neck_dom d /\
     &0 < d /\ d <= &1 / &10 /\ d <= eps1 /\ &72 * (&1 + abs K0) * d <= &1 / &2 /\
     &2 * &1 * (&72 * (&1 + abs K0) * d) <= &1 / &2 /\
     (&1 + &2 * &1 * (&72 * (&1 + abs K0) * d)) pow (rfs_kreg eps1 + 2) *
       ((&1 + &72 * (&1 + abs K0) * d) * (sqrt(&0) + sqrt M * d) +
        (&2 + &4 * &1) * (&72 * (&1 + abs K0) * d)) < eps1
     ==> rfs_evolving_neck V eps1 ((N:real^3->A) u0) t (&1) (N o (\v. norm u0 % v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K0")
    (CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `D = \v:real^3. norm(u0:real^3) % v` THEN
  SUBGOAL_THEN `p2c_regular_view p3h_cylview` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_CYLVIEW_REGULAR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `&2`; `u0:real^3`] P3H_CYL_EXACT_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> let th1 = CONJUNCT1 th in
                       let th2 = REWRITE_RULE[th1] (CONJUNCT2 th) in
                       ASSUME_TAC th1 THEN ASSUME_TAC (CONJUNCT1 th2) THEN
                       LABEL_TAC "fam" (CONJUNCT2 th2)) THEN
  SUBGOAL_THEN `?w0:real^3. w0 IN sphere(vec 0,&1) /\ (D:real^3->real^3) w0 = u0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN EXISTS_TAC `inv(norm(u0:real^3)) % u0` THEN
    SUBGOAL_THEN `&0 < norm(u0:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[IN_SPHERE_0; VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1. y1 IN sphere(vec 0,&1) /\ (D:real^3->real^3) y1 = u0
         ==> lrm_deriv_norm2 0
               (\z. &1 %%
                    rfs_pullback (rfs_vatlas p3h_cylview (&0)) D
                                 (rfs_vmetric p3h_cylview (&0)) z) y1 <= K0 pow 2`
  (LABEL_TAC "cb") THENL
   [USE_THEN "K0" (MP_TAC o SPECL [`p3h_cylview`; `eps:real`; `u0:real^3`; `&0`; `&2`;
                                   `D:real^3->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p3_view_close p3h_cylview (&0) (&1)
      (IMAGE (D:real^3->real^3) (rfs_neck_dom eps)) (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t (rfs_vscalar V t (y:A)) (N:real^3->A)
      {s | --(&2) < s /\ s <= &0} d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_NECK_VIEW_CLOSE_CYL THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "D" THEN MATCH_MP_TAC OPEN_SCALING THEN
      ASM_REWRITE_TAC[NORM_EQ_0; rfs_neck_dom; OPEN_ANNULUS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. --(&2) < s /\ s <= &0
        ==> smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (t + s / rfs_vscalar V t (y:A)))
                                  (rfs_vatlas V (t + s / rfs_vscalar V t y)) /\
            riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t y))
                              (rfs_vmetric V (t + s / rfs_vscalar V t y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the scalar ratio: R(N u0) / R(y) >= 1/2 *)
  MP_TAC(ISPECL [`p3h_cylview`; `eps:real`; `u0:real^3`; `&0`; `&2`; `D:real^3->real^3`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `rfs_vscalar V t (y:A)`; `N:real^3->A`; `d:real`; `K0:real`;
                 `w0:real^3`] P2B9_SCALAR_RATIO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY REAL_ARITH_TAC THEN USE_THEN "cb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg eps1`; `M:real`; `K0:real`; `eps:real`; `eps1:real`; `&2`; `&1`;
                 `d:real`; `&0`; `p3h_cylview`; `u0:real^3`; `&0`; `D:real^3->real^3`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `t:real`; `rfs_vscalar V t (y:A)`; `N:real^3->A`] P3H_ENECK_CORE_X) THEN
  ANTS_TAC THENL [ALL_TAC; EXPAND_TAC "D" THEN SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* (b2) necks of the pre-surgery view that avoid the surgery                 *)
(* move to the history view at the event time.  Pullbacks depend on the      *)
(* metric only at the image point; on the kept region the old atlas and the  *)
(* new one agree smoothly (identity diffeo) and the limit metric is the new  *)
(* metric (rfs_same_metric_on of rfs_event_ok).                              *)
(* ========================================================================= *)

let P3H_PULLBACK_PT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) (g:A->real^N^N) g' y.
     smooth_manifold_atlas top atlas /\ e y IN topspace top /\ g (e y) = g' (e y)
     ==> rfs_pullback atlas e g y = rfs_pullback atlas e g' y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback; metric_local; o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(e:real^N->A) y` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* On the kept region the limit metric is the pullback of the new metric by *)
(* the identity (rfs_same_metric_on read at the preferred charts).          *)

let P3H_SAME_METRIC_PT = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool) topY atlasY (gl:A->real^3^3) gY W x.
     smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
     rfs_same_metric_on atlasX gl atlasY gY W /\
     x IN W /\ x IN topspace topX /\ x IN topspace topY
     ==> gl x = mfd_pullback_metric atlasX atlasY (\z. z) gY x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_same_metric_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`chart_at (atlasX:((A->bool)#(A->real^3))->bool) x`;
    `chart_at (atlasY:((A->bool)#(A->real^3))->bool) x`;
    `SND(chart_at (atlasX:((A->bool)#(A->real^3))->bool) x) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gl:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_pullback_metric] THEN
  SUBGOAL_THEN `SND(chart_at (atlasY:((A->bool)#(A->real^3))->bool) x) o (\z:A. z) o
                chart_inv (chart_at (atlasX:((A->bool)#(A->real^3))->bool) x) =
                SND(chart_at atlasY x) o chart_inv (chart_at atlasX x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; REFL_TAC]);;

(* A kept point of an event (in both the old and the new stage) is not on a *)
(* surgery sphere.                                                          *)

let P3H_KEPT_NOT_SPHERE = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev w.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     w IN topspace topX /\ w IN topspace topY
     ==> ~(w IN mfd_cut_spheres (ev_index ev) (ev_neck ev))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_cut_cap" with Failure _ -> false)) THEN
  REWRITE_TAC[mfd_cut_cap; mfd_diffeo] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "homeomorphic_maps" with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IMAGE_ID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:A) IN topspace (ev_ztop ev)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:A) IN topspace topY` THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:A) IN mfd_cut_cores (ev_index ev) (ev_capp ev) (ev_capm ev))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* (b2) part 2: an evolving neck of the pre-surgery view at T_k whose image *)
(* lies in the new stage is an evolving neck of the history view at T_k,    *)
(* with the same scalar curvature at the centre.                            *)

let P3H_PREVIEW_TO_VIEW = prove
 (`!(hs:(A)rfs_history) k eps x L (e:real^3->A).
     rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
     rfs_evolving_neck (rfs_preview hs k) eps x (hs_time hs k) L e /\
     IMAGE e (rfs_neck_dom eps) SUBSET topspace (hs_top hs k)
     ==> rfs_vscalar (rfs_view hs) (hs_time hs k) x =
         rfs_vscalar (rfs_preview hs k) (hs_time hs k) x /\
         rfs_evolving_neck (rfs_view hs) eps x (hs_time hs k) L e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN STRIP_TAC THEN
  (* the history data *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "times")
    (CONJUNCTS_THEN2 (LABEL_TAC "stages") (LABEL_TAC "events")))) THEN
  USE_THEN "events" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "stages" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (hs_atlas (hs:(A)rfs_history) k)
                                  (hs_metric hs k (hs_time hs k))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_from")) (concl th) &&
      can (find_term (fun t -> t = `hs_metric (hs:(A)rfs_history) k`)) (concl th))) THEN
    SIMP_TAC[ricci_flow_from];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `hs_time (hs:(A)rfs_history) k`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN USE_THEN "times" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!v. v < hs_time (hs:(A)rfs_history) k
                    ==> rfs_vtop (rfs_view hs) v = rfs_vtop (rfs_preview hs k) v /\
                        rfs_vatlas (rfs_view hs) v = rfs_vatlas (rfs_preview hs k) v /\
                        rfs_vmetric (rfs_view hs) v = rfs_vmetric (rfs_preview hs k) v`
  (LABEL_TAC "before") THENL
   [X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `v:real`] P3H_PREVIEW_BEFORE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vtop (rfs_view (hs:(A)rfs_history)) (hs_time hs k) = hs_top hs k /\
                rfs_vatlas (rfs_view hs) (hs_time hs k) = hs_atlas hs k /\
                rfs_vmetric (rfs_view hs) (hs_time hs k) = hs_metric hs k (hs_time hs k)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]; ALL_TAC] THEN
  (* the event *)
  ABBREV_TAC `ev = hs_event (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `Om = ev_omega (ev:(A)rfs_event)` THEN
  ABBREV_TAC `gl = ev_limit (ev:(A)rfs_event)` THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (k - 1)) Om /\
                rfs_limit_metric (hs_top hs (k - 1),hs_atlas hs (k - 1)) Om (hs_time hs k)
                                 (hs_metric hs (k - 1)) gl /\
                rfs_same_metric_on (hs_atlas hs (k - 1)) gl (hs_atlas hs k)
                  (hs_metric hs k (hs_time hs k))
                  (topspace (hs_top hs k) INTER topspace (hs_top hs (k - 1))) /\
                topspace (hs_top hs k) INTER topspace (hs_top hs (k - 1)) SUBSET Om`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_event_ok (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_metric (hs:(A)rfs_history) (k - 1)) (hs_time hs k)
                   (hs_top hs k,hs_atlas hs k) (hs_metric hs k) (ev:(A)rfs_event)` THEN
    ASM_REWRITE_TAC[rfs_event_ok] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the preview neck at T_k *)
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th))) THEN
  REWRITE_TAC[P3H_PREVIEW_AT_TOP; P3H_PREVIEW_AT_METRIC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[rfs_neck] th)) THEN
  ABBREV_TAC `Rp = rfs_vscalar (rfs_preview (hs:(A)rfs_history) k) (hs_time hs k) x` THEN
  SUBGOAL_THEN `mfd_scalar (restrict_atlas (hs_atlas (hs:(A)rfs_history) (k - 1)) Om)
                           (restrict_metric (hs_atlas hs (k - 1)) Om gl) x = Rp`
  ASSUME_TAC THENL
   [EXPAND_TAC "Rp" THEN REWRITE_TAC[P3H_VSCALAR_ALT; P3H_PREVIEW_AT_METRIC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) (k - 1)) (hs_atlas hs (k - 1))
                          (rfs_neck_dom eps) (e:real^3->A) /\
                IMAGE e (rfs_neck_dom eps) SUBSET Om` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC APX_PARAM_FROM_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `W = IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `open_in (hs_top (hs:(A)rfs_history) (k - 1)) W` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param (hs_top (hs:(A)rfs_history) (k - 1)) (hs_atlas hs (k - 1))
                   (rfs_neck_dom eps) (e:real^3->A)` THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[mfd_param; mfd_diffeo] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `W SUBSET topspace (hs_top (hs:(A)rfs_history) (k - 1))` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  (* the identity diffeo from the old stage to the new one on W *)
  SUBGOAL_THEN `mfd_diffeo (hs_top (hs:(A)rfs_history) (k - 1)) (hs_atlas hs (k - 1)) W
                           (hs_top hs k) (hs_atlas hs k) W (\z. z) (\z. z)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_event_ok] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_event_ok")) (concl th))) THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                   `ev_index (ev:(A)rfs_event)`; `ev_neck (ev:(A)rfs_event)`;
                   `ev_capp (ev:(A)rfs_event)`; `ev_capm (ev:(A)rfs_event)`; `W:A->bool`]
                  APX_CUT_SUBDIFFEO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `w:A` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P3H_KEPT_NOT_SPHERE THEN
      MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`;
                            `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                            `hs_metric (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                            `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                            `hs_metric (hs:(A)rfs_history) k`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `open_in (ev_ztop (ev:(A)rfs_event)) (topspace(ev_ztop ev) DIFF ev_disc ev)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `W SUBSET topspace(ev_ztop (ev:(A)rfs_event)) DIFF ev_disc ev` ASSUME_TAC THENL
     [UNDISCH_TAC `W SUBSET topspace (hs_top (hs:(A)rfs_history) k)` THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `W:A->bool`; `ev_ztop (ev:(A)rfs_event)`; `ev_zatlas (ev:(A)rfs_event)`;
                   `topspace(ev_ztop (ev:(A)rfs_event)) DIFF ev_disc ev`; `W:A->bool`;
                   `\z:A. z`; `\z:A. z`] APX_MFD_DIFFEO_RESTRICT_TARGET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the neck parametrizes the new stage *)
  SUBGOAL_THEN `mfd_param (hs_top (hs:(A)rfs_history) k) (hs_atlas hs k) (rfs_neck_dom eps)
                          (e:real^3->A)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->A) = (\z. z) o e` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                          `W:A->bool`; `W:A->bool`; `\z:A. z`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  (* the pullbacks at T_k agree *)
  SUBGOAL_THEN
   `!z. z IN rfs_neck_dom eps
        ==> rfs_pullback (hs_atlas (hs:(A)rfs_history) k) (e:real^3->A)
                         (hs_metric hs k (hs_time hs k)) z =
            rfs_pullback (restrict_atlas (hs_atlas hs (k - 1)) Om) e
                         (restrict_metric (hs_atlas hs (k - 1)) Om gl) z`
  (LABEL_TAC "pb") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^3->A) z IN W` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `gl:A->real^3^3`; `Om:A->bool`; `rfs_neck_dom eps`; `e:real^3->A`; `z:real^3`]
                  P3H_RFS_PULLBACK_RESTRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `rfs_pullback (hs_atlas (hs:(A)rfs_history) (k - 1)) (e:real^3->A) gl z =
      rfs_pullback (hs_atlas hs (k - 1)) e
        (mfd_pullback_metric (hs_atlas hs (k - 1)) (hs_atlas hs k) (\z:A. z)
                             (hs_metric hs k (hs_time hs k))) z`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P3H_PULLBACK_PT THEN EXISTS_TAC `hs_top (hs:(A)rfs_history) (k - 1)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P3H_SAME_METRIC_PT THEN
      MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_top (hs:(A)rfs_history) k`;
                            `topspace (hs_top (hs:(A)rfs_history) k) INTER
                             topspace (hs_top hs (k - 1))`] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `W:A->bool`; `W:A->bool`;
                   `\z:A. z`; `\z:A. z`; `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`;
                   `z:real^3`] P2B9_PULLBACK_COMPOSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(\z:A. z) o (e:real^3->A) = e` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; REFL_TAC];
    ALL_TAC] THEN
  (* the scalar curvature at the centre *)
  SUBGOAL_THEN `open(rfs_neck_dom eps)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k (hs_time hs k)) x = Rp`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `Rp:real`)) THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `y0:real^3 IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `hs_metric (hs:(A)rfs_history) k (hs_time hs k)`; `rfs_neck_dom eps`;
                   `e:real^3->A`; `y0:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`subtopology (hs_top (hs:(A)rfs_history) (k - 1)) Om`;
                   `restrict_atlas (hs_atlas (hs:(A)rfs_history) (k - 1)) Om`;
                   `restrict_metric (hs_atlas (hs:(A)rfs_history) (k - 1)) Om gl`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `y0:real^3`] APX_PULLBACK_SCALAR_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
      MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (k - 1)`; `hs_time (hs:(A)rfs_history) k`;
                            `hs_metric (hs:(A)rfs_history) (k - 1)`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "pb" (MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar (rfs_view (hs:(A)rfs_history)) (hs_time hs k) x = Rp` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P3H_VSCALAR_ALT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the neck at T_k *)
    REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rfs_close_on] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_on")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "restrict_atlas")) (concl th))) THEN
    ASM_REWRITE_TAC[rfs_close_on] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dn:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= d ==> b <= d`) THEN
    MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "pb" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^3) IN rfs_neck_dom eps`)]);
    (* persistence *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = hs_time (hs:(A)rfs_history) k` THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[mfd_diffeo] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th) &&
        can (find_term (fun t -> t = `hs_top (hs:(A)rfs_history) k`)) (concl th))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "before" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_preview")) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    (* the family *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_fam")) (concl th))) THEN
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `df:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
      REWRITE_TAC[P3H_PREVIEW_AT_METRIC] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= d ==> b <= d`) THEN
      MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "pb" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^3) IN rfs_neck_dom eps`)]);
      ALL_TAC] THEN
    SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k + s / Rp < hs_time hs k` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x < &0 ==> t + x < t`) THEN
      SUBGOAL_THEN `&0 < Rp` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "before" (MP_TAC o C MP (ASSUME `hs_time (hs:(A)rfs_history) k + s / Rp < hs_time hs k`) o
                       SPEC `hs_time (hs:(A)rfs_history) k + s / Rp`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* ========================================================================= *)
(* Numerics for the constants of case (2b).                                  *)
(* ========================================================================= *)

(* The numerical conditions of the core transfer are monotone in delta, so a *)
(* threshold from P2B9_DELTA_EXISTS works for every smaller precision.      *)

let P3H_DELTA_MONO = prove
 (`!Sd eps1 M K0 L a n delta d.
     &0 <= Sd /\ &0 <= M /\ &0 < L /\ &0 < d /\ d <= delta /\
     delta <= &1 / &10 /\ delta <= eps1 /\
     &72 * (&1 + abs K0) * delta <= &1 / &2 /\
     &2 * L * (&72 * (&1 + abs K0) * delta) <= &1 / &2 /\
     L < a * (&1 - &72 * (&1 + abs K0) * delta) /\
     (&1 + &2 * L * (&72 * (&1 + abs K0) * delta)) pow n *
     ((&1 + &72 * (&1 + abs K0) * delta) * (Sd + sqrt M * delta) +
      (&2 + &4 * L) * (&72 * (&1 + abs K0) * delta)) < eps1
     ==> d <= &1 / &10 /\ d <= eps1 /\ &72 * (&1 + abs K0) * d <= &1 / &2 /\
         &2 * L * (&72 * (&1 + abs K0) * d) <= &1 / &2 /\
         L < a * (&1 - &72 * (&1 + abs K0) * d) /\
         (&1 + &2 * L * (&72 * (&1 + abs K0) * d)) pow n *
         ((&1 + &72 * (&1 + abs K0) * d) * (Sd + sqrt M * d) +
          (&2 + &4 * L) * (&72 * (&1 + abs K0) * d)) < eps1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&72 * (&1 + abs K0) * d <= &72 * (&1 + abs K0) * delta /\
                &0 <= &72 * (&1 + abs K0) * d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `md = &72 * (&1 + abs K0) * d` THEN
  ABBREV_TAC `mD = &72 * (&1 + abs K0) * delta` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < a` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a * (&1 - mD) <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * x ==> a * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * L * md <= &2 * L * mD /\ &0 <= &2 * L * md` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a * (&1 - mD)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + &2 * L * mD) pow n *
                ((&1 + mD) * (Sd + sqrt M * delta) + (&2 + &4 * L) * mD)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
        REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> s + x <= s + y`) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]]);;

(* The same conditions are monotone in the length L as well (for the exact- *)
(* length transfer the length is only known to be at most 2).               *)

let P3H_DELTA_MONO_L = prove
 (`!Sd eps1 M K0 L L' n delta d.
     &0 <= Sd /\ &0 <= M /\ &0 < L' /\ L' <= L /\ &0 < d /\ d <= delta /\
     delta <= &1 / &10 /\ delta <= eps1 /\
     &72 * (&1 + abs K0) * delta <= &1 / &2 /\
     &2 * L * (&72 * (&1 + abs K0) * delta) <= &1 / &2 /\
     (&1 + &2 * L * (&72 * (&1 + abs K0) * delta)) pow n *
     ((&1 + &72 * (&1 + abs K0) * delta) * (Sd + sqrt M * delta) +
      (&2 + &4 * L) * (&72 * (&1 + abs K0) * delta)) < eps1
     ==> d <= &1 / &10 /\ d <= eps1 /\ &72 * (&1 + abs K0) * d <= &1 / &2 /\
         &2 * L' * (&72 * (&1 + abs K0) * d) <= &1 / &2 /\
         (&1 + &2 * L' * (&72 * (&1 + abs K0) * d)) pow n *
         ((&1 + &72 * (&1 + abs K0) * d) * (Sd + sqrt M * d) +
          (&2 + &4 * L') * (&72 * (&1 + abs K0) * d)) < eps1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&72 * (&1 + abs K0) * d <= &72 * (&1 + abs K0) * delta /\
                &0 <= &72 * (&1 + abs K0) * d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `K0:real` REAL_ABS_POS) THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `md = &72 * (&1 + abs K0) * d` THEN
  ABBREV_TAC `mD = &72 * (&1 + abs K0) * delta` THEN
  SUBGOAL_THEN `&2 * L' * md <= &2 * L * mD /\ &0 <= &2 * L' * md` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 + &4 * L') * md <= (&2 + &4 * L) * mD` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(&1 + &2 * L * mD) pow n *
                ((&1 + mD) * (Sd + sqrt M * delta) + (&2 + &4 * L) * mD)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> s + x <= s + y`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE]]]);;

(* ========================================================================= *)
(* (b3) the containment of the neck images reduced to the                  *)
(* axial coordinate.  sval of the neck coordinate of a far point of the   *)
(* standard solution is A0 + 4 - dist; the dilated neck domain is a band  *)
(* in sval.                                                                 *)
(* ========================================================================= *)

let P3H_NC_SVAL = prove
 (`!g0 A0 (z:real^3).
     ~(z = vec 0)
     ==> ~(p3_std_nc g0 A0 z = vec 0) /\
         apx_sval (p3_std_nc g0 A0 z) = A0 + &4 - p3_std_dist g0 z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(p3_std_nc g0 A0 (z:real^3)) = exp((A0 + &4 - p3_std_dist g0 z) / sqrt(&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_nc; NORM_MUL; REAL_ABS_EXP] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0; REAL_MUL_RID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[REAL_EXP_NZ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[apx_sval; LOG_EXP] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let P3H_DILATE_DOM_SVAL = prove
 (`!(u0:real^3) eps w.
     ~(u0 = vec 0) /\ &0 < eps /\ ~(w = vec 0) /\
     abs(apx_sval w - apx_sval u0) < inv eps
     ==> w IN IMAGE (\v. norm u0 % v) (rfs_neck_dom eps)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `inv(norm(u0:real^3)) % (w:real^3)` THEN
  SUBGOAL_THEN `&0 < norm(u0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(norm(u0:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(inv(norm(u0:real^3)) % (w:real^3)) = apx_sval w - apx_sval u0`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_SCALE; LOG_INV] THEN REWRITE_TAC[apx_sval] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(inv(norm(u0:real^3)) % (w:real^3) = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ABBREV_TAC `v = inv(norm(u0:real^3)) % (w:real^3)` THEN
  SUBGOAL_THEN `abs(apx_sval v) < inv eps` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; apx_sval] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(v:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm(v:real^3))) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    UNDISCH_TAC `abs(sqrt(&2) * log(norm(v:real^3))) < inv eps` THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:real^3) = exp(log(norm v))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC);;

(* The containment needed by Prop 15.2: if the far neck e of the standard   *)
(* solution moves the axial coordinate dist by less than 1/e1 from dist(q),  *)
(* its image under Phi lies in the dilated sub-neck N o D of the surgery     *)
(* neck N centred at Phi q.                                                  *)

let P3H_IMAGE_CONTAIN_AXIAL = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k j (Phi:real^3->A) xi q (e:real^3->real^3) S e1.
     p3_cap_param (md,g0,A0) (dl,h) hs k j Phi xi /\ &0 < e1 /\
     ~(q = vec 0) /\
     --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 q /\
     A0 + &4 - p3_std_dist g0 q < &0 /\
     (!v. v IN S
          ==> ~(e v = vec 0) /\
              --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 (e v) /\
              A0 + &4 - p3_std_dist g0 (e v) < &0 /\
              abs(p3_std_dist g0 (e v) - p3_std_dist g0 q) < inv e1)
     ==> Phi q = ev_neck (hs_event hs k) j (p3_std_nc g0 A0 q) /\
         IMAGE (Phi o e) S SUBSET
         IMAGE (ev_neck (hs_event hs k) j o (\v. norm(p3_std_nc g0 A0 q) % v))
               (rfs_neck_dom e1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p3_cap_param]) THEN
  DISCH_TAC THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `S:real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (CONJ
    (ASSUME `--(inv(dl(hs_time (hs:(A)rfs_history) k))) < A0 + &4 - p3_std_dist g0 ((e:real^3->real^3) v)`)
    (ASSUME `A0 + &4 - p3_std_dist g0 ((e:real^3->real^3) v) < &0`))]) o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_neck")) (concl th))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] P3H_NC_SVAL) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(e:real^3->real^3) v`] P3H_NC_SVAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p3_std_nc g0 A0 q`; `e1:real`; `p3_std_nc g0 A0 ((e:real^3->real^3) v)`]
               P3H_DILATE_DOM_SVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; o_THM] THEN MESON_TAC[]);;

(* A strong eps-neck at (x,t) is a strong canonical neighbourhood. *)

let P3H_CANON_FROM_NECK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t (e:real^3->A).
     rfs_strong_neck V eps x t e ==> p3_canon_at V C eps x t`,
  REWRITE_TAC[FORALL_PAIR_THM; p3_canon_at; rfs_strong_canonical] THEN MESON_TAC[]);;

let P3H_CANONV_FROM_NECK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t e.
     rfs_strong_neck V eps x t e ==> p3_canonv_at V C eps x t`,
  REWRITE_TAC[p3_canonv_at; p3_strong_canonv] THEN MESON_TAC[]);;

(* Points of the kept half of a surgery neck (sval < 0) are points of the  *)
(* new stage: they are Phi-images of far points (p3_cap_param).             *)

let P3H_NECK_KEPT_IN_STAGE = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k j (Phi:real^3->A) xi w.
     p3_cap_param (md,g0,A0) (dl,h) hs k j Phi xi /\
     w IN rfs_neck_dom (dl(hs_time hs k)) /\ apx_sval w < &0
     ==> ev_neck (hs_event hs k) j w = Phi (xi w) /\
         ev_neck (hs_event hs k) j w IN topspace (hs_top hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_cap_param]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `xi:real^3->real^3`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_std_nc")) (concl th) &&
    not (can (find_term (fun t -> is_const t && fst(dest_const t) = "jacobian")) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(&2) * log(norm(w:real^3)) <= &0` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_sval (w:real^3) < &0` THEN REWRITE_TAC[apx_sval] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((xi:real^3->real^3) w = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `p3_std_nc g0 A0 ((xi:real^3->real^3) w) = w` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p3_std_nc; VECTOR_MUL_RZERO] THEN
    MP_TAC(SPECL [`dl(hs_time (hs:(A)rfs_history) k):real`; `w:real^3`] P3H_NECK_DOM_NONZERO) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `(xi:real^3->real^3) w`] P3H_NC_SVAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `A0 + &4 - p3_std_dist g0 ((xi:real^3->real^3) w) < &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_sval")) (lhs(concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^3->A) ((xi:real^3->real^3) w) =
                ev_neck (hs_event hs k) j (p3_std_nc g0 A0 (xi w))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_neck")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_std_nc")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ev_neck (hs_event (hs:(A)rfs_history) k) j (w:real^3) = Phi ((xi:real^3->real^3) w)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> t = `w:real^3`)) (lhs(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_neck")) (lhs(concl th)))) THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                 `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) < A0 + &4 - p3_std_dist g0 x}`;
                 `Phi:real^3->A`;
                 `{x:real^3 | --(inv(dl(hs_time (hs:(A)rfs_history) k))) < A0 + &4 - p3_std_dist g0 x}`]
                MFD_PARAM_IMAGE_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

