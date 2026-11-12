(* ========================================================================= *)
(* Unit pc_p3_c177e: MT Lemma 17.7, case (2b) (p. 405-406)                 *)
(* and the route theorem.  P3H_177_FARNECK proves P3H_177_FARNECK_STATEMENT *)
(* (pc_p3_c177a) from the regularity of history and flow views and         *)
(* Thm 12.5: the far neck of the standard solution transfers to an evolving *)
(* beta eps-neck at (x,ts) reaching back to the surgery time (a,            *)
(* P3H_FAR_TRANSFER), the length-2 surgery neck re-centred at x is a strong *)
(* beta eps/2-neck at the surgery time (b, P3H_FAR_RECENTRE), the axial     *)
(* estimate (pc_p3_c177d) gives the containment of the images, and Prop    *)
(* 15.2 (P3E_PROP_15_2, pc_p3e_152h) glues them.  P3_LEMMA_17_7_ROUTE      *)
(* follows with P3H_LEMMA_17_7_FROM_FAR (pc_p3_c177b).                      *)
(* ========================================================================= *)

needs "src/pc_p3_c177d.ml";;
needs "src/pc_p3_c177b.ml";;
needs "src/pc_p3e_152h.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* (a) applied: the far neck of the standard solution at (q,tp), reaching   *)
(* back to time 0, gives through the view closeness of Prop 16.5 (rescaled  *)
(* to time tp) an evolving e2-neck at (Phi q, ts) whose length reaches back *)
(* exactly to the surgery time T1 = ts - tp h^2.                            *)
(* ========================================================================= *)

let P3H_NUM_SD_MONO = prove
 (`!X n A Sd Sd' B C e1.
     &0 < X /\ &0 <= A /\ Sd' <= Sd /\ X pow n * (A * (Sd + B) + C) < e1
     ==> X pow n * (A * (Sd' + B) + C) < e1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `X pow n * (A * (Sd + B) + C)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `!a x y c:real. a * x <= a * y ==> a * x + c <= a * y + c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let P3H_FAR_TRANSFER = prove
 (`!K0 M e2 eps_in (G:real->real^3->real^3^3) (hs:(A)rfs_history) T1 h (Phi:real^3->A) W J dq
    delta tp q (e:real^3->real^3) ts.
     (!V' eps' x' t' a' (e':real^3->real^3).
        p2c_regular_view V' /\ rfs_evolving_neck V' eps' x' t' a' e' /\ eps' < &1 / &4
        ==> !y0. y0 IN sphere(vec 0,&1) /\ e' y0 = x'
                 ==> lrm_deriv_norm2 0
                       (\z. rfs_vscalar V' t' x' %%
                            rfs_pullback (rfs_vatlas V' t') e' (rfs_vmetric V' t') z) y0
                     <= K0 pow 2) /\
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 (rfs_kreg e2) G0 G1 y <= &1 / &4
         ==> lck_dist2 (rfs_kreg e2) G0 (\z. G0 z + G2 z - G1 z) y <=
             M * lck_dist2 (rfs_kreg e2) G1 G2 y) /\
     &0 <= M /\
     P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
     rfs_history_ok hs /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) T1 (inv(h pow 2)) Phi J dq /\
     &0 < h /\ T1 + tp * h pow 2 = ts /\ &0 < tp /\ tp < &1 /\
     (!s. &0 < s /\ s <= tp ==> s IN J) /\
     rfs_evolving_neck
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
     tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q < &5 / &4 /\
     &9 / &10 <= mfd_scalar (open_set_atlas (:real^3)) (G tp) q /\
     IMAGE e (rfs_neck_dom eps_in) SUBSET W /\
     &0 < eps_in /\ eps_in <= e2 /\ eps_in < &1 / &4 /\
     &0 < delta /\ delta <= &1 / &10 /\ delta <= e2 /\
     &72 * (&1 + abs K0) * delta <= &1 / &2 /\
     &2 * &2 * (&72 * (&1 + abs K0) * delta) <= &1 / &2 /\
     (&1 + &2 * &2 * (&72 * (&1 + abs K0) * delta)) pow (rfs_kreg e2 + 2) *
       ((&1 + &72 * (&1 + abs K0) * delta) * (eps_in + sqrt M * delta) +
        (&2 + &4 * &2) * (&72 * (&1 + abs K0) * delta)) < e2 /\
     &0 < dq /\ dq <= delta /\
     (&1 + inv(mfd_scalar (open_set_atlas (:real^3)) (G tp) q)) pow (rfs_kreg delta) *
       dq pow 2 <= delta pow 2
     ==> &0 < rfs_vscalar (rfs_view hs) ts (Phi q) /\
         rfs_evolving_neck (rfs_view hs) e2 (Phi q) ts
           (tp * h pow 2 * rfs_vscalar (rfs_view hs) ts (Phi q)) (Phi o e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "K0") (CONJUNCTS_THEN2 (LABEL_TAC "base")
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
  SUBGOAL_THEN `&0 < R /\ &0 < tp * R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_vscalar (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                   (G:real->real^3->real^3^3)) tp q = R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[rfs_flow_view; rfs_vscalar]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2c_regular_view (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                        {s | &0 <= s /\ s < &1} (G:real->real^3->real^3^3))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT] o check (fun th ->
      can (find_term (fun t -> is_const t &&
                     fst(dest_const t) = "P2C_FLOW_VIEW_REGULAR_STATEMENT")) (concl th))) THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    ALL_TAC] THEN
  (* the neck at (q,tp): its image is open, its centre y0 *)
  SUBGOAL_THEN `(tp * R) / R = tp` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in))` ASSUME_TAC THENL
   [MP_TAC(SPEC `tp:real` (CONJUNCT1(CONJUNCT2(CONJUNCT2(REWRITE_RULE[P2B9_EVOLVING_NECK_ALT]
      (ASSUME `rfs_evolving_neck
         (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                        (G:real->real^3->real^3^3)) eps_in q tp (tp * R) e`)))))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_REFL] THEN
    REWRITE_TAC[rfs_flow_view; rfs_vtop; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM OPEN_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN sphere(vec 0,&1) /\ (e:real^3->real^3) y0 = q`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1(REWRITE_RULE[P2B9_EVOLVING_NECK_ALT]
      (ASSUME `rfs_evolving_neck
         (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                        (G:real->real^3->real^3^3)) eps_in q tp (tp * R) e`))) THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the K0 bound at the centre of the neck at (q,tp) *)
  USE_THEN "K0" (MP_TAC o SPECL
    [`rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                    (G:real->real^3->real^3^3)`;
     `eps_in:real`; `q:real^3`; `tp:real`; `tp * R`; `e:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the family bound d0 < eps_in^2 *)
  MP_TAC(MATCH_MP P2B9_NECK_SUP (ASSUME `rfs_evolving_neck
         (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                        (G:real->real^3->real^3^3)) eps_in q tp (tp * R) e`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  (* the closeness at the scale of the neck *)
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `W:real^3->bool`;
                 `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in)`; `hs:(A)rfs_history`;
                 `T1:real`; `h:real`; `Phi:real^3->A`; `J:real->bool`; `dq:real`; `tp:real`;
                 `R:real`; `tp * R`; `delta:real`; `ts:real`] P3H_VIEW_CLOSE_RESCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < tp + s / R /\ tp + s / R <= tp` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `!x tp. --tp < x ==> &0 < tp + x`) THEN
          ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `!x tp. x <= &0 ==> tp + x <= tp`) THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!s. --(tp * R) < s /\ s <= &0
        ==> smooth_manifold_atlas
              (rfs_vtop (rfs_view (hs:(A)rfs_history)) (ts + s / (R * inv(h pow 2))))
              (rfs_vatlas (rfs_view hs) (ts + s / (R * inv(h pow 2)))) /\
            riemannian_metric (rfs_vatlas (rfs_view hs) (ts + s / (R * inv(h pow 2))))
              (rfs_vmetric (rfs_view hs) (ts + s / (R * inv(h pow 2))))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P3_HIST_VIEW_SLICES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the scalar ratio at (Phi q, ts) *)
  MP_TAC(ISPECL [`rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                    (G:real->real^3->real^3^3)`;
                 `eps_in:real`; `q:real^3`; `tp:real`; `tp * R`; `e:real^3->real^3`;
                 `rfs_view (hs:(A)rfs_history)`; `ts:real`; `R * inv(h pow 2)`;
                 `Phi:real^3->A`; `delta:real`; `K0:real`; `y0:real^3`] P2B9_SCALAR_RATIO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `X = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts ((Phi:real^3->A) q)` THEN
  SUBGOAL_THEN `&0 < R * inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= X / (R * inv(h pow 2)) /\
                X / (R * inv(h pow 2)) <= &1 + &72 * (&1 + abs K0) * delta`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < X / (R * inv(h pow 2))` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < tp * h pow 2 * X /\ tp * h pow 2 * X <= &2 /\
                tp * h pow 2 * X <= (tp * R) * (X / (R * inv(h pow 2)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `tp * h pow 2 * X = (tp * R) * (X / (R * inv(h pow 2)))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(tp * R) * (&1 + &72 * (&1 + abs K0) * delta)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&5 / &4 * (&1 + &72 * (&1 + abs K0) * delta)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the numerics at the actual length, with sqrt d0 for eps_in *)
  MP_TAC(SPECL [`eps_in:real`; `e2:real`; `M:real`; `K0:real`; `&2`;
                `tp * h pow 2 * X`; `rfs_kreg e2 + 2`; `delta:real`; `delta:real`]
               P3H_DELTA_MONO_L) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sqrt d0 <= eps_in` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps_in pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg e2`; `M:real`; `K0:real`; `eps_in:real`; `e2:real`; `tp * R`;
                 `tp * h pow 2 * X`; `delta:real`; `d0:real`;
                 `rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                    (G:real->real^3->real^3^3)`;
                 `q:real^3`; `tp:real`; `e:real^3->real^3`; `rfs_view (hs:(A)rfs_history)`;
                 `ts:real`; `R * inv(h pow 2)`; `Phi:real^3->A`] P3H_ENECK_CORE_X) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `eps_in pow 2 <= &1 / &4` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `eps_in * eps_in <= eps_in * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P3H_NUM_SD_MONO THEN EXISTS_TAC `eps_in:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= &72 * (&1 + abs K0) * delta` ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!x. &0 <= x ==> &0 < &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* (b) applied: the length-2 surgery neck of p3_neck2_ok, re-centred at the *)
(* point Phi q of its kept half, is a strong e1-neck of the history at the  *)
(* surgery time (P3H_RECENTRE_CORE in the preview, P3H_PREVIEW_TO_VIEW).    *)
(* ========================================================================= *)

let P3H_DILATE_IN_DOM = prove
 (`!(u0:real^3) e1 d v.
     ~(u0 = vec 0) /\ &0 < e1 /\ &0 < d /\ abs(apx_sval u0) + inv e1 <= inv d /\
     v IN rfs_neck_dom e1
     ==> norm u0 % v IN rfs_neck_dom d /\ ~(norm u0 % v = vec 0) /\
         apx_sval(norm u0 % v) < apx_sval u0 + inv e1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e1:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(u0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(u0:real^3) % (v:real^3) = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(norm(u0:real^3) % (v:real^3)) = apx_sval u0 + apx_sval v`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_SCALE] THEN REWRITE_TAC[apx_sval]; ALL_TAC] THEN
  ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC);;

let P3H_FAR_RECENTRE = prove
 (`!K0 M e1 md g0 A0 dl h (hs:(A)rfs_history) k j (Phi:real^3->A) xi q.
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
         lck_dist2 (rfs_kreg e1) G0 G1 y <= &1 / &4
         ==> lck_dist2 (rfs_kreg e1) G0 (\z. G0 z + G2 z - G1 z) y <=
             M * lck_dist2 (rfs_kreg e1) G1 G2 y) /\
     &0 <= M /\
     rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\
     1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
     p3_neck2_ok (dl,h) hs k /\
     p3_cap_param (md,g0,A0) (dl,h) hs k j Phi xi /\
     &0 < e1 /\ e1 < &1 / &4 /\ ~(q = vec 0) /\
     A0 + &4 + inv e1 < p3_std_dist g0 q /\
     (p3_std_dist g0 q - (A0 + &4)) + inv e1 <= inv(dl(hs_time hs k)) /\
     &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= &1 / &10 /\ dl(hs_time hs k) <= e1 /\
     &72 * (&1 + abs K0) * dl(hs_time hs k) <= &1 / &2 /\
     &2 * &1 * (&72 * (&1 + abs K0) * dl(hs_time hs k)) <= &1 / &2 /\
     (&1 + &2 * &1 * (&72 * (&1 + abs K0) * dl(hs_time hs k))) pow (rfs_kreg e1 + 2) *
       ((&1 + &72 * (&1 + abs K0) * dl(hs_time hs k)) *
        (sqrt(&0) + sqrt M * dl(hs_time hs k)) +
        (&2 + &4 * &1) * (&72 * (&1 + abs K0) * dl(hs_time hs k))) < e1
     ==> Phi q = ev_neck (hs_event hs k) j (p3_std_nc g0 A0 q) /\
         rfs_strong_neck (rfs_view hs) e1 (Phi q) (hs_time hs k)
           (ev_neck (hs_event hs k) j o (\v. norm(p3_std_nc g0 A0 q) % v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K0")
    (CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] P3H_NC_SVAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* Phi q = N u0 (the cap parametrization on the far annulus) *)
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `h:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
                 `xi:real^3->real^3`; `q:real^3`; `\v:real^3. v`; `{}:real^3->bool`;
                 `e1:real`] P3H_IMAGE_CONTAIN_AXIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    SUBGOAL_THEN `&0 < inv e1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = dl(hs_time (hs:(A)rfs_history) k):real` THEN
  ABBREV_TAC `u0 = p3_std_nc g0 A0 (q:real^3)` THEN
  ABBREV_TAC `N = ev_neck (hs_event (hs:(A)rfs_history) k) j` THEN
  SUBGOAL_THEN `&0 < inv e1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval (u0:real^3)) + inv e1 <= inv d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the length-2 surgery neck in the preview *)
  MP_TAC(ASSUME `p3_neck2_ok (dl,h) (hs:(A)rfs_history) k`) THEN
  REWRITE_TAC[p3_neck2_ok] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s. --(&2) < s /\ s <= &0
        ==> smooth_manifold_atlas
              (rfs_vtop (rfs_preview (hs:(A)rfs_history) k)
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
              (rfs_neck_dom d) (N:real^3->A)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `d:real`; `y:A`; `&2`; `N:real^3->A`;
                   `s:real`] P3H_PREVIEW_NECK_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* re-centring in the preview *)
  MP_TAC(ISPECL [`K0:real`; `M:real`; `e1:real`; `e1:real`; `rfs_preview (hs:(A)rfs_history) k`;
                 `d:real`; `y:A`; `hs_time (hs:(A)rfs_history) k`; `N:real^3->A`;
                 `u0:real^3`] P3H_RECENTRE_CORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u0:real^3`; `e1:real`; `d:real`; `v:real^3`] P3H_DILATE_IN_DOM) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  (* the re-centred neck lies in the kept stage: preview -> view *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `e1:real`; `(N:real^3->A) u0`; `&1`;
                 `(N:real^3->A) o (\v:real^3. norm(u0:real^3) % v)`] P3H_PREVIEW_TO_VIEW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u0:real^3`; `e1:real`; `d:real`; `v:real^3`] P3H_DILATE_IN_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                   `h:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
                   `xi:real^3->real^3`; `norm(u0:real^3) % (v:real^3)`]
                  P3H_NECK_KEPT_IN_STAGE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[rfs_strong_neck]);;

(* ========================================================================= *)
(* Case (2b) of MT Lemma 17.7 (p. 405-406), P3H_177_FARNECK_STATEMENT: the  *)
(* far neck of the standard solution with normalized length below          *)
(* 1 + eps_in.  (a) P3H_FAR_TRANSFER gives an evolving beta eps-neck at      *)
(* (x,ts) reaching back exactly to the surgery time T_k; (b)               *)
(* P3H_FAR_RECENTRE a strong beta eps/2-neck at (x,T_k) from the length-2  *)
(* surgery neck; the axial estimate (P3H_177_AXIAL) gives the containment  *)
(* of the images (P3H_IMAGE_CONTAIN_AXIAL); Prop 15.2 (P3E_PROP_15_2)      *)
(* glues them into a strong eps-neck at (x,ts).                             *)
(* ========================================================================= *)

let P3H_DQ_ARITH = prove
 (`!R dq delta n.
     &9 / &10 <= R /\ &0 < dq /\ &0 < delta /\ delta <= &1 /\
     dq <= delta / (&19 / &9) pow n
     ==> dq <= delta /\ (&1 + inv R) pow n * dq pow 2 <= delta pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= (&19 / &9) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dq * (&19 / &9) pow n <= delta` ASSUME_TAC THENL
   [UNDISCH_TAC `dq <= delta / (&19 / &9) pow n` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `dq <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dq * (&19 / &9) pow n` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv R <= &10 / &9` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&9 / &10)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + inv R) pow n <= (&19 / &9) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((&19 / &9) pow n * dq) * dq` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]]);;

let P3H_STRUCT_FACTS = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) k.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ p3_hfun C hf /\
     1 <= k /\ k <= hs_count hs /\ &0 <= hs_time hs k
     ==> rfs_history_ok hs /\ &0 < dl(hs_time hs k) /\
         &0 < p3_hscale hf rp dl (hs_time hs k) /\
         p3_neck2_ok (dl,p3_hscale hf rp dl) hs k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[p3_hscale] THEN
  UNDISCH_TAC `p3_hfun C hf` THEN REWRITE_TAC[p3_hfun] THEN
  DISCH_THEN(MP_TAC o SPECL [`(dl:real->real)(hs_time (hs:(A)rfs_history) k) *
                             (rp:real->real)(hs_time hs k)`;
                            `(dl:real->real)(hs_time (hs:(A)rfs_history) k)`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    SIMP_TAC[]]);;

let P3H_177_FARNECK = prove
 (`!u:A->bool.
     P2C_HISTORY_REGULAR_STATEMENT u /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2_THM_12_5_STATEMENT
     ==> P3H_177_FARNECK_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P3H_177_FARNECK_STATEMENT] THEN
  MP_TAC(MATCH_MP P3H_177_AXIAL (CONJ (ASSUME `P2_THM_12_5_STATEMENT`)
                                      (ASSUME `P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)`))) THEN
  REWRITE_TAC[P3H_177_AXIAL_STATEMENT] THEN DISCH_THEN(LABEL_TAC "AX") THEN
  MP_TAC(INST_TYPE [`:real^3`,`:A`] (MATCH_MP P2B9_NECK_CENTRE_UNIFORM P2B_REQ_LRG_RM_NEAR)) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0")) THEN
  EXISTS_TAC `&1 / &50` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `g0:real^3->real^3^3`; `A0:real`] THEN STRIP_TAC THEN
  (* beta from Prop 15.2, e2 = beta eps, e1 = beta eps / 2 *)
  MP_TAC(SPEC `eps:real` (REWRITE_RULE[P3_PROP_15_2_STATEMENT]
    (ISPEC `u:A->bool` P3E_PROP_15_2))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "152")))) THEN
  SUBGOAL_THEN `&0 < beta * eps /\ beta * eps <= &1 / &100 /\ &0 < beta * eps / &2 /\
                beta * eps / &2 < &1 / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < beta * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `beta * eps <= &1 / &2 * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "AX" (MP_TAC o SPEC `beta * eps` o C MP (ASSUME `p3_std_initial g0 A0`) o
                    SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `KA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AX2"))) THEN
  MP_TAC(SPEC `rfs_kreg (beta * eps)` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT]
    P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M2"))) THEN
  MP_TAC(SPEC `rfs_kreg (beta * eps / &2)` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT]
    P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M1"))) THEN
  MP_TAC(SPECL [`beta * eps / &2`; `beta * eps`; `M2:real`; `K0:real`; `&2`; `&3`;
                `rfs_kreg (beta * eps) + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delT:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`&0`; `beta * eps / &2`; `M1:real`; `K0:real`; `&1`; `&2`;
                `rfs_kreg (beta * eps / &2) + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delR:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(KA + &2) / beta + &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x. &0 <= x ==> &1 <= x + &1`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps_in:real`; `C:real`; `hf:real->real->real`; `md:real->real`;
                       `i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`;
                       `m:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(beta * eps / &2) /\ inv(beta * eps / &2) = &2 / (beta * eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
                    SUBGOAL_THEN `~(beta = &0) /\ ~(eps = &0)` MP_TAC THENL
                     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `KA * eps_in <= beta * eps /\ eps_in <= beta * eps / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(KA + &2 + beta) * eps_in <= beta * eps` ASSUME_TAC THENL
     [SUBGOAL_THEN `(KA + &2 + beta) * eps_in = beta * (((KA + &2) / beta + &1) * eps_in)`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < beta` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= KA * eps_in /\ &0 <= beta * eps_in` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (delT / (&19 / &9) pow (rfs_kreg delT))
                  (min delR (inv(abs m + inv(beta * eps / &2) + &1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`dlt:real`; `rs':num->real`; `ks':num->real`; `dd:num->real`;
                       `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
                       `xi:real^3->real^3`; `ts:real`; `x:A`; `G:real->real^3->real^3^3`;
                       `theta1:real`; `dq2:real`; `tp:real`; `q:real^3`; `e:real^3->real^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(Phi:real^3->A) q = x`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_step_hyp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `p3_stepf rs'`; `p3_stepf dd`;
                 `hs:(A)rfs_history`; `k:num`] P3H_STRUCT_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3) /\ G (&0) = g0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[P2C_HISTORY_REGULAR_STATEMENT] o check (fun th ->
      concl th = `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3) /\ &0 < A0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  (* the axial estimate *)
  REMOVE_THEN "AX2" (MP_TAC o SPECL [`eps_in:real`; `G:real->real^3->real^3^3`; `q:real^3`;
                                     `tp:real`; `e:real^3->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* facts about q *)
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                   (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[ricci_flow_from; ricci_flow_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0:real^3) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tp * mfd_scalar (open_set_atlas (:real^3))
                         ((G:real->real^3->real^3^3) tp) q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_flow_view (euclidean,open_set_atlas (:real^3))
                      {s | &0 <= s /\ s < &1} (G:real->real^3->real^3^3)`;
                   `eps_in:real`; `q:real^3`; `tp:real`;
                   `tp * mfd_scalar (open_set_atlas (:real^3))
                           ((G:real->real^3->real^3^3) tp) q`;
                   `e:real^3->real^3`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT] o
          check (fun th -> concl th = `P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)`)) THEN
        ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
        ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 q < m /\ A0 + &5 <= p3_std_dist g0 q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in) SUBSET
                   {z | p3_std_dist g0 z < m}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `A0 + &5`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `A0 + &5 <= p3_std_dist g0 q` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* (a): the transfer to the history at ts *)
  SUBGOAL_THEN
   `!s. &0 < s /\ s <= tp
        ==> s IN {s | &0 <= s /\ s < theta1 /\
                      hs_time (hs:(A)rfs_history) k +
                      s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2 <= ts /\
                      hs_time hs k +
                      s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2 <
                      rfs_horizon hs}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k) pow 2 <=
      tp * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tp * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q
                < &5 / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &72 * (&1 + abs K0) * delT` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + &2 * &2 * (&72 * (&1 + abs K0) * delT)) pow (rfs_kreg (beta * eps) + 2) *
    ((&1 + &72 * (&1 + abs K0) * delT) * (eps_in + sqrt M2 * delT) +
     (&2 + &4 * &2) * (&72 * (&1 + abs K0) * delT)) < beta * eps` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_NUM_SD_MONO THEN EXISTS_TAC `beta * eps / &2` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q`;
                `dq2:real`; `delT:real`; `rfs_kreg delT`] P3H_DQ_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `M2:real`; `beta * eps`; `eps_in:real`;
                 `G:real->real^3->real^3^3`; `hs:(A)rfs_history`;
                 `hs_time (hs:(A)rfs_history) k`;
                 `p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k)`;
                 `Phi:real^3->A`; `{z | p3_std_dist g0 z < m}`;
                 `{s | &0 <= s /\ s < theta1 /\
                       hs_time (hs:(A)rfs_history) k +
                       s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2
                       <= ts /\
                       hs_time hs k +
                       s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2
                       < rfs_horizon hs}`;
                 `dq2:real`; `delT:real`; `tp:real`; `q:real^3`; `e:real^3->real^3`;
                 `ts:real`] P3H_FAR_TRANSFER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `X = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts ((Phi:real^3->A) q)` THEN
  (* (b): the re-centred surgery neck at the surgery time *)
  MP_TAC(SPECL [`&0`; `beta * eps / &2`; `M1:real`; `K0:real`; `&1`; `&2`;
                `rfs_kreg (beta * eps / &2) + 2`; `delR:real`;
                `p3_stepf dd (hs_time (hs:(A)rfs_history) k)`] P3H_DELTA_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN ASM_REAL_ARITH_TAC;
                  STRIP_TAC] THEN
  SUBGOAL_THEN `abs m + inv(beta * eps / &2) + &1 <=
                inv(p3_stepf dd (hs_time (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `M1:real`; `beta * eps / &2`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `p3_stepf dd`;
                 `p3_hscale hf (p3_stepf rs') (p3_stepf dd)`; `hs:(A)rfs_history`; `k:num`;
                 `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `q:real^3`]
                P3H_FAR_RECENTRE) THEN
  REWRITE_TAC[SQRT_0] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                  DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  (* the containment of the images (axial estimate) *)
  SUBGOAL_THEN `rfs_neck_dom (beta * eps) SUBSET rfs_neck_dom eps_in` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN rfs_neck_dom (beta * eps)
        ==> ~((e:real^3->real^3) v = vec 0) /\
            --(inv(p3_stepf dd (hs_time (hs:(A)rfs_history) k))) <
            A0 + &4 - p3_std_dist g0 (e v) /\
            A0 + &4 - p3_std_dist g0 (e v) < &0 /\
            abs(p3_std_dist g0 (e v) - p3_std_dist g0 q) < &2 / (beta * eps)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^3->real^3) v IN IMAGE e (rfs_neck_dom eps_in)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `A0 + &5 <= p3_std_dist g0 ((e:real^3->real^3) v) /\
                  p3_std_dist g0 (e v) < m` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `A0 + &5`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in) SUBSET
                     {z | p3_std_dist g0 z < m}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(p3_std_dist g0 ((e:real^3->real^3) v) - p3_std_dist g0 q) <
                  &2 / (beta * eps)` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&2 / (beta * eps)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `A0 + &5 <= p3_std_dist g0 ((e:real^3->real^3) v)` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `p3_stepf dd`;
                 `p3_hscale hf (p3_stepf rs') (p3_stepf dd)`; `hs:(A)rfs_history`; `k:num`;
                 `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `q:real^3`;
                 `e:real^3->real^3`; `rfs_neck_dom (beta * eps)`; `beta * eps / &2`]
                P3H_IMAGE_CONTAIN_AXIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                  DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  (* Prop 15.2 glues (a) and (b) *)
  REMOVE_THEN "152" (MP_TAC o SPECL
   [`hs:(A)rfs_history`; `(Phi:real^3->A) q`; `ts:real`;
    `tp * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k) pow 2 * X`;
    `(Phi:real^3->A) o (e:real^3->real^3)`;
    `ev_neck (hs_event (hs:(A)rfs_history) k) j o
     (\v:real^3. norm(p3_std_nc g0 A0 q) % v)`]) THEN
  SUBGOAL_THEN
   `ts - (tp * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time (hs:(A)rfs_history) k) pow 2 *
          X) / X = hs_time hs k` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < X` THEN
    UNDISCH_TAC `hs_time (hs:(A)rfs_history) k +
                 tp * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2 = ts` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `e3:real^3->A`) THEN
  MATCH_MP_TAC P3H_CANONV_FROM_NECK THEN EXISTS_TAC `e3:real^3->A` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The route theorem for MT Lemma 17.7 (pc_p3_route R12): Lemma 17.7 from   *)
(* the route inputs, through P3H_LEMMA_17_7_FROM_FAR (pc_p3_c177b) and the *)
(* case (2b) theorem P3H_177_FARNECK.                                       *)
(* ========================================================================= *)

let P3_LEMMA_17_7_ROUTE = prove
 (`!u:A->bool. P3_LEMMA_17_7_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_LEMMA_17_7_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3H_LEMMA_17_7_FROM_FAR THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3H_177_FARNECK THEN ASM_REWRITE_TAC[]);;

