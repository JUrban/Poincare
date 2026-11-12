(* ========================================================================= *)
(* Unit pc_p3_c177a: MT Lemma 17.7 (p. 403-406), part 1.                    *)
(* A point x of the first bad time near a surgery cap: the history facts,   *)
(* Claim 17.8 (the elapsed time is below theta1 in the surgery scale), and *)
(* the transfer tools for the canonical neighbourhoods of Thm 12.32 at the  *)
(* corresponding point of the standard solution.                            *)
(* ========================================================================= *)

needs "src/pc_p3_c172e.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Transfer tools with a general scalar lower bound b at the                *)
(* source point (the cap of Thm 12.32 lies in the closeness region, and it  *)
(* transfers to a cap of the history slice), and the rescaling of the view  *)
(* closeness of Prop 16.5 to the normalization of a neck at (q, t').        *)
(* ========================================================================= *)

let P3H_CAP_TO_HIST_GEN = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
     !C eps C' eps' Kr.
       &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\ eps' <= eps0
       ==> ?delta. &0 < delta /\
             !(G0:real^3->real^3^3) q U Y (top:A topology) atlas g h W (Phi:real^3->A) d b.
               metric_field (:real^3) G0 /\
               rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C eps U Y /\ q IN Y /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local (open_set_atlas (:real^3))
                               (chart_at (open_set_atlas (:real^3)) y)
                               (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                            (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
               hausdorff_space top /\ smooth_manifold_atlas top atlas /\
               riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
               mfd_param top atlas W Phi /\ U SUBSET W /\
               &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
               (&1 + inv b) pow (rfs_kreg delta) * d < delta pow 2 /\
               (!y. y IN W
                    ==> lck_dist2 (rfs_kreg delta) G0
                          (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
               ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C' eps' U' Y' /\
                           Phi q IN Y'`,
  MP_TAC(ISPECL [`(:real^3)`; `(:A)`] P2B_PROP_9_79_CAP_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF"))) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `Phi':A->real^3`) THEN
  SUBGOAL_THEN `open_in euclidean (U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo euclidean (open_set_atlas (:real^3)) U (top:A topology)
                           (atlas:((A->bool)#(A->real^3))->bool)
                           (IMAGE (Phi:real^3->A) U) Phi Phi'` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `W:real^3->bool` THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) W` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Rq = mfd_scalar (open_set_atlas (:real^3)) (G0:real^3->real^3^3) q` THEN
  ABBREV_TAC `P = rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REMOVE_THEN "CF" (MP_TAC o SPECL
    [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `G0:real^3->real^3^3`;
     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `\z:A. inv(h pow 2) %% (g:A->real^3^3) z`; `q:real^3`; `U:real^3->bool`;
     `Y:real^3->bool`; `Phi:real^3->A`; `Phi':A->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN
      REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_COMPACT_IMP_COMPLETE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `(&1 + inv b) pow (rfs_kreg delta) * d` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
    SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV];
                      ALL_TAC] THEN
    SUBGOAL_THEN
     `!Fm:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
      MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[SND; P2B9_PULLBACK_METRIC_CMUL] THEN REWRITE_TAC[P3H_PULLBACK_OPEN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field W (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) /\
                  metric_field W (G0:real^3->real^3^3)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[mfd_param] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[mfd_diffeo; OPEN_IN_EUCLIDEAN]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_kreg delta`; `W:real^3->bool`; `G0:real^3->real^3^3`;
                   `\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z`; `Rq:real`; `y:real^3`]
                  P2B9S_LCK_SCALE_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv Rq) pow rfs_kreg delta * d` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN
        SUBGOAL_THEN `&0 < inv Rq` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [SUBGOAL_THEN `&0 < inv Rq` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          SUBGOAL_THEN `inv Rq <= inv b` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lck_dist2 (rfs_kreg delta) (G0:real^3->real^3^3)
                      (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `W:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U':A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Y':A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (\z:A. inv(h pow 2) %% (g:A->real^3^3) z) C' eps' U' Y'` THEN
  ASM_SIMP_TAC[P2BCS_CAP_CMUL]);;

let P3H_CAP_IN_REGION_GEN = prove
 (`!eps. &0 < eps /\ eps <= &1 / &4
     ==> ?dd0. &0 < dd0 /\
           !g0 A0 (Gt:real^3->real^3^3) s m d0 dd C epsc U Y q b.
             p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
             inv eps < d0 /\ d0 + inv eps < m /\ &0 < dd /\ dd <= dd0 /\
             (!x. d0 - inv eps < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps
                  ==> lck_dist2 (rfs_kreg eps)
                        (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
             rfs_cap (euclidean,open_set_atlas (:real^3)) Gt C epsc U Y /\ q IN Y /\
             p3_std_dist g0 q < d0 /\
             &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
             C * inv(sqrt b) <= sqrt(&1 - s) / (&2 * eps)
             ==> U SUBSET {x | p3_std_dist g0 x < d0 + inv eps}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:real^3`,`:A`] P3H_SHORT_CURVE_STAYS)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^3) IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2B_CAP_CORE_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `Gt:real^3->real^3^3`; `C:real`; `epsc:real`; `U:real^3->bool`;
                 `Y:real^3->bool`; `q:real^3`] P2B_CAP_SUP_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_dist_in (euclidean,open_set_atlas (:real^3)) Gt U q z <
                C * inv(sqrt(sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) Gt) U)))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                CONJUNCT2 o GEN_REWRITE_RULE I [rfs_cap] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
    REWRITE_TAC[rfs_sup_lt; FORALL_IN_GSPEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `dm:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dm:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * inv(sqrt(sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) Gt) U))) <=
                C * inv(sqrt b)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `Gt:real^3->real^3^3`; `C:real`; `epsc:real`; `U:real^3->bool`;
                     `Y:real^3->bool`] P2B_CAP_RATIO) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `q:real^3`)
        (X_CHOOSE_THEN `dr:real` (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPECL [`q:real^3`; `q:real^3`])))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas (:real^3)) Gt q` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar (open_set_atlas (:real^3)) Gt q` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `Gt:real^3->real^3^3`; `U:real^3->bool`; `q:real^3`; `z:real^3`;
                 `C * inv(sqrt b)`] P3H_DIST_IN_SHORT_CURVE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `Gt:real^3->real^3^3`; `C:real`; `epsc:real`; `U:real^3->bool`;
                     `Y:real^3->bool`] APX_CAP_JOINABLE) THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < m}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3N_STD_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  REMOVE_THEN "S" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `euclidean:(real^3)topology`;
     `open_set_atlas (:real^3)`; `Gt:real^3->real^3^3`; `\x:real^3. x`; `m:real`; `&1`;
     `Gt:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`; `gamma:real->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; REAL_LT_01; P3H_ID_PULLBACK] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX; P2BL_LCK_DIST2_REFL] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC P3H_ID_PARAM THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let P3H_VIEW_CLOSE_RESCALE = prove
 (`!(G:real->real^3->real^3^3) W W' (hs:(A)rfs_history) T1 h (Phi:real^3->A) J dq tp R a
    delta ts.
     rfs_history_ok hs /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) T1 (inv(h pow 2)) Phi J dq /\
     &0 < h /\ &0 < R /\ T1 + tp * h pow 2 = ts /\
     W' SUBSET W /\ open W' /\
     (!s. --a < s /\ s <= &0 ==> tp + s / R IN J /\ &0 <= tp + s / R /\ tp + s / R < &1) /\
     (!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) (G t)) /\
     &0 < dq /\ dq <= delta /\ (&1 + inv R) pow (rfs_kreg delta) * dq pow 2 <= delta pow 2
     ==> p3_view_close
           (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
           tp R W' (rfs_view hs) ts (R * inv(h pow 2)) Phi {s | --a < s /\ s <= &0} delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(h pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[p3_view_close] THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ABBREV_TAC `sg = tp + s / R` THEN
  SUBGOAL_THEN `sg IN J /\ &0 <= sg /\ sg < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ts + s / (R * inv(h pow 2)) = T1 + sg * h pow 2` SUBST1_TAC THENL
   [EXPAND_TAC "sg" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `T1 + tp * h pow 2 = ts`)) THEN
    UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `W:real^3->bool`; `hs:(A)rfs_history`; `T1:real`;
                 `h:real`; `Phi:real^3->A`; `J:real->bool`; `dq:real`; `sg:real`]
                P3H_VIEW_CLOSE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sg:real` o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [p3_view_close] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_view_close")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 + sg / &1 = sg /\ T1 + sg / inv(h pow 2) = T1 + sg * h pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ADD_LID; REAL_DIV_1; real_div; REAL_INV_INV]; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS; GSYM rfs_vtop; GSYM rfs_vatlas; GSYM rfs_vmetric] THEN
  REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi':A->real^3`) (K ALL_TAC)) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `psi':A->real^3` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`W:real^3->bool`; `IMAGE (Phi:real^3->A) W`] THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `(&1 + inv R) pow (rfs_kreg delta) * d` THEN
  SUBGOAL_THEN `&0 < (&1 + inv R) pow (rfs_kreg delta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    SUBGOAL_THEN `&0 < inv R` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&1 + inv R) pow (rfs_kreg delta) * dq pow 2` THEN
    ASM_SIMP_TAC[REAL_LT_LMUL];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_at (open_set_atlas (:real^3)) y = ((:real^3),(\x:real^3. x))`
  SUBST1_TAC THENL [MATCH_MP_TAC RFB_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Fm:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) Fm = Fm`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC RFB_OPEN_SET_METRIC_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[SND; ETA_AX; P3H_PULLBACK_OPEN_UNIV; GSYM MATRIX_CMUL_ASSOC] THEN
  ABBREV_TAC `P = rfs_pullback (rfs_atlas_at (hs:(A)rfs_history) (T1 + sg * h pow 2))
                    (Phi:real^3->A) (rfs_metric_at hs (T1 + sg * h pow 2))` THEN
  SUBGOAL_THEN `(y:real^3) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W ((G:real->real^3->real^3^3) sg) /\
                metric_field W (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[mfd_param; mfd_diffeo; OPEN_IN]];
      MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) (T1 + sg * h pow 2)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `T1 + sg * h pow 2`] P3_HIST_VIEW_SLICES) THEN
      ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_kreg delta`; `W:real^3->bool`; `(G:real->real^3->real^3^3) sg`;
                 `\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z`; `R:real`; `y:real^3`]
                P2B9S_LCK_SCALE_LE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg dq) ((G:real->real^3->real^3^3) sg)
                (\z:real^3. inv(h pow 2) %% (P:real^3->real^3^3) z) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `W:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The history facts of Lemma 17.7 (the cap parameterization                *)
(* of the event (k,j), y = Phi qy in its core, the step bounds at T_k, the  *)
(* canonical assumption at the threshold r' before ts, and the persistence  *)
(* of y on (T_k,ts]); the standard flow facts used with Thm 12.32 and R14.  *)
(* ========================================================================= *)

let P3H_177_HIST_FACTS = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt rs' ks' dd (hs:(A)rfs_history) ts x y k j tp.
     1 <= i /\ &0 < eps /\ eps <= &1 / &8 /\ rs 0 = eps /\ &0 < r' /\ &0 < tp /\
     tp * r' pow 2 <= &1 / &64 /\ rs' (SUC i) = r' /\ p3_hfun C hf /\
     p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
     p3_T i <= ts /\ ts < rfs_horizon hs /\
     rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts) C eps (p3_stepf rs') /\
     inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
     1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
     ts - tp * inv(rfs_vscalar (rfs_view hs) ts x) <= hs_time hs k /\ hs_time hs k < ts /\
     y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
     p3_flowline hs y (hs_time hs k) ts
     ==> ?Phi xi qy.
           p3_cap_param (md,g0,A0)
             (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd)) hs k j Phi xi /\
           y = Phi qy /\ p3_std_dist g0 qy <= A0 + &4 /\ &0 < hs_time hs k /\
           p3_stepf dd (hs_time hs k) <= dlt /\ p3_stepf rs' (hs_time hs k) <= eps /\
           &0 < p3_stepf dd (hs_time hs k) /\
           &0 < p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) /\
           (!t z. &0 <= t /\ t < ts /\ z IN topspace(rfs_top_at hs t) /\
                  inv(r' pow 2) <= rfs_vscalar (rfs_view hs) t z
                  ==> p3_canon_at (rfs_view hs) C eps z t) /\
           (!tau. hs_time hs k < tau /\ tau <= ts ==> y IN topspace(rfs_top_at hs tau))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_step_hyp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_step_hyp")) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_struct] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_struct")) (concl th))) THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `&0 < inv(r' pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the cap parameterization of event (k,j) *)
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_ok")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[p3_cap_ok] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->A` (X_CHOOSE_TAC `xi:real^3->real^3`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p3_cap_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_cap_param")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SYM) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?qy. (y:A) = Phi qy /\ p3_std_dist g0 qy <= A0 + &4` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:A) IN IMAGE Phi {x | &0 <= A0 + &4 - p3_std_dist g0 x}` MP_TAC THENL
     [UNDISCH_TAC `(y:A) IN IMAGE (ev_capm (hs_event (hs:(A)rfs_history) k) j)
                                  (cball(vec 0,&1))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Phi:real^3->A`; `xi:real^3->real^3`; `qy:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the time of the event is after p3_T (i - 1) *)
  SUBGOAL_THEN `r' <= eps /\ tp * inv Q <= &1 / &64` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r' <= eps` ASSUME_TAC THENL
     [SUBGOAL_THEN `rs' 0 = (eps:real)` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `rs' (SUC i) = (r':real)`)) THEN
      MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tp * r' pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `r' pow 2 = inv(inv(r' pow 2))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_INV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_T (i - 1) <= hs_time (hs:(A)rfs_history) k /\ &0 < hs_time hs k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_T i = &2 * p3_T (i - 1) /\ &1 / &32 <= p3_T (i - 1)` MP_TAC THENL
     [SUBGOAL_THEN `i = SUC(i - 1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
                                                  [th]) THENL
       [UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p3_T; real_pow] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&1 <= a ==> &1 / &32 <= a / &32`) THEN
        MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `i <= p3_step (hs_time (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`hs_time (hs:(A)rfs_history) k`; `i - 1`] P3_STEP_GE) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= i` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3_stepf rs' (hs_time (hs:(A)rfs_history) k) /\
                &0 < p3_stepf dd (hs_time hs k)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `p3_stepf rs'`)) (concl th) &&
      not (can (find_term (fun t -> t = `s:real`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REWRITE_TAC[p3_stepf] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dd:num->real) i` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `dd:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p3_stepf] THEN
    SUBGOAL_THEN `rs' 0 = (eps:real)` (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THENL
     [ASM_MESON_TAC[LE_0]; ALL_TAC] THEN
    MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[p3_hscale] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p3_hfun] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_hfun")) (concl th))) THEN
    DISCH_THEN(MP_TAC o SPECL
      [`p3_stepf dd (hs_time (hs:(A)rfs_history) k) * p3_stepf rs' (hs_time hs k)`;
       `p3_stepf dd (hs_time (hs:(A)rfs_history) k)`]) THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_canonical_assumption (rfs_trunc (rfs_view (hs:(A)rfs_history)) ts) C eps
                   (p3_stepf rs')` THEN
    REWRITE_TAC[P3H_TRUNC_CANON_BAD] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[p3h_bad; NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a ==> ~(a /\ ~b) ==> b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(r' pow 2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[p3_stepf] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `rs' (SUC i) = (r':real)`)) THEN
    MP_TAC(SPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P3_STEP_LE THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `p3_flowline (hs:(A)rfs_history) y (hs_time hs k) ts` THEN
    REWRITE_TAC[p3_flowline] THEN DISCH_THEN(MP_TAC o SPEC `tau:real` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let P3H_STD_FLOW_FACTS = prove
 (`!g0 A0 (G:real->real^3->real^3^3) c C_in eps_in Kr.
     p3_std_flow g0 (&1) G /\ &0 < c /\
     (!G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1
              ==> c / (&1 - t) <= mfd_scalar (open_set_atlas (:real^3)) (G t) x) /\
     (!G x t. p3_std_flow g0 (&1) G /\ &0 < t /\ t < &1
              ==> (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C_in eps_in U Y /\
                         x IN Y) \/
                  (?e. rfs_evolving_neck
                         (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                        {s | &0 <= s /\ s < &1} G)
                         eps_in x t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) x) e /\
                       !z. z IN IMAGE e (rfs_neck_dom eps_in)
                           ==> A0 + &5 <= p3_std_dist g0 z) \/
                  (?e. rfs_evolving_neck
                         (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                        {s | &0 <= s /\ s < &1} G)
                         eps_in x t (&1 + eps_in) e)) /\
     (!G t x U.
        p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1 /\
        rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G t) C_in eps_in x U
        ==> !y l. y IN U /\ l <= 2
                  ==> lrm_deriv_norm2 l
                        (metric_local (open_set_atlas (:real^3))
                           (chart_at (open_set_atlas (:real^3)) y)
                           (\z. mfd_scalar (open_set_atlas (:real^3)) (G t) x %% G t z))
                        (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr)
     ==> (!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) (G s)) /\
         (!s z. &0 <= s /\ s < &1 ==> c / (&1 - s) <= lscalar (G s) z) /\
         (!s z. &0 < s /\ s < &1
                ==> lrm_deriv_norm2 0 (G s) z <= Kr * lscalar (G s) z pow 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) ((G:real->real^3->real^3^3) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_STD_FLOW_FIELD THEN
    EXISTS_TAC `g0:real^3->real^3^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s z. &0 <= s /\ s < &1
                      ==> c / (&1 - s) <= lscalar ((G:real->real^3->real^3^3) s) z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `lscalar ((G:real->real^3->real^3^3) s) z =
                  mfd_scalar (open_set_atlas (:real^3)) (G s) z` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFB_OPEN_SET_MFD_SCALAR THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `z:real^3`; `s:real`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_cap")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `C_in:real`;
                 `eps_in:real`; `z:real^3`; `s:real`] P3H_1232_CANON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P3H_RM_FROM_C2 THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `c / (&1 - s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_scalar")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    FIRST_ASSUM(MP_TAC o SPECL [`G:real->real^3->real^3^3`; `s:real`; `z:real^3`;
                                 `U:real^3->bool`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
            (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* MT Claim 17.8.  The scale of the surgery is not small                    *)
(* compared with R(x)^(-1/2) (h^2 Q >= c/(2 Dp), from the cap curvature at  *)
(* T_k and R(y) <= Dp Q), and the elapsed time in the surgery scale is      *)
(* below theta1 (P3H_CLAIM_17_3_HIST with M = 4 Dp tp, or directly when     *)
(* h^2 Q >= 4 tp).                                                          *)
(* ========================================================================= *)

let P3H_177_CLAIM = prove
 (`!g0 A0 (G:real->real^3->real^3^3) (hs:(A)rfs_history) k j (Phi:real^3->A) xi md
    (dl:real->real) (hh:real->real) ts y qy c D Dp tp Q Kr theta0 theta1 m dd3 dq2.
     p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) G /\ rfs_history_ok hs /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < m}
       (rfs_view hs) (hs_time hs k) (inv(hh(hs_time hs k) pow 2)) Phi
       {s | &0 <= s /\ s < theta1 /\ hs_time hs k + s * hh(hs_time hs k) pow 2 <= ts /\
            hs_time hs k + s * hh(hs_time hs k) pow 2 < rfs_horizon hs} dq2 /\
     k <= hs_count hs /\ hs_time hs k < ts /\ ts < rfs_horizon hs /\
     &0 < Q /\ ts - tp * inv Q <= hs_time hs k /\
     p3_cap_param (md,g0,A0) (dl,hh) hs k j Phi xi /\
     &0 < hh(hs_time hs k) /\ &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= md dd3 /\
     y = Phi qy /\ p3_std_dist g0 qy <= A0 + &4 /\ A0 + &4 < m /\
     (!tau. hs_time hs k < tau /\ tau <= ts ==> y IN topspace(rfs_top_at hs tau)) /\
     (!s. hs_time hs k <= s /\ s <= ts ==> rfs_vscalar (rfs_view hs) s y <= Dp * Q) /\
     &0 < Dp /\ &0 < tp /\ &0 < c /\
     (!s. &0 <= s /\ s < &1 ==> metric_field (:real^3) (G s)) /\
     (!s z. &0 <= s /\ s < &1 ==> c / (&1 - s) <= lscalar (G s) z) /\
     (!s z. &0 < s /\ s < &1 ==> lrm_deriv_norm2 0 (G s) z <= Kr * lscalar (G s) z pow 2) /\
     &0 <= Kr /\ &1 <= D /\
     (!q. p3_std_dist g0 q <= A0 + &4
          ==> abs(lscalar g0 q) <= D /\ lrm_deriv_norm2 0 g0 q <= D pow 2) /\
     &0 < dd3 /\ dd3 <= &1 / &10 /\ A0 + &4 < inv dd3 /\ &72 * (&1 + D) * dd3 <= c / &2 /\
     &0 <= theta0 /\ theta0 < theta1 /\ theta1 < &1 /\ &1 / &2 <= theta1 /\
     &0 < dq2 /\ dq2 <= &1 / &10 /\ &72 * sqrt Kr * dq2 <= &1 / &2 /\
     (!s. theta0 <= s /\ s < theta1 ==> &2 * (&4 * Dp * tp) + &144 * dq2 < c / (&1 - s))
     ==> c / (&2 * Dp) <= hh(hs_time hs k) pow 2 * Q /\
         (ts - hs_time hs k) / hh(hs_time hs k) pow 2 < theta1`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ABBREV_TAC `h = (hh:real->real) (hs_time (hs:(A)rfs_history) k)` THEN
  (* the scalar curvature of y at the surgery time *)
  SUBGOAL_THEN `rfs_vscalar (rfs_view (hs:(A)rfs_history)) (hs_time hs k) y =
                mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `hs_time (hs:(A)rfs_history) k`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`md:real->real`; `g0:real^3->real^3^3`; `A0:real`; `dl:real->real`;
                 `hh:real->real`; `hs:(A)rfs_history`; `k:num`; `j:num`; `Phi:real^3->A`;
                 `xi:real^3->real^3`; `dd3:real`; `D:real`; `qy:real^3`] P3H_CAP_SCALAR_T) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> --a < b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o SPEC `qy:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `D:real`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(D:real) = D` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `c <= lscalar (g0:real^3->real^3^3) qy` ASSUME_TAC THENL
   [SUBGOAL_THEN `(G:real->real^3->real^3^3) (&0) = g0` (SUBST1_TAC o SYM) THENL
     [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
      SIMP_TAC[p3_std_flow; p3_partial_std];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `qy:real^3`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `c:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th) &&
      not (can (find_term (fun t -> t = `theta0:real`)) (concl th)) &&
      not (can (find_term (fun t -> t = `dd3:real`)) (concl th)))) THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN DISCH_THEN MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) (y:A)
                <= Dp * Q`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `rfs_vscalar (rfs_view (hs:(A)rfs_history)) (hs_time hs k) y =
                  mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k)) y`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `Dp:real`)) (concl th) &&
      not (can (find_term (fun t -> t = `tp:real`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `c / &2 <= Dp * (h pow 2 * Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `h pow 2 * mfd_scalar (hs_atlas hs k) (hs_metric hs k (hs_time hs k))
                                     ((Phi:real^3->A) qy)` THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `Dp * (h pow 2 * Q) = h pow 2 * (Dp * Q)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < Dp ==> &0 < &2 * Dp`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&4 * tp <= h pow 2 * Q` THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 / &4` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tp * inv Q` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < m}`;
                 `hs:(A)rfs_history`; `hs_time (hs:(A)rfs_history) k`; `ts:real`; `h:real`;
                 `Phi:real^3->A`; `y:A`; `qy:real^3`; `c:real`; `theta0:real`; `theta1:real`;
                 `&4 * Dp * tp`; `dq2:real`; `Kr:real`] P3H_CLAIM_17_3_HIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(y:A) = (Phi:real^3->A) qy`)) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Dp * Q) * h pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `Dp:real`)) (concl th) &&
          not (can (find_term (fun t -> t = `tp:real`)) (concl th)))) THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(Dp * Q) * h pow 2 = Dp * (h pow 2 * Q)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&4 * Dp * tp = Dp * (&4 * tp)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POS]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Alternative (1) of Thm 12.32 at (q, t'): the cap lies in                 *)
(* the closeness region and transfers to a (C,eps)-cap of the slice at ts   *)
(* with x = Phi q in its core.                                              *)
(* ========================================================================= *)

let P3H_POW_CLOSE_ARITH = prove
 (`!p d dq2 delta.
     &1 <= p /\ d < dq2 pow 2 /\ &0 < dq2 /\ dq2 * p <= delta
     ==> p * d < delta pow 2 /\ p * dq2 pow 2 <= delta pow 2 /\ dq2 <= delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p * dq2 pow 2 <= delta pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dq2 * p) pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN
      SUBGOAL_THEN `p * dq2 pow 2 = dq2 pow 2 * p` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `p * dq2 pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dq2 * p` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC]);;

let P3H_177_CAP_CASE = prove
 (`!g0 A0 (Gt:real^3->real^3^3) tp q (top:A topology) atlas g h m (Phi:real^3->A) x
    C eps C_in eps_in Kr c delta eps_n dd0n ddx d2 A1 epsp dq2 d U Y.
     p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= tp /\ tp < &1 /\
     rfs_cap (euclidean,open_set_atlas (:real^3)) Gt C_in eps_in U Y /\ q IN Y /\
     (!z U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) Gt C_in eps_in z U
            ==> !y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local (open_set_atlas (:real^3))
                               (chart_at (open_set_atlas (:real^3)) y)
                               (\w. mfd_scalar (open_set_atlas (:real^3)) Gt z %% Gt w))
                            (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
     (!z. A1 < p3_std_dist g0 z
          ==> lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow tp)) Gt z
              < epsp pow 2) /\
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ &0 < h /\
     mfd_param top atlas {z | p3_std_dist g0 z < m} Phi /\
     p3_std_dist g0 q < d2 /\ Phi q = x /\
     (!y. p3_std_dist g0 y < m
          ==> lck_dist2 (rfs_kreg dq2) Gt
                (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d) /\
     d < dq2 pow 2 /\
     (!G0 q U Y (top:A topology) atlas g h W (Phi:real^3->A) d b.
        metric_field (:real^3) G0 /\
        rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C_in eps_in U Y /\ q IN Y /\
        (!y l. y IN U /\ l <= 2
               ==> lrm_deriv_norm2 l
                     (metric_local (open_set_atlas (:real^3))
                        (chart_at (open_set_atlas (:real^3)) y)
                        (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                     (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
        mfd_param top atlas W Phi /\ U SUBSET W /\
        &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
        (&1 + inv b) pow (rfs_kreg delta) * d < delta pow 2 /\
        (!y. y IN W
             ==> lck_dist2 (rfs_kreg delta) G0
                   (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
        ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C eps U' Y' /\
                    Phi q IN Y') /\
     (!g0 A0 (Gt:real^3->real^3^3) s m d0 dd C epsc U Y q b.
        p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
        inv eps_n < d0 /\ d0 + inv eps_n < m /\ &0 < dd /\ dd <= dd0n /\
        (!x. d0 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps_n
             ==> lck_dist2 (rfs_kreg eps_n)
                   (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
        rfs_cap (euclidean,open_set_atlas (:real^3)) Gt C epsc U Y /\ q IN Y /\
        p3_std_dist g0 q < d0 /\
        &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
        C * inv(sqrt b) <= sqrt(&1 - s) / (&2 * eps_n)
        ==> U SUBSET {x | p3_std_dist g0 x < d0 + inv eps_n}) /\
     &0 < c /\ c <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
     &0 < dq2 /\ &0 < delta /\ dq2 * (&1 + inv c) pow (rfs_kreg delta) <= delta /\
     &0 < eps_n /\ eps_n <= &1 / &4 /\ &0 < ddx /\ ddx <= dd0n /\
     &0 < epsp /\ epsp <= eps_n /\ epsp <= ddx /\
     inv eps_n < d2 /\ d2 + inv eps_n < m /\ A1 + inv eps_n < d2 /\
     C_in * inv(sqrt c) <= sqrt(&1 - tp) / (&2 * eps_n)
     ==> ?U' Y'. rfs_cap (top,atlas) g C eps U' Y' /\ x IN Y'`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 < inv eps_n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2B_CAP_CORE_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET {z | p3_std_dist g0 z < d2 + inv eps_n}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `dd0n:real`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`A0:real`; `Gt:real^3->real^3^3`; `tp:real`; `m:real`;
                          `ddx:real`; `C_in:real`; `eps_in:real`; `Y:real^3->bool`;
                          `q:real^3`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3H_SHELL_CLOSE THEN
    MAP_EVERY EXISTS_TAC [`A1:real`; `epsp:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) Gt C_in eps_in q U`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `Y:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&1 + inv c) pow (rfs_kreg delta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN
    SUBGOAL_THEN `&0 < inv c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(&1 + inv c) pow (rfs_kreg delta)`; `d:real`; `dq2:real`; `delta:real`]
               P3H_POW_CLOSE_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`Gt:real^3->real^3^3`; `q:real^3`; `U:real^3->bool`; `Y:real^3->bool`;
     `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `h:real`;
     `{z:real^3 | p3_std_dist g0 z < m}`; `Phi:real^3->A`; `d:real`; `c:real`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
    can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_canonical_nbhd"))
            (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2"))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(U:real^3->bool) SUBSET {z | p3_std_dist g0 z < d2 + inv eps_n}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `d2 + inv eps_n` THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg dq2) Gt
                    (\z. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) (g:A->real^3^3) z) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `{z:real^3 | p3_std_dist g0 z < m}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV] THEN
          MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `{z:real^3 | p3_std_dist g0 z < m}`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
           [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
            ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[REAL_POW_LT]];
          MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `U':A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Y':A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Alternative (3) of Thm 12.32 at (q, t'): an evolving neck                *)
(* of length 1 + eps_in lies in the closeness region (the short path from   *)
(* each of its points to q stays there) and transfers by Prop 9.79 (neck   *)
(* form) to a strong eps-neck at (x, ts), through the closeness of Prop     *)
(* 16.5 rescaled to the normalization of the neck.                          *)
(* ========================================================================= *)

let P3H_NECK_IN_REGION = prove
 (`?eps1. &0 < eps1 /\
     !eps_n. &0 < eps_n /\ eps_n <= &1 / &4
       ==> ?dd0. &0 < dd0 /\
             !g0 A0 (Gt:real^3->real^3^3) s m d0 dd epsn1 q (e:real^3->real^3) b.
               p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
               inv eps_n < d0 /\ d0 + inv eps_n < m /\ &0 < dd /\ dd <= dd0 /\
               (!x. d0 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps_n
                    ==> lck_dist2 (rfs_kreg eps_n)
                          (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
               rfs_neck (euclidean,open_set_atlas (:real^3)) Gt epsn1 q e /\
               &0 < epsn1 /\ epsn1 <= eps1 /\ p3_std_dist g0 q < d0 /\
               &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
               (&1 + &1 / &10) * inv(sqrt b) * (inv epsn1 + &5) <=
               sqrt(&1 - s) / (&2 * eps_n)
               ==> IMAGE e (rfs_neck_dom epsn1) SUBSET
                   {x | p3_std_dist g0 x < d0 + inv eps_n}`,
  MP_TAC(SPEC `&1 / &10` (INST_TYPE [`:real^3`,`:A`] P3H_NECK_SHORT_PATH)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SP"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps_n:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INST_TYPE [`:real^3`,`:A`] P3H_SHORT_CURVE_STAYS)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dd0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3)) /\
                riemannian_metric (open_set_atlas (:real^3)) (Gt:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `(:real^3)` OPEN_SET_ATLAS) THEN REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  USE_THEN "SP" (MP_TAC o SPECL
    [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `Gt:real^3->real^3^3`;
     `epsn1:real`; `q:real^3`; `e:real^3->real^3`; `y0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `Gt:real^3->real^3^3`; `gamma:real->real^3`; `&0`; `&1`]
                MFD_LENGTH_REVERSE) THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) (Gt:real^3->real^3^3) q)) <=
                inv(sqrt b)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv epsn1 + &5` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length (open_set_atlas (:real^3)) (Gt:real^3->real^3^3) gamma (&0) (&1) <
                &1 * sqrt(&1 - s) / (&2 * eps_n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &10) * inv(sqrt(mfd_scalar (open_set_atlas (:real^3))
                                            (Gt:real^3->real^3^3) q)) * (inv epsn1 + &5)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &10) * inv(sqrt b) * (inv epsn1 + &5)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REMOVE_THEN "S" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `euclidean:(real^3)topology`;
     `open_set_atlas (:real^3)`; `Gt:real^3->real^3^3`; `\x:real^3. x`; `m:real`; `&1`;
     `Gt:real^3->real^3^3`; `s:real`; `d0:real`; `dd:real`;
     `\t. (gamma:real->real^3) (&1 - t)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; REAL_LT_01; P3H_ID_PULLBACK] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX; P2BL_LCK_DIST2_REFL] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC P3H_ID_PARAM THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3N_STD_BALL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `&0 < inv eps_n` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL]];
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL; REAL_SUB_REFL] THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let P3H_177_NECK_CASE = prove
 (`!(G:real->real^3->real^3^3) (hs:(A)rfs_history) T1 ts h (Phi:real^3->A) theta1 dq2 m g0
    tp q x C eps eps_in (e:real^3->real^3) deltaN c.
     rfs_history_ok hs /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < m} (rfs_view hs) T1 (inv(h pow 2)) Phi
       {s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
            T1 + s * h pow 2 < rfs_horizon hs} dq2 /\
     &0 < h /\ T1 + tp * h pow 2 = ts /\ ts < rfs_horizon hs /\ &0 <= tp /\
     tp < theta1 /\ theta1 <= &1 /\
     p2c_regular_view
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G) /\
     rfs_evolving_neck
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       eps_in q tp (&1 + eps_in) e /\
     IMAGE e (rfs_neck_dom eps_in) SUBSET {x | p3_std_dist g0 x < m} /\
     (!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) (G t)) /\
     Phi q = x /\
     &0 < c /\ c <= mfd_scalar (open_set_atlas (:real^3)) (G tp) q /\
     &0 < dq2 /\ dq2 * (&1 + inv c) pow (rfs_kreg deltaN) <= deltaN /\
     (!V x t e V' t' Q' psi.
        p2c_regular_view (V:(real->(real^3)topology)#
                            (real->((real^3->bool)#(real^3->real^3))->bool)#
                            (real->real^3->real^3^3)) /\
        rfs_evolving_neck V eps_in x t (&1 + eps_in) e /\
        (!s. --(&1 + eps_in) < s /\ s <= &0
             ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                       (rfs_vatlas V' (t' + s / Q')) /\
                 riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                   (rfs_vmetric V' (t' + s / Q'))) /\
        p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps_in))
          (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
              (real->A->real^3^3)) t' Q' psi {s | --(&1 + eps_in) < s /\ s <= &0} deltaN
        ==> ?e'. rfs_strong_neck V' eps (psi x) t' e')
     ==> p3_canonv_at (rfs_view hs) C eps x ts`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `tp < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `V = rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                                (G:real->real^3->real^3^3)` THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
  SUBGOAL_THEN `rfs_vscalar (V:(real->(real^3)topology)#
                               (real->((real^3->bool)#(real^3->real^3))->bool)#
                               (real->real^3->real^3^3)) tp q = R` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "R"] THEN
    REWRITE_TAC[P2B9_RFS_VSCALAR; rfs_flow_view; rfs_vatlas; rfs_vmetric];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the neck image is open and inside W *)
  SUBGOAL_THEN `open (IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[P2B9_EVOLVING_NECK_ALT] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck"))
          (concl th) && not (is_forall(concl th)))) THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `rfs_neck_dom eps_in`; `e:real^3->real^3`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_IN];
    ALL_TAC] THEN
  (* the normalized times of the neck lie in the closeness range *)
  SUBGOAL_THEN
   `!s. --(&1 + eps_in) < s /\ s <= &0
        ==> tp + s / R IN {s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
                               T1 + s * h pow 2 < rfs_horizon (hs:(A)rfs_history)} /\
            &0 <= tp + s / R /\ tp + s / R < &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s / R <= &0 /\ &0 < s / R + (&1 + eps_in) / R` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN REWRITE_TAC[GSYM real_div] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= tp + s / R /\ tp + s / R < &1` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `tp + s / R` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  REWRITE_RULE[P2B9_EVOLVING_NECK_ALT] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck"))
            (concl th) && not (is_forall(concl th)))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[rfs_flow_view; rfs_vtop; IN_ELIM_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
      REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
      MP_TAC(SPEC `eps_in:real` APX_UNIT_SPHERE_NECK_DOM) THEN
      FIRST_ASSUM(MP_TAC o REWRITE_RULE[P2B9_EVOLVING_NECK_ALT] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_evolving_neck"))
            (concl th) && not (is_forall(concl th)))) THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q:real^3) IN IMAGE (e:real^3->real^3) (sphere(vec 0,&1))` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `T1 + (tp + s / R) * h pow 2 <= ts` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `T1 + tp * h pow 2 = ts`)) THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_ARITH `a + b + c <= a + b <=> c <= &0`] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + inv R) pow (rfs_kreg deltaN) * dq2 pow 2 <= deltaN pow 2 /\ dq2 <= deltaN`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= (&1 + inv c) pow (rfs_kreg deltaN) /\
                  (&1 + inv R) pow (rfs_kreg deltaN) <= (&1 + inv c) pow (rfs_kreg deltaN)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < inv c /\ &0 < inv R /\ inv R <= inv c` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`(&1 + inv c) pow (rfs_kreg deltaN)`; `&0`; `dq2:real`; `deltaN:real`]
                 P3H_POW_CLOSE_ARITH) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + inv c) pow (rfs_kreg deltaN) * dq2 pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `{x:real^3 | p3_std_dist g0 x < m}`;
                 `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in)`; `hs:(A)rfs_history`;
                 `T1:real`; `h:real`; `Phi:real^3->A`;
                 `{s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
                       T1 + s * h pow 2 < rfs_horizon (hs:(A)rfs_history)}`;
                 `dq2:real`; `tp:real`; `R:real`; `&1 + eps_in`; `deltaN:real`; `ts:real`]
                P3H_VIEW_CLOSE_RESCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME
    `rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                   (G:real->real^3->real^3^3) = V`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`V:(real->(real^3)topology)#(real->((real^3->bool)#(real^3->real^3))->bool)#
        (real->real^3->real^3^3)`;
     `q:real^3`; `tp:real`; `e:real^3->real^3`; `rfs_view (hs:(A)rfs_history)`; `ts:real`;
     `R * inv(h pow 2)`; `Phi:real^3->A`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC P3_HIST_VIEW_SLICES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `e':real^3->A`) THEN
  REWRITE_TAC[p3_canonv_at] THEN EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[p3_strong_canonv] THEN DISJ1_TAC THEN
  EXISTS_TAC `e':real^3->A` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Shortening an evolving neck, and the lift of the path from               *)
(* y = Phi qy to x (d(x,y) < Ap Q^(-1/2), short in the exit scale by Claim  *)
(* 17.8) to the standard solution: q with Phi q = x.                        *)
(* ========================================================================= *)

let P3H_EVNECK_SHORTEN = prove
 (`!V eps (x:A) t a b e.
     rfs_evolving_neck V eps x t a e /\ &0 < b /\ b <= a
     ==> rfs_evolving_neck V eps x t b e`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `x:A`; `t:real`; `a:real`; `b:real`; `e:real^3->A`] THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_persists; rfs_close_fam; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) (G t) x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck ((TM:real->A topology) t,(AT:real->((A->bool)#(A->real^3))->bool) t)
                          (G t) eps x e` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `t - b / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t) (G t) x` THEN
    ASM_REWRITE_TAC[REAL_ARITH `t - a <= t - b <=> b <= a`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3H_177_LIFT_ARITH = prove
 (`!h Q c Dp tp theta1 eps_n Ap.
     &0 < h /\ &0 < Q /\ &0 < c /\ &0 < Dp /\ c / (&2 * Dp) <= h pow 2 * Q /\
     &0 <= tp /\ tp < theta1 /\ theta1 < &1 /\ &0 < eps_n /\ &0 < Ap /\
     &2 * eps_n * Ap <= sqrt(c / (&2 * Dp)) * sqrt(&1 - theta1)
     ==> Ap * inv(sqrt Q) <= h * sqrt(&1 - tp) / (&2 * eps_n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Q /\ sqrt(c / (&2 * Dp)) <= h * sqrt Q /\
                sqrt(&1 - theta1) <= sqrt(&1 - tp) /\ &0 <= sqrt(c / (&2 * Dp)) /\
                &0 <= sqrt(&1 - theta1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `h * sqrt Q = sqrt(h pow 2 * Q)` SUBST1_TAC THENL
       [REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * sqrt(&1 - tp) / (&2 * eps_n) = (h * sqrt(&1 - tp)) / (&2 * eps_n)`
  SUBST1_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < e ==> &0 < &2 * e`] THEN
  SUBGOAL_THEN `(Ap * inv(sqrt Q)) * (&2 * eps_n) = inv(sqrt Q) * (&2 * eps_n * Ap)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * sqrt(&1 - tp) = inv(sqrt Q) * ((h * sqrt Q) * sqrt(&1 - tp))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(c / (&2 * Dp)) * sqrt(&1 - theta1)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let P3H_177_LIFT = prove
 (`!g0 A0 (top:A topology) atlas (g:A->real^3^3) (Phi:real^3->A) m h (Gt:real^3->real^3^3)
    tp d1 ddx dd0l eps_n x y qy r.
     (!g0 A0 top atlas (g:A->real^3^3) Phi m h G0 s d0 dd gamma qy.
        p3_std_initial g0 A0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
        metric_field (:real^3) G0 /\ &0 <= s /\ s < &1 /\
        inv eps_n < d0 /\ d0 + inv eps_n < m /\ &0 < dd /\ dd <= dd0l /\ dd <= &1 / &2 /\
        (!y. p3_std_dist g0 y < m
             ==> lck_dist2 (rfs_kreg eps_n) G0
                   (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < dd pow 2) /\
        (!x. d0 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps_n
             ==> lck_dist2 (rfs_kreg eps_n)
                   (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) G0 x < dd pow 2) /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
        p3_std_dist g0 qy < d0 /\ gamma(&0) = Phi qy /\
        mfd_length atlas g gamma (&0) (&1) < h * sqrt(&1 - s) / (&2 * eps_n)
        ==> ?q c. p3_std_dist g0 q < d0 + inv eps_n /\ Phi q = gamma(&1) /\
                  mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
                  c(&0) = qy /\ c(&1) = q /\
                  (!t. &0 <= t /\ t <= &1 ==> p3_std_dist g0 (c t) < d0 + inv eps_n) /\
                  mfd_length (open_set_atlas (:real^3)) G0 c (&0) (&1) <=
                  sqrt(&2) / h * mfd_length atlas g gamma (&0) (&1)) /\
     p3_std_initial g0 A0 /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\
     mfd_param top atlas {x | p3_std_dist g0 x < m} Phi /\ &0 < h /\
     metric_field (:real^3) Gt /\ &0 <= tp /\ tp < &1 /\
     inv eps_n < d1 /\ d1 + inv eps_n < m /\ &0 < ddx /\ ddx <= dd0l /\ ddx <= &1 / &2 /\
     (!y. p3_std_dist g0 y < m
          ==> lck_dist2 (rfs_kreg eps_n) Gt
                (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y < ddx pow 2) /\
     (!x. d1 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d1 + inv eps_n
          ==> lck_dist2 (rfs_kreg eps_n)
                (mpullback (p3_std_nc g0 A0) (cylinder_flow tp)) Gt x < ddx pow 2) /\
     y IN mfd_ball (top,atlas) g x r /\ y = Phi qy /\ p3_std_dist g0 qy < d1 /\
     r <= h * sqrt(&1 - tp) / (&2 * eps_n)
     ==> ?q. p3_std_dist g0 q < d1 + inv eps_n /\ Phi q = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LF") STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x r` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `y:A`; `r:real`] APX_DIST_SHORT_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `&1`] MFD_LENGTH_REVERSE) THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
  USE_THEN "LF" (MP_TAC o SPECL
    [`g0:real^3->real^3^3`; `A0:real`; `top:A topology`;
     `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `Phi:real^3->A`; `m:real`;
     `h:real`; `Gt:real^3->real^3^3`; `tp:real`; `d1:real`; `ddx:real`;
     `\t. (gamma:real->A) (&1 - t)`; `qy:real^3`]) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(y:A) = (Phi:real^3->A) qy`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  BETA_TAC THEN REWRITE_TAC[REAL_SUB_REFL] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* The alternatives of Thm 12.32 at (q, t') give a strong                   *)
(* canonical neighbourhood at (x, ts): (1) a cap, (3) and (2) with length   *)
(* at least 1 + eps_in a strong neck; (2) with a shorter length is a        *)
(* hypothesis here (the neck from time 0 reaches back past the surgery).    *)
(* ========================================================================= *)

let P3H_177_CASES = prove
 (`!g0 A0 (G:real->real^3->real^3^3) (hs:(A)rfs_history) T1 ts h (Phi:real^3->A) theta1 dq2
    m tp q x C eps C_in eps_in Kr c delta deltaN eps_n eps1N dd0n dd0r ddx d2 A1 epsp d.
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < m} (rfs_view hs) T1 (inv(h pow 2)) Phi
       {s | &0 <= s /\ s < theta1 /\ T1 + s * h pow 2 <= ts /\
            T1 + s * h pow 2 < rfs_horizon hs} dq2 /\
     &0 < h /\ T1 + tp * h pow 2 = ts /\ ts < rfs_horizon hs /\ &0 < tp /\
     tp < theta1 /\ theta1 <= &1 /\
     p2c_regular_view
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G) /\
     (!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) (G t)) /\
     ((?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G tp) C_in eps_in U Y /\ q IN Y) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
           !z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) \/
      (?e. rfs_evolving_neck
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             eps_in q tp (&1 + eps_in) e)) /\
     (!z U. rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G tp) C_in eps_in z U
            ==> !y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local (open_set_atlas (:real^3))
                               (chart_at (open_set_atlas (:real^3)) y)
                               (\w. mfd_scalar (open_set_atlas (:real^3)) (G tp) z %% G tp w))
                            (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
     (!z. A1 < p3_std_dist g0 z
          ==> lck_dist2 (rfs_kreg epsp) (mpullback (p3_std_nc g0 A0) (cylinder_flow tp)) (G tp) z
              < epsp pow 2) /\
     hausdorff_space (rfs_top_at hs ts) /\
     smooth_manifold_atlas (rfs_top_at hs ts) (rfs_atlas_at hs ts) /\
     riemannian_metric (rfs_atlas_at hs ts) (rfs_metric_at hs ts) /\
     compact_space (rfs_top_at hs ts) /\
     mfd_param (rfs_top_at hs ts) (rfs_atlas_at hs ts) {z | p3_std_dist g0 z < m} Phi /\
     (!y. p3_std_dist g0 y < m
          ==> lck_dist2 (rfs_kreg dq2) (G tp)
                (\z. inv(h pow 2) %% rfs_pullback (rfs_atlas_at hs ts) Phi (rfs_metric_at hs ts) z)
                y <= d) /\
     d < dq2 pow 2 /\
     p3_std_dist g0 q < d2 /\ Phi q = x /\
     &0 < c /\ c <= mfd_scalar (open_set_atlas (:real^3)) (G tp) q /\
     (!G0 q U Y (top:A topology) atlas g h W (Phi:real^3->A) d b.
        metric_field (:real^3) G0 /\
        rfs_cap (euclidean,open_set_atlas (:real^3)) G0 C_in eps_in U Y /\ q IN Y /\
        (!y l. y IN U /\ l <= 2
               ==> lrm_deriv_norm2 l
                     (metric_local (open_set_atlas (:real^3))
                        (chart_at (open_set_atlas (:real^3)) y)
                        (\z. mfd_scalar (open_set_atlas (:real^3)) G0 q %% G0 z))
                     (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr) /\
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ &0 < h /\
        mfd_param top atlas W Phi /\ U SUBSET W /\
        &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) G0 q /\
        (&1 + inv b) pow (rfs_kreg delta) * d < delta pow 2 /\
        (!y. y IN W
             ==> lck_dist2 (rfs_kreg delta) G0
                   (\z. inv(h pow 2) %% rfs_pullback atlas Phi g z) y <= d)
        ==> ?U' Y'. U' SUBSET IMAGE Phi U /\ rfs_cap (top,atlas) g C eps U' Y' /\
                    Phi q IN Y') /\
     (!g0 A0 (Gt:real^3->real^3^3) s m d0 dd C epsc U Y q b.
        p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
        inv eps_n < d0 /\ d0 + inv eps_n < m /\ &0 < dd /\ dd <= dd0n /\
        (!x. d0 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps_n
             ==> lck_dist2 (rfs_kreg eps_n)
                   (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
        rfs_cap (euclidean,open_set_atlas (:real^3)) Gt C epsc U Y /\ q IN Y /\
        p3_std_dist g0 q < d0 /\
        &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
        C * inv(sqrt b) <= sqrt(&1 - s) / (&2 * eps_n)
        ==> U SUBSET {x | p3_std_dist g0 x < d0 + inv eps_n}) /\
     (!g0 A0 (Gt:real^3->real^3^3) s m d0 dd epsn1 q (e:real^3->real^3) b.
        p3_std_initial g0 A0 /\ metric_field (:real^3) Gt /\ &0 <= s /\ s < &1 /\
        inv eps_n < d0 /\ d0 + inv eps_n < m /\ &0 < dd /\ dd <= dd0r /\
        (!x. d0 - inv eps_n < p3_std_dist g0 x /\ p3_std_dist g0 x < d0 + inv eps_n
             ==> lck_dist2 (rfs_kreg eps_n)
                   (mpullback (p3_std_nc g0 A0) (cylinder_flow s)) Gt x < dd pow 2) /\
        rfs_neck (euclidean,open_set_atlas (:real^3)) Gt epsn1 q e /\
        &0 < epsn1 /\ epsn1 <= eps1N /\ p3_std_dist g0 q < d0 /\
        &0 < b /\ b <= mfd_scalar (open_set_atlas (:real^3)) Gt q /\
        (&1 + &1 / &10) * inv(sqrt b) * (inv epsn1 + &5) <= sqrt(&1 - s) / (&2 * eps_n)
        ==> IMAGE e (rfs_neck_dom epsn1) SUBSET {x | p3_std_dist g0 x < d0 + inv eps_n}) /\
     (!V x t e V' t' Q' psi.
        p2c_regular_view (V:(real->(real^3)topology)#
                            (real->((real^3->bool)#(real^3->real^3))->bool)#
                            (real->real^3->real^3^3)) /\
        rfs_evolving_neck V eps_in x t (&1 + eps_in) e /\
        (!s. --(&1 + eps_in) < s /\ s <= &0
             ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                       (rfs_vatlas V' (t' + s / Q')) /\
                 riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                   (rfs_vmetric V' (t' + s / Q'))) /\
        p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps_in))
          (V':(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
              (real->A->real^3^3)) t' Q' psi {s | --(&1 + eps_in) < s /\ s <= &0} deltaN
        ==> ?e'. rfs_strong_neck V' eps (psi x) t' e') /\
     (!e. rfs_evolving_neck
            (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
            eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
          (!z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) /\
          tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q < &1 + eps_in
          ==> p3_canonv_at (rfs_view hs) C eps x ts) /\
     &0 < dq2 /\ &0 < delta /\ dq2 * (&1 + inv c) pow (rfs_kreg delta) <= delta /\
     dq2 * (&1 + inv c) pow (rfs_kreg deltaN) <= deltaN /\
     &0 < eps_n /\ eps_n <= &1 / &4 /\ &0 < ddx /\ ddx <= dd0n /\ ddx <= dd0r /\
     &0 < epsp /\ epsp <= eps_n /\ epsp <= ddx /\
     inv eps_n < d2 /\ d2 + inv eps_n < m /\ A1 + inv eps_n < d2 /\
     &0 < eps_in /\ eps_in <= eps1N /\
     C_in * inv(sqrt c) <= sqrt(&1 - theta1) / (&2 * eps_n) /\
     (&1 + &1 / &10) * inv(sqrt c) * (inv eps_in + &5) <= sqrt(&1 - theta1) / (&2 * eps_n)
     ==> p3_canonv_at (rfs_view hs) C eps x ts`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 <= tp /\ tp < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 - theta1) / (&2 * eps_n) <= sqrt(&1 - tp) / (&2 * eps_n)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < e ==> &0 < &2 * e`] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) ((G:real->real^3->real^3^3) tp)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the neck routine shared by alternatives (2) with long length and (3) *)
  SUBGOAL_THEN
   `!e. rfs_evolving_neck
          (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
          eps_in q tp (&1 + eps_in) e
        ==> p3_canonv_at (rfs_view (hs:(A)rfs_history)) C eps x ts`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3->real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `rfs_neck (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)
                           eps_in q e` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_evolving_neck
          (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
                         (G:real->real^3->real^3^3)) eps_in q tp (&1 + eps_in) e` THEN
      REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
      REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in) SUBSET
                  {z | p3_std_dist g0 z < d2 + inv eps_n}` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `dd0r:real`)) (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`A0:real`; `(G:real->real^3->real^3^3) tp`; `tp:real`; `m:real`;
                            `ddx:real`; `q:real^3`; `c:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3H_SHELL_CLOSE THEN
        MAP_EVERY EXISTS_TAC [`A1:real`; `epsp:real`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC P3H_177_NECK_CASE THEN
    MAP_EVERY EXISTS_TAC
     [`G:real->real^3->real^3^3`; `T1:real`; `h:real`; `Phi:real^3->A`; `theta1:real`;
      `dq2:real`; `m:real`; `g0:real^3->real^3^3`; `tp:real`; `q:real^3`; `eps_in:real`;
      `e:real^3->real^3`; `deltaN:real`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e:real^3->real^3) (rfs_neck_dom eps_in) SUBSET
                 {z | p3_std_dist g0 z < d2 + inv eps_n}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `d2 + inv eps_n` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 MP_TAC (DISJ_CASES_THEN2 MP_TAC MP_TAC) o check (fun th ->
    is_disj(concl th))) THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `Y:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL
     [`g0:real^3->real^3^3`; `A0:real`; `(G:real->real^3->real^3^3) tp`; `tp:real`; `q:real^3`;
      `rfs_top_at (hs:(A)rfs_history) ts`; `rfs_atlas_at (hs:(A)rfs_history) ts`;
      `rfs_metric_at (hs:(A)rfs_history) ts`; `h:real`; `m:real`; `Phi:real^3->A`; `x:A`;
      `C:real`; `eps:real`; `C_in:real`; `eps_in:real`; `Kr:real`; `c:real`; `delta:real`;
      `eps_n:real`; `dd0n:real`; `ddx:real`; `d2:real`; `A1:real`; `epsp:real`; `dq2:real`;
      `d:real`; `U:real^3->bool`; `Y:real^3->bool`] P3H_177_CAP_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y':A->bool` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[p3_canonv_at] THEN EXISTS_TAC `U':A->bool` THEN
    REWRITE_TAC[p3_strong_canonv; P2C_RFS_VIEW_PARTS] THEN DISJ2_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `Y':A->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->real^3` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `&1 + eps_in <=
                   tp * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q`
    THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&1 + eps_in`)) (concl th) &&
        not (can (find_term (fun t -> t = `deltaN:real`)) (concl th)) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_std_dist"))
                 (concl th)))) THEN
      EXISTS_TAC `e:real^3->real^3` THEN MATCH_MP_TAC P3H_EVNECK_SHORTEN THEN
      EXISTS_TAC `tp * mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_std_dist")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_canonv_at")) (concl th))) THEN
      EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_TAC `e:real^3->real^3`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&1 + eps_in`)) (concl th) &&
      not (can (find_term (fun t -> t = `deltaN:real`)) (concl th)) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_std_dist"))
               (concl th)))) THEN
    EXISTS_TAC `e:real^3->real^3` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The numerical facts about the constants of the Lemma 17.7                *)
(* assembly, and the statement of the remaining case (2b) of Thm 12.32: the *)
(* neck from time 0 with normalized length below 1 + eps_in (MT p. 405-406; *)
(* its proof needs the surgery necks to evolve for rescaled time 2).        *)
(* ========================================================================= *)

let P3H_177_NUM_EPSN = prove
 (`!c Dp Ap C_in eps_in theta1.
     &0 < c /\ &0 < Dp /\ &0 < Ap /\ &1 < C_in /\ &0 < eps_in /\ theta1 < &1
     ==> ?eps_n. &0 < eps_n /\ eps_n <= &1 / &4 /\
                 C_in * inv(sqrt c) <= sqrt(&1 - theta1) / (&2 * eps_n) /\
                 (&1 + &1 / &10) * inv(sqrt c) * (inv eps_in + &5) <=
                 sqrt(&1 - theta1) / (&2 * eps_n) /\
                 &2 * eps_n * Ap <= sqrt(c / (&2 * Dp)) * sqrt(&1 - theta1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = sqrt(&1 - theta1)` THEN
  ABBREV_TAC `w1 = C_in * inv(sqrt c)` THEN
  ABBREV_TAC `w2 = (&1 + &1 / &10) * inv(sqrt c) * (inv eps_in + &5)` THEN
  ABBREV_TAC `w3 = &2 * Ap * inv(sqrt(c / (&2 * Dp)))` THEN
  SUBGOAL_THEN `&0 < S /\ &0 < sqrt c /\ &0 < sqrt(c / (&2 * Dp))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < w1 /\ &0 < w2 /\ &0 < w3` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w1"; "w2"; "w3"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x + &5`) THEN ASM_SIMP_TAC[REAL_LT_INV];
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]];
    ALL_TAC] THEN
  ABBREV_TAC `B = &2 * w1 + &2 * w2 + w3 + &1` THEN
  SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &4) (S / B)` THEN
  SUBGOAL_THEN `&0 < S / B` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `min (&1 / &4) (S / B) * B <= S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(S / B) * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `en = min (&1 / &4) (S / B)` THEN
  SUBGOAL_THEN `&0 < en /\ en <= &1 / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "en" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= en * w1 /\ &0 <= en * w2 /\ &0 <= en * w3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < e ==> &0 < &2 * e`] THEN
  UNDISCH_TAC `en * B <= S` THEN EXPAND_TAC "B" THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  SUBGOAL_THEN `&2 * en * Ap = (en * w3) * sqrt(c / (&2 * Dp))` SUBST1_TAC THENL
   [EXPAND_TAC "w3" THEN UNDISCH_TAC `&0 < sqrt(c / (&2 * Dp))` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

let P3H_NUM_DD3C = prove
 (`!A0 D c.
     &1 <= D /\ &0 < c
     ==> ?dd3. &0 < dd3 /\ dd3 <= &1 / &10 /\ A0 + &4 < inv dd3 /\
               &72 * (&1 + D) * dd3 <= c / &2`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (&1 / &10) (min (inv(abs A0 + &5)) (c / (&144 * (&1 + D))))` THEN
  ABBREV_TAC `dd3 = min (&1 / &10) (min (inv(abs A0 + &5)) (c / (&144 * (&1 + D))))` THEN
  SUBGOAL_THEN `&0 < inv(abs A0 + &5) /\ &0 < c / (&144 * (&1 + D))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd3 /\ dd3 <= &1 / &10 /\ dd3 <= inv(abs A0 + &5) /\
                dd3 <= c / (&144 * (&1 + D))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd3" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `abs A0 + &5` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `dd3 <= c / (&144 * (&1 + D))` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= D ==> &0 < &144 * (&1 + D)`] THEN
    REAL_ARITH_TAC]);;

let P3H_NUM_DQ2 = prove
 (`!Kr c delta deltaN eps_n ddx dF dqT.
     &0 <= Kr /\ &0 < c /\ &0 < delta /\ &0 < deltaN /\ &0 < eps_n /\ &0 < ddx /\
     &0 < dF /\ &0 < dqT
     ==> ?dq2. &0 < dq2 /\ dq2 <= &1 / &10 /\ &72 * sqrt Kr * dq2 <= &1 / &2 /\
               dq2 <= dqT /\ dq2 <= eps_n /\ dq2 <= ddx /\ dq2 <= dF /\
               dq2 * (&1 + inv c) pow (rfs_kreg delta) <= delta /\
               dq2 * (&1 + inv c) pow (rfs_kreg deltaN) <= deltaN`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `p1 = (&1 + inv c) pow (rfs_kreg delta)` THEN
  ABBREV_TAC `p2 = (&1 + inv c) pow (rfs_kreg deltaN)` THEN
  SUBGOAL_THEN `&0 < p1 /\ &0 < p2 /\ &0 <= sqrt Kr` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p1"; "p2"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT; MATCH_MP_TAC REAL_POW_LT; MATCH_MP_TAC SQRT_POS_LE] THEN
    TRY(MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < &1 + x`) THEN
        MATCH_MP_TAC REAL_LT_INV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min (min (min (&1 / &10) (inv(&144 * (&1 + sqrt Kr)))) (min dqT eps_n))
                  (min (min ddx dF) (min (delta / p1) (deltaN / p2)))` THEN
  ABBREV_TAC `q = min (min (min (&1 / &10) (inv(&144 * (&1 + sqrt Kr)))) (min dqT eps_n))
                      (min (min ddx dF) (min (delta / p1) (deltaN / p2)))` THEN
  SUBGOAL_THEN `&0 < inv(&144 * (&1 + sqrt Kr)) /\ &0 < delta / p1 /\ &0 < deltaN / p2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q /\ q <= &1 / &10 /\ q <= inv(&144 * (&1 + sqrt Kr)) /\ q <= dqT /\
                q <= eps_n /\ q <= ddx /\ q <= dF /\ q <= delta / p1 /\ q <= deltaN / p2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `q <= inv(&144 * (&1 + sqrt Kr))` THEN
    REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= k ==> &0 < &144 * (&1 + k)`] THEN
    SUBGOAL_THEN `&0 <= sqrt Kr * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `q <= delta / p1` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ];
    UNDISCH_TAC `q <= deltaN / p2` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]);;

let P3H_NUM_RSTAR = prove
 (`!tb. &0 < tb ==> &0 < inv(&8 * (&1 + tb)) /\ tb * inv(&8 * (&1 + tb)) pow 2 <= &1 / &64`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN
  SUBGOAL_THEN `&0 < (&8 * (&1 + tb)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&0 <= tb * tb` MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                                             ASM_REAL_ARITH_TAC]);;

(* The neck-from-time-0 alternative of Thm 12.32 at (q, t') with normalized *)
(* length below 1 + eps_in, as an explicit statement (MT p. 405-406): the   *)
(* strong eps-neck at (x, ts) must reach back past the surgery time.  The  *)
(* bound m on the neck region precedes dF: the surgery control must keep    *)
(* the region inside the surgery neck chart (1/dl > m).                     *)

let P3H_177_FARNECK_STATEMENT = new_definition
 `P3H_177_FARNECK_STATEMENT (u:A->bool) <=>
    ?epsF. &0 < epsF /\
      !eps g0 A0. &0 < eps /\ eps <= epsF /\ p3_std_initial g0 A0
        ==> ?KF. &1 <= KF /\
              !eps_in C hf md i rs ks ds r' m.
                 &0 < eps_in /\ KF * eps_in <= eps /\ &1 < C /\
                 p3_hfun C hf /\ p3_modulus md /\ 1 <= i /\ rs 0 = eps /\
                 p3_seq_upto i rs /\ &0 < r' /\ r' <= rs i
                 ==> ?dF. &0 < dF /\
                       !dlt rs' ks' dd (hs:(A)rfs_history) k j Phi xi ts x G theta1 dq2 tp q e.
                          rs' (SUC i) = r' /\
                          p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                          rfs_canonical_assumption (rfs_trunc (rfs_view hs) ts)
                                                   C eps (p3_stepf rs') /\
                          1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                          p3_cap_param (md,g0,A0)
                            (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd)) hs k j
                            Phi xi /\
                          p3_stepf dd (hs_time hs k) <= dF /\
                          &0 < hs_time hs k /\ hs_time hs k < ts /\ ts < rfs_horizon hs /\
                          x IN topspace(rfs_top_at hs ts) /\
                          p3_std_flow g0 (&1) G /\
                          p3_view_close
                            (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                           {s | &0 <= s /\ s < &1} G)
                            (&0) (&1) {z | p3_std_dist g0 z < m} (rfs_view hs) (hs_time hs k)
                            (inv(p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2))
                            Phi
                            {s | &0 <= s /\ s < theta1 /\
                                 hs_time hs k +
                                 s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k)
                                     pow 2 <= ts /\
                                 hs_time hs k +
                                 s * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k)
                                     pow 2 < rfs_horizon hs}
                            dq2 /\
                          &0 < dq2 /\ dq2 <= dF /\ theta1 < &1 /\
                          hs_time hs k +
                          tp * p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2 =
                          ts /\
                          &0 < tp /\ tp < theta1 /\ Phi q = x /\
                          rfs_evolving_neck
                            (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                           {s | &0 <= s /\ s < &1} G)
                            eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
                          (!z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) /\
                          tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q < &1 + eps_in /\
                          IMAGE e (rfs_neck_dom eps_in) SUBSET {z | p3_std_dist g0 z < m}
                          ==> p3_canonv_at (rfs_view hs) C eps x ts`;;

