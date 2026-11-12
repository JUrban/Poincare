(* ========================================================================= *)
(* pc_soul_ball: a step towards the topology at a soul (piece (c) of the     *)
(* statements of pc_p2b_c994req for MT Cor 9.94). At a soul p of a complete  *)
(* connected Riemannian manifold (every other point regular for d_p, the     *)
(* output of CMP_R5_SOUL) every compact set lies in the unit ball of a ball  *)
(* chart b with b(0) = p (SOULB_BIG_BALL).                                   *)
(* Route: a normal ball chart phi at p (geodesics layer); the regular field  *)
(* Z of CMP_R6 on a closed annulus about p, cut off by chi                  *)
(* (MFD_SMOOTH_CUTOFF); the flow Phi of chi Z (MFLOW_GEN); along its lines  *)
(* d_p grows at rate c where chi = 1 (CMP_R7, with the generic flow-line    *)
(* lemma SOULB_FLOWLINE_C1), so the backward flow over a long time T brings *)
(* the compact set into the normal ball of radius delta, and                *)
(* b = Phi_T o phi o (delta %) (MFD_PARAM_COMPOSE_DIFFEO).                   *)
(* ========================================================================= *)

needs "src/pc_cmp_regf.ml";;
needs "src/pc_cmp_fvar.ml";;
needs "src/pc_mfd_flow.ml";;
needs "src/pc_mfd_cflow.ml";;
needs "src/pc_mfd_cutoff.ml";;
needs "src/pc_smt_glue.ml";;
needs "src/pc_geo_normal.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_geo_lisom.ml";;
needs "src/pc_geo_jacobi.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_smt_radial.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Flow lines of mfl_hyp fields (pc_mfd_flow) are C^1 curves.               *)
(* For s in J the flow line r |-> mfl_flow X s (lift r) x is an             *)
(* mfd_c1_curve on every [a,b] with lift a, lift b in J, and its velocity    *)
(* at time t (preferred coordinates) is X t at the point.                   *)
(* ------------------------------------------------------------------------- *)

let SOULB_FLOWLINE_C1 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J K s x a b.
     mfl_hyp top atlas X J K /\ s IN J /\ x IN topspace top /\ a <= b /\
     lift a IN J /\ lift b IN J
     ==> mfd_c1_curve (top,atlas) (\r. mfl_flow top atlas X s (lift r) x) a b /\
         (!t. a < b /\ a <= t /\ t <= b
              ==> mfd_velocity atlas (\r. mfl_flow top atlas X s (lift r) x) a b t =
                  X t (mfl_flow top atlas X s (lift t) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hausdorff_space (top:A topology) /\
                smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
                is_interval (J:real^1->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfl_hyp]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[lift a,lift b] SUBSET (J:real^1->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [IS_INTERVAL_1]) THEN
    MAP_EVERY EXISTS_TAC [`lift a`; `lift b`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`] MFLOW_GEN) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "COC")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "DER") (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `mfl_flow top atlas (X:real->A->real^N) s (lift a) (x:A) IN topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_IN THEN MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`; `lift a`; `lift b`;
                 `mfl_flow top atlas (X:real->A->real^N) s (lift a) (x:A)`] MFL_FLOW_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->A` (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  REWRITE_TAC[SEGMENT_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!r. a <= r /\ r <= b
                    ==> mfl_flow top atlas (X:real->A->real^N) s (lift r) (x:A) = gam(lift r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `lift r IN interval[lift a,lift b]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mfl_flow top atlas (X:real->A->real^N) (lift a) (lift r)
                  (mfl_flow top atlas X s (lift a) (x:A))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "COC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(gam:real^1->A)(lift a)`)) THEN
      MATCH_MP_TAC MFL_FLOW_CURVE THEN
      MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`; `interval[lift a,lift b]`] THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                  (\r. mfl_flow top atlas (X:real->A->real^N) s (lift r) (x:A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `(gam:real^1->A) o lift` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL; o_THM] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (interval[lift a,lift b])` THEN CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_LIFT];
          REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IMAGE_LIFT_REAL_INTERVAL;
                      SUBSET_REFL]];
        UNDISCH_TAC `mfl_curve top atlas (X:real->A->real^N) (interval[lift a,lift b]) gam` THEN
        SIMP_TAC[mfl_curve]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c r. c IN atlas /\ r IN interval[lift a,lift b] /\
          mfl_flow top atlas (X:real->A->real^N) s r (x:A) IN FST c
          ==> ((\r'. SND c (mfl_flow top atlas X s r' x)) has_vector_derivative
               mfd_vrep atlas (X (drop r)) c (SND c (mfl_flow top atlas X s r x))) (at r)`
  (LABEL_TAC "DLEM") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "DER" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[mfd_c1_curve; LIFT_DROP] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
    EXISTS_TAC `\(r:real^1) (h:real^1). drop h % mfd_vrep atlas ((X:real->A->real^N) (drop r)) c
                  (SND c (mfl_flow top atlas X s r (x:A)))` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM has_vector_derivative] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `h:real^1` THEN REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      SUBGOAL_THEN
       `(\r:real^1. mfd_vrep atlas ((X:real->A->real^N) (drop r)) c
                      (SND c (mfl_flow top atlas X s r (x:A)))) =
        mfl_field atlas X c o (\r. pastecart r (SND c (mfl_flow top atlas X s r x)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MFL_FIELD_PASTECART]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[differentiable_on; IN_ELIM_THM] THEN X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
        MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
        REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `\h:real^1. drop h % mfd_vrep atlas ((X:real->A->real^N) (drop r)) c
                      (SND c (mfl_flow top atlas X s r (x:A)))` THEN
        REWRITE_TAC[GSYM has_vector_derivative] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(J:real^1->bool) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                         `c:(A->bool)#(A->real^N)`] MFL_HYP_CHART) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; PASTECART_IN_PCROSS] THEN
          X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
           [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]]]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[mfd_velocity; LIFT_DROP] THEN
  SUBGOAL_THEN `mfl_flow top atlas (X:real->A->real^N) s (lift t) (x:A) IN topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_IN THEN MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lift t IN interval[lift a,lift b]` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfl_flow top atlas (X:real->A->real^N) s (lift t) (x:A)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                     (mfl_flow top atlas (X:real->A->real^N) s (lift t) (x:A))` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mfd_vrep atlas ((X:real->A->real^N) (drop(lift t))) c0
                (SND c0 (mfl_flow top atlas X s (lift t) (x:A)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    REMOVE_THEN "DLEM" (MP_TAC o SPECL [`c0:(A->bool)#(A->real^N)`; `lift t`]) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
    REWRITE_TAC[LIFT_DROP] THEN EXPAND_TAC "c0" THEN
    MATCH_MP_TAC MCF_VREP_AT THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A field Z smooth (in chart representation) on an open set W,              *)
(* cut off by a smooth chi that vanishes off a compact L inside W, is an    *)
(* mfl_hyp field on the whole time line, with support L.                    *)
(* ------------------------------------------------------------------------- *)

let SOULB_CUTOFF_VREP_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (chi:A->real) W L c.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
     c IN atlas /\
     smooth_map_on (IMAGE (SND c) (FST c INTER W)) (mfd_vrep atlas Z c) /\
     mfd_smooth atlas (\x. lift(chi x)) /\
     compact_in top L /\ L SUBSET W /\ (!x. x IN topspace top DIFF L ==> chi x = &0)
     ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas (\x. chi x % Z x) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed_in top (L:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] MCF_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `chart_inv (c:(A->bool)#(A->real^N)) y IN W` THENL
   [EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\y:real^N. drop(((\x:A. lift(chi x)) o chart_inv (c:(A->bool)#(A->real^N))) y) %
                             mfd_vrep atlas (Z:A->real^N) c y` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MCF_VREP_CMUL THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
        SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[ETA_AX] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
          EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
          CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(chi x))` THEN
          REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]];
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER (topspace top DIFF L))` THEN
    SUBGOAL_THEN `~(chart_inv (c:(A->bool)#(A->real^N)) y IN L)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
      REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN
      EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. vec 0:real^N` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (u:A)) = u` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(chi:A->real) u = &0` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      BETA_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFL_VREP_ZERO THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[]]]);;

let SOULB_CUTOFF_HYP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) (chi:A->real) W L.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open_in top W /\
     (!c. c IN atlas
          ==> smooth_map_on (IMAGE (SND c) (FST c INTER W)) (mfd_vrep atlas Z c)) /\
     mfd_smooth atlas (\x. lift(chi x)) /\
     compact_in top L /\ L SUBSET W /\ (!x. x IN topspace top DIFF L ==> chi x = &0)
     ==> mfl_hyp top atlas (\t:real x. chi x % Z x) (:real^1) L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mfl_hyp; OPEN_UNIV; IS_INTERVAL_UNIV; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    REWRITE_TAC[mfl_field] THEN MATCH_MP_TAC MFL_SMOOTH_SNDCART THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SOULB_CUTOFF_VREP_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `W:A->bool`; `L:A->bool`] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Along a flow line of chi Z, where Z is a regular field as                *)
(* given by CMP_R6 on W (unit, at an obtuse angle with every minimal        *)
(* direction to p) and 0 <= chi vanishes off L inside W, d_p increases by   *)
(* at least c times the length (CMP_R7); the speed is chi.                 *)
(* ------------------------------------------------------------------------- *)

let SOULB_CUTOFF_ANGLE = prove
 (`!(g:B->real^3^3) (Z:B->real^3) (chi:B->real) W L c x v d.
     L SUBSET W /\ &0 <= chi x /\ (~(x IN L) ==> chi x = &0) /\ &0 < c /\
     (x IN W ==> Z x dot (g x ** Z x) = &1) /\
     (x IN W ==> Z x dot (g x ** v) <= --c * d) /\ &0 <= d
     ==> (chi x % Z x) dot (g x ** v) <=
         --c * sqrt((chi x % Z x) dot (g x ** (chi x % Z x))) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ASM_CASES_TAC `(x:B) IN W` THENL
   [SUBGOAL_THEN `(Z:B->real^3) x dot ((g:B->real^3^3) x ** Z x) = &1` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID; GSYM REAL_POW_2] THEN
    ASM_SIMP_TAC[POW_2_SQRT] THEN
    SUBGOAL_THEN `(Z:B->real^3) x dot ((g:B->real^3^3) x ** v) <= --c * d` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `chi * z <= chi * (--c * d) ==> chi * z <= --c * chi * d`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(chi:B->real) x = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; SQRT_0; REAL_MUL_RZERO; REAL_LE_REFL]]);;

let SOULB_FLOW_MONO = prove
 (`!top atlas (g:B->real^3^3) p (Z:B->real^3) (chi:B->real) W L c y a b.
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     mfl_hyp top atlas (\t:real x. chi x % Z x) (:real^1) L /\
     L SUBSET W /\ (!x. &0 <= chi x) /\ (!x. x IN topspace top DIFF L ==> chi x = &0) /\
     &0 < c /\
     (!x. x IN W ==> Z x dot (g x ** Z x) = &1) /\
     (!x v. x IN W /\ v IN mfd_exp_dom (top,atlas) g x /\
            mfd_exp (top,atlas) g x v = p /\
            mfd_tnorm g x v = mfd_dist (top,atlas) g x p
            ==> Z x dot (g x ** v) <= --c * mfd_tnorm g x v) /\
     y IN topspace top /\ a <= b
     ==> mfd_dist (top,atlas) g p
           (mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift a) y) +
         c * mfd_length atlas g
               (\r. mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift r) y) a b
         <= mfd_dist (top,atlas) g p
              (mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift b) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                       (lift(&0)) (lift r) (y:B) IN topspace top` (LABEL_TAC "FIN") THENL
   [GEN_TAC THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`(:real^1)`; `L:B->bool`] THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = b`)) THEN
    REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
   [UNDISCH_TAC `a <= b` THEN UNDISCH_TAC `~(a:real = b)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t:real x. (chi:B->real) x % (Z:B->real^3) x`; `(:real^1)`; `L:B->bool`;
                 `lift(&0)`; `y:B`; `a:real`; `b:real`] SOULB_FLOWLINE_C1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "VEL")) THEN
  MP_TAC(REWRITE_RULE[CMP_R7_FIRST_VARIATION_STATEMENT]
           (ISPEC `UNIV:B->bool` CMP_R7_FIRST_VARIATION)) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `p:B`;
     `\r. mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                    (lift(&0)) (lift r) (y:B)`; `a:real`; `b:real`; `c:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_speed] THEN
    USE_THEN "VEL" (fun th -> MP_TAC(MP (SPEC `t:real` th)
      (CONJ (ASSUME `a < b`) (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`))))) THEN
    BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SOULB_CUTOFF_ANGLE THEN
    MAP_EVERY EXISTS_TAC [`W:B->bool`; `L:B->bool`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN topspace top DIFF L ==> (chi:B->real) x = &0`) (concl th))) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN W ==> (Z:B->real^3) x dot ((g:B->real^3^3) x ** Z x) = &1`) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x v. x IN W /\ v IN mfd_exp_dom (top,atlas) (g:B->real^3^3) x /\
               mfd_exp (top,atlas) g x v = (p:B) /\
               mfd_tnorm g x v = mfd_dist (top,atlas) g x p
               ==> (Z:B->real^3) x dot (g x ** v) <= --c * mfd_tnorm g x v`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        can (term_match [] `mfd_tnorm (g:B->real^3^3) x v`) (lhs(concl th)))) THEN
      MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Small facts. A normal ball chart at p whose images of the balls of radius *)
(* r <= r0 are the metric balls; d_p is bounded on compact sets (the         *)
(* statement of APXT_COMPACT_BOUNDED in pc_apx_twoends.ml, which this file   *)
(* does not load); the closed metric annuli about p are compact in a         *)
(* complete connected manifold.                                              *)
(* ------------------------------------------------------------------------- *)

let SOULB_NORMAL = prove
 (`!top atlas (g:A->real^N^N) (p:A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ p IN topspace top
     ==> ?E r0. &0 < r0 /\
                !r. &0 < r /\ r <= r0
                    ==> mfd_param top atlas (ball(vec 0,r))
                                  (\w. mfd_exp (top,atlas) g p (E ** w)) /\
                        IMAGE (\w. mfd_exp (top,atlas) g p (E ** w)) (ball(vec 0,r)) =
                        mfd_ball (top,atlas) g p r /\
                        mfd_exp (top,atlas) g p (E ** vec 0) = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_orthonormal_frame (g:A->real^N^N) p E` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_orthonormal_frame]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] MFD_EXP_LOCAL_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `E:real^N^N`] MFD_NORMAL_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`E:real^N^N`; `min r1 r2`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `E:real^N^N`; `r:real`] GEON_NORMAL_PARAM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_INJ_BALL_MONO THEN
      EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_normal_chart; FST; SND] THEN SIMP_TAC[];
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

let SOULB_COMPACT_DIST_BOUND = prove
 (`!top atlas (g:A->real^N^N) K x0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?D. !k. k IN K ==> mfd_dist (top,atlas) g x0 k <= D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`] MFD_DIST_CONTINUOUS_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`;
                 `\y:A. mfd_dist (top,atlas) (g:A->real^N^N) x0 y`; `K:A->bool`]
                IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SOULB_ANNULUS_COMPACT = prove
 (`!top atlas (g:A->real^N^N) (p:A) r R.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top
     ==> compact_in top {x | x IN topspace top /\ r <= mfd_dist (top,atlas) g p x /\
                             mfd_dist (top,atlas) g p x <= R}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) p R` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_HOPF_RINOW_POINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`] MFD_DIST_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{x | x IN topspace top /\ r <= mfd_dist (top,atlas) (g:A->real^N^N) p x /\
                       mfd_dist (top,atlas) g p x <= R} =
                  {x | x IN topspace top /\
                       (\y:A. mfd_dist (top,atlas) g p y) x IN real_interval[r,R]}`
    SUBST1_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL; EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* The backward flow.  If the flow line from y ends after time              *)
(* T0 at a point with d_p <= R, where R < c T0, and chi = 1 on every point  *)
(* with de <= d_p <= R, then d_p(y) < de: otherwise the whole line has      *)
(* speed 1 and d_p grows by c T0 along it (SOULB_FLOW_MONO).               *)
(* ------------------------------------------------------------------------- *)

let SOULB_BACKFLOW = prove
 (`!top atlas (g:B->real^3^3) p (Z:B->real^3) (chi:B->real) W L A c T0 de R y.
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     mfl_hyp top atlas (\t:real x. chi x % Z x) (:real^1) L /\
     L SUBSET W /\ (!x. &0 <= chi x) /\ (!x. x IN topspace top DIFF L ==> chi x = &0) /\
     (!x. x IN A ==> chi x = &1) /\ A SUBSET W /\
     (!x. x IN topspace top /\ de <= mfd_dist (top,atlas) g p x /\
          mfd_dist (top,atlas) g p x <= R ==> x IN A) /\
     &0 < c /\ &0 < T0 /\ R < c * T0 /\
     (!x. x IN W ==> Z x dot (g x ** Z x) = &1) /\
     (!x v. x IN W /\ v IN mfd_exp_dom (top,atlas) g x /\
            mfd_exp (top,atlas) g x v = p /\
            mfd_tnorm g x v = mfd_dist (top,atlas) g x p
            ==> Z x dot (g x ** v) <= --c * mfd_tnorm g x v) /\
     y IN topspace top /\
     mfd_dist (top,atlas) g p
       (mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift T0) y) <= R
     ==> mfd_dist (top,atlas) g p y < de`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!r. mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                       (lift(&0)) (lift r) (y:B) IN topspace top` (LABEL_TAC "FIN") THENL
   [GEN_TAC THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`(:real^1)`; `L:B->bool`] THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                  (lift(&0)) (lift(&0)) (y:B) = y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\t:real x. (chi:B->real) x % (Z:B->real^3) x`; `(:real^1)`; `L:B->bool`]
      MFLOW_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a <= b
          ==> &0 <= c * mfd_length atlas (g:B->real^3^3)
                          (\r. mfl_flow top atlas
                                 (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                                 (lift(&0)) (lift r) (y:B)) a b`
  (LABEL_TAC "CL") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\t:real x. (chi:B->real) x % (Z:B->real^3) x`; `(:real^1)`; `L:B->bool`;
                   `lift(&0)`; `y:B`; `a:real`; `b:real`] SOULB_FLOWLINE_C1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a <= b
          ==> mfd_dist (top,atlas) (g:B->real^3^3) p
                (mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                   (lift(&0)) (lift a) (y:B)) +
              c * mfd_length atlas g
                    (\r. mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift r) y) a b
              <= mfd_dist (top,atlas) g p
                   (mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift b) y)`
  (LABEL_TAC "MONO") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SOULB_FLOW_MONO THEN
    MAP_EVERY EXISTS_TAC [`W:B->bool`; `L:B->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. &0 <= r /\ r <= T0
        ==> mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
              (lift(&0)) (lift r) (y:B) IN A`
  (LABEL_TAC "INA") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "MONO" (fun th -> MP_TAC(MP (SPECL [`&0`; `r:real`] th) (ASSUME `&0 <= r`))) THEN
    USE_THEN "CL" (fun th -> MP_TAC(MP (SPECL [`&0`; `r:real`] th) (ASSUME `&0 <= r`))) THEN
    USE_THEN "MONO" (fun th -> MP_TAC(MP (SPECL [`r:real`; `T0:real`] th) (ASSUME `r <= T0`))) THEN
    USE_THEN "CL" (fun th -> MP_TAC(MP (SPECL [`r:real`; `T0:real`] th) (ASSUME `r <= T0`))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x. x IN topspace top /\ de <= mfd_dist (top,atlas) (g:B->real^3^3) p x /\
           mfd_dist (top,atlas) g p x <= R ==> x IN (A:B->bool)`) (concl th))) THEN
    USE_THEN "FIN" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:B->real^3^3)
      (\r. mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
             (lift(&0)) (lift r) (y:B)) (&0) T0 = T0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\t:real x. (chi:B->real) x % (Z:B->real^3) x`; `(:real^1)`; `L:B->bool`;
                   `lift(&0)`; `y:B`; `&0`; `T0:real`] SOULB_FLOWLINE_C1) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[IN_UNIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "VEL" o CONJUNCT2) THEN
    REWRITE_TAC[mfd_length] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `real_integral (real_interval[&0,T0]) (\r. &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `r:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN
      USE_THEN "VEL" (fun th -> MP_TAC(MP (SPEC `r:real` th)
        (CONJ (ASSUME `&0 < T0`) (CONJ (ASSUME `&0 <= r`) (ASSUME `r <= T0`))))) THEN
      BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "INA" (fun th -> ASSUME_TAC(MP (SPEC `r:real` th)
        (CONJ (ASSUME `&0 <= r`) (ASSUME `r <= T0`)))) THEN
      SUBGOAL_THEN
       `(chi:B->real) (mfl_flow top atlas (\t:real x. chi x % (Z:B->real^3) x)
                         (lift(&0)) (lift r) (y:B)) = &1` SUBST1_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!x. x IN (A:B->bool) ==> (chi:B->real) x = &1`) (concl th))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN
      SUBGOAL_THEN
       `(Z:B->real^3) (mfl_flow top atlas (\t:real x. (chi:B->real) x % Z x)
                         (lift(&0)) (lift r) (y:B)) dot
        ((g:B->real^3^3) (mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift r) y) **
         Z (mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift r) y)) = &1`
      SUBST1_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!x. x IN W ==> (Z:B->real^3) x dot ((g:B->real^3^3) x ** Z x) = &1`) (concl th))) THEN
        ASM SET_TAC[];
        REWRITE_TAC[SQRT_1]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "MONO" (fun th -> MP_TAC(MP (SPECL [`&0`; `T0:real`] th)
    (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < T0`)))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `y:B`] MFD_DIST_POS_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The big ball at a soul (SOULB_BIG_BALL).                                 *)
(* ------------------------------------------------------------------------- *)

let SOULB_BIG_BALL = prove
 (`!top atlas (g:B->real^3^3) p K.
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     compact_in top K
     ==> ?b. mfd_ball_chart top atlas b /\ b(vec 0) = p /\
             K SUBSET IMAGE b (ball(vec 0,&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `p:B`] SOULB_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3^3` (X_CHOOSE_THEN `r0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NOR")))) THEN
  ABBREV_TAC `de = r0 / &4` THEN
  SUBGOAL_THEN `&0 < de /\ &2 * de <= r0 /\ de <= r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "de" THEN UNDISCH_TAC `&0 < r0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* a bound R for d_p on K *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `K:B->bool`; `p:B`] SOULB_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `R0:real`) THEN
  ABBREV_TAC `R = abs R0 + &1` THEN
  SUBGOAL_THEN `&0 < R /\ !k. k IN K ==> mfd_dist (top,atlas) (g:B->real^3^3) p k <= R`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:B` o check (fun th -> can (term_match []
      `!k. k IN K ==> mfd_dist (top,atlas) (g:B->real^3^3) p k <= R0`) (concl th))) THEN
    REWRITE_TAC[ASSUME `(k:B) IN K`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the closed annulus A and the regular field on it *)
  ABBREV_TAC `A = {x | x IN topspace top /\
                       de / &2 <= mfd_dist (top,atlas) (g:B->real^3^3) p x /\
                       mfd_dist (top,atlas) g p x <= R}` THEN
  SUBGOAL_THEN `compact_in top (A:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC SOULB_ANNULUS_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:B. x IN A ==> x IN topspace top /\ ~(x = p)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `de / &2 <= mfd_dist (top,atlas) (g:B->real^3^3) p p` THEN
    ASM_SIMP_TAC[MFD_DIST_REFL] THEN UNDISCH_TAC `&0 < de` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[CMP_R6_REGULAR_FIELD_STATEMENT]
           (ISPEC `UNIV:B->bool` CMP_R6_REGULAR_FIELD)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `g:B->real^3^3`; `p:B`; `A:B->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) (g:B->real^3^3) p x`)
        (concl th))) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:B->bool` (X_CHOOSE_THEN `Z:B->real^3` (X_CHOOSE_THEN `c:real`
    STRIP_ASSUME_TAC))) THEN
  (* the cut-off *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`] MFD_DIST_CONTINUOUS_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `W' = W INTER {x | x IN topspace top /\
                                mfd_dist (top,atlas) (g:B->real^3^3) p x IN {t | t > de / &4}}` THEN
  SUBGOAL_THEN `open_in top (W':B->bool) /\ (A:B->bool) SUBSET W' /\ W' SUBSET W /\ ~(p IN W')`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `euclideanreal` THEN
      ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_GT];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:B) IN A` THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[real_gt] THEN
      UNDISCH_TAC `&0 < de` THEN
      UNDISCH_TAC `de / &2 <= mfd_dist (top,atlas) (g:B->real^3^3) p x` THEN
      REAL_ARITH_TAC;
      SET_TAC[];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN ASM_SIMP_TAC[MFD_DIST_REFL] THEN
      UNDISCH_TAC `&0 < de` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `A:B->bool`; `W':B->bool`] MFD_SMOOTH_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:B->real` (X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `L:B->bool`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(L:B->bool) SUBSET W /\ ~(p IN L) /\ (!x. &0 <= (chi:B->real) x) /\
                (!x. x IN A ==> chi x = &1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfl_hyp top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x) (:real^1) L`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SOULB_CUTOFF_HYP THEN EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the flow and its properties *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t:real x. (chi:B->real) x % (Z:B->real^3) x`; `(:real^1)`; `L:B->bool`]
    MFLOW_GEN) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "REFL") (CONJUNCTS_THEN2 (LABEL_TAC "COC")
    (CONJUNCTS_THEN2 (LABEL_TAC "DIF") (CONJUNCTS_THEN2 (LABEL_TAC "OFF") (K ALL_TAC))))) THEN
  ABBREV_TAC `T0 = R / c + &1` THEN
  SUBGOAL_THEN `&0 < T0 /\ R < c * T0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN
    SUBGOAL_THEN `&0 < R / c` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    CONJ_TAC THENL [UNDISCH_TAC `&0 < R / c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the backward flow brings K into the normal ball of radius de *)
  SUBGOAL_THEN
   `!x:B. x IN K
          ==> mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                (lift T0) (lift(&0)) x IN mfd_ball (top,atlas) (g:B->real^3^3) p de`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
    ABBREV_TAC `y = mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                      (lift T0) (lift(&0)) (x:B)` THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN MATCH_MP_TAC MFL_FLOW_IN THEN
      MAP_EVERY EXISTS_TAC [`(:real^1)`; `L:B->bool`] THEN ASM_REWRITE_TAC[IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                    (lift(&0)) (lift T0) (y:B) = x` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN
      USE_THEN "COC" (fun th -> REWRITE_TAC[MP (SPECL [`lift T0`; `lift(&0)`; `lift T0`; `x:B`] th)
        (ASSUME `(x:B) IN topspace top`)]) THEN
      USE_THEN "REFL" (fun th -> REWRITE_TAC[MP (SPECL [`lift T0`; `x:B`] th)
        (ASSUME `(x:B) IN topspace top`)]);
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) p (x:B) <= R` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!k. k IN K ==> mfd_dist (top,atlas) (g:B->real^3^3) p k <= R`) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!z:B. z IN topspace top /\ de <= mfd_dist (top,atlas) (g:B->real^3^3) p z /\
                        mfd_dist (top,atlas) g p z <= R ==> z IN A` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < de` THEN
      UNDISCH_TAC `de <= mfd_dist (top,atlas) (g:B->real^3^3) p z` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SOULB_BACKFLOW THEN
    MAP_EVERY EXISTS_TAC [`Z:B->real^3`; `chi:B->real`; `W:B->bool`; `L:B->bool`;
                          `A:B->bool`; `c:real`; `T0:real`; `R:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the ball chart *)
  EXISTS_TAC `\w:real^3. mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                           (lift(&0)) (lift T0)
                           (mfd_exp (top,atlas) (g:B->real^3^3) p (E ** (de % w)))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN
    SUBGOAL_THEN
     `(\w:real^3. mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                    (lift(&0)) (lift T0)
                    (mfd_exp (top,atlas) (g:B->real^3^3) p (E ** (de % w)))) =
      mfl_flow top atlas (\t:real x. chi x % Z x) (lift(&0)) (lift T0) o
      ((\w. mfd_exp (top,atlas) g p (E ** w)) o (\w:real^3. de % w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `topspace top:B->bool`; `topspace top:B->bool`;
                          `mfl_flow top atlas (\t:real x. (chi:B->real) x % (Z:B->real^3) x)
                             (lift T0) (lift(&0))`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_param top atlas (ball(vec 0,&2))
                    ((\w. mfd_exp (top,atlas) (g:B->real^3^3) p ((E:real^3^3) ** w)) o
                     (\w:real^3. de % w))` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2 * de)`; `ball(vec 0:real^3,de * &2)`;
                            `\w:real^3. inv de % w`] THEN
      ASM_SIMP_TAC[SMT_DIFFEO_SCALING_BALL] THEN CONJ_TAC THENL
       [USE_THEN "NOR" (MP_TAC o SPEC `&2 * de`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < de` THEN REAL_ARITH_TAC;
                        SIMP_TAC[]];
        REWRITE_TAC[REAL_MUL_SYM; SUBSET_REFL]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `ball(vec 0:real^3,&2)`;
                   `(\w. mfd_exp (top,atlas) (g:B->real^3^3) p ((E:real^3^3) ** w)) o
                    (\w:real^3. de % w)`] MFD_PARAM_MAPS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    USE_THEN "NOR" (fun th -> MP_TAC(MP (SPEC `de:real` th)
      (CONJ (ASSUME `&0 < de`) (ASSUME `de <= r0`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "OFF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o check (fun th -> can (term_match []
      `!x:B. x IN K ==> mfl_flow top atlas (X:real->B->real^3) (s:real^1) (t:real^1) x IN
                         mfd_ball (top,atlas) (g:B->real^3^3) p (r:real)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "NOR" (fun th -> MP_TAC(MP (SPEC `de:real` th)
      (CONJ (ASSUME `&0 < de`) (ASSUME `de <= r0`)))) THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv de % w0:real^3` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      USE_THEN "COC" (fun th -> REWRITE_TAC[MP (SPECL [`lift T0`; `lift(&0)`; `lift T0`; `x:B`] th)
        (ASSUME `(x:B) IN topspace top`)]) THEN
      USE_THEN "REFL" (fun th -> REWRITE_TAC[MP (SPECL [`lift T0`; `x:B`] th)
        (ASSUME `(x:B) IN topspace top`)]);
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_MUL_LID]]]);;

