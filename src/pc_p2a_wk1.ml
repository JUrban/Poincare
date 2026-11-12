(* ========================================================================= *)
(* Unit pc_p2a_wk1: flow views and chart data for W3                         *)
(* (P2B_REQ_P2A_WEAK_STATEMENT) and FL9.  FL0 at N = 3 (P2AW_FLOW_VIEW_3: |- *)
(* P2A_FLOW_VIEW_STATEMENT u n for n:3->bool): the view of a flow that is    *)
(* complete with bounded curvature is a smooth view setting, open sets are   *)
(* regions, interior times are smooth and the top time is backward-smooth;   *)
(* through the regular-view lemmas of Part 2C (pc_p2c_fview) and the 3-d     *)
(* bridges of pc_p2a_defs.                                                   *)
(* ========================================================================= *)

needs "src/pc_p2a_fldefs.ml";;
needs "src/pc_p2b_w3iface.ml";;
needs "src/pc_p2c_fview.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* FL0 at N = 3.                                                             *)
(* ------------------------------------------------------------------------- *)

(* The bridge P2AB_RMETRIC_VFAM of pc_p2a_brg, copied with its proof because *)
(* the closure of that unit is large.                                        *)

let P2AW_RMETRIC_VFAM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b.
     p2a_rmetric V W b = p2c_vfam V W b`,
  REWRITE_TAC[FUN_EQ_THM; p2a_rmetric; p2c_vfam; P2A_VIEW_PROJ_3]);;

(* The metrics of such a flow are Riemannian at every time of [a,b].        *)

let P2AW_CBFLOW_METRIC = prove
 (`!top atlas a b (g:real->A->real^3^3).
     p2a_cbflow (top,atlas) a b g
     ==> !t. a <= t /\ t <= b
             ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2AF_CBFLOW_3] THEN STRIP_TAC THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "t" with Failure _ -> false)) THEN
  ASM_REAL_ARITH_TAC);;

let P2AW_CBFLOW_REGULAR = prove
 (`!top atlas a b (g:real->A->real^3^3).
     p2a_cbflow (top,atlas) a b g
     ==> p2c_regular_view (rfs_flow_view (top,atlas) (real_interval[a,b]) g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "MET" o MATCH_MP P2AW_CBFLOW_METRIC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [P2AF_CBFLOW_3]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MATCH_MP_TAC P2CF_FLOW_VIEW_REGULAR_GEN THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "MET" (MP_TAC o SPEC `t:real`) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= a' /\ b' <= b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2CF_INTERVAL_LOWER THEN
        MAP_EVERY EXISTS_TAC [`b':real`; `\s:real. s <= b`] THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `b':real = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CF_RFU_LEFT THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REAL_ARITH_TAC]);;

(* Open sets of M persist on every subinterval of [a,b] and are regions.    *)

let P2AW_CBFLOW_REGION = prove
 (`!top atlas a b (g:real->A->real^3^3) W a' b'.
     p2a_cbflow (top,atlas) a b g /\ open_in top W /\ a <= a' /\ a' < b' /\ b' <= b
     ==> p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b]) g) W a' b'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AW_CBFLOW_REGULAR) THEN
  REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "VF")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "DF") (K ALL_TAC))))) THEN
  SUBGOAL_THEN
   `rfs_persists (rfs_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) W a' b'`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfs_flow_view; rfs_persists] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s IN real_interval[a,b]` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o MATCH_MP P2AW_CBFLOW_METRIC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P2A_FLOW_VIEW_3; p2a_region; P2A_PERSISTS_3; P2A_VIEW_PROJ_3;
              P2AW_RMETRIC_VFAM; P2A_FLOW_UPTO_3] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "DF" (MP_TAC o SPECL [`W:A->bool`; `a':real`; `b':real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "VF" (MP_TAC o SPECL [`W:A->bool`; `a':real`; `b':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[p2c_vflow]]]);;

(* FL0 at N = 3.                                                             *)

let P2AW_FLOW_VIEW_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_VIEW_STATEMENT u n`,
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `n:3->bool`] THEN
  REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                       `g:real->A->real^3^3`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `a < b /\ smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                hausdorff_space top`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[P2AF_CBFLOW_3; ricci_flow_from; ricci_flow_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2a_svs; p2a_flow_view; p2a_vtop; p2a_vatlas; p2a_vmetric] THEN
    X_GEN_TAC `t:real` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_DISCRETE_TOPOLOGY; TOPSPACE_DISCRETE_TOPOLOGY] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o MATCH_MP P2AW_CBFLOW_METRIC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_REAL_INTERVAL]; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2a_smooth] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`topspace top:A->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL];
    REWRITE_TAC[p2a_bsmooth] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`topspace top:A->bool`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2AW_CBFLOW_REGION THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL]]);;

