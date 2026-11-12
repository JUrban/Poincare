(* ========================================================================= *)
(* Unit pc_p2c_hreg (Part 2C): P2C_HISTORY_REGULAR without hypotheses.  The  *)
(* views of surgery histories are regular: conjunct 1 of p2c_regular_view    *)
(* (Hausdorff, smooth and riemannian nonempty slices) is the p2a_svs clause  *)
(* of P2AB_HIST_VIEW_X (unit pc_p2a_brg), conjuncts 2, 3 and 4 are           *)
(* P2AH_P2C_REGIONS_THM (unit pc_p2a_hreg), and conjunct 5 is the            *)
(* from-smoothness of history views (P2CY_HIST_FROM_SMOOTH).  With           *)
(* P2CW_THM_5_11 (unit pc_p2c_fl511) this gives MT Thm 5.11 without          *)
(* hypotheses.                                                               *)
(* ========================================================================= *)

needs "src/pc_p2a_brg.ml";;
needs "src/pc_p2c_fl511.ml";;
needs "src/pc_p2c_vfrom.ml";;

prioritize_real();;
type_invention_error := true;;

let P2CY_VIEW_ACCESSORS = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2a_vtop V = rfs_vtop V /\ p2a_vatlas V = rfs_vatlas V /\
     p2a_vmetric V = rfs_vmetric V`,
  REWRITE_TAC[FORALL_PAIR_THM; p2a_vtop; p2a_vatlas; p2a_vmetric;
              rfs_vtop; rfs_vatlas; rfs_vmetric]);;


(* ------------------------------------------------------------------------- *)
(* The from-smoothness of history views (conjunct 5 of p2c_regular_view,     *)
(* p2cz_from_smooth of unit pc_p2c_vfrom):                                   *)
(* a nonempty W open at a lives in a stage k; the identity is a diffeo from *)
(* a to a time s in (a,b] of the same stage (P2AH_STAGE_DIFFEO) and from s  *)
(* to b (P2AH_DIFFEO_CHAIN).                                                 *)
(* ------------------------------------------------------------------------- *)

let P2CY_HIST_FROM_SMOOTH = prove
 (`!hs:(A)rfs_history. rfs_history_ok hs ==> p2cz_from_smooth (rfs_view hs)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2cz_from_smooth] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `W:A->bool = {}` THEN ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY] THEN
  UNDISCH_TAC `open_in (rfs_vtop (rfs_view (hs:(A)rfs_history)) a) W` THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) b) W` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[rfs_view; rfs_persists] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. open_in (rfs_top_at (hs:(A)rfs_history) s) W
                    ==> &0 <= s /\ s < rfs_horizon hs`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(W:A->bool = {})` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2AH_SLICE_EMPTY THEN
    MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `s:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ a < rfs_horizon (hs:(A)rfs_history) /\
                &0 <= b /\ b < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `a:real`] P2AH_SLAB_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `b:real`] P2AH_SLAB_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `m:num`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = min b ((a + hs_time (hs:(A)rfs_history) (k + 1)) / &2)` THEN
  SUBGOAL_THEN `a < s /\ s <= b /\ hs_time (hs:(A)rfs_history) k <= s /\
                s < hs_time hs (k + 1)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_top_at (hs:(A)rfs_history) a = hs_top hs k /\
                rfs_atlas_at hs a = hs_atlas hs k /\
                rfs_top_at hs s = hs_top hs k /\ rfs_atlas_at hs s = hs_atlas hs k /\
                rfs_top_at hs b = hs_top hs m /\ rfs_atlas_at hs b = hs_atlas hs m`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC P2AH_DIFFEO_TRANS THEN
  MAP_EVERY EXISTS_TAC [`rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AH_STAGE_DIFFEO THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC P2AH_DIFFEO_CHAIN THEN MAP_EVERY EXISTS_TAC [`m:num`; `a:real`] THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* P2C_HISTORY_REGULAR and MT Thm 5.11 without hypotheses; conjunct 5 of     *)
(* p2c_regular_view is P2CY_HIST_FROM_SMOOTH.                                *)
(* ------------------------------------------------------------------------- *)

let P2CY_HISTORY_REGULAR = prove
 (`!u:A->bool. P2C_HISTORY_REGULAR_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN
  X_GEN_TAC `hs:(A)rfs_history` THEN DISCH_TAC THEN
  MP_TAC(SPEC `hs:(A)rfs_history` P2CY_HIST_FROM_SMOOTH) THEN
  ASM_REWRITE_TAC[p2cz_from_smooth] THEN DISCH_TAC THEN
  REWRITE_TAC[p2c_regular_view] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `u:A->bool` P2AH_P2C_REGIONS_THM) THEN
  REWRITE_TAC[P2AH_P2C_REGIONS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `u:A->bool` P2AB_HIST_VIEW_X) THEN
  REWRITE_TAC[P2A_HIST_VIEW_X_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[p2a_svs; P2CY_VIEW_ACCESSORS] THEN MESON_TAC[]);;

let P2CY_THM_5_11 = prove
 (`!u:A->bool. P2_THM_5_11_STATEMENT u (:real^3)`,
  MESON_TAC[P2CW_THM_5_11; P2CY_HISTORY_REGULAR]);;

