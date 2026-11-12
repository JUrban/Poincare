(* ========================================================================= *)
(* pc_p2a_defs2: corrected P2A statements.  The slice atlas of a view must  *)
(* be locally constant on each side of every time (p2a_atlas_lc).  Without  *)
(* it p2a_pc1 is vacuous when the atlas changes at every time, admissible   *)
(* curves need not be absolutely continuous, and P2A_MIN_LGEOD_STATEMENT    *)
(* fails.  FIX forms of L2, L4, L7, L12 and of the route obligations O7-O9  *)
(* add the hypothesis; the originals imply their FIX forms where the        *)
(* hypotheses allow it.  Flow views and history views satisfy the           *)
(* hypothesis (P2A_ATLAS_LC_FLOW_VIEW, P2A_ATLAS_LC_RFS_FLOW_VIEW,          *)
(* P2A_ATLAS_LC_HIST).                                                      *)
(* ========================================================================= *)

needs "src/pc_p2a_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The atlas condition.                                                      *)
(* ------------------------------------------------------------------------- *)

let p2a_atlas_lc = new_definition
 `p2a_atlas_lc (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) <=>
    !t. ?d. &0 < d /\
            (!s s'. t - d < s /\ s < t /\ t - d < s' /\ s' < t
                    ==> p2a_vatlas V s = p2a_vatlas V s') /\
            (!s s'. t < s /\ s < t + d /\ t < s' /\ s' < t + d
                    ==> p2a_vatlas V s = p2a_vatlas V s')`;;

(* ------------------------------------------------------------------------- *)
(* FIX forms: the statements of pc_p2a_defs with p2a_atlas_lc V added.      *)
(* ------------------------------------------------------------------------- *)

(* L2 (MT Lemma 7.2 regularity): minimizers are corner-free L-geodesics from *)
(* x.                                                                        *)

let P2A_MIN_LGEOD_FIX_STATEMENT = new_definition
 `P2A_MIN_LGEOD_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma.
       p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma
       ==> ?Z. Z IN p2a_Ldom V tt x b /\ p2a_pc1 V tt gamma (&0) b {} /\
               !tau. &0 <= tau /\ tau <= b ==> gamma tau = p2a_Lgeo V tt x Z b tau`;;

(* L4 (MT Prop 6.30 first half).                                             *)

let P2A_INJ_FIX_STATEMENT = new_definition
 `P2A_INJ_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b b1 Z Z'.
       p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\
       Z IN p2a_Smin V tt x b /\ Z' IN p2a_Smin V tt x b /\ &0 < b1 /\ b1 < b /\
       p2a_Lexp V tt x b1 Z = p2a_Lexp V tt x b1 Z'
       ==> Z = Z'`;;

(* L7: Lx is upper semicontinuous on slices.                                 *)

let P2A_LX_USC_FIX_STATEMENT = new_definition
 `P2A_LX_USC_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma e.
       p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\
       &0 < e
       ==> ?O. open_in (rfs_vtop V (tt - b)) O /\ gamma b IN O /\
               !q. q IN O
                   ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = q /\
                                p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e`;;

(* L12: smoothing corners.                                                   *)

let P2A_SMOOTHING_FIX_STATEMENT = new_definition
 `P2A_SMOOTHING_FIX_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma e.
       p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\
       &0 < e
       ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                    p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                    !tau. &0 <= tau /\ tau <= b
                          ==> mfd_dist (rfs_vtop V (tt - tau),rfs_vatlas V (tt - tau))
                                       (rfs_vmetric V (tt - tau))
                                       (gamma' tau) (gamma tau) < e`;;

(* O7-O9 against the FIX forms.                                              *)

let P2A_ROUTE_MIN_LGEOD_FIX_STATEMENT = new_definition
 `P2A_ROUTE_MIN_LGEOD_FIX_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u
    ==> P2A_MIN_LGEOD_FIX_STATEMENT u`;;

let P2A_ROUTE_INJ_FIX_STATEMENT = new_definition
 `P2A_ROUTE_INJ_FIX_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_LGEOD_FLOW_STATEMENT u /\
    P2A_MIN_LGEOD_FIX_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u
    ==> P2A_INJ_FIX_STATEMENT u`;;

let P2A_ROUTE_LX_USC_FIX_STATEMENT = new_definition
 `P2A_ROUTE_LX_USC_FIX_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_SMOOTHING_FIX_STATEMENT u ==> P2A_LX_USC_FIX_STATEMENT u`;;

(* ------------------------------------------------------------------------- *)
(* Each original implies its FIX form (only where the FIX form does not      *)
(* weaken a hypothesis: the FIX forms of O8 and O9 assume less than O8, O9). *)
(* ------------------------------------------------------------------------- *)

let P2A_MIN_LGEOD_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_MIN_LGEOD_STATEMENT u ==> P2A_MIN_LGEOD_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_MIN_LGEOD_STATEMENT; P2A_MIN_LGEOD_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2A_INJ_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_INJ_STATEMENT u ==> P2A_INJ_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_INJ_STATEMENT; P2A_INJ_FIX_STATEMENT] THEN
  MESON_TAC[]);;

let P2A_LX_USC_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_LX_USC_STATEMENT u ==> P2A_LX_USC_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_LX_USC_STATEMENT; P2A_LX_USC_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2A_SMOOTHING_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_SMOOTHING_STATEMENT u ==> P2A_SMOOTHING_FIX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_SMOOTHING_STATEMENT; P2A_SMOOTHING_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2A_ROUTE_MIN_LGEOD_ORIG_IMP_FIX = prove
 (`!u:A->bool. P2A_ROUTE_MIN_LGEOD_STATEMENT u ==> P2A_ROUTE_MIN_LGEOD_FIX_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2A_ROUTE_MIN_LGEOD_STATEMENT; P2A_ROUTE_MIN_LGEOD_FIX_STATEMENT] THEN
  MESON_TAC[P2A_MIN_LGEOD_ORIG_IMP_FIX]);;

(* ------------------------------------------------------------------------- *)
(* The hypothesis holds for views with a constant atlas (flow views) and    *)
(* for history views (finitely many stage times).                           *)
(* ------------------------------------------------------------------------- *)

let P2A_ATLAS_LC_CONST = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N).
        (!s s'. p2a_vatlas V s = p2a_vatlas V s') ==> p2a_atlas_lc V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_atlas_lc] THEN GEN_TAC THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM_MESON_TAC[]);;

let P2A_ATLAS_LC_FLOW_VIEW = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (J:real->bool)
    (g:real->A->real^N^N).
        p2a_atlas_lc (p2a_flow_view (top,atlas) J g)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2A_ATLAS_LC_CONST THEN
  REWRITE_TAC[p2a_flow_view; p2a_vatlas]);;

let P2A_ATLAS_LC_RFS_FLOW_VIEW = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (J:real->bool)
    (g:real->A->real^3^3).
        p2a_atlas_lc (rfs_flow_view (top,atlas) J g)`,
  REWRITE_TAC[GSYM P2A_FLOW_VIEW_3; P2A_ATLAS_LC_FLOW_VIEW]);;

(* The atlas of a history view is constant on intervals containing no      *)
(* stage time (strictly after the left end).                                *)

let P2A_RFS_ATLAS_AT_EQ = prove
 (`!hs:(A)rfs_history s s'.
        rfs_history_ok hs /\ s <= s' /\
        (!k. k <= hs_count hs + 1 ==> ~(s < hs_time hs k /\ hs_time hs k <= s'))
        ==> rfs_atlas_at hs s = rfs_atlas_at hs s'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) 0 = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_history_ok]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) s' <=> rfs_live hs s` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_live] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `hs_count (hs:(A)rfs_history) + 1`) THEN
    ASM_REWRITE_TAC[LE_0; LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_atlas_at] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFS_SLAB) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) s` THEN
    ASM_REWRITE_TAC[rfs_live; rfs_horizon] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFS_SLAB_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rfs_slab (hs:(A)rfs_history) s + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2A_ATLAS_LC_HIST = prove
 (`!hs:(A)rfs_history. rfs_history_ok hs ==> p2a_atlas_lc (rfs_view hs)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2a_atlas_lc; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
  X_GEN_TAC `t:real` THEN
  MP_TAC(ISPECL [`lift t`;
                 `IMAGE (\k. lift(hs_time (hs:(A)rfs_history) k))
                        {k | k <= hs_count hs + 1}`] FINITE_SET_AVOID) THEN
  ANTS_TAC THENL [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o
     REWRITE_RULE[IMP_CONJ; FORALL_IN_IMAGE; IN_ELIM_THM; DIST_LIFT; LIFT_EQ]))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s s'. (t - d < s /\ s <= s' /\ s' < t) \/ (t < s /\ s <= s' /\ s' < t + d)
           ==> rfs_atlas_at (hs:(A)rfs_history) s = rfs_atlas_at hs s'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2A_RFS_ATLAS_AT_EQ THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= s' \/ s' <= s`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

