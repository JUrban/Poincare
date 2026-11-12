(* ========================================================================= *)
(* Unit pc_p2a_reach: the moving-endpoint analogue of P2AO_VERT_EXT          *)
(* (pc_p2a_p164) for the core of MT Prop 16.1 (MT 16.6, pc_p3_s161), the     *)
(* theorem P2ARC_BALL_REACH (statement P2ARC_BALL_REACH_STATEMENT): an       *)
(* admissible curve gamma to y = gamma(b) is extended over [b, b + D] to any *)
(* point z of the ball B(y, tt - b - D, rho) inside a set W persisting over  *)
(* (tt - b - D - eta, tt - b], with L <= L(gamma) + sqrt(b + D) (Rmax D +    *)
(* Lam rho^2 / D) + e, given R <= Rmax on W and the comparison g(s) <= Lam   *)
(* g(tt - b - D) of the region family p2ah_fam (reference slice tt - b).     *)
(* Route: a constant piece at y, then a minimizing geodesic of the compact   *)
(* slice tt - b - D moved affinely in s = sqrt(tau), glued chart window by   *)
(* chart window (supremum argument as in P2AU_ADM_EXISTS), the corner        *)
(* smoothed (P2AXS_SMOOTHING_X).                                             *)
(* ========================================================================= *)

needs "src/pc_p2a_p164.ml";;
needs "src/pc_geo_hr.ml";;

prioritize_real();;
type_invention_error := true;;

let P2ARC_BALL_REACH_STATEMENT = new_definition
 `P2ARC_BALL_REACH_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) tt x b (gamma:real->A) D eta W Rmax Lam rho.
       rfs_history_ok hs /\ rfs_L_adm hs tt x b gamma /\ &0 < D /\ b + D < tt /\
       &0 < eta /\ &0 <= Rmax /\ &0 <= Lam /\ &0 < rho /\
       x IN topspace(rfs_top_at hs tt) /\
       (?r dt. &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt) /\
       rfs_persists (rfs_view hs) W (tt - b - D - eta) (tt - b) /\
       mfd_ball (rfs_top_at hs (tt - b - D),rfs_atlas_at hs (tt - b - D))
                (rfs_metric_at hs (tt - b - D)) (gamma b) rho SUBSET W /\
       (!s y. tt - b - D <= s /\ s <= tt - b /\ y IN W
              ==> mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at hs s) y <= Rmax) /\
       (!s y v. tt - b - D <= s /\ s <= tt - b /\ y IN W
                ==> v dot (p2ah_fam hs W (tt - b) s y ** v) <=
                    Lam * (v dot (p2ah_fam hs W (tt - b) (tt - b - D) y ** v)))
       ==> !z e. z IN mfd_ball (rfs_top_at hs (tt - b - D),rfs_atlas_at hs (tt - b - D))
                               (rfs_metric_at hs (tt - b - D)) (gamma b) rho /\ &0 < e
                 ==> ?gamma'. rfs_L_adm hs tt x (b + D) gamma' /\ gamma'(b + D) = z /\
                              rfs_L_length hs tt gamma' (b + D) <=
                              rfs_L_length hs tt gamma b +
                              sqrt(b + D) * (Rmax * D + Lam * rho pow 2 / D) + e`;;

(* ========================================================================= *)
(* Helpers copied from units outside this closure (proofs unchanged up to    *)
(* renaming): curves in restricted atlases, speeds under the identity        *)
(* diffeomorphism of a region (pullback metric), minimizing geodesics, the   *)
(* curve diameter, the integral of inv(sqrt s) and integral comparison off   *)
(* the end points.                                                           *)
(* ========================================================================= *)

let p2arc_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* from pc_p2a_par.ml *)
let P2ARC_C1_CURVE_UNRESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_c1_curve (top,atlas) gamma a b /\
         (!t. t IN real_interval[a,b] ==> gamma t IN W)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[a,b] ==> (gamma:real->A) t IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (gamma:real->A)
                   (topspace (subtopology euclideanreal (real_interval[a,b]))) SUBSET W` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U INTER W:A->bool,phi:A->real^N)`) THEN
  REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[FST; SND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

(* from pc_p3_s16l15.ml *)
let P2ARC_SPEED_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) (gamma:real->A) a b t.
     smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b /\
     t IN real_interval[a,b]
     ==> mfd_speed (restrict_atlas atlas W) (restrict_metric atlas W g) gamma a b t =
         mfd_speed atlas g gamma a b t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2ARC_C1_CURVE_UNRESTRICT) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top /\ gamma t IN W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN restrict_atlas atlas W` ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U INTER W:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* from pc_p3_s16l15.ml *)
let P2ARC_C1_CURVE_SUBTOP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (top,atlas) gamma a b /\
     (!t. t IN real_interval[a,b] ==> gamma t IN W)
     ==> mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`UW:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

(* from pc_p2b_979s.ml *)
let P2ARC_PB_SPEED = prove
 (`!top atlas top' atlas' U U' (psi:A->B) psi' (g':B->real^N^N) (gamma:real->A) a b t.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
     (!s. s IN real_interval[a,b] ==> gamma s IN U) /\ t IN real_interval[a,b]
     ==> mfd_c1_curve (top',atlas') (psi o gamma) a b /\
         mfd_speed atlas' g' (psi o gamma) a b t =
         mfd_speed atlas (mfd_pullback_metric atlas atlas' psi g') gamma a b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `mfd_c1_curve (top',atlas':((B->bool)#(B->real^N))->bool)
                 ((psi:A->B) o (gamma:real->A)) a b`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `U:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B)((gamma:real->A) t) IN topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(psi:A->B)((gamma:real->A) t)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool)
                            ((psi:A->B)((gamma:real->A) t))` THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N) ((gamma:real->A) t) =
                mpullback (SND (c':(B->bool)#(B->real^N)) o psi o
                           chart_inv (c:(A->bool)#(A->real^N)))
                          (metric_local atlas' c' g') (SND c (gamma t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_pullback_metric] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(psi:A->B) o (gamma:real->A)`; `a:real`; `b:real`;
                 `t:real`; `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`]
                MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)`;
                 `gamma:real->A`; `a:real`; `b:real`;
                 `t:real`; `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^N^N)`;
                 `(gamma:real->A) t`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (c':(B->bool)#(B->real^N)) ((psi:A->B)((gamma:real->A)(drop s))))
      (at (lift t) within interval[lift a,lift b]) =
    frechet_derivative (SND c' o psi o chart_inv (c:(A->bool)#(A->real^N)))
      (at (SND c (gamma t)))
      (vector_derivative (\s. SND c (gamma(drop s)))
         (at (lift t) within interval[lift a,lift b]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `U:A->bool`; `psi:A->B`; `gamma:real->A`;
                   `a:real`; `b:real`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                   `lift t`] GRGD_PUSH_VD) THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (SND (c':(B->bool)#(B->real^N)) o (psi:A->B) o
                               chart_inv (c:(A->bool)#(A->real^N)))
                              (at (SND c ((gamma:real->A) t))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `U:A->bool`; `psi:A->B`; `c:(A->bool)#(A->real^N)`;
                   `c':(B->bool)#(B->real^N)`; `(gamma:real->A) t`]
                  GRGD_CHART_MAP_DIFF) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c ((gamma:real->A) t)) = gamma t`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GRGD_QUAD_CONGR THEN ASM_REWRITE_TAC[]);;

(* from pc_rfa_dist.ml *)
let P2ARC_GEO_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x
     ==> mfd_c1_curve (top,atlas) (mfd_geo (top,atlas) g x v) (&0) (&1) /\
         mfd_geo (top,atlas) g x v (&0) = x /\
         mfd_geo (top,atlas) g x v (&1) = mfd_exp (top,atlas) g x v /\
         mfd_length atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) = mfd_tnorm g x v /\
         !u. u IN real_interval[&0,&1]
             ==> mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) u =
                 mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,&1] SUBSET J` ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
    ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `is_realinterval (J:real->bool)` THEN
    REWRITE_TAC[is_realinterval; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC th THEN MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gam:real->A`; `J:real->bool`; `&0`; `&1`] MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LT_01; REAL_SUB_RZERO; REAL_MUL_LID] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_exp] THEN
  X_GEN_TAC `u:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_speed] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `J:real->bool`; `u:real`; `&0`]
                MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[mfd_tnorm]);;

(* from pc_p2c_c1116.ml *)
let P2ARC_CURVE_DIAM = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t1 t2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma a b /\
     t1 IN real_interval[a,b] /\ t2 IN real_interval[a,b]
     ==> mfd_joinable (top,atlas) (gamma t1) (gamma t2) /\
         mfd_dist (top,atlas) g (gamma t1) (gamma t2) <= mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u v. a <= u /\ u <= v /\ v <= b
          ==> mfd_joinable (top,atlas) ((gamma:real->A) u) (gamma v) /\
              mfd_dist (top,atlas) (g:A->real^N^N) (gamma u) (gamma v) <=
              mfd_length atlas g gamma a b`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `u:real`; `b:real`]
                  MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `u:real`; `v:real`; `b:real`]
                  MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma:real->A) u v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `u:real`] MFD_LENGTH_POS_LE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `v:real`; `b:real`] MFD_LENGTH_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `t1 <= t2 \/ t2 <= t1:real`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t2:real`; `t1:real`]) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM]);;

(* from pc_p2a_flow.ml *)
let P2ARC_INV_SQRT_INTEGRAL = prove
 (`!e1 e2. &0 < e1 /\ e1 <= e2
           ==> ((\s. inv(sqrt s)) has_real_integral (&2 * sqrt e2 - &2 * sqrt e1))
               (real_interval[e1,e2])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. &2 * sqrt s`; `\s. inv(sqrt s)`; `e1:real`; `e2:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt x) = &2 * inv(&2 * sqrt x)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt x` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT]);;

(* from pc_p2a_flow.ml *)
let P2ARC_INTEGRAL_LE_INTERIOR = prove
 (`!f g c d.
     f real_integrable_on real_interval[c,d] /\ g real_integrable_on real_interval[c,d] /\
     (!x. c < x /\ x < d ==> f x <= g x)
     ==> real_integral (real_interval[c,d]) f <= real_integral (real_interval[c,d]) g`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f' = \x. if x = c \/ x = d then g x else (f:real->real) x` THEN
  SUBGOAL_THEN `real_negligible {c,d}` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NEGLIGIBLE_INSERT; REAL_NEGLIGIBLE_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN real_interval[c,d] DIFF {c,d} ==> (f':real->real) x = f x`
  ASSUME_TAC THENL
   [EXPAND_TAC "f'" THEN REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[c,d]) f = real_integral (real_interval[c,d]) f'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{c:real,d}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `{c:real,d}`; `real_interval[c,d]`]
                  REAL_INTEGRABLE_SPIKE) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "f'" THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Chart windows of the path s -> c4((s - A)/(B - A)) for a C1 curve c4 on   *)
(* [-m,1+m] (P2AU_PATH_WINDOW of pc_p2a_flow with the margin m in place of   *)
(* 1).                                                                       *)
(* ========================================================================= *)

(* from pc_p2a_flow.ml *)
let P2ARC_PATH_WINDOW = prove
 (`!top atlas (c4:real->A) m A B s0.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     &0 < m /\ mfd_c1_curve (top,atlas) c4 (--m) (&1 + m) /\ A < B /\ A <= s0 /\ s0 <= B
     ==> ?d (U:A->bool) (phi:A->real^N) (sol:real^1->real^N).
            &0 < d /\ (U,phi) IN atlas /\
            !s. abs(s - s0) < d
                ==> c4((s - A) / (B - A)) IN U /\
                    sol(lift s) = phi(c4((s - A) / (B - A))) /\
                    sol differentiable (at (lift s)) /\
                    (\v. vector_derivative sol (at v)) continuous (at (lift s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < B - A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (s0 - A) / (B - A) /\ (s0 - A) / (B - A) <= &1` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `u0 = (s0 - A) / (B - A)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c4:real->A) u0 IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `--m`; `&1 + m`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `k = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((c4:real->A) u0)` THEN
  SUBGOAL_THEN `(k:(A->bool)#(A->real^N)) IN atlas /\ (c4:real->A) u0 IN FST k /\
                open_in top (FST k)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c4:real->A) u0`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    ALL_TAC] THEN
  ABBREV_TAC `Sk = {x | x IN interval[lift(--m),lift(&1 + m)] /\
                        (c4:real->A)(drop x) IN FST (k:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 Sk (\x. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)(drop x)))`
  MP_TAC THENL
   [EXPAND_TAC "Sk" THEN
    UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (c4:real->A) (--m) (&1 + m)` THEN
    REWRITE_TAC[mfd_c1_curve] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable; CONTINUOUSLY_DIFFERENTIABLE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "C"))) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(lift u0,r) SUBSET Sk` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                   `--m`; `&1 + m`; `FST(k:(A->bool)#(A->real^N))`] GRGD_CURVE_TIMES_OPEN_IN) THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SK"))) THEN
    SUBGOAL_THEN `lift u0 IN (O:real^1->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `lift u0 IN Sk` MP_TAC THENL
       [EXPAND_TAC "Sk" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "SK" SUBST1_TAC THEN SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    UNDISCH_TAC `open(O:real^1->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `lift u0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (m / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SK" SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `x IN ball(lift u0,min e (m / &2))` THEN
      REWRITE_TAC[IN_BALL; IN_INTERVAL_1; LIFT_DROP; DIST_REAL; GSYM drop] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      UNDISCH_TAC `x IN ball(lift u0,min e (m / &2))` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(lift u0,r)
        ==> ((\x. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)(drop x))) has_derivative
             (f':real^1->real^1->real^N) x) (at x) /\
            (\y. f' y (vec 1)) continuous (at x)`
  (LABEL_TAC "BALL") THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)(drop x))`;
                     `(f':real^1->real^1->real^N) x`; `x:real^1`; `ball(lift u0,r)`]
                    HAS_DERIVATIVE_WITHIN_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `Sk:real^1->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "D" MATCH_MP_TAC THEN ASM SET_TAC[];
      USE_THEN "C" (MP_TAC o SPEC `vec 1:real^1`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\y. (f':real^1->real^1->real^N) y (vec 1)) continuous_on ball(lift u0,r)`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Sk:real^1->bool` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  (* the affine reparametrization *)
  ABBREV_TAC `gm = \v:real^1. inv(B - A) % (v - lift A)` THEN
  SUBGOAL_THEN `!v:real^1. (gm:real^1->real^1) v = lift((drop v - A) / (B - A))`
  ASSUME_TAC THENL
   [EXPAND_TAC "gm" THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_SUB; LIFT_DROP] THEN
    GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^1. ((gm:real^1->real^1) has_derivative (\h. inv(B - A) % h)) (at v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gm" THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    MP_TAC(ISPECL [`\v:real^1. v`; `\h:real^1. h`; `\v:real^1. lift A`;
                   `\h:real^1. vec 0:real^1`; `at (v:real^1)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. abs(drop v - s0) < r * (B - A) ==> (gm:real^1->real^1) v IN ball(lift u0,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_BALL; DIST_LIFT] THEN
    EXPAND_TAC "u0" THEN
    SUBGOAL_THEN `(s0 - A) / (B - A) - (drop v - A) / (B - A) = (s0 - drop v) / (B - A)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < B - A` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the vector derivative of sol in the window *)
  SUBGOAL_THEN
   `!v. abs(drop v - s0) < r * (B - A)
        ==> ((\v. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)((drop v - A) / (B - A))))
             has_vector_derivative
             (inv(B - A) % (f':real^1->real^1->real^N) ((gm:real^1->real^1) v) (vec 1)))
            (at v)`
  (LABEL_TAC "VD") THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\v. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)((drop v - A) / (B - A)))) =
      (\x. SND k (c4(drop x))) o (gm:real^1->real^1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN
     `(\h:real^1. drop h % inv(B - A) % (f':real^1->real^1->real^N) ((gm:real^1->real^1) v)
                    (vec 1)) =
      f' (gm v) o (\h. inv(B - A) % h)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
      SUBGOAL_THEN `linear((f':real^1->real^1->real^N) ((gm:real^1->real^1) v))` ASSUME_TAC THENL
       [USE_THEN "BALL" (MP_TAC o SPEC `(gm:real^1->real^1) v`) THEN
        ANTS_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (find_term (fun t -> t = `ball(lift u0,r)`)) (concl th) &&
            not (p2arc_mentions "has_derivative" th))) THEN
          ASM_REWRITE_TAC[];
          SIMP_TAC[has_derivative]];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(B - A) % (h:real^1) = (inv(B - A) * drop h) % vec 1` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM LIFT_EQ_CMUL; LIFT_DROP]; ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "BALL" (MP_TAC o SPEC `(gm:real^1->real^1) v`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `ball(lift u0,r)`)) (concl th) &&
        not (p2arc_mentions "has_derivative" th))) THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `r * (B - A)` THEN EXISTS_TAC `FST(k:(A->bool)#(A->real^N))` THEN
  EXISTS_TAC `SND(k:(A->bool)#(A->real^N))` THEN
  EXISTS_TAC `\v:real^1. SND(k:(A->bool)#(A->real^N)) ((c4:real->A)((drop v - A) / (B - A)))` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; PAIR] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
      can (find_term (fun t -> t = `gm:real^1->real^1`)) (concl th) &&
      can (find_term (fun t -> t = `ball(lift u0,r)`)) (concl th) &&
      not (p2arc_mentions "has_derivative" th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lift((s - A) / (B - A)) IN Sk` MP_TAC THENL
     [ASM SET_TAC[]; EXPAND_TAC "Sk" THEN SIMP_TAC[IN_ELIM_THM; LIFT_DROP]];
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % inv(B - A) %
                (f':real^1->real^1->real^N) ((gm:real^1->real^1) (lift s)) (vec 1)` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN USE_THEN "VD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\v:real^1. inv(B - A) % (f':real^1->real^1->real^N) ((gm:real^1->real^1) v)
                                          (vec 1)` THEN
    EXISTS_TAC `r * (B - A) - abs(s - s0)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      USE_THEN "VD" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN
    SUBGOAL_THEN `(\v:real^1. (f':real^1->real^1->real^N) ((gm:real^1->real^1) v) (vec 1)) =
                  (\y. f' y (vec 1)) o gm` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      ASM_MESON_TAC[];
      USE_THEN "BALL" (MP_TAC o SPEC `(gm:real^1->real^1) (lift s)`) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]; SIMP_TAC[]]]]);;

(* ========================================================================= *)
(* p2a_admx and the L-length depend only on the curve on [0,b] (the p2a_admx *)
(* form of P2AU_ADM_CONG of pc_p2a_flow).                                    *)
(* ========================================================================= *)

let P2ARC_ADMX_CONG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) gamma'.
     p2a_admx V tt x b gamma /\ (!s. &0 <= s /\ s <= b ==> gamma' s = gamma s)
     ==> p2a_admx V tt x b gamma' /\
         p2a_L_length V tt gamma' b = p2a_L_length V tt gamma b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma':real->A) b`;
    `&0`; `b:real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IE") (LABEL_TAC "LE"))] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[p2a_L_length] THEN USE_THEN "LE" (SUBST1_TAC o SYM) THEN REFL_TAC] THEN
  UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt x b (gamma:real->A)` THEN
  REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma':real->A)(&0) = x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      can (find_term (fun t -> t = `gamma':real->A`)) (concl th) && is_forall(concl th))) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tau0:real`; `O:A->bool`] o check (fun th ->
      can (find_term (fun t -> t = `O:A->bool`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    EXISTS_TAC `P:real->bool` THEN
    UNDISCH_TAC `p2a_pc1x (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt (gamma:real->A) (&0) b P` THEN
    REWRITE_TAC[p2a_pc1x] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "T")) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "T" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma':real->A)(drop s) = gamma(drop s)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    USE_THEN "IE" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ========================================================================= *)
(* In a compact slice every point z of the ball B(y,rho) is the end c(1) of  *)
(* a minimizing geodesic c with c(0) = y, constant speed d = dist(y,z) < rho *)
(* on [0,1], C1 on [-m,1+m] for some m > 0, and c[-m,1+m] inside the ball.   *)
(* ========================================================================= *)

(* Complete case: geodesics are defined for all times. *)

let P2ARC_MAXINT_UNIV = prove
 (`!top atlas (g:A->real^N^N) x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ mfd_exp_dom (top,atlas) g x = (:real^N)
     ==> mfd_geo_maxint (top,atlas) g x v = (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `t:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t % (v:real^N)` o REWRITE_RULE[EXTENSION; IN_UNIV] o
    check (fun th -> p2arc_mentions "mfd_exp_dom" th)) THEN
  REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`; `t:real`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RID]);;

let P2ARC_GEO_PATH = prove
 (`!top atlas (g:A->real^N^N) y z rho.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_space top /\ z IN mfd_ball (top,atlas) g y rho
     ==> ?(c:real->A) d m.
           &0 <= d /\ d < rho /\ &0 < m /\ c(&0) = y /\ c(&1) = z /\
           mfd_c1_curve (top,atlas) c (--m) (&1 + m) /\
           mfd_c1_curve (top,atlas) c (&0) (&1) /\
           (!t. t IN real_interval[&0,&1] ==> mfd_speed atlas g c (&0) (&1) t = d) /\
           (!t. t IN real_interval[--m,&1 + m] ==> c t IN mfd_ball (top,atlas) g y rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mfd_ball; IN_ELIM_THM] o
    check (fun th -> p2arc_mentions "mfd_ball" th)) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) (g:A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_COMPACT_IMP_COMPLETE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `z:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) y z` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = mfd_geo (top,atlas) (g:A->real^N^N) y v` THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) y v = (:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2ARC_MAXINT_UNIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `v:real^N`] P2ARC_GEO_FACTS) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `m = (rho - d) / (&4 * (d + &1))` THEN
  SUBGOAL_THEN `&0 < m /\ m * (d + &1) = (rho - d) / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 <= d` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:real->A`; `d:real`; `m:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= m * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:real->A`; `(:real)`; `--m`; `&1 + m`] MFD_GEODESIC_C1_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((c:real->A)(--m))
                   (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) c (--m)) = d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `c:real->A`; `(:real)`; `--m`; `&0`] MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:real->A`; `--m`; `&1 + m`; `&0`; `t:real`] P2ARC_CURVE_DIAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `((&1 + m) - --m) * d` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((&1 + m) - --m) * d = d + &2 * (m * d)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m * d <= (rho - d) / &4` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m * (d + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Speeds on a region W with reference slice r.  A curve C1 in the slice r   *)
(* with values in W has, in every slice s in (a,r), the speed sqrt(v dot G_s *)
(* v) with v its velocity in the restricted atlas of r and G_s = p2ah_fam hs *)
(* W r s (the slice-s metric moved to that atlas); hence the comparison of   *)
(* the G_s gives the speed comparison (as P3N_PAR_SPEED_CMP of               *)
(* pc_p3_s16l15).                                                            *)
(* ========================================================================= *)

let P2ARC_FAM_RMETRIC = prove
 (`!(hs:(A)rfs_history) W r t.
     p2ah_fam hs W r t = p2a_rmetric (rfs_view hs) W r t`,
  REWRITE_TAC[p2ah_fam; p2a_rmetric; rfs_view; p2a_vatlas; p2a_vmetric]);;

(* The region facts in history notation. *)

let P2ARC_REGION_FACTS = prove
 (`!(hs:(A)rfs_history) W a r.
     p2a_region (rfs_view hs) W a r
     ==> (!s. a < s /\ s <= r
              ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
                  open_in (rfs_top_at hs s) W /\
                  mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) W
                             (rfs_top_at hs r) (rfs_atlas_at hs r) W (\y:A. y) (\y. y) /\
                  mfd_diffeo (rfs_top_at hs r) (rfs_atlas_at hs r) W
                             (rfs_top_at hs s) (rfs_atlas_at hs s) W (\y:A. y) (\y. y)) /\
         (!s. a < s /\ s < r
              ==> smooth_manifold_atlas (subtopology (rfs_top_at hs r) W)
                                        (restrict_atlas (rfs_atlas_at hs r) W) /\
                  riemannian_metric (restrict_atlas (rfs_atlas_at hs r) W)
                                    (p2ah_fam hs W r s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2a_region; rfs_view; p2a_persists; p2a_vtop; p2a_vatlas; p2a_vmetric] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pers") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (LABEL_TAC "flow"))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REMOVE_THEN "pers" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_diffeo (rfs_top_at (hs:(A)rfs_history) s) (rfs_atlas_at hs s) W
                             (rfs_top_at hs r) (rfs_atlas_at hs r) W (\y:A. y) (\y. y)`
    ASSUME_TAC THENL
     [USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "flow" (MP_TAC o REWRITE_RULE[p2a_flow_upto; ricci_flow_on]) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[P2ARC_FAM_RMETRIC] THEN
  REWRITE_TAC[rfs_view] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The speed in the slice s through the restricted atlas of r. *)

let P2ARC_SPEED_FAM = prove
 (`!(hs:(A)rfs_history) W a r s (mu:real->A) p q t.
     p2a_region (rfs_view hs) W a r /\ a < s /\ s < r /\
     mfd_c1_curve (rfs_top_at hs r,rfs_atlas_at hs r) mu p q /\ p < q /\
     (!u. u IN real_interval[p,q] ==> mu u IN W) /\ t IN real_interval[p,q]
     ==> mfd_speed (rfs_atlas_at hs s) (rfs_metric_at hs s) mu p q t =
         sqrt(mfd_velocity (restrict_atlas (rfs_atlas_at hs r) W) mu p q t dot
              (p2ah_fam hs W r s (mu t) **
               mfd_velocity (restrict_atlas (rfs_atlas_at hs r) W) mu p q t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2ARC_REGION_FACTS) THEN
  SUBGOAL_THEN `a < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> p2arc_mentions "mfd_diffeo" th)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> p2arc_mentions "mfd_diffeo" th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) r`; `rfs_atlas_at (hs:(A)rfs_history) r`;
                 `rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                 `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`;
                 `rfs_metric_at (hs:(A)rfs_history) s`; `mu:real->A`; `p:real`; `q:real`;
                 `t:real`] P2ARC_PB_SPEED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:A. y) o (mu:real->A) = mu` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) r`; `rfs_atlas_at (hs:(A)rfs_history) r`;
                 `W:A->bool`;
                 `mfd_pullback_metric (rfs_atlas_at (hs:(A)rfs_history) r)
                                      (rfs_atlas_at hs s) (\y:A. y) (rfs_metric_at hs s)`;
                 `mu:real->A`; `p:real`; `q:real`; `t:real`] P2ARC_SPEED_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2ARC_C1_CURVE_SUBTOP THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[mfd_speed] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN
  SUBGOAL_THEN `~(s:real = r)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2ah_fam; ETA_AX]);;

(* The speed comparison. *)

let P2ARC_SPEED_CMP = prove
 (`!(hs:(A)rfs_history) W a r s s0 Lam (mu:real->A) p q t.
     p2a_region (rfs_view hs) W a r /\
     a < s /\ s < r /\ a < s0 /\ s0 < r /\
     (!y v. y IN W ==> v dot (p2ah_fam hs W r s y ** v) <=
                       Lam * (v dot (p2ah_fam hs W r s0 y ** v))) /\
     mfd_c1_curve (rfs_top_at hs s0,rfs_atlas_at hs s0) mu p q /\ p < q /\
     (!u. u IN real_interval[p,q] ==> mu u IN W) /\ t IN real_interval[p,q]
     ==> mfd_speed (rfs_atlas_at hs s) (rfs_metric_at hs s) mu p q t pow 2 <=
         Lam * mfd_speed (rfs_atlas_at hs s0) (rfs_metric_at hs s0) mu p q t pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cmp") STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2ARC_REGION_FACTS) THEN
  SUBGOAL_THEN `a < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the curve in the slice r *)
  SUBGOAL_THEN `mfd_c1_curve (rfs_top_at (hs:(A)rfs_history) r,rfs_atlas_at hs r) mu p q`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> p2arc_mentions "mfd_diffeo" th)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> p2arc_mentions "mfd_diffeo" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s0`; `rfs_atlas_at (hs:(A)rfs_history) s0`;
                   `rfs_top_at (hs:(A)rfs_history) r`; `rfs_atlas_at (hs:(A)rfs_history) r`;
                   `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`;
                   `rfs_metric_at (hs:(A)rfs_history) r`; `mu:real->A`; `p:real`; `q:real`;
                   `t:real`] P2ARC_PB_SPEED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\y:A. y) o (mu:real->A) = mu` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `r:real`; `s:real`;
                 `mu:real->A`; `p:real`; `q:real`; `t:real`] P2ARC_SPEED_FAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `r:real`; `s0:real`;
                 `mu:real->A`; `p:real`; `q:real`; `t:real`] P2ARC_SPEED_FAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `v = mfd_velocity (restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) r) W)
                               (mu:real->A) p q t` THEN
  SUBGOAL_THEN `(mu:real->A) t IN W /\
                (mu:real->A) t IN topspace(subtopology (rfs_top_at (hs:(A)rfs_history) r) W)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) r`; `rfs_atlas_at (hs:(A)rfs_history) r`;
                   `mu:real->A`; `p:real`; `q:real`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. a < s' /\ s' < r
         ==> &0 <= v dot (p2ah_fam (hs:(A)rfs_history) W r s' ((mu:real->A) t) ** v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real` o check (fun th ->
      p2arc_mentions "riemannian_metric" th && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology (rfs_top_at (hs:(A)rfs_history) r) W`;
                   `restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) r) W`;
                   `p2ah_fam (hs:(A)rfs_history) W r s'`; `(mu:real->A) t`]
                  RIEMANNIAN_METRIC_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v dot (p2ah_fam (hs:(A)rfs_history) W r s ((mu:real->A) t) ** v) /\
                &0 <= v dot (p2ah_fam (hs:(A)rfs_history) W r s0 ((mu:real->A) t) ** v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN USE_THEN "cmp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* An admissible curve g0 on [0,A^2] ending at c4(0) continues along the     *)
(* path tau -> c4((sqrt tau - A)/(B - A)) to an admissible curve on [0,B^2], *)
(* for a C1 curve c4 of the slice r inside a region W on (a,r] (chart        *)
(* windows P2ARC_PATH_WINDOW, segments P2A_CHART_CURVE_SEG, gluing           *)
(* P2AXR_SEG_GLUE_X, supremum argument as in P2AU_ADM_EXISTS).               *)
(* ========================================================================= *)

let P2ARC_ADMX_PATH = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x (g0:real->A) W a r (c4:real->A) m A B.
     p2a_svs V /\ p2a_region V W a r /\ r < tt /\
     &0 < m /\ mfd_c1_curve (p2a_vtop V r,p2a_vatlas V r) c4 (--m) (&1 + m) /\
     (!u. u IN real_interval[--m,&1 + m] ==> c4 u IN W) /\
     &0 < A /\ A < B /\ a < tt - B pow 2 /\ tt - A pow 2 < r /\
     p2a_admx V tt x (A pow 2) g0 /\ g0(A pow 2) = c4(&0)
     ==> p2a_admx V tt x (B pow 2)
           (\tau. if tau <= A pow 2 then g0 tau else c4((sqrt tau - A) / (B - A)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (LABEL_TAC "inW") STRIP_ASSUME_TAC)))))) THEN
  ABBREV_TAC `gamma = \tau. if tau <= A pow 2 then (g0:real->A) tau
                             else (c4:real->A)((sqrt tau - A) / (B - A))` THEN
  SUBGOAL_THEN `a < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < B pow 2 - A pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) r)
                  (p2a_vatlas V r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a:real`; `r:real`; `r:real`]
                  P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the path agrees with c4 after A^2 *)
  SUBGOAL_THEN `!tau. A pow 2 <= tau
                      ==> (gamma:real->A) tau = (c4:real->A)((sqrt tau - A) / (B - A))`
  (LABEL_TAC "PATH") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN EXPAND_TAC "gamma" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `tau = A pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_SUB_REFL; real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  (* the supremum argument over the s-parameter *)
  ABBREV_TAC `Ts = {s | A <= s /\ s <= B /\
                        p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt x (s pow 2) (gamma:real->A)}` THEN
  SUBGOAL_THEN `(A:real) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `A pow 2`; `g0:real->A`;
                   `gamma:real->A`] P2ARC_ADMX_CONG) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "gamma" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Ts:real->bool = {}) /\ (!s. s IN Ts ==> s <= B)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "Ts" THEN SIMP_TAC[IN_ELIM_THM]]; ALL_TAC] THEN
  ABBREV_TAC `ss = sup (Ts:real->bool)` THEN
  SUBGOAL_THEN `A <= ss /\ ss <= B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN CONJ_TAC THENL
     [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) r`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) r`;
                 `c4:real->A`; `m:real`; `A:real`; `B:real`; `ss:real`] P2ARC_PATH_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `sol:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WIN"))))))) THEN
  SUBGOAL_THEN `?s1. s1 IN Ts /\ ss - d < s1` (X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC SUP_APPROACH THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `A <= s1 /\ s1 <= B /\
                p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x (s1 pow 2) (gamma:real->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s1:real) IN Ts` THEN EXPAND_TAC "Ts" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 <= ss` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s1:real = B` THENL
   [UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x (s1 pow 2) (gamma:real->A)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s2 = min B (ss + d / &2)` THEN
  SUBGOAL_THEN `s1 < s2 /\ s2 <= B /\ s2 <= ss + d / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the time window of the region *)
  SUBGOAL_THEN `&0 < tt - r /\ sqrt(tt - r) < A /\ B < sqrt(tt - a)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < tt - r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the chart segment on [s1^2, s2^2] *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a:real`; `r:real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`; `s1:real`; `s2:real`;
                 `max (ss - d) (sqrt(tt - r))`; `min (ss + d) (sqrt(tt - a))`]
                P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MAX_LT] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_MAX_LT; REAL_LT_MIN] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 <= sqrt(tt - r)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `tt - r < s pow 2 /\ s pow 2 < tt - a` MP_TAC THENL
       [CONJ_TAC THENL
         [SUBGOAL_THEN `sqrt(tt - r) pow 2 < s pow 2` MP_TAC THENL
           [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
            ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
          SUBGOAL_THEN `s pow 2 < sqrt(tt - a) pow 2` MP_TAC THENL
           [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
            SUBGOAL_THEN `&0 <= tt - a` (fun th -> SIMP_TAC[th; SQRT_POW_2]) THEN
            ASM_REAL_ARITH_TAC]];
        REAL_ARITH_TAC];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTER] THEN USE_THEN "inW" MATCH_MP_TAC THEN
      SUBGOAL_THEN `&0 < B - A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < m /\ &0 <= x ==> --m <= x`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 < m /\ x <= &1 ==> x <= &1 + m`) THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  ABBREV_TAC `seg = \tau'. chart_inv ((U:A->bool) INTER W,(phi:A->real^N))
                                     ((sol:real^1->real^N)(lift(sqrt tau')))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!tau'. s1 pow 2 <= tau' /\ tau' <= s2 pow 2
                       ==> (seg:real->A) tau' = gamma tau'` ASSUME_TAC THENL
   [X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= tau'` ASSUME_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s1 /\ &0 <= s2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s1 <= sqrt tau' /\ sqrt tau' <= s2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; ARITH_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `A pow 2 <= tau'` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "WIN" (MP_TAC o SPEC `sqrt tau'`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "PATH" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `A pow 2 <= tau'`)]) THEN
    EXPAND_TAC "seg" THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a:real`; `r:real`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN USE_THEN "inW" MATCH_MP_TAC THEN
    SUBGOAL_THEN `&0 < B - A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < m /\ &0 <= x ==> --m <= x`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < m /\ x <= &1 ==> x <= &1 + m`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `seg:real->A`; `gamma:real->A`;
                 `\tau'. if tau' <= s1 pow 2 then (gamma:real->A) tau' else seg tau'`;
                 `s2 pow 2`; `s1 pow 2`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[];
      X_GEN_TAC `tau':real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau' = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt x (s2 pow 2) (gamma:real->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `s2 pow 2`;
                   `\tau'. if tau' <= s1 pow 2 then (gamma:real->A) tau' else seg tau'`;
                   `gamma:real->A`] P2ARC_ADMX_CONG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `tau':real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s2:real) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 <= ss` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s2:real = B` ASSUME_TAC THENL
   [UNDISCH_TAC `min B (ss + d / &2) = s2` THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt x (s2 pow 2) (gamma:real->A)` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The choice of the vertical piece length D0 = D (rho^2 - d^2) / (2 rho^2)  *)
(* and its arithmetic, and the integral of the constant piece (as in         *)
(* P2AO_VERT_EXT_VIEW).                                                      *)
(* ========================================================================= *)

let P2ARC_D0_ARITH = prove
 (`!b D d rho.
     &0 < b /\ &0 < D /\ &0 <= d /\ d < rho
     ==> &0 < D * (rho pow 2 - d pow 2) / (&2 * rho pow 2) /\
         D * (rho pow 2 - d pow 2) / (&2 * rho pow 2) < D /\
         sqrt(b + D * (rho pow 2 - d pow 2) / (&2 * rho pow 2)) < sqrt(b + D) /\
         d pow 2 /
         (&2 * (sqrt(b + D) - sqrt(b + D * (rho pow 2 - d pow 2) / (&2 * rho pow 2)))) <=
         sqrt(b + D) * rho pow 2 / D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho /\ d pow 2 < rho pow 2 /\ &0 < rho pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D0 = D * (rho pow 2 - d pow 2) / (&2 * rho pow 2)` THEN
  SUBGOAL_THEN `&0 < D0 /\ D0 < D /\ (D - D0) * rho pow 2 = D * (rho pow 2 + d pow 2) / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &2 * x`] THEN
      MP_TAC(SPEC `d:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < rho pow 2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = sqrt(b + D0)` THEN ABBREV_TAC `B = sqrt(b + D)` THEN
  SUBGOAL_THEN `&0 < A /\ A < B /\ A pow 2 = b + D0 /\ B pow 2 = b + D` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &2 * (B - A)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(B * rho pow 2 / D) * (&2 * (B - A)) = (&2 * (B - A) * B * rho pow 2) / D`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(B - A) * (B + A) = D - D0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(B - A) * (B + A) = B pow 2 - A pow 2` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B - A) * (B + A) <= &2 * (B - A) * B` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * (B - A) * B - (B - A) * (B + A) = (B - A) pow 2` MP_TAC THENL
     [CONV_TAC REAL_RING; MP_TAC(SPEC `B - A` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(D - D0) * rho pow 2` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d pow 2 * D <= rho pow 2 * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(B - A) * (B + A) = D - D0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

(* The constant piece contributes at most K Rmax (b2 - b). *)

let P2ARC_CONST_INTEGRAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (y:A) b b2 Rmax K.
     &0 < b /\ b < b2 /\ &0 <= Rmax /\ sqrt b2 <= K /\
     p2a_lseg V tt b b2 (\tau. y) /\
     (!s. tt - b2 <= s /\ s <= tt - b
          ==> mfd_scalar (p2a_vatlas V s) (p2a_vmetric V s) y <= Rmax)
     ==> real_integral (real_interval[b,b2]) (p2a_L_integrand V tt (\tau. y) b2) <=
         K * Rmax * (b2 - b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[b,b2]) (\sig. K * Rmax)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `p2a_lseg (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt b b2 (\tau. (y:A))` THEN
      REWRITE_TAC[p2a_lseg] THEN SIMP_TAC[];
      X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)`; `tt:real`; `y:A`; `b2:real`;
                     `sig:real`] P2AO_CONST_INTEGRAND) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt sig * Rmax` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]];
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The integral of the moving piece.  On [A^2,B^2] the curve follows c((sqrt *)
(* tau - A)/(B - A)) for a curve c of the slice s0 with constant speed d;    *)
(* its speed at tau in the slice tt - tau is at most sqrt(Lam) d / (2 sqrt   *)
(* tau (B - A)) (P2ARC_SPEED_CMP), so the L-integrand is at most B Rmax +    *)
(* Lam d^2 / (4 (B - A)^2 sqrt tau).                                         *)
(* ========================================================================= *)

let P2ARC_H_DERIV = prove
 (`!A B tau. &0 < tau
     ==> ((\t. (sqrt t - A) / (B - A)) has_real_derivative (inv(&2 * sqrt tau) / (B - A)))
         (atreal tau)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  SUBGOAL_THEN `inv(&2 * sqrt tau) = inv(&2 * sqrt tau) - &0` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; HAS_REAL_DERIVATIVE_CONST; ETA_AX]);;

let P2ARC_MOVE_INTEGRAL = prove
 (`!(hs:(A)rfs_history) tt W a r s0 (c:real->A) d A B (gf:real->A) Rmax Lam x.
     p2a_region (rfs_view hs) W a r /\
     a < s0 /\ s0 < r /\ &0 < A /\ A < B /\ tt - A pow 2 < r /\ s0 <= tt - B pow 2 /\
     &0 <= Rmax /\ &0 <= Lam /\
     mfd_c1_curve (rfs_top_at hs s0,rfs_atlas_at hs s0) c (&0) (&1) /\
     (!u. u IN real_interval[&0,&1] ==> c u IN W) /\
     (!u. u IN real_interval[&0,&1]
          ==> mfd_speed (rfs_atlas_at hs s0) (rfs_metric_at hs s0) c (&0) (&1) u = d) /\
     (!s y. s0 <= s /\ s <= r /\ y IN W
            ==> mfd_scalar (rfs_atlas_at hs s) (rfs_metric_at hs s) y <= Rmax) /\
     (!s y v. s0 <= s /\ s <= r /\ y IN W
              ==> v dot (p2ah_fam hs W r s y ** v) <=
                  Lam * (v dot (p2ah_fam hs W r s0 y ** v))) /\
     p2a_admx (rfs_view hs) tt x (B pow 2) gf /\
     (!tau. A pow 2 <= tau ==> gf tau = c((sqrt tau - A) / (B - A)))
     ==> real_integral (real_interval[A pow 2,B pow 2])
           (p2a_L_integrand (rfs_view hs) tt gf (B pow 2)) <=
         B * Rmax * (B pow 2 - A pow 2) + Lam * d pow 2 / (&2 * (B - A))`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "reg as0 s0r A0 AB tA s0B Rm Lm c1 inW spd Rb cmp adm gfe" THEN
  SUBGOAL_THEN `&0 < B - A /\ &0 < A pow 2 /\ A pow 2 < B pow 2 /\
                sqrt(A pow 2) = A /\ sqrt(B pow 2) = B` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `h = \t. (sqrt t - A) / (B - A)` THEN
  ABBREV_TAC `h' = \t. inv(&2 * sqrt t) / (B - A)` THEN
  (* the time change *)
  SUBGOAL_THEN
   `!t. t IN real_interval[A pow 2,B pow 2]
        ==> (h:real->real) t IN real_interval[&0,&1] /\
            (h has_real_derivative (h':real->real) t)
            (atreal t within real_interval[A pow 2,B pow 2])`
  (LABEL_TAC "H") THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `A <= sqrt t /\ sqrt t <= B` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `sqrt(A pow 2) <= sqrt t` MP_TAC THENL
         [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `sqrt t <= sqrt(B pow 2)` MP_TAC THENL
         [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "h" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MAP_EVERY EXPAND_TAC ["h"; "h'"] THEN MATCH_MP_TAC P2ARC_H_DERIV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real->real) real_continuous_on real_interval[A pow 2,B pow 2]`
  ASSUME_TAC THENL
   [EXPAND_TAC "h'" THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[ETA_AX; REAL_CONTINUOUS_ON_SQRT];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < sqrt t` MP_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the moved curve *)
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) s0) (rfs_atlas_at hs s0)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2ARC_REGION_FACTS) THEN
    DISCH_THEN(MP_TAC o SPEC `s0:real` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (rfs_top_at (hs:(A)rfs_history) s0,rfs_atlas_at hs s0)
                  ((c:real->A) o (h:real->real)) (A pow 2) (B pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`; `h':real->real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN real_interval[A pow 2,B pow 2] ==> ((c:real->A) o (h:real->real)) u IN W`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "inW" MATCH_MP_TAC THEN USE_THEN "H" (MP_TAC o SPEC `u:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[A pow 2,B pow 2]
        ==> mfd_speed (rfs_atlas_at (hs:(A)rfs_history) s0) (rfs_metric_at hs s0)
                      ((c:real->A) o (h:real->real)) (A pow 2) (B pow 2) t =
            inv(&2 * sqrt t) / (B - A) * d`
  (LABEL_TAC "SPD0") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s0`; `rfs_atlas_at (hs:(A)rfs_history) s0`;
                   `rfs_metric_at (hs:(A)rfs_history) s0`; `c:real->A`; `&0`; `&1`;
                   `h:real->real`; `h':real->real`; `A pow 2`; `B pow 2`; `t:real`]
                  GRGD_SPEED_REPARAM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `(h:real->real) t IN real_interval[&0,&1]` ASSUME_TAC THENL
     [USE_THEN "H" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "spd" (fun th -> ASM_SIMP_TAC[th]) THEN
    EXPAND_TAC "h'" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &2 * x`) THEN
    MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `(t:real) IN real_interval[A pow 2,B pow 2]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the bound and its integral *)
  ABBREV_TAC `kk = Lam * d pow 2 / (&4 * (B - A) pow 2)` THEN
  SUBGOAL_THEN
   `((\t. B * Rmax + kk * inv(sqrt t)) has_real_integral
     (B * Rmax * (B pow 2 - A pow 2) + Lam * d pow 2 / (&2 * (B - A))))
    (real_interval[A pow 2,B pow 2])`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `B * Rmax * (B pow 2 - A pow 2) + Lam * d pow 2 / (&2 * (B - A)) =
                  (B * Rmax) * (B pow 2 - A pow 2) +
                  kk * (&2 * sqrt(B pow 2) - &2 * sqrt(A pow 2))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "kk" THEN
      UNDISCH_TAC `&0 < B - A` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC P2ARC_INV_SQRT_INTEGRAL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  MATCH_MP_TAC P2ARC_INTEGRAL_LE_INTERIOR THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `B pow 2`] THEN CONJ_TAC THENL
     [USE_THEN "adm" (MP_TAC o REWRITE_RULE[p2a_admx]) THEN SIMP_TAC[];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real) IN real_interval[A pow 2,B pow 2]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ &0 < sqrt t /\ sqrt t <= B` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT] THEN
    SUBGOAL_THEN `sqrt t <= sqrt(B pow 2)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gf:real->A) t = ((c:real->A) o (h:real->real)) t /\
                (!s. s IN real_interval[A pow 2,B pow 2]
                     ==> (gf:real->A) s = ((c:real->A) o (h:real->real)) s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN EXPAND_TAC "h" THEN CONJ_TAC THENL
     [USE_THEN "gfe" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      USE_THEN "gfe" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_L_integrand; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN BETA_TAC THEN
  (* the speed through the moved curve *)
  SUBGOAL_THEN
   `mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (tt - t)) (rfs_metric_at hs (tt - t))
              (gf:real->A) (&0) (B pow 2) t =
    mfd_speed (rfs_atlas_at hs (tt - t)) (rfs_metric_at hs (tt - t))
              ((c:real->A) o (h:real->real)) (A pow 2) (B pow 2) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2A_SPEED_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`A pow 2`; `B pow 2`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `r:real`; `tt - t`; `s0:real`;
                 `Lam:real`; `(c:real->A) o (h:real->real)`; `A pow 2`; `B pow 2`; `t:real`]
                P2ARC_SPEED_CMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:A`; `v:real^3`] THEN DISCH_TAC THEN
      USE_THEN "cmp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "SPD0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `(t:real) IN real_interval[A pow 2,B pow 2]`)]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - t)) (rfs_metric_at hs (tt - t))
                           (((c:real->A) o (h:real->real)) t) <= Rmax`
  ASSUME_TAC THENL
   [USE_THEN "Rb" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `st = sqrt t` THEN
  ABBREV_TAC `Sp = mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (tt - t))
                     (rfs_metric_at hs (tt - t)) ((c:real->A) o (h:real->real))
                     (A pow 2) (B pow 2) t` THEN
  ABBREV_TAC `Rc = mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - t))
                     (rfs_metric_at hs (tt - t)) (((c:real->A) o (h:real->real)) t)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `st * (Rmax + Lam * (inv(&2 * st) / (B - A) * d) pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `st * Lam * (inv(&2 * st) / (B - A) * d) pow 2 = kk * inv st` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN UNDISCH_TAC `&0 < st` THEN UNDISCH_TAC `&0 < B - A` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `st * Rmax <= B * Rmax` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The assembly, history form.  The history bridge P2AB_HIST_VIEW_X turns    *)
(* rfs_L_adm into p2a_admx and persisting sets into regions; gamma is        *)
(* continued by the constant piece at gamma b on [b, b + D0] and by the      *)
(* geodesic from gamma b to z on [b + D0, b + D] (P2ARC_ADMX_PATH), the      *)
(* corner is smoothed (P2AXS_SMOOTHING_X) and the result is rfs_L_adm by the *)
(* bridge.                                                                   *)
(* ========================================================================= *)

let P2ARC_BALL_REACH = prove
 (`!u:A->bool. P2ARC_BALL_REACH_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2ARC_BALL_REACH_STATEMENT] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "hok ladm D bD eta Rm Lm rho xin par pers ball Rb cmp" THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `e:real`] THEN INTRO_TAC "zin e" THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_L_adm]; ALL_TAC] THEN
  MP_TAC(ISPEC `(:A)` P2AB_HIST_VIEW_X) THEN REWRITE_TAC[P2A_HIST_VIEW_X_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `tt < rfs_horizon (hs:(A)rfs_history)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_TOPSPACE_LIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tt - b - D /\ tt - b - D < tt - b /\ tt - b < tt` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the slice tt - b - D *)
  SUBGOAL_THEN `hausdorff_space (rfs_top_at (hs:(A)rfs_history) (tt - b - D)) /\
                smooth_manifold_atlas (rfs_top_at hs (tt - b - D)) (rfs_atlas_at hs (tt - b - D)) /\
                riemannian_metric (rfs_atlas_at hs (tt - b - D)) (rfs_metric_at hs (tt - b - D)) /\
                compact_space (rfs_top_at hs (tt - b - D))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - b - D`] P3_HIST_VIEW_SLICES) THEN
    ASM_REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_svs (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) b IN W` ASSUME_TAC THENL
   [USE_THEN "ball" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
    USE_THEN "zin" (MP_TAC o REWRITE_RULE[mfd_ball; IN_ELIM_THM]) THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  (* the region *)
  ABBREV_TAC `a = (tt - b - D) - min eta ((tt - b - D) / &2)` THEN
  SUBGOAL_THEN `&0 <= a /\ a < tt - b - D /\ tt - b - D - eta <= a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (rfs_view (hs:(A)rfs_history)) W a (tt - b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2arc_mentions "rfs_persists" th && p2arc_mentions "p2a_region" th)) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2A_PERSISTS_MONO THEN EXISTS_TAC `tt - b - D - eta` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b gamma` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2arc_mentions "p2a_admx" th && p2arc_mentions "rfs_L_adm" th)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the geodesic from gamma b to z *)
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) (tt - b - D)`;
                 `rfs_atlas_at (hs:(A)rfs_history) (tt - b - D)`;
                 `rfs_metric_at (hs:(A)rfs_history) (tt - b - D)`; `(gamma:real->A) b`;
                 `z:A`; `rho:real`] P2ARC_GEO_PATH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `m:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "spd") (LABEL_TAC "cball")))))))))))) THEN
  SUBGOAL_THEN `!u. u IN real_interval[--m,&1 + m] ==> (c:real->A) u IN W` (LABEL_TAC "cW")
  THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "ball" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    USE_THEN "cball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN real_interval[&0,&1] ==> (c:real->A) u IN W` (LABEL_TAC "cW01")
  THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    USE_THEN "cW" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the vertical piece length D0 and the scales A, B *)
  MP_TAC(ISPECL [`b:real`; `D:real`; `d:real`; `rho:real`] P2ARC_D0_ARITH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D0 = D * (rho pow 2 - d pow 2) / (&2 * rho pow 2)` THEN
  ABBREV_TAC `A = sqrt(b + D0)` THEN ABBREV_TAC `B = sqrt(b + D)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "arith")))) THEN
  SUBGOAL_THEN `&0 < A /\ A pow 2 = b + D0 /\ B pow 2 = b + D` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the constant piece *)
  SUBGOAL_THEN `p2a_smooth (rfs_view (hs:(A)rfs_history)) ((gamma:real->A) b) (tt - b)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_admx (rfs_view (hs:(A)rfs_history)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `(gamma:real->A) b`; `W:A->bool`;
                 `a:real`; `b:real`; `b + D0`] P2AO_CONST_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `gc = \tau. if tau <= b then (gamma:real->A) tau else gamma b` THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`;
                 `\tau:real. (gamma:real->A) b`; `gamma:real->A`; `gc:real->A`; `b + D0`;
                 `b:real`] P2AXR_SEG_GLUE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "gc" THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    X_GEN_TAC `tau:real` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Lgc"))] THEN
  (* the geodesic in the slice tt - b *)
  SUBGOAL_THEN `mfd_c1_curve (p2a_vtop (rfs_view (hs:(A)rfs_history)) (tt - b),
                              p2a_vatlas (rfs_view hs) (tt - b)) (c:real->A) (--m) (&1 + m)`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2ARC_REGION_FACTS o
      check (fun th -> p2arc_mentions "p2a_region" th && not(is_forall(concl th)))) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `tt - b` th) THEN MP_TAC(SPEC `tt - b - D` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) (tt - b - D)`;
                   `rfs_atlas_at (hs:(A)rfs_history) (tt - b - D)`;
                   `rfs_top_at (hs:(A)rfs_history) (tt - b)`;
                   `rfs_atlas_at (hs:(A)rfs_history) (tt - b)`;
                   `W:A->bool`; `W:A->bool`; `\w:A. w`; `\w:A. w`;
                   `rfs_metric_at (hs:(A)rfs_history) (tt - b)`; `c:real->A`; `--m`; `&1 + m`;
                   `&0`] P2ARC_PB_SPEED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(\w:A. w) o (c:real->A) = c` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `gc:real->A`; `W:A->bool`;
                 `a:real`; `tt - b`; `c:real->A`; `m:real`; `A:real`; `B:real`]
                P2ARC_ADMX_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "gc" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(b + D0 <= b)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `gf = \tau. if tau <= A pow 2 then (gc:real->A) tau
                         else (c:real->A)((sqrt tau - A) / (B - A))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!tau. A pow 2 <= tau
                      ==> (gf:real->A) tau = (c:real->A)((sqrt tau - A) / (B - A))`
  (LABEL_TAC "gfe") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN EXPAND_TAC "gf" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `tau = A pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_SUB_REFL; real_div; REAL_MUL_LZERO] THEN
    EXPAND_TAC "gc" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(b + D0 <= b)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the length *)
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `gf:real->A`;
                 `B pow 2`; `A pow 2`] P2AXR_LENGTH_SPLIT_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "split")] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `A pow 2`; `gc:real->A`;
                 `gf:real->A`] P2ARC_ADMX_CONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    EXPAND_TAC "gf" THEN ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "Lgf" o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `(gamma:real->A) b`; `b:real`;
                 `b + D0`; `Rmax:real`; `B:real`] P2ARC_CONST_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      REWRITE_TAC[P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
      USE_THEN "Rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `W:A->bool`; `a:real`; `tt - b`;
                 `tt - b - D`; `c:real->A`; `d:real`; `A:real`; `B:real`; `gf:real->A`;
                 `Rmax:real`; `Lam:real`; `x:A`] P2ARC_MOVE_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  (* smoothing and the conclusion *)
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `tt:real`; `x:A`; `B pow 2`; `gf:real->A`;
                 `e:real`] P2AXS_SMOOTHING_X) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[P2A_ATLAS_LC_HIST]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->A` (CONJUNCTS_THEN2 (LABEL_TAC "g1adm")
    (CONJUNCTS_THEN2 (LABEL_TAC "g1end") (LABEL_TAC "g1L")))) THEN
  EXISTS_TAC `g1:real->A` THEN
  SUBGOAL_THEN `b + D = B pow 2` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      p2arc_mentions "p2a_adm1" th && p2arc_mentions "rfs_L_adm" th &&
      not(p2arc_mentions "p2a_min" th))) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "g1adm" ACCEPT_TAC];
    USE_THEN "g1end" SUBST1_TAC THEN
    USE_THEN "gfe" (MP_TAC o SPEC `B pow 2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `sqrt(B pow 2) = B` SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(B - A) / (B - A) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P2A_L_LENGTH_VIEW] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p2a_L_length (rfs_view (hs:(A)rfs_history)) tt gf (B pow 2) + e` THEN
  CONJ_TAC THENL [USE_THEN "g1L" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_L_length (rfs_view (hs:(A)rfs_history)) tt gf (B pow 2) =
                p2a_L_length (rfs_view hs) tt gamma b +
                real_integral (real_interval[b,b + D0])
                  (p2a_L_integrand (rfs_view hs) tt (\tau. (gamma:real->A) b) (b + D0)) +
                real_integral (real_interval[A pow 2,B pow 2])
                  (p2a_L_integrand (rfs_view hs) tt gf (B pow 2))`
  SUBST1_TAC THENL
   [USE_THEN "split" SUBST1_TAC THEN USE_THEN "Lgf" SUBST1_TAC THEN
    SUBGOAL_THEN `p2a_L_length (rfs_view (hs:(A)rfs_history)) tt gc (A pow 2) =
                  p2a_L_length (rfs_view hs) tt gc (b + D0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "Lgc" SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Lam * d pow 2 / (&2 * (B - A)) <= B * (Lam * rho pow 2 / D)` MP_TAC THENL
   [SUBGOAL_THEN `B * (Lam * rho pow 2 / D) = Lam * (B * rho pow 2 / D)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `B pow 2 - A pow 2 = D - D0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `real_integral (real_interval[A pow 2,B pow 2])
                 (p2a_L_integrand (rfs_view (hs:(A)rfs_history)) tt (gf:real->A) (B pow 2)) <=
               B * Rmax * (B pow 2 - A pow 2) + Lam * d pow 2 / (&2 * (B - A))` THEN
  UNDISCH_TAC `real_integral (real_interval[b,b + D0])
                 (p2a_L_integrand (rfs_view (hs:(A)rfs_history)) tt (\tau. (gamma:real->A) b)
                                  (b + D0)) <=
               B * Rmax * ((b + D0) - b)` THEN
  UNDISCH_TAC `B pow 2 - A pow 2 = D - D0` THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

