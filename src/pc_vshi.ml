(* ========================================================================= *)
(* pc_vshi: Shi's local derivative estimates for views, in a file with few   *)
(* dependencies. It contains renamed copies, each with its origin, of the    *)
(* chain behind P2BU_SHI_VIEW_CC and P2BU_KR_BOUND (pc_p2c_blowup), taken    *)
(* from pc_p2c_fl511, pc_p2c_cgunif, pc_p2c_l112 and pc_apx_local; the       *)
(* copies carry VSHI_ names, so that files loading both the originals and    *)
(* pc_vshi have no name clash. It depends only on RFA_P2_THM_3_28            *)
(* (pc_rfa_shi328) and the rescaling base (pc_rfa_shiscale). Main results:   *)
(* the view estimate VSHI_SHI_VIEW_CC, and the scaled curvature-derivative   *)
(* bound VSHI_KR_BOUND in the form of the Kr hypotheses of the statements    *)
(* P2C_REQ_CAP_FIX and P2C_REQ_SLICE_FIX.                                    *)
(* ========================================================================= *)

needs "src/pc_rfa_shiscale.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The renamed copies, in dependency order.                                  *)
(* ========================================================================= *)

(* VSHI_MPULLBACK_CHART_INDEP: renamed copy of APX_MPULLBACK_CHART_INDEP (pc_apx_local.ml). *)

let VSHI_MPULLBACK_CHART_INDEP = prove
 (`!top atlas (V:A->bool) (psi:A->real^N) V' psi' (g:A->real^N^N)
    (h:real^N->A) N z.
        smooth_manifold_atlas top atlas /\ (V,psi) IN atlas /\
        (V',psi') IN atlas /\
        open N /\ z IN N /\ (!w. w IN N ==> h w IN V INTER V') /\
        (psi o h) differentiable at z
        ==> mpullback (psi o h) (metric_local atlas (V,psi) g) z =
            mpullback (psi' o h) (metric_local atlas (V',psi') g) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->A) z IN V INTER V'` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative ((psi':A->real^N) o h) (at z) =
    chart_jac (V,psi) (V',psi') ((h:real^N->A) z) o
    frechet_derivative ((psi:A->real^N) o h) (at z)`
  ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `frechet_derivative
        (chart_trans (V:A->bool,psi:A->real^N) (V',psi') o
         ((psi:A->real^N) o (h:real^N->A))) (at z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `N:real^N->bool` THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHART_TRANS_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h:real^N->A) w IN V INTER V'` MP_TAC THENL
       [ASM_SIMP_TAC[]; SIMP_TAC[IN_INTER]];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; o_THM] THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (V:A->bool,psi:A->real^N) (V',psi') ((h:real^N->A) z)) /\
    linear(frechet_derivative ((psi:A->real^N) o h) (at z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN ASM_SIMP_TAC[MATRIX_COMPOSE] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`; `V':A->bool`; `psi':A->real^N`;
                 `g:A->real^N^N`; `(h:real^N->A) z`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* VSHI_PARAM_CHART_REP: renamed copy of APX_PARAM_CHART_REP (pc_apx_local.ml). *)

let VSHI_PARAM_CHART_REP = prove
 (`!top atlas s (e:real^N->A) (V:A->bool) (psi:A->real^N).
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        (V,psi) IN atlas
        ==> ?e'. diffeomorphism_on {z | z IN s /\ e z IN V}
                                   (IMAGE psi (V INTER IMAGE e s))
                                   (psi o e) (e' o chart_inv (V,psi)) /\
                 (!z. z IN s ==> e'(e z) = z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[mfd_param] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param"))
        (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `e':A->real^N`) THEN
  EXISTS_TAC `e':A->real^N` THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`;
                 `open_set_atlas (:real^N)`; `s:real^N->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `IMAGE (e:real^N->A) s`; `e:real^N->A`; `e':A->real^N`;
                 `(:real^N)`; `\x:real^N. x`; `V:A->bool`; `psi:A->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; open_set_atlas; IN_SING] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^N. x) {x | x IN (:real^N) INTER s /\ (e:real^N->A) x IN V} =
    {z | z IN s /\ e z IN V}`
  SUBST1_TAC THENL [REWRITE_TAC[IMAGE_ID; INTER_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | y IN V INTER IMAGE (e:real^N->A) s /\ (e':A->real^N) y IN (:real^N)} =
    V INTER IMAGE e s`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(psi:A->real^N) o (e:real^N->A) o chart_inv ((:real^N),\x:real^N. x) =
    psi o e`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. x) o (e':A->real^N) o chart_inv (V:A->bool,psi:A->real^N) =
    e' o chart_inv (V,psi)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* VSHI_RFS_PULLBACK_CHART: renamed copy of APX_RFS_PULLBACK_CHART (pc_apx_local.ml). *)

let VSHI_RFS_PULLBACK_CHART = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) (V:A->bool) (psi:A->real^N) z.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        (V,psi) IN atlas /\ z IN s /\ e z IN V
        ==> rfs_pullback atlas e g z =
            mpullback (psi o e) (metric_local atlas (V,psi) g) z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param"))
          (concl th))) THEN
  SUBGOAL_THEN `(e:real^N->A) z IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s:real^N->bool`; `e:real^N->A`; `s:real^N->bool`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) z`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_pullback] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) z)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V':A->bool`; `psi':A->real^N`] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSHI_MPULLBACK_CHART_INDEP THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `{w | w IN s /\ (e:real^N->A) w IN V INTER V'}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                  MFDM_CHART) THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `(V:A->bool,psi:A->real^N)` th) THEN
      MP_TAC(SPEC `(V':A->bool,psi':A->real^N)` th)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; GSYM OPEN_IN];
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    SIMP_TAC[IN_ELIM_THM];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                  VSHI_PARAM_CHART_REP) THEN
    ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`{z | z IN s /\ (e:real^N->A) z IN V}`;
                   `(psi:A->real^N) o (e:real^N->A)`; `z:real^N`; `vec 0:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

(* VSHI_PARAM_LOCAL_REP: renamed copy of APX_PARAM_LOCAL_REP (pc_apx_local.ml). *)

let VSHI_PARAM_LOCAL_REP = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_param top atlas s e /\ y IN s
        ==> ?N N' h'.
              open N /\ y IN N /\ N SUBSET s /\
              diffeomorphism_on N N' (SND(chart_at atlas (e y)) o e) h' /\
              metric_field N' (metric_local atlas (chart_at atlas (e y)) g) /\
              (!z. z IN N
                   ==> rfs_pullback atlas e g z =
                       mpullback (SND(chart_at atlas (e y)) o e)
                                 (metric_local atlas (chart_at atlas (e y)) g) z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param"))
          (concl th))) THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s:real^N->bool`; `e:real^N->A`; `s:real^N->bool`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `psi:A->real^N`]
                VSHI_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`{z | z IN s /\ (e:real^N->A) z IN V}`;
    `IMAGE (psi:A->real^N) (V INTER IMAGE (e:real^N->A) s)`;
    `(e2:A->real^N) o chart_inv (V:A->bool,psi:A->real^N)`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on];
    SET_TAC[];
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; SET_TAC[]]];
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC VSHI_RFS_PULLBACK_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* VSHI_PULLBACK_SECTIONAL_GEN: renamed copy of APX_PULLBACK_SECTIONAL_GEN (pc_apx_local.ml). *)

let VSHI_PULLBACK_SECTIONAL_GEN = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) y u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_param top atlas s e /\ y IN s
        ==> lsectional (rfs_pullback atlas e g) y u v =
            mfd_sectional atlas g (e y)
              (frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) u)
              (frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                VSHI_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  TRANS_TAC EQ_TRANS
   `lsectional (mpullback (SND(chart_at atlas ((e:real^N->A) y)) o e)
                          (metric_local atlas (chart_at atlas (e y))
                                        (g:A->real^N^N))) y u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`N':real^N->bool`; `N:real^N->bool`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) o e`;
                   `h':real^N->real^N`;
                   `metric_local atlas (chart_at atlas ((e:real^N->A) y))
                                 (g:A->real^N^N)`; `y:real^N`; `u:real^N`; `v:real^N`]
                  MFDR_LSECTIONAL_PULLBACK) THEN
    ASM_REWRITE_TAC[o_THM; mfd_sectional]]);;

(* VSHI_BALL_SUBSET: renamed copy of P2CU_BALL_SUBSET (pc_p2c_cgunif.ml). *)

let VSHI_BALL_SUBSET = prove
 (`!top atlas (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas
     ==> mfd_ball (top,atlas) g x r SUBSET topspace top`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

(* VSHI_C1_CURVE_RESTRICT: renamed copy of P2CW_C1_CURVE_RESTRICT (pc_p2c_fl511.ml). *)

let VSHI_C1_CURVE_RESTRICT = prove
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

(* VSHI_LENGTH_RESTRICT: renamed copy of P2CW_LENGTH_RESTRICT (pc_p2c_fl511.ml). *)

let VSHI_LENGTH_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) (gamma:real->A) a b.
     smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_length (restrict_atlas atlas W) (restrict_metric atlas W g) gamma a b =
         mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VSHI_C1_CURVE_RESTRICT) THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
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

(* VSHI_BALL_CURVE: renamed copy of P2C_BALL_CURVE (pc_p2c_l112.ml). *)

let VSHI_BALL_CURVE = prove
 (`!top atlas (g:A->real^N^N) x y r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN mfd_ball (top,atlas) g x r
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y /\
                 mfd_length atlas g gamma (&0) (&1) < r`,
  REWRITE_TAC[mfd_ball; IN_ELIM_THM; mfd_dist; mfd_joinable] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y}`; `r:real`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN MESON_TAC[]]);;

(* VSHI_RESTRICT_BALL: renamed copy of P2CW_RESTRICT_BALL (pc_p2c_fl511.ml). *)

let VSHI_RESTRICT_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) x r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W
     ==> mfd_ball (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g) x r
         SUBSET mfd_ball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`] RIEMANNIAN_METRIC_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `x:A`; `y:A`; `r:real`] VSHI_BALL_CURVE) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP VSHI_C1_CURVE_RESTRICT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] VSHI_LENGTH_RESTRICT) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* VSHI_REGION_BALL_COMPACT_CC: renamed copy of P2BU_REGION_BALL_COMPACT_CC (pc_p2c_blowup.ml). *)

let VSHI_REGION_BALL_COMPACT_CC = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W y r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top (top closure_of W) /\
     open_in top W /\ &0 < r /\ mfd_ball (top,atlas) g y (&2 * r) SUBSET W
     ==> compact_in (subtopology top W)
           (subtopology top W closure_of
            mfd_ball (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g) y r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = mfd_ball (subtopology top W,
                            restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) W)
                           (restrict_metric atlas W (g:A->real^3^3)) (y:A) r` THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) y r` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC VSHI_RESTRICT_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (S:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) y (&2 * r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) y r` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) y r` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET W` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) W`;
                   `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) W g`; `y:A`; `r:real`]
           VSHI_BALL_SUBSET) THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(W:A->bool) INTER S = S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) INTER (top closure_of S) = top closure_of S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `(top:A topology) closure_of W` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W:A->bool` THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
      ASM_REWRITE_TAC[]];
    ASM SET_TAC[]]);;

(* VSHI_BALL_MONO: renamed copy of P2CU_BALL_MONO (pc_p2c_cgunif.ml). *)

let VSHI_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) x r s.
     r <= s ==> mfd_ball (top,atlas) g x r SUBSET mfd_ball (top,atlas) g x s`,
  REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LTE_TRANS]);;

(* VSHI_BALL_SHIFT: renamed copy of P2CU_BALL_SHIFT (pc_p2c_cgunif.ml). *)

let VSHI_BALL_SHIFT = prove
 (`!top atlas (g:A->real^N^N) x y A r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN mfd_ball (top,atlas) g x A
     ==> mfd_ball (top,atlas) g y r SUBSET mfd_ball (top,atlas) g x (A + r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_TRANS];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* VSHI_SHI_SCALED: renamed copy of P2CW_SHI_SCALED (pc_p2c_fl511.ml). *)

let VSHI_SHI_SCALED = prove
 (`!l K A tau.
     &0 < K /\ &0 < A /\ &0 < tau
     ==> ?C. !top atlas a b (g:real->A->real^3^3) x q.
               hausdorff_space top /\ rfs_flow_upto (top,atlas) a b g /\ &0 < q /\
               tau <= q * (b - a) /\ x IN topspace top /\
               compact_in top
                 (top closure_of mfd_ball (top,atlas) (g b) x (A * inv(sqrt q))) /\
               (!t y. a < t /\ t <= b /\
                      y IN mfd_ball (top,atlas) (g b) x (A * inv(sqrt q))
                      ==> mfd_rm_norm atlas (g t) y <= K * q)
               ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) (g b))
                                     (SND(chart_at atlas x) x) <= C * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `(:A)` RFA_P2_THM_3_28) THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `K:real`; `A:real`; `tau:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `Cl:real` THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `x:A`; `q:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `(q * b) / q = b` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `!rr. mfd_ball (top,atlas) (\z. q %% (g:real->A->real^3^3) b z) x rr =
                     mfd_ball (top,atlas) (g b) x (rr * inv(sqrt q))` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) b`; `q:real`; `x:A`; `rr:real`] MFD_BALL_SCALE) THEN
    ASM_SIMP_TAC[real_div];
    ALL_TAC] THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `q * a:real`; `q * b:real`;
    `\t x. q %% (g:real->A->real^3^3) (t / q) x`; `x:A`]) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_RFS_FLOW_UPTO_RESCALE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `a < t / q /\ t / q <= b` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t. (z:A) IN s /\ s SUBSET t ==> z IN t`) THEN
        EXISTS_TAC `mfd_ball (top,atlas) ((g:real->A->real^3^3) b) x (A * inv(sqrt q))` THEN
        ASM_SIMP_TAC[VSHI_BALL_SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `K = (K * q) / q` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) b`; `x:A`; `A / &2 * inv(sqrt q)`]
                  MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[SQRT_POS_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                    ((g:real->A->real^3^3) b)`;
                 `q:real`; `l:num`; `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`]
         RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) b)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < q pow (l + 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_INV] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

(* VSHI_REGULAR_SLICE: renamed copy of P2C_REGULAR_SLICE (pc_p2c_l112.ml). *)

let VSHI_REGULAR_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     p2c_regular_view V /\ x IN topspace(rfs_vtop V t)
     ==> hausdorff_space (rfs_vtop V t) /\
         smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
         riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `t:real` o CONJUNCT1) ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

(* VSHI_VIEW_EXPAND: renamed copy of P2C_VIEW_EXPAND (pc_p2c_l112.ml). *)

let VSHI_VIEW_EXPAND = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     (!t x. rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x) /\
     (!t x r. rfs_vball V t x r =
              mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r) /\
     (!W a b. rfs_persists V W a b <=>
              !s. a < s /\ s <= b
                  ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                      open_in (rfs_vtop V s) W)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vball; rfs_persists; rfs_vtop; rfs_vatlas;
              rfs_vmetric]);;

(* VSHI_VFAM_DERIV_LAST: renamed copy of P2CW_VFAM_DERIV_LAST (pc_p2c_fl511.ml). *)

let VSHI_VFAM_DERIV_LAST = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b l x.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < b /\ x IN W
     ==> lrm_deriv_norm2 l
           (metric_local (restrict_atlas (rfs_vatlas V b) W)
                         (chart_at (restrict_atlas (rfs_vatlas V b) W) x) (p2c_vfam V W b b))
           (SND(chart_at (restrict_atlas (rfs_vatlas V b) W) x) x) =
         p3_vderiv2 V l b x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL VSHI_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] VSHI_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `x:A`]
         MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND; p2c_vfam; ETA_AX; p3_vderiv2] THEN
  MP_TAC(ISPECL [`l:num`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) b`;
                 `(U:A->bool,phi:A->real^3)`; `x:A`] RFA_RMD2_CHART) THEN
  ASM_REWRITE_TAC[FST; SND; rfa_rmd2] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[]]);;

(* VSHI_DIFFEO_DERIV_INJ: renamed copy of P2CW_DIFFEO_DERIV_INJ (pc_p2c_fl511.ml). *)

let VSHI_DIFFEO_DERIV_INJ = prove
 (`!s t (h:real^N->real^N) h'.
     diffeomorphism_on s t h h'
     ==> !y. y IN s
             ==> linear(frechet_derivative h (at y)) /\
                 !u v. frechet_derivative h (at y) u = frechet_derivative h (at y) v
                       ==> u = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) y IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^N) has_derivative frechet_derivative h (at y)) (at y) /\
                ((h':real^N->real^N) has_derivative frechet_derivative h' (at (h y)))
                  (at (h y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`t:real^N->bool`; `h':real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at y))` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `frechet_derivative (h':real^N->real^N) (at (h y)) o
                frechet_derivative (h:real^N->real^N) (at y) = (\w. w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(h':real^N->real^N) o (h:real^N->real^N)` THEN
    EXISTS_TAC `y:real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `open(s:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\w:real^N. w`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN X_GEN_TAC `w:real^N` THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_THM th `u:real^N`) THEN MP_TAC(AP_THM th `v:real^N`)) THEN
  REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

(* VSHI_PULLBACK_METRIC_LOCAL_W: renamed copy of P2C_PULLBACK_METRIC_LOCAL_W (pc_p2c_l112.ml). *)

let VSHI_PULLBACK_METRIC_LOCAL_W = prove
 (`!top atlas W top' atlas' W' (f:A->B) f' (g':B->real^N^N) (U:A->bool)
    (phi:A->real^N) (V:B->bool) (psi:B->real^N) x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas W top' atlas' W' f f' /\
        (U,phi) IN atlas /\ (V,psi) IN atlas' /\ x IN U /\ x IN W /\ f x IN V
        ==> metric_local atlas (U,phi) (mfd_pullback_metric atlas atlas' f g')
                         (phi x) =
            mpullback (psi o f o chart_inv (U,phi))
                      (metric_local atlas' (V,psi) g') (phi x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (W':B->bool)`)) THEN
    UNDISCH_TAC `IMAGE (f:A->B) W SUBSET W'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN U`)]) THEN
  REWRITE_TAC[mfd_pullback_metric] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c0:(A->bool)#(A->real^N)`) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`,
           `c0':(B->bool)#(B->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V0:B->bool`; `psi0:B->real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`U0:A->bool`; `phi0:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U0:A->bool,phi0:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  (* the chart representative h0 of f at x is smooth near phi0 x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W':B->bool`; `f:A->B`; `f':B->A`;
                 `U0:A->bool`; `phi0:A->real^N`; `V0:B->bool`; `psi0:B->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `h0 = (psi0:B->real^N) o (f:A->B) o chart_inv (U0:A->bool,phi0:A->real^N)` THEN
  SUBGOAL_THEN `(h0:real^N->real^N) differentiable at ((phi0:A->real^N) x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi0:A->real^N)
                      {z | z IN U0 INTER W /\ (f:A->B) z IN V0}`;
                   `h0:real^N->real^N`; `(phi0:A->real^N) x`; `vec 0:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h0:real^N->real^N) ((phi0:A->real^N) x) = (psi0:B->real^N) (f x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h0" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the derivative identity, by locality and the chain rule *)
  SUBGOAL_THEN
   `frechet_derivative ((psi:B->real^N) o (f:A->B) o chart_inv (U,phi))
                       (at ((phi:A->real^N) x)) =
    chart_jac (V0,psi0) (V,psi) (f x) o
    frechet_derivative (h0:real^N->real^N) (at ((phi0:A->real^N) x)) o
    chart_jac (U,phi) (U0,phi0) x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`]
                  MFDM_CHART) THEN
    DISCH_THEN(MP_TAC o SPEC `(V0:B->bool,psi0:B->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `frechet_derivative
        (\y. chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)
               ((h0:real^N->real^N)
                  (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)))
        (at ((phi:A->real^N) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `IMAGE (phi:A->real^N)
                    {z | z IN U INTER {z | z IN U0 INTER W /\ (f:A->B) z IN V0} /\
                         f z IN V}` THEN
      REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `open_in top {z | z IN U0 INTER W /\ (f:A->B) z IN V0}` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                         `(U0:A->bool,phi0:A->real^N)`; `(V0:B->bool,psi0:B->real^N)`;
                         `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
          ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                       `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                       `{z | z IN U0 INTER W /\ (f:A->B) z IN V0}`; `f:A->B`]
                      MFDM_CHART_DOMAIN_OPEN) THEN
        REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
          EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
          SIMP_TAC[]];
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXPAND_TAC "h0" THEN
        REWRITE_TAC[o_THM] THEN
        MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                      `U:A->bool`; `phi:A->real^N`; `U0:A->bool`; `phi0:A->real^N`;
                      `z:A`] CHART_TRANS_AT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `w:real^N` THEN
    REWRITE_TAC[chart_jac; SND] THEN
    SUBGOAL_THEN
     `chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) differentiable at (phi x) /\
      chart_trans (U,phi) (U0,phi0) (phi x) = phi0 x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `chart_jac (U:A->bool,phi:A->real^N) (U0,phi0) x` THEN
        MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[IN_INTER];
        MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `chart_trans (V0:B->bool,psi0:B->real^N) (V,psi) differentiable
      at (psi0((f:A->B) x))`
    ASSUME_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `chart_jac (V0:B->bool,psi0:B->real^N) (V,psi) ((f:A->B) x)` THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC
       [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y))
      differentiable at (phi x)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)) =
        h0 o chart_trans (U,phi) (U0,phi0)`
       SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)`;
      `chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)`;
      `(phi:A->real^N) x`; `w:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL
     [`chart_trans (U:A->bool,phi:A->real^N) (U0,phi0)`; `h0:real^N->real^N`;
      `(phi:A->real^N) x`; `w:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LRG_MPULLBACK_EQ] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((psi:B->real^N) o (f:A->B) o chart_inv (U,phi)) ((phi:A->real^N) x) =
    psi (f x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `V0:B->bool`; `psi0:B->real^N`; `V:B->bool`; `psi:B->real^N`;
                `g':B->real^N^N`; `(f:A->B) x`] METRIC_LOCAL_JAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (U:A->bool,phi:A->real^N) (U0,phi0) (x:A)) /\
    linear(chart_jac (V0:B->bool,psi0:B->real^N) (V,psi) ((f:A->B) x)) /\
    linear(frechet_derivative (h0:real^N->real^N) (at ((phi0:A->real^N) x)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE; MATRIX_TRANSP_MUL;
               MATRIX_MUL_ASSOC]);;

(* VSHI_REGULAR_DIFFEO: renamed copy of P2C_REGULAR_DIFFEO (pc_p2c_l112.ml). *)

let VSHI_REGULAR_DIFFEO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s.
     p2c_regular_view V /\ a < s /\ s <= b /\ rfs_persists V W a b
     ==> mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) W (rfs_vtop V b) (rfs_vatlas V b) W
                    (\y:A. y) (\y. y)`,
  REWRITE_TAC[p2c_regular_view] THEN MESON_TAC[]);;

(* VSHI_VFAM_PULLBACK_LOCAL: renamed copy of P2CW_VFAM_PULLBACK_LOCAL (pc_p2c_fl511.ml). *)

let VSHI_VFAM_PULLBACK_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s U (phi:A->real^3) z.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < s /\ s < b /\
     (U,phi) IN rfs_vatlas V b /\ z IN IMAGE phi (U INTER W)
     ==> metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                      (p2c_vfam V W b s) z =
         rfs_pullback (rfs_vatlas V s) (chart_inv (U,phi)) (rfs_vmetric V s) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) o
                REWRITE_RULE[IN_IMAGE]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL VSHI_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN U INTER W` THEN REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (y:A)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN(LABEL_TAC "ch") THEN USE_THEN "ch" SUBST1_TAC THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(s:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam] THEN REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`;
                 `mfd_pullback_metric (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
                    (rfs_vatlas V s) (\y:A. y) (rfs_vmetric V s)`; `y:A`]
         METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s`;
                 `U:A->bool`; `phi:A->real^3`; `U':A->bool`; `psi:A->real^3`; `y:A`]
         VSHI_PULLBACK_METRIC_LOCAL_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC VSHI_REGULAR_DIFFEO THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(y:A) IN U INTER W` THEN SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rfs_pullback] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ch" SUBST1_TAC THEN REWRITE_TAC[SND] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[o_DEF]);;

(* VSHI_VFAM_RM_NORM_LE: renamed copy of P2CW_VFAM_RM_NORM_LE (pc_p2c_fl511.ml). *)

let VSHI_VFAM_RM_NORM_LE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s x.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < s /\ s <= b /\ x IN W
     ==> mfd_rm_norm (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b s) x <=
         p3_vrm V s x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL VSHI_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s) /\
    x IN topspace(rfs_vtop V b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `x:A`] VSHI_REGULAR_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] VSHI_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[p2c_vfam; ETA_AX; p3_vrm] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC MFD_RM_NORM_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3_vrm] THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`; `x:A`]
         MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[mfd_sectional; SND] THEN
  ABBREV_TAC `O = IMAGE (phi:A->real^3) (U INTER W)` THEN
  SUBGOAL_THEN `open(O:real^3->bool) /\ (phi:A->real^3) x IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s) (rfs_vatlas V s) O
              (chart_inv (U:A->bool,phi:A->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_EQ THEN EXISTS_TAC `(\y:A. y) o chart_inv (U:A->bool,phi:A->real^3)` THEN
    ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) b`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
      `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "O" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
      MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC VSHI_REGULAR_DIFFEO THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                     `W:A->bool`; `y:A`] MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                 (U INTER W,phi:A->real^3) (p2c_vfam V W b s)) (phi x) u v =
    lsectional (rfs_pullback (rfs_vatlas V s) (chart_inv (U,phi)) (rfs_vmetric V s))
               (phi x) u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC VSHI_VFAM_PULLBACK_LOCAL THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s`;
                 `O:real^3->bool`; `chart_inv (U:A->bool,phi:A->real^3)`;
                 `(phi:A->real^3) x`; `u:real^3`; `v:real^3`]
         VSHI_PULLBACK_SECTIONAL_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `x:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN
  EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (x:A)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U':A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `W:A->bool`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `U:A->bool`; `phi:A->real^3`; `U':A->bool`;
                 `psi:A->real^3`] MFDR_DIFFEO_CHART_REP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MATCH_MP_TAC VSHI_REGULAR_DIFFEO THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^3) x` o MATCH_MP VSHI_DIFFEO_DERIV_INJ) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->real^3) o (\y:A. y) o chart_inv (U:A->bool,phi:A->real^3) =
                psi o chart_inv (U,phi)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`frechet_derivative ((psi:A->real^3) o chart_inv (U:A->bool,phi:A->real^3))
                                     (at (phi(x:A)))`; `{vec 0:real^3,u,v}`]
         COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]));;

(* VSHI_REGULAR_VFLOW: renamed copy of P2C_REGULAR_VFLOW (pc_p2c_l112.ml). *)

let VSHI_REGULAR_VFLOW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b ==> p2c_vflow V W a b`,
  REWRITE_TAC[p2c_regular_view] THEN MESON_TAC[]);;

(* VSHI_SHI_VIEW_CC: renamed copy of P2BU_SHI_VIEW_CC (pc_p2c_blowup.ml). *)

let VSHI_SHI_VIEW_CC = prove
 (`!l K R tau.
     &0 < K /\ &0 < R /\ &0 < tau
     ==> ?C. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) x0 a b q y.
               p2c_regular_view V /\
               compact_in (rfs_vtop V b)
                 (rfs_vtop V b closure_of rfs_vball V b x0 ((&4 * R) * inv(sqrt q))) /\
               x0 IN topspace(rfs_vtop V b) /\ &0 < q /\ a < b /\ tau <= q * (b - a) /\
               rfs_persists V (rfs_vball V b x0 ((&4 * R) * inv(sqrt q))) a b /\
               (!s z. a < s /\ s <= b /\ z IN rfs_vball V b x0 ((&4 * R) * inv(sqrt q))
                      ==> p3_vrm V s z <= K * q) /\
               y IN rfs_vball V b x0 (R * inv(sqrt q))
               ==> p3_vderiv2 V l b y <= C * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `K:real`; `R:real`; `tau:real`] VSHI_SHI_SCALED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x0:A`; `a:real`; `b:real`; `q:real`; `y:A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x0:A`] VSHI_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R * inv(sqrt q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * R) * inv(sqrt q) = &4 * (R * inv(sqrt q))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `r = R * inv(sqrt q)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VSHI_VIEW_EXPAND]) THEN
  REWRITE_TAC[VSHI_VIEW_EXPAND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(&4 * R) * inv(sqrt q) = &4 * r`]) THEN
  ABBREV_TAC `W = mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) (&4 * r)` THEN
  SUBGOAL_THEN `p2c_vflow (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W a b`
  MP_TAC THENL
   [MATCH_MP_TAC VSHI_REGULAR_VFLOW THEN ASM_REWRITE_TAC[VSHI_VIEW_EXPAND]; ALL_TAC] THEN
  REWRITE_TAC[p2c_vflow; VSHI_VIEW_EXPAND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) r SUBSET W /\
    mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (y:A) (&2 * r) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MATCH_MP_TAC VSHI_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) (r + &2 * r)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSHI_BALL_SHIFT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC VSHI_BALL_MONO THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) W b b =
                restrict_metric (rfs_vatlas V b) W (rfs_vmetric V b)`
  ASSUME_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `l:num`; `y:A`]
         VSHI_VFAM_DERIV_LAST) THEN
  ASM_REWRITE_TAC[VSHI_VIEW_EXPAND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b) W`;
    `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b) W`;
    `a:real`; `b:real`;
    `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) W b`;
    `y:A`; `q:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    MATCH_MP_TAC VSHI_REGION_BALL_COMPACT_CC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_metric (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
                        (rfs_vmetric V b)`; `y:A`; `r:real`] VSHI_BALL_SUBSET) THEN
      ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSHI_VFAM_RM_NORM_LE THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[VSHI_VIEW_EXPAND];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:A) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[]]]);;

(* VSHI_KR_BOUND: renamed copy of P2BU_KR_BOUND (pc_p2c_blowup.ml). *)

let VSHI_KR_BOUND = prove
 (`!top atlas (gA:A->real^N^N) Q c CA y'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas gA /\ y' IN topspace top /\
     &0 < Q /\ &1 <= c /\ &0 <= CA /\
     (!l. l <= 2
          ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y') gA)
                (SND(chart_at atlas y') y') <= CA * Q pow (l + 2))
     ==> !l. l <= 2
             ==> lrm_deriv_norm2 l
                   (metric_local atlas (chart_at atlas y') (\z. c %% (Q %% gA z)))
                   (SND(chart_at atlas y') y') <= CA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y':A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC; METRIC_LOCAL_CMUL] THEN
  SUBGOAL_THEN `&0 < c * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y':A)))
                        (FST(chart_at atlas y'))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y':A))
                    (gA:A->real^N^N)`;
                 `c * Q`; `l:num`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y':A)) y'`]
                RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (gA:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "lrm_deriv_norm2" with _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= inv(c * Q) pow (l + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(c * Q) pow (l + 2) * (CA * Q pow (l + 2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(c * Q) pow (l + 2) * (CA * Q pow (l + 2)) = CA * inv c pow (l + 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; REAL_POW_MUL; REAL_POW_INV] THEN
    SUBGOAL_THEN `~(Q pow (l + 2) = &0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC]);;

