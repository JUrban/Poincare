(* ========================================================================= *)
(* pc_apx_local: local geometry of necks for the Appendix layer (MT Appendix *)
(* A): naturality of curvature under parametrizations (N1b and its Ricci and *)
(* sectional versions), the pulled-back metric of a neck as a metric field,  *)
(* N0, and the SC_SPHERE_SEP discharge of the event chain.                   *)
(* ========================================================================= *)

needs "src/pc_apx_event.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfs_sanity.ml";;
needs "src/pc_smt_sep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Chart independence of pulled-back metric representatives,                 *)
(* chart representatives of parametrizations, rfs_pullback near a point.    *)
(* ------------------------------------------------------------------------- *)

let APX_MPULLBACK_CHART_INDEP = prove
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

(* The chart representative of a parametrization e: psi o e is a            *)
(* diffeomorphism of {z IN s | e z IN V} onto psi(V INTER e(s)).            *)

let APX_PARAM_CHART_REP = prove
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

(* rfs_pullback near a point is the pullback through any one chart. *)

let APX_RFS_PULLBACK_CHART = prove
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
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC APX_MPULLBACK_CHART_INDEP THEN
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
                  APX_PARAM_CHART_REP) THEN
    ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`{z | z IN s /\ (e:real^N->A) z IN V}`;
                   `(psi:A->real^N) o (e:real^N->A)`; `z:real^N`; `vec 0:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

(* Near y, rfs_pullback is the pullback of the chart representative of g by *)
(* the diffeomorphism psi o e (psi the preferred chart at e y).              *)

let APX_PARAM_LOCAL_REP = prove
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
                APX_PARAM_CHART_REP) THEN
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
    MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* The pulled-back metric is a metric field, and scalar, Ricci and           *)
(* sectional curvature are natural under parametrizations.                  *)

let APX_RFS_PULLBACK_FIELD = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_param top atlas s e
        ==> metric_field s (rfs_pullback atlas e g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_PARAM_MAPS]; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `N:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback (SND(chart_at atlas ((e:real^N->A) y)) o e)
                        (metric_local atlas (chart_at atlas (e y)) (g:A->real^N^N))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`N':real^N->bool`; `h':real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let APX_PULLBACK_SCALAR_GEN = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_param top atlas s e /\ y IN s
        ==> mfd_scalar atlas g (e y) = lscalar (rfs_pullback atlas e g) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  TRANS_TAC EQ_TRANS
   `lscalar (mpullback (SND(chart_at atlas ((e:real^N->A) y)) o e)
                       (metric_local atlas (chart_at atlas (e y))
                                     (g:A->real^N^N))) y` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`N':real^N->bool`; `N:real^N->bool`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) o e`;
                   `h':real^N->real^N`;
                   `metric_local atlas (chart_at atlas ((e:real^N->A) y))
                                 (g:A->real^N^N)`; `y:real^N`] LSCALAR_PULLBACK) THEN
    ASM_REWRITE_TAC[o_THM; mfd_scalar] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REFL_TAC;
    MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[]]);;

let APX_PULLBACK_RICCI_GEN = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) y u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_param top atlas s e /\ y IN s
        ==> lricci (rfs_pullback atlas e g) y u v =
            mfd_ricci atlas g (e y)
              (frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) u)
              (frechet_derivative (SND(chart_at atlas (e y)) o e) (at y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  TRANS_TAC EQ_TRANS
   `lricci (mpullback (SND(chart_at atlas ((e:real^N->A) y)) o e)
                      (metric_local atlas (chart_at atlas (e y))
                                    (g:A->real^N^N))) y u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`N':real^N->bool`; `N:real^N->bool`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) o e`;
                   `h':real^N->real^N`;
                   `metric_local atlas (chart_at atlas ((e:real^N->A) y))
                                 (g:A->real^N^N)`; `y:real^N`; `u:real^N`; `v:real^N`]
                  LRICCI_PULLBACK) THEN
    ASM_REWRITE_TAC[o_THM; mfd_ricci]]);;

let APX_PULLBACK_SECTIONAL_GEN = prove
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
                APX_PARAM_LOCAL_REP) THEN
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

(* ------------------------------------------------------------------------- *)
(* N0, a delta-neck is an eps-neck for delta <= eps (needs the               *)
(* k-monotonicity LCK_DIST_MONO of pc_lrg_stab and the metric field fact    *)
(* APX_RFS_PULLBACK_FIELD).                                                   *)
(* ------------------------------------------------------------------------- *)

let APX_KREG_MONO = prove
 (`!dl eps. &0 < dl /\ dl <= eps ==> rfs_kreg eps <= rfs_kreg dl`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[RFS_KREG] THEN
  MATCH_MP_TAC FLOOR_MONO THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_REWRITE_TAC[]);;

let APX_NECK_DOM_MONO = prove
 (`!dl eps. &0 < dl /\ dl <= eps ==> rfs_neck_dom eps SUBSET rfs_neck_dom dl`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps) <= inv(sqrt(&2) * dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `exp(--(inv(sqrt(&2) * eps)))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(inv(sqrt(&2) * eps))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE]]);;

let APX_NECK_DOM_NONZERO = prove
 (`!eps. rfs_neck_dom eps SUBSET (:real^3) DELETE vec 0`,
  GEN_TAC THEN REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM;
                          IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM NORM_POS_LT] THEN
  MP_TAC(SPEC `--(inv(sqrt(&2) * eps))` REAL_EXP_POS_LT) THEN
  ASM_REAL_ARITH_TAC);;

let APX_NECK_MONO_GEN = prove
 (`!top atlas (g:A->real^3^3) dl eps x e.
        &0 < dl /\ dl <= eps /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g dl x (e:real^3->A)
        ==> rfs_neck (top,atlas) g eps x e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_neck_dom eps SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS];
    ALL_TAC] THEN
  UNDISCH_TAC
   `rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
      (\y. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g y)` THEN
  REWRITE_TAC[rfs_close_on] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dl pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
      (\y. mfd_scalar atlas (g:A->real^3^3) x %% rfs_pullback atlas (e:real^3->A) g y) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; APX_NECK_DOM_NONZERO] THEN
      REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS];
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* The statement forms of N0 and N1b. *)

let APX_NECK_MONO = prove
 (`!w:A->bool. APX_NECK_MONO_STATEMENT w`,
  REWRITE_TAC[APX_NECK_MONO_STATEMENT] THEN MESON_TAC[APX_NECK_MONO_GEN]);;

let APX_PULLBACK_SCALAR = prove
 (`!w:A->bool. APX_PULLBACK_SCALAR_STATEMENT w`,
  REWRITE_TAC[APX_PULLBACK_SCALAR_STATEMENT] THEN
  MESON_TAC[APX_PULLBACK_SCALAR_GEN]);;

(* ------------------------------------------------------------------------- *)
(* The event chain with the sphere separation leaf discharged                *)
(* (SMT_SC_SPHERE_SEP of pc_smt_sep proves APX_SC_SPHERE_SEP_STATEMENT).    *)
(* ------------------------------------------------------------------------- *)

let APX_EVENT_TOPOLOGY_FROM_LEAVES_SEP = prove
 (`!w:A->bool.
        APX_STRONG_NECK_EARLIER_STATEMENT w /\ APX_REGION_STATEMENT w /\
        APX_A25_STATEMENT w /\ APX_EXCLUDE_STATEMENT w /\
        SMT_TWISTED_SPHERE_STATEMENT w
        ==> EVENT_TOPOLOGY_STATEMENT w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_EVENT_TOPOLOGY_FROM_LEAVES THEN
  ASM_REWRITE_TAC[SMT_SC_SPHERE_SEP]);;

