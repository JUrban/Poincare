(* ========================================================================= *)
(* Unit pc_p2b_979 (Part 2B): MT Prop 9.79, stability of necks under         *)
(* closeness of views.  Main theorems (statements in pc_p2b_defs):           *)
(* P2B_NECK_OPEN_STATEMENT, P2B_NECK_OPEN_L_STATEMENT (same eps, delta       *)
(* depending on the neck) and P2B_PROP_9_79_NECK_FIX_STATEMENT (eps < eps',  *)
(* uniform delta; the body of P2_PROP_9_79_NECK of pc_p3_iface), proved from *)
(* the statements P2B_REQ_LRG_BASE_STATEMENT (change of base of the C^k      *)
(* distance) and, for the uniform form, P2B_REQ_LRG_RM_NEAR_STATEMENT, both  *)
(* theorems of pc_p2b_979s.                                                  *)
(*                                                                           *)
(* Contents: closeness and pullbacks along parametrizations (chart           *)
(* naturality of lck_dist2, composition of pullbacks); change of base        *)
(* between two shrinking cylinders; evolving necks in regular views; the     *)
(* transfer core; choice of delta and the main theorems; static necks.       *)
(* ========================================================================= *)

needs "src/pc_p2b_lim.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_smt_glue.ml";;
needs "src/pc_p2c_l112.ml";;
needs "src/pc_p2a_lgeo2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Closeness of two metrics read through a parametrization e equals their    *)
(* closeness in the preferred chart at e y (P2B9_LCK_PARAM); pullbacks       *)
(* compose: pulling back by e the pullback by psi is pulling back by psi o e *)
(* (P2B9_PULLBACK_COMPOSE).                                                  *)
(* ------------------------------------------------------------------------- *)

let P2B9_RFS_PULLBACK_CMUL = prove
 (`!atlas (e:real^N->A) (g:A->real^N^N) k.
     rfs_pullback atlas e (\y. k %% g y) = (\z. k %% rfs_pullback atlas e g z)`,
  REWRITE_TAC[rfs_pullback; METRIC_LOCAL_CMUL; mpullback; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P2B9_LCK_PARAM = prove
 (`!top atlas (g0:A->real^N^N) g s (e:real^N->A) k y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     riemannian_metric atlas g /\ mfd_param top atlas s e /\ y IN s
     ==> lck_dist2 k (rfs_pullback atlas e g0) (rfs_pullback atlas e g) y =
         lck_dist2 k (metric_local atlas (chart_at atlas (e y)) g0)
                     (metric_local atlas (chart_at atlas (e y)) g)
                     (SND(chart_at atlas (e y)) (e y))`,
  REPEAT STRIP_TAC THEN
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
  ABBREV_TAC `N = {z | z IN s /\ (e:real^N->A) z IN V}` THEN
  ABBREV_TAC `N' = IMAGE (psi:A->real^N) (V INTER IMAGE (e:real^N->A) s)` THEN
  SUBGOAL_THEN `open (N:real^N->bool) /\ open (N':real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!h:A->real^N^N. riemannian_metric atlas h
                ==> metric_field N' (metric_local atlas (V,psi) h)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) h` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "N'" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:A->real^N^N. !z. z IN N
                ==> rfs_pullback atlas e h z =
                    mpullback (psi o e) (metric_local atlas (V,psi) h) z` ASSUME_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `z:real^N` THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 k (mpullback (psi o (e:real^N->A))
                             (metric_local atlas (V,psi) (g0:A->real^N^N)))
                          (mpullback (psi o e) (metric_local atlas (V,psi) g)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->real^N)((e:real^N->A) y) = (psi o e) y` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`N':real^N->bool`; `N:real^N->bool`;
                        `(e2:A->real^N) o chart_inv (V:A->bool,psi:A->real^N)`] THEN
  ASM_SIMP_TAC[]);;

let P2B9_PULLBACK_COMPOSE = prove
 (`!top atlas top' atlas' s (e:real^N->A) W W' (psi:A->B) psi' (g':B->real^N^N) y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_param top atlas s e /\ IMAGE e s SUBSET W /\
     mfd_diffeo top atlas W top' atlas' W' psi psi' /\ y IN s
     ==> rfs_pullback atlas e (mfd_pullback_metric atlas atlas' psi g') y =
         rfs_pullback atlas' (psi o e) g' y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top' atlas' s ((psi:A->B) o (e:real^N->A))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `W:A->bool`; `W':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace top /\ e y IN W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `s:real^N->bool`; `e:real^N->A`; `s:real^N->bool`]
                    MFD_PARAM_IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B)((e:real^N->A) y) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `s:real^N->bool`; `(psi:A->B) o (e:real^N->A)`; `s:real^N->bool`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_pullback; o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(psi:A->B)((e:real^N->A) y)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((psi:A->B)((e:real^N->A) y))`,
           `c':(B->bool)#(B->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:B->bool`; `chi:B->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `U:A->bool`; `phi:A->real^N`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:A->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "d1") ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `s:real^N->bool`; `(psi:A->B) o (e:real^N->A)`; `V:B->bool`; `chi:B->real^N`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:B->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "d2") ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `W':B->bool`;
                 `psi:A->B`; `psi':B->A`; `U:A->bool`; `phi:A->real^N`;
                 `V:B->bool`; `chi:B->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "d3") THEN
  ABBREV_TAC `K = (chi:B->real^N) o (psi:A->B) o chart_inv (U:A->bool,phi:A->real^N)` THEN
  SUBGOAL_THEN `((phi:A->real^N) o (e:real^N->A)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z | z IN s /\ (e:real^N->A) z IN U}` THEN
    USE_THEN "d1" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^N->real^N) differentiable at ((phi:A->real^N)((e:real^N->A) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) {x | x IN U INTER W /\ (psi:A->B) x IN V}` THEN
    USE_THEN "d3" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((phi:A->real^N) o (e:real^N->A))
                (mpullback (K:real^N->real^N)
                   (metric_local atlas' (V:B->bool,chi:B->real^N) (g':B->real^N^N))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN REWRITE_TAC[o_THM] THEN EXPAND_TAC "K" THEN
    MATCH_MP_TAC P2C_PULLBACK_METRIC_LOCAL_W THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `W:A->bool`; `top':B topology`;
                          `W':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((K:real^N->real^N) o (phi:A->real^N) o (e:real^N->A))
                (metric_local atlas' (V:B->bool,chi:B->real^N) (g':B->real^N^N)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_COMPOSE THEN ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
  EXISTS_TAC `{z | z IN s /\ (e:real^N->A) z IN U} INTER
              {z | z IN s /\ ((psi:A->B) o e) z IN V}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN
    USE_THEN "d1" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]) THEN
    USE_THEN "d2" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]);
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM];
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[]]);;

let P2B9_MPULLBACK_ID = prove
 (`!(G:real^N->real^N^N) z. mpullback (\x. x) G z = G z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^N. x) (at z) = (\x. x)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P2B9_FIELD_BACK = prove
 (`!N N' (h:real^N->real^N) h' (Fm:real^N->real^N^N).
     diffeomorphism_on N N' h h' /\ metric_field N (mpullback h Fm)
     ==> metric_field N' Fm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `mpullback (h':real^N->real^N) (mpullback (h:real^N->real^N) Fm)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `h:real^N->real^N`] THEN
    ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `(h':real^N->real^N) z IN N` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((h:real^N->real^N) o (h':real^N->real^N)) Fm z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_COMPOSE THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `mpullback (\x:real^N. x) Fm z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN EXISTS_TAC `N':real^N->bool` THEN
    ASM_SIMP_TAC[o_THM];
    REWRITE_TAC[P2B9_MPULLBACK_ID]]);;

let P2B9_LCK_PARAM_DIFFEO = prove
 (`!top atlas top' atlas' s (e:real^N->A) W W' (psi:A->B) psi'
    (g:A->real^N^N) (g':B->real^N^N) k y.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_param top atlas s e /\ IMAGE e s SUBSET W /\
     mfd_diffeo top atlas W top' atlas' W' psi psi' /\ y IN s
     ==> lck_dist2 k (rfs_pullback atlas e g) (rfs_pullback atlas' (psi o e) g') y =
         lck_dist2 k (metric_local atlas (chart_at atlas (e y)) g)
                     (metric_local atlas (chart_at atlas (e y))
                                   (mfd_pullback_metric atlas atlas' psi g'))
                     (SND(chart_at atlas (e y)) (e y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top' atlas' s ((psi:A->B) o (e:real^N->A))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `W:A->bool`; `W':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN s
                ==> rfs_pullback atlas' ((psi:A->B) o (e:real^N->A)) (g':B->real^N^N) z =
                    rfs_pullback atlas e (mfd_pullback_metric atlas atlas' psi g') z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2B9_PULLBACK_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `s:real^N->bool`;
                          `W:A->bool`; `W':B->bool`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
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
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `V:A->bool`; `phi:A->real^N`]
                APX_PARAM_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:A->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "dd") ASSUME_TAC)) THEN
  ABBREV_TAC `N = {z | z IN s /\ (e:real^N->A) z IN V}` THEN
  ABBREV_TAC `N' = IMAGE (phi:A->real^N) (V INTER IMAGE (e:real^N->A) s)` THEN
  SUBGOAL_THEN `open (N:real^N->bool) /\ open (N':real^N->bool)` STRIP_ASSUME_TAC THENL
   [USE_THEN "dd" (fun th -> REWRITE_TAC[REWRITE_RULE[diffeomorphism_on] th]); ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN N /\ N SUBSET s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `!h:A->real^N^N. !z. z IN N
                ==> rfs_pullback atlas e h z =
                    mpullback (phi o e) (metric_local atlas (V,phi) h) z` ASSUME_TAC THENL
   [GEN_TAC THEN X_GEN_TAC `z:real^N` THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field N' (metric_local atlas (V:A->bool,phi:A->real^N) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) V` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,phi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "N'" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field N' (metric_local atlas (V:A->bool,phi:A->real^N)
                                  (mfd_pullback_metric atlas atlas' (psi:A->B)
                                                       (g':B->real^N^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2B9_FIELD_BACK THEN
    MAP_EVERY EXISTS_TAC [`N:real^N->bool`; `(phi:A->real^N) o (e:real^N->A)`;
                          `(e2:A->real^N) o chart_inv (V:A->bool,phi:A->real^N)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `rfs_pullback atlas' ((psi:A->B) o (e:real^N->A)) (g':B->real^N^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
       [UNDISCH_TAC `(N:real^N->bool) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 k (mpullback (phi o (e:real^N->A))
                             (metric_local atlas (V,phi) (g:A->real^N^N)))
                          (mpullback (phi o e) (metric_local atlas (V,phi)
                             (mfd_pullback_metric atlas atlas' (psi:A->B)
                                                  (g':B->real^N^N)))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
       [UNDISCH_TAC `(N:real^N->bool) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N)((e:real^N->A) y) = (phi o e) y` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC [`N':real^N->bool`; `N:real^N->bool`;
                        `(e2:A->real^N) o chart_inv (V:A->bool,phi:A->real^N)`] THEN
  ASM_REWRITE_TAC[]);;

let P2B9_PULLBACK_METRIC_CMUL = prove
 (`!atlas atlas' (f:A->B) (g':B->real^N^N) c.
     mfd_pullback_metric atlas atlas' f (\y. c %% g' y) =
     (\x. c %% mfd_pullback_metric atlas atlas' f g' x)`,
  REWRITE_TAC[mfd_pullback_metric; METRIC_LOCAL_CMUL; mpullback; FUN_EQ_THM] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P2B9_MCLOSE_PARAM = prove
 (`!top atlas top' atlas' s (e:real^N->A) W W' (psi:A->B) psi'
    (g:A->real^N^N) (g':B->real^N^N) Q Q' k eps.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\ &0 < Q /\ &0 < Q' /\
     mfd_param top atlas s e /\ IMAGE e s SUBSET W /\
     mfd_diffeo top atlas W top' atlas' W' psi psi' /\
     rfs_mclose k eps atlas W (\y. Q %% g y)
                (\y. Q' %% mfd_pullback_metric atlas atlas' psi g' y)
     ==> ?d. d < eps pow 2 /\
             !y. y IN s
                 ==> lck_dist2 k (\z. Q %% rfs_pullback atlas e g z)
                                 (\z. Q' %% rfs_pullback atlas' (psi o e) g' z) y <= d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_mclose] THEN STRIP_TAC THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`; `W:A->bool`; `W':B->bool`;
                 `psi:A->B`; `psi':B->A`; `\y. Q %% (g:A->real^N^N) y`;
                 `\y. Q' %% (g':B->real^N^N) y`; `k:num`; `y:real^N`]
                P2B9_LCK_PARAM_DIFFEO) THEN
  ASM_SIMP_TAC[RIEMANNIAN_METRIC_CMUL] THEN
  REWRITE_TAC[P2B9_RFS_PULLBACK_CMUL; P2B9_PULLBACK_METRIC_CMUL] THEN
  DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2B9_PARAM_LSCALAR_SCALED = prove
 (`!top atlas (g:A->real^N^N) s e c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s /\ &0 < c
     ==> lscalar (\z. c %% rfs_pullback atlas e g z) y = mfd_scalar atlas g (e y) / c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `rfs_pullback atlas (e:real^N->A) (g:A->real^N^N)`;
                 `c:real`; `y:real^N`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC APX_PULLBACK_SCALAR_GEN THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The shrinking cylinders are affine in s and share their Christoffel       *)
(* symbols, so the C^k distance to cylinder_flow s is controlled by the one  *)
(* to cylinder_flow s1 for nearby s, s1 <= 0 (P2B9_CYL_BASE2).               *)
(* ------------------------------------------------------------------------- *)

let P2B9_CYL_AFFINE = prove
 (`!s s1 (y:real^3).
     cylinder_flow s y - cylinder_flow s1 y =
     cylinder_flow (s - s1) y - cylinder_flow (&0) y`,
  REWRITE_TAC[cylinder_flow; CART_EQ; MATRIX_SUB_COMPONENT; MATRIX_ADD_COMPONENT;
              MATRIX_CMUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

let P2B9_CYL_COMPARE2 = prove
 (`!s s1 (y:real^3) x.
     s <= &0 /\ ~(y = vec 0)
     ==> x dot (cylinder_flow s1 y ** x) <=
         (&1 + abs(s - s1)) * (x dot (cylinder_flow s y ** x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((x:real^3) dot y) pow 2 <= norm(y:real^3) pow 2 * (x dot x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `X = (x:real^3) dot x` THEN
  ABBREV_TAC `t = ((x:real^3) dot y) pow 2 / r` THEN
  SUBGOAL_THEN `&0 <= t /\ t <= X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE;
                                     REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u / &2 * (&2 / r * (&2 / r * (((x:real^3) dot y) * (x dot y)))) =
        (&2 / r) * (u * t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = &2 / r` THEN ABBREV_TAC `d = abs(s - s1)` THEN
  SUBGOAL_THEN `&0 <= d /\ s - s1 <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((&1 + d) * (&1 - s) - (&1 - s1)) * (X - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 <= d * --s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `q * ((&1 - s1) * X + s1 * t) <= q * ((&1 + d) * ((&1 - s) * X + s * t))
    ==> (&1 - s1) * X * q + q * (s1 * t) <=
        (&1 + d) * ((&1 - s) * X * q + q * (s * t))`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2B9_CYL0_LE = prove
 (`!s (y:real^3) x.
     s <= &0 /\ ~(y = vec 0)
     ==> x dot (cylinder_flow (&0) y ** x) <= x dot (cylinder_flow s y ** x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&0`; `s:real`; `y:real^3`; `x:real^3`] P2B9_CYL_COMPARE2) THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_SUB_LZERO; REAL_ABS_NEG] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real`; `&0`; `y:real^3`; `x:real^3`] P2B9_CYL_COMPARE2) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((x:real^3) dot y) pow 2 <= norm(y:real^3) pow 2 * (x dot x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `X = (x:real^3) dot x` THEN
  ABBREV_TAC `t = ((x:real^3) dot y) pow 2 / r` THEN
  SUBGOAL_THEN `&0 <= t /\ t <= X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE;
                                     REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u / &2 * (&2 / r * (&2 / r * (((x:real^3) dot y) * (x dot y)))) =
        (&2 / r) * (u * t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = &2 / r` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= q * (--s * (X - t))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2B9_CYL_NABLA_SPLIT2 = prove
 (`!s s1 t (G:real^3->real^3^3).
     s < &1 /\ s1 < &1 /\ t SUBSET ((:real^3) DELETE vec 0) /\ metric_field t G
     ==> !l y u. y IN t
           ==> lnabla_iter 2 l (cylinder_flow s)
                 (\z u. lmetric2 G z u - lmetric2 (cylinder_flow s) z u) y u =
               lnabla_iter 2 l (cylinder_flow s1)
                 (\z u. lmetric2 G z u - lmetric2 (cylinder_flow s1) z u) y u +
               (if l = 0
                then lmetric2 (cylinder_flow s1) y u - lmetric2 (cylinder_flow s) y u
                else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow s) /\ metric_field t (cylinder_flow s1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z a b. z IN t
            ==> christoffel (cylinder_flow s) z a b =
                christoffel (cylinder_flow s1) z a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CHRISTOFFEL_CYLINDER_FLOW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s1`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`; `cylinder_flow s1`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`] LRG_LMETRIC2_FIELD) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s1`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (G:real^3->real^3^3) z u - lmetric2 (cylinder_flow s) z u) =
    (\x u. &1 * (lmetric2 G x u - lmetric2 (cylinder_flow s1) x u) +
           &1 * (lmetric2 (cylinder_flow s1) x u - lmetric2 (cylinder_flow s) x u))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow s`;
     `\z u. lmetric2 (G:real^3->real^3^3) z u - lmetric2 (cylinder_flow s1) z u`;
     `\z u. lmetric2 (cylinder_flow s1) z u - lmetric2 (cylinder_flow s) z u`;
     `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPECL [`2`; `cylinder_flow s`; `cylinder_flow s1`;
     `\z u. lmetric2 (G:real^3->real^3^3) z u - lmetric2 (cylinder_flow s1) z u`;
     `t:real^3->bool`] LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_EQ_ADD_LCANCEL] THEN
  STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
   [REWRITE_TAC[lnabla_iter]; ALL_TAC] THEN
  REWRITE_TAC[NOT_SUC] THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (cylinder_flow s1) z u - lmetric2 (cylinder_flow s) z u) =
    (\x u. &1 * lmetric2 (cylinder_flow s1) x u +
           --(&1) * lmetric2 (cylinder_flow s) x u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow s`;
     `lmetric2 (cylinder_flow s1)`; `lmetric2 (cylinder_flow s)`;
     `&1`; `--(&1)`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPECL [`2`; `cylinder_flow s`; `cylinder_flow s1`;
     `lmetric2 (cylinder_flow s1)`; `t:real^3->bool`]
     LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s1`] LRG_LNABLA_ITER_METRIC) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`] LRG_LNABLA_ITER_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REAL_ARITH_TAC);;

let P2B9_CYL_D_NORM2 = prove
 (`!s s1 (y:real^3).
     s <= &0 /\ abs(s - s1) <= &1 / &2 /\ ~(y = vec 0)
     ==> ltnorm2 2 (cylinder_flow s)
           (\z u. lmetric2 (cylinder_flow s1) z u - lmetric2 (cylinder_flow s) z u) y
         <= &2 * (s - s1) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s < &1 /\ s1 < &1 /\ s1 - s < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(SPEC `s:real` RFB_CYL_METRIC_FIELD) THEN
  MP_TAC(SPEC `s1:real` RFB_CYL_METRIC_FIELD) THEN
  MP_TAC(SPEC `s1 - s:real` RFB_CYL_METRIC_FIELD) THEN
  MP_TAC(SPEC `&0` RFB_CYL_METRIC_FIELD) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < &1`] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ltnorm2 2 (cylinder_flow s)
                (\z u. lmetric2 (cylinder_flow (s1 - s)) z u -
                       lmetric2 (cylinder_flow (&0)) z u) (y:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    REWRITE_TAC[lmetric2] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM DOT_RSUB; GSYM MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC P2B9_CYL_AFFINE;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 pow 2 *
              ltnorm2 2 (cylinder_flow (&0))
                (\z u. lmetric2 (cylinder_flow (s1 - s)) z u -
                       lmetric2 (cylinder_flow (&0)) z u) (y:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                     `cylinder_flow (s1 - s)`] LRG_LMETRIC2_DIFF_FIELD) THEN
      ASM_SIMP_TAC[];
      GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC P2B9_CYL0_LE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_CYL_D_NORM] THEN REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

let P2B9_CYL_BASE2 = prove
 (`!k s s1 t (G:real^3->real^3^3) y.
      s <= &0 /\ abs(s - s1) <= &1 / &2 /\ t SUBSET ((:real^3) DELETE vec 0) /\
      metric_field t G /\ y IN t
      ==> sqrt(lck_dist2 k (cylinder_flow s) G y)
          <= (&1 + abs(s - s1)) pow (k + 2) *
             (sqrt(lck_dist2 k (cylinder_flow s1) G y) + &2 * abs(s - s1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s < &1 /\ s1 < &1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow s) /\ metric_field t (cylinder_flow s1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real`; `s1:real`; `t:real^3->bool`; `G:real^3->real^3^3`]
         P2B9_CYL_NABLA_SPLIT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SPLIT") THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s1`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`; `cylinder_flow s1`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow s1`;
                 `\z u. lmetric2 (G:real^3->real^3^3) z u -
                        lmetric2 (cylinder_flow s1) z u`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "FS") THEN
  ABBREV_TAC `lam = &1 + abs(s - s1)` THEN
  SUBGOAL_THEN `&1 <= lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= lam pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = lck_dist2 k (cylinder_flow s1) (G:real^3->real^3^3) y` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[lck_dist2] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..k) (\l. ltnorm2 (2 + l) (cylinder_flow s)
                     (lnabla_iter 2 l (cylinder_flow s1)
                       (\z u. lmetric2 (G:real^3->real^3^3) z u -
                              lmetric2 (cylinder_flow s1) z u)) y) <=
    lam pow (k + 2) * L`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[lck_dist2; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam pow (2 + l) *
                ltnorm2 (2 + l) (cylinder_flow s1)
                  (lnabla_iter 2 l (cylinder_flow s1)
                    (\z u. lmetric2 (G:real^3->real^3^3) z u -
                           lmetric2 (cylinder_flow s1) z u)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "lam" THEN GEN_TAC THEN MATCH_MP_TAC P2B9_CYL_COMPARE2 THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(sum(0..k) (\l. ltnorm2 (2 + l) (cylinder_flow s)
                          (lnabla_iter 2 l (cylinder_flow s1)
                            (\z u. lmetric2 (G:real^3->real^3^3) z u -
                                   lmetric2 (cylinder_flow s1) z u)) y)) +
    sqrt(sum(0..k) (\l. if l = 0
                        then ltnorm2 2 (cylinder_flow s)
                               (\z u. lmetric2 (cylinder_flow s1) z u -
                                      lmetric2 (cylinder_flow s) z u) y
                        else &0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC LRG_SQRT_SUM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th]);
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
     [REWRITE_TAC[ADD_CLAUSES; lnabla_iter] THEN
      MATCH_MP_TAC LRG_LTNORM2_TRIANGLE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[NOT_SUC; SQRT_0; REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
      USE_THEN "SPLIT" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[NOT_SUC; REAL_ADD_RID]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
  MP_TAC(ISPECL [`s:real`; `s1:real`; `y:real^3`] P2B9_CYL_D_NORM2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sqrt(ltnorm2 2 (cylinder_flow s)
           (\z u. lmetric2 (cylinder_flow s1) z u - lmetric2 (cylinder_flow s) z u) y)
    <= &2 * abs(s - s1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&2 * (s - s1) pow 2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
                    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
                    ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(sum(0..k) (\l. ltnorm2 (2 + l) (cylinder_flow s)
                          (lnabla_iter 2 l (cylinder_flow s1)
                            (\z u. lmetric2 (G:real^3->real^3^3) z u -
                                   lmetric2 (cylinder_flow s1) z u)) y)) <=
    lam pow (k + 2) * sqrt L`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(lam pow (k + 2) * L)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * abs(s - s1) <= lam pow (k + 2) * (&2 * abs(s - s1))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2B9_NECK_POINT = prove
 (`!k k1 kd M s s1 t (G1:real^3->real^3^3) G2 c d0 dd y.
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k1 G0 G1 y <= &1 / &4
         ==> lck_dist2 k1 G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k1 G1 G2 y) /\
     &0 <= M /\ k1 <= k /\ k1 <= kd /\
     s <= &0 /\ s1 <= &0 /\ abs(s - s1) <= &1 / &2 /\
     t SUBSET ((:real^3) DELETE vec 0) /\
     metric_field t G1 /\ metric_field t G2 /\ y IN t /\ &0 < c /\
     lck_dist2 k (cylinder_flow s1) G1 y <= d0 /\ d0 <= &1 / &4 /\
     lck_dist2 kd G1 G2 y <= dd
     ==> sqrt(lck_dist2 k1 (cylinder_flow s) (\z. c %% G2 z) y)
         <= (&1 + abs(s - s1)) pow (k1 + 2) *
            (c * (sqrt d0 + sqrt(M * dd)) + abs(c - &1) * sqrt(&3) +
             &2 * abs(s - s1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s1 < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow s1) /\
                metric_field t (\z. c %% (G2:real^3->real^3^3) z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD] THEN ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k1 (cylinder_flow s1) (G1:real^3->real^3^3) y <= d0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 k (cylinder_flow s1) (G1:real^3->real^3^3) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k1 (G1:real^3->real^3^3) G2 y <= dd` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 kd (G1:real^3->real^3^3) G2 y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 k1 (cylinder_flow s1)
      (\z. cylinder_flow s1 z + (G2:real^3->real^3^3) z - G1 z) y <= M * dd`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * lck_dist2 k1 (G1:real^3->real^3^3) G2 y` THEN CONJ_TAC THENL
     [USE_THEN "base" MATCH_MP_TAC THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(lck_dist2 k1 (cylinder_flow s1) (G2:real^3->real^3^3) y)
    <= sqrt d0 + sqrt(M * dd)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 k1 (cylinder_flow s1) (G1:real^3->real^3^3) y) +
                sqrt(lck_dist2 k1 (cylinder_flow s1)
                       (\z. cylinder_flow s1 z + (G2:real^3->real^3^3) z - G1 z) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_TRIANGLE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]] THEN
    ALL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(lck_dist2 k1 (cylinder_flow s1) (\z. c %% (G2:real^3->real^3^3) z) y)
    <= c * (sqrt d0 + sqrt(M * dd)) + abs(c - &1) * sqrt(&3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * sqrt(lck_dist2 k1 (cylinder_flow s1) (G2:real^3->real^3^3) y) +
                abs(c - &1) * sqrt(&(dimindex(:3)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_RESCALE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[DIMINDEX_3] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + abs(s - s1)) pow (k1 + 2) *
              (sqrt(lck_dist2 k1 (cylinder_flow s1) (\z. c %% (G2:real^3->real^3^3) z) y) +
               &2 * abs(s - s1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2B9_CYL_BASE2 THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Evolving necks in regular views.  The neck chart of an evolving neck of a *)
(* regular view is a parametrization in every slice of its time interval     *)
(* (P2B9_REGULAR_NECK_SLICE); a view close to it carries the composed chart  *)
(* and the closeness in neck coordinates (P2B9_VIEW_SLICE_DATA); the scalar  *)
(* curvature at the image of the centre is R Q' up to a factor 1 + O(delta)  *)
(* (P2B9_SCALAR_RATIO).                                                      *)
(* ------------------------------------------------------------------------- *)

let P2B9_RFS_VSCALAR = prove
 (`!V t (x:A). rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vatlas; rfs_vmetric]);;

let P2B9_REGULAR_NECK_SLICE = prove
 (`!V eps x t a (e:real^3->A) s.
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\ --a < s /\ s <= &0
     ==> &0 < rfs_vscalar V t x /\
         hausdorff_space (rfs_vtop V (t + s / rfs_vscalar V t x)) /\
         smooth_manifold_atlas (rfs_vtop V (t + s / rfs_vscalar V t x))
                               (rfs_vatlas V (t + s / rfs_vscalar V t x)) /\
         riemannian_metric (rfs_vatlas V (t + s / rfs_vscalar V t x))
                           (rfs_vmetric V (t + s / rfs_vscalar V t x)) /\
         mfd_param (rfs_vtop V (t + s / rfs_vscalar V t x))
                   (rfs_vatlas V (t + s / rfs_vscalar V t x)) (rfs_neck_dom eps) e /\
         x IN IMAGE e (rfs_neck_dom eps)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `x:A`; `t:real`; `a:real`; `e:real^3->A`; `s:real`] THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "reg") (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[rfs_evolving_neck; rfs_neck; rfs_persists] THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                             ((G:real->A->real^3^3) t) x` THEN
  ABBREV_TAC `u = t + s / R` THEN
  SUBGOAL_THEN `t - a / R < u /\ u <= t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SUBGOAL_THEN `--a / R < s / R /\ s / R <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
      REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas ((TM:real->A topology) u)
                                      ((AT:real->((A->bool)#(A->real^3))->bool) u) /\
                open_in (TM u) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(topspace((TM:real->A topology) u) = {})` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "reg" (MP_TAC o CONJUNCT1 o REWRITE_RULE[p2c_regular_view]) THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "reg" (MP_TAC o el 3 o CONJUNCTS o REWRITE_RULE[p2c_regular_view]) THEN
  REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  DISCH_THEN(MP_TAC o SPECL [`IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                             `t - a / R`; `t:real`; `u:real`]) THEN
  ASM_REWRITE_TAC[rfs_persists] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) = (\y. y) o e` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`(TM:real->A topology) t`;
                        `(AT:real->((A->bool)#(A->real^3))->bool) t`;
                        `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                        `IMAGE (e:real^3->A) (rfs_neck_dom eps)`; `\y:A. y`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]);;

let P2B9_VIEW_SLICE_DATA = prove
 (`!V eps x t a (e:real^3->A) V' t' Q' (psi:A->B) delta s.
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\
     (!s. --a < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                    (rfs_vatlas V' (t' + s / Q')) /\
              riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                (rfs_vmetric V' (t' + s / Q'))) /\
     p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
       V' t' Q' psi {s | --a < s /\ s <= &0} delta /\
     --a < s /\ s <= &0
     ==> mfd_param (rfs_vtop V' (t' + s / Q')) (rfs_vatlas V' (t' + s / Q'))
                   (rfs_neck_dom eps) (psi o e) /\
         (!X. open X /\ X SUBSET rfs_neck_dom eps
              ==> open_in (rfs_vtop V' (t' + s / Q')) (IMAGE (psi o e) X)) /\
         ?dd. dd < delta pow 2 /\
              !y. y IN rfs_neck_dom eps
                  ==> lck_dist2 (rfs_kreg delta)
                        (\z. rfs_vscalar V t x %%
                             rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                          (rfs_vmetric V (t + s / rfs_vscalar V t x)) z)
                        (\z. Q' %% rfs_pullback (rfs_vatlas V' (t' + s / Q')) (psi o e)
                                                (rfs_vmetric V' (t' + s / Q')) z) y <= dd`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "vp") (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[p3_view_close] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `s:real`))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi':B->A`) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "vp" (fun th -> MP_TAC(MATCH_MP (SPEC `s:real` th)
                    (CONJ (ASSUME `--a < s`) (ASSUME `s <= &0`)))) THEN STRIP_TAC THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t (x:A)` THEN
  ABBREV_TAC `u = t + s / R` THEN ABBREV_TAC `u' = t' + s / Q'` THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) u') (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) u') (rfs_neck_dom eps)
              ((psi:A->B) o (e:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                          `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                          `IMAGE (psi:A->B) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    EXISTS_TAC `rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) u'` THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2B9_MCLOSE_PARAM THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`; `rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) u'`;
                        `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                        `IMAGE (psi:A->B) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
                        `psi':B->A`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  UNDISCH_TAC `&0 < rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t (x:A)` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let P2B9_SCALAR_RATIO = prove
 (`!V eps x t a (e:real^3->A) V' t' Q' (psi:A->B) delta K0 y0.
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\
     (!s. --a < s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                    (rfs_vatlas V' (t' + s / Q')) /\
              riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                (rfs_vmetric V' (t' + s / Q'))) /\
     p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
       V' t' Q' psi {s | --a < s /\ s <= &0} delta /\
     &0 < delta /\ delta <= &1 / &10 /\
     y0 IN sphere(vec 0,&1) /\ e y0 = x /\
     lrm_deriv_norm2 0 (\z. rfs_vscalar V t x %%
                            rfs_pullback (rfs_vatlas V t) e (rfs_vmetric V t) z) y0
     <= K0 pow 2
     ==> abs(rfs_vscalar V' t' (psi x) / Q' - &1) <= &72 * (&1 + abs K0) * delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) eps x t a e` THEN
    SPEC_TAC(`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`,
             `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; rfs_evolving_neck] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Q'` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_view_close (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t (rfs_vscalar V t x)
                   (IMAGE e (rfs_neck_dom eps))
                   (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                       (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta` THEN
    SIMP_TAC[p3_view_close];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                    (real->B->real^3^3)`; `t':real`; `Q':real`; `psi:A->B`;
                 `delta:real`; `&0`] P2B9_VIEW_SLICE_DATA) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `--a < &0 <=> &0 < a`;
                  real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))))) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP (SPEC `&0` (check (is_forall o concl) th))
     (CONJ (MATCH_MP (REAL_ARITH `&0 < a ==> --a < &0`) (ASSUME `&0 < a`))
           (SPEC `&0` REAL_LE_REFL)))) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN
    UNDISCH_TAC `rfs_evolving_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) eps x t a (e:real^3->A)` THEN
    SPEC_TAC(`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`,
             `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; rfs_evolving_neck; rfs_neck] THEN
    REPEAT STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (rfs_neck_dom eps) (\z. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x %%
             rfs_pullback (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (e:real^3->A) (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) z) /\ metric_field (rfs_neck_dom eps) (\z. Q' %% rfs_pullback (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t')
                                ((psi:A->B) o (e:real^3->A)) (rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t') z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (\z. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x %%
             rfs_pullback (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (e:real^3->A) (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) z) (\z. Q' %% rfs_pullback (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t')
                                ((psi:A->B) o (e:real^3->A)) (rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t') z) y0) <= delta` (LABEL_TAC "sq") THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(delta pow 2)` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg delta) (\z. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x %%
             rfs_pullback (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) (e:real^3->A) (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) z) (\z. Q' %% rfs_pullback (rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t')
                                ((psi:A->B) o (e:real^3->A)) (rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) t') z) y0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `rfs_neck_dom eps`;
     `\z. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) t x %%
          rfs_pullback (rfs_vatlas V t) (e:real^3->A) (rfs_vmetric V t) z`;
     `\z. Q' %% rfs_pullback (rfs_vatlas (V':(real->B topology)#
                                             (real->((B->bool)#(B->real^3))->bool)#
                                             (real->B->real^3^3)) t')
                             ((psi:A->B) o (e:real^3->A)) (rfs_vmetric V' t') z`;
     `y0:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t`;
                 `rfs_neck_dom eps`; `e:real^3->A`;
                 `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x`; `y0:real^3`]
                P2B9_PARAM_LSCALAR_SCALED) THEN
  MP_TAC(ISPECL [`rfs_vtop (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                               (real->B->real^3^3)) t'`;
                 `rfs_vatlas (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                 (real->B->real^3^3)) t'`;
                 `rfs_vmetric (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                                  (real->B->real^3^3)) t'`;
                 `rfs_neck_dom eps`; `(psi:A->B) o (e:real^3->A)`; `Q':real`; `y0:real^3`]
                P2B9_PARAM_LSCALAR_SCALED) THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN
  SUBGOAL_THEN `rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) t x /
                rfs_vscalar V t x = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= b ==> x <= c`) THEN
  REWRITE_TAC[REAL_ARITH `&8 * &3 pow 2 * k * d = (&72 * k) * d`] THEN
  REWRITE_TAC[REAL_ARITH `&72 * (&1 + abs K0) * delta = (&72 * (&1 + abs K0)) * delta`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sq" ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Transfer of an evolving neck along a close view.  The rescaling factor c  *)
(* = R' / Q' is within m = 72 (1 + abs K0) delta of 1, the normalized time s *)
(* of the new neck corresponds to s / c of the old one (P2B9_TIME_SHIFT),    *)
(* and the C^k distance to the shrinking cylinder is bounded at every point  *)
(* (P2B9_ENECK_POINTWISE); P2B9_ENECK_CORE gives the evolving eps1-neck of   *)
(* length L at (psi x, t') for explicit smallness conditions on delta.  The  *)
(* change of base of lck_dist2 between arbitrary metrics is a hypothesis     *)
(* (the statement P2B_REQ_LRG_BASE_STATEMENT).                               *)
(* ------------------------------------------------------------------------- *)

let P2B9_BND_ARITH = prove
 (`!n L m delta c h Sd M dd.
     &0 <= L /\ &0 <= m /\ &0 <= delta /\ &0 < c /\ abs(c - &1) <= m /\
     &0 <= h /\ h <= &2 * L * m /\ &0 <= Sd /\ &0 <= M /\ &0 <= dd /\
     dd <= delta pow 2
     ==> (&1 + h) pow n * (c * (Sd + sqrt(M * dd)) + abs(c - &1) * sqrt(&3) + &2 * h)
         <= (&1 + &2 * L * m) pow n *
            ((&1 + m) * (Sd + sqrt M * delta) + (&2 + &4 * L) * m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(M * dd) <= sqrt M * delta` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(delta pow 2)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; POW_2_SQRT; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(M * dd)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&3)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * (Sd + sqrt(M * dd)) <= (&1 + m) * (Sd + sqrt M * delta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) * sqrt(&3) <= m * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2B9_EVOLVING_NECK_ALT = prove
 (`!V eps (x:A) t len e.
     rfs_evolving_neck V eps x t len e <=>
     rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps x e /\ &0 < len /\
     (!s. t - len / rfs_vscalar V t x < s /\ s <= t
          ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
              open_in (rfs_vtop V s) (IMAGE e (rfs_neck_dom eps))) /\
     rfs_close_fam (rfs_kreg eps) eps {s | --len < s /\ s <= &0}
                   (rfs_neck_dom eps) cylinder_flow
                   (\s y. rfs_vscalar V t x %%
                          rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                       (rfs_vmetric V (t + s / rfs_vscalar V t x)) y)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_evolving_neck; rfs_persists; rfs_vtop; rfs_vatlas;
              rfs_vmetric; rfs_vscalar]);;

let P2B9_TIME_SHIFT = prove
 (`!a L m c s.
     &0 < L /\ abs(c - &1) <= m /\ m <= &1 / &2 /\ L < a * (&1 - m) /\
     --L < s /\ s <= &0
     ==> &0 < c /\ --a < s / c /\ s / c <= &0 /\ abs(s - s / c) <= &2 * L * m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= c /\ &0 < c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < a` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a * (&1 - m) <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `a * (&1 - m) <= a * c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
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

let P2B9_ENECK_POINTWISE = prove
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
     m <= &1 / &2 /\ &2 * L * m <= &1 / &2 /\ L < a * (&1 - m) /\
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
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a * (&1 - m)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 <= a` THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `a * (&1 - m) < &0` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < --a * b ==> a * b < &0`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = s / c` THEN
  SUBGOAL_THEN `s1 <= &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real`; `&0`; `c:real`] REAL_LE_LDIV_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--a < s1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`--a`; `s:real`; `c:real`] REAL_LT_RDIV_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `a * (&1 - m) <= a * c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
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

let P2B9_ENECK_CORE = prove
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
     L < a * (&1 - &72 * (&1 + abs K0) * delta) /\
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
                 `m:real`] P2B9_ENECK_POINTWISE) THEN
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
    MP_TAC(ISPECL [`a:real`; `L:real`; `m:real`; `c:real`; `(u - t') * R'`] P2B9_TIME_SHIFT) THEN
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

(* ------------------------------------------------------------------------- *)
(* The neck forms of MT Prop 9.79.  Explicit choice of delta                 *)
(* (P2B9_DELTA_EXISTS); the closeness margin and the curvature bound at the  *)
(* centre of a given evolving neck (non-uniform), or uniformly from          *)
(* P2B_REQ_LRG_RM_NEAR_STATEMENT; the theorems P2B_NECK_OPEN_L,              *)
(* P2B_NECK_OPEN (same eps, delta depending on the neck) and                 *)
(* P2B_PROP_9_79_NECK_FIX (eps < eps', uniform delta), as implications from  *)
(* these two statements.                                                     *)
(* ------------------------------------------------------------------------- *)

let P2B9_POW_BOUND = prove
 (`!n x. &0 <= x /\ &n * x <= inv(&2) ==> (&1 + x) pow n <= &1 + &2 * &n * x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp x pow n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_EXP_N] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= &1 + &2 * z ==> y <= &1 + &2 * z`) THEN
    MP_TAC(SPEC `&n * x` REAL_EXP_BOUND_LEMMA) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_MUL_ASSOC]]]);;

let P2B9_DELTA_EXISTS = prove
 (`!Sd eps1 M K0 L a n.
     &0 <= Sd /\ Sd < eps1 /\ &0 <= M /\ &0 < L /\ L < a
     ==> ?delta. &0 < delta /\ delta <= &1 / &10 /\ delta <= eps1 /\
                 &72 * (&1 + abs K0) * delta <= &1 / &2 /\
                 &2 * L * (&72 * (&1 + abs K0) * delta) <= &1 / &2 /\
                 L < a * (&1 - &72 * (&1 + abs K0) * delta) /\
                 (&1 + &2 * L * (&72 * (&1 + abs K0) * delta)) pow n *
                 ((&1 + &72 * (&1 + abs K0) * delta) * (Sd + sqrt M * delta) +
                  (&2 + &4 * L) * (&72 * (&1 + abs K0) * delta)) < eps1`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = &72 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&72 <= q` ASSUME_TAC THENL [EXPAND_TAC "q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sM = sqrt M` THEN
  SUBGOAL_THEN `&0 <= sM` ASSUME_TAC THENL
   [EXPAND_TAC "sM" THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `Q = Sd + &2 * sM + &2 + &4 * L` THEN
  SUBGOAL_THEN `&2 <= Q` ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `P = &4 * &n * L` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C = P * Sd + Q + P * Q` THEN
  SUBGOAL_THEN `&2 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    SUBGOAL_THEN `&0 <= P * Sd /\ &0 <= P * Q` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = min (min (&1 / &2) (inv(&4 * L)))
                      (min (min ((a - L) / (&2 * a)) (inv(P + &1)))
                           (min eps1 ((eps1 - Sd) / (&2 * C))))` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `m <= &1 / &2 /\ m <= inv(&4 * L) /\ m <= (a - L) / (&2 * a) /\
                m <= inv(P + &1) /\ m <= eps1 /\ m <= (eps1 - Sd) / (&2 * C)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LE_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `m / q` THEN
  SUBGOAL_THEN `&72 * (&1 + abs K0) * m / q = m` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `q * m / q` THEN CONJ_TAC THENL
     [EXPAND_TAC "q" THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&72 <= q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m / q /\ m / q <= m / &72` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `m * (&4 * L) <= &1 /\ m * (P + &1) <= &1 /\ m * (&2 * a) <= a - L /\
                m * (&2 * C) <= eps1 - Sd`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`m:real`; `&1`; `&4 * L`] REAL_LE_RDIV_EQ);
      MP_TAC(ISPECL [`m:real`; `&1`; `P + &1`] REAL_LE_RDIV_EQ);
      MP_TAC(ISPECL [`m:real`; `a - L`; `&2 * a`] REAL_LE_RDIV_EQ);
      MP_TAC(ISPECL [`m:real`; `eps1 - Sd`; `&2 * C`] REAL_LE_RDIV_EQ)] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `m / q <= m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m / &72` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `a * m <= (a - L) / &2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &2 * L * m) pow n <= &1 + P * m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `&2 * L * m`] P2B9_POW_BOUND) THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&n * &2 * L * m = (P * m) / &2` SUBST1_TAC THENL
       [EXPAND_TAC "P" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= m` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= &1 + y ==> x <= &1 + z`) THEN
    EXPAND_TAC "P" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Y = sM * m / q` THEN
  SUBGOAL_THEN `&0 <= Y /\ Y <= sM * m /\ m * Y <= Y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + m) * (Sd + Y) + (&2 + &4 * L) * m <= Sd + m * Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    SUBGOAL_THEN `m * (sM * m) <= sM * m` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + P * m) * (Sd + m * Q) <= Sd + m * C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    SUBGOAL_THEN `(P * Q) * (m * m) <= (P * Q) * m` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m * C < eps1 - Sd` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < m * C` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 + P * m) * (Sd + m * Q)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    SUBGOAL_THEN `&0 <= L * m` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let P2B9_NECK_CENTRE_BOUND = prove
 (`!V eps x t a (e:real^3->A).
     rfs_evolving_neck V eps x t a e
     ==> ?K0. !y0. y0 IN sphere(vec 0,&1) /\ e y0 = x
                   ==> lrm_deriv_norm2 0
                         (\z. rfs_vscalar V t x %%
                              rfs_pullback (rfs_vatlas V t) e (rfs_vmetric V t) z) y0
                       <= K0 pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; rfs_neck] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
  EXISTS_TAC `&1 + abs(lrm_deriv_norm2 0
                         (\z. rfs_vscalar V t (x:A) %%
                              rfs_pullback (rfs_vatlas V t) (e:real^3->A)
                                           (rfs_vmetric V t) z) y1)` THEN
  X_GEN_TAC `y0:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `y0:real^3 = y1` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop V (t:real):A topology`;
                          `rfs_vatlas V (t:real):((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e:real^3->A`] THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 + abs x) * abs x ==> x <= (&1 + abs x) pow 2`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC);;

let P2B9_NECK_SUP = prove
 (`!V eps x t a (e:real^3->A).
     rfs_evolving_neck V eps x t a e
     ==> ?d0. &0 <= d0 /\ d0 < eps pow 2 /\
              !s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
                    ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                          (\z. rfs_vscalar V t x %%
                               rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                            (rfs_vmetric V (t + s / rfs_vscalar V t x)) z) y
                        <= d0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; rfs_close_fam; rfs_neck] THEN
  STRIP_TAC THEN EXISTS_TAC `max d (&0)` THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MAX_LT] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
    REWRITE_TAC[REAL_MAX_MAX] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^3`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let P2B_NECK_OPEN_L_FROM_REQ = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_REQ_LRG_BASE_STATEMENT ==> P2B_NECK_OPEN_L_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_REQ_LRG_BASE_STATEMENT; P2B_NECK_OPEN_L_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "req") THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `t:real`; `a:real`; `L:real`; `e:real^3->A`] THEN
  STRIP_TAC THEN
  USE_THEN "req" (MP_TAC o SPEC `rfs_kreg eps`) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`] P2B9_NECK_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sup")))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`] P2B9_NECK_CENTRE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "cb")) THEN
  MP_TAC(ISPECL [`sqrt d0`; `eps:real`; `M:real`; `K0:real`; `L:real`; `a:real`;
                 `rfs_kreg eps + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `t':real`; `Q':real`; `psi:A->B`] THEN STRIP_TAC THEN
  EXISTS_TAC `(psi:A->B) o (e:real^3->A)` THEN
  MATCH_MP_TAC P2B9_ENECK_CORE THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg eps`; `M:real`; `K0:real`; `eps:real`; `a:real`;
                        `delta:real`; `d0:real`;
                        `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `t:real`; `Q':real`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REAL_ARITH_TAC]);;

let P2B_NECK_OPEN_FROM_REQ = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_REQ_LRG_BASE_STATEMENT ==> P2B_NECK_OPEN_STATEMENT u w`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2B_NECK_OPEN_L_FROM_REQ) THEN
  DISCH_THEN(MP_TAC o SPECL [`u:A->bool`; `w:B->bool`]) THEN
  REWRITE_TAC[P2B_NECK_OPEN_L_STATEMENT; P2B_NECK_OPEN_STATEMENT; rfs_strong_neck] THEN
  DISCH_THEN(LABEL_TAC "l") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "l" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let P2B9_NECK_CENTRE_UNIFORM = prove
 (`P2B_REQ_LRG_RM_NEAR_STATEMENT
   ==> ?K0. !V eps x t a (e:real^3->A).
              p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\ eps < &1 / &4
              ==> !y0. y0 IN sphere(vec 0,&1) /\ e y0 = x
                       ==> lrm_deriv_norm2 0
                             (\z. rfs_vscalar V t x %%
                                  rfs_pullback (rfs_vatlas V t) e (rfs_vmetric V t) z) y0
                           <= K0 pow 2`,
  REWRITE_TAC[P2B_REQ_LRG_RM_NEAR_STATEMENT] THEN DISCH_TAC THEN
  X_CHOOSE_TAC `Kc:real` APX_CYL0_RM_BOUND THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `K:real` o SPEC `Kc pow 2`) THEN
  EXISTS_TAC `&1 + abs K` THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `eps:real`; `x:A`; `t:real`; `a:real`; `e:real^3->A`] THEN
  STRIP_TAC THEN X_GEN_TAC `y0:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_evolving_neck V eps (x:A) t a (e:real^3->A)` THEN
    REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `--a < &0 <=> &0 < a`;
                  real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_evolving_neck V eps (x:A) t a (e:real^3->A)` THEN
  REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `norm(y0:real^3) = &1` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K:real` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 + abs x) * abs x ==> x <= (&1 + abs x) pow 2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    length(fst(strip_forall(concl th))) = 4)) THEN
  MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `cylinder_flow (&0)`] THEN
  ASM_SIMP_TAC[APX_NECK_CYL_FIELD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                (\y. rfs_vscalar V t (x:A) %%
                     rfs_pullback (rfs_vatlas V t) (e:real^3->A) (rfs_vmetric V t) y) y0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN CONJ_TAC THENL
   [REWRITE_TAC[P2B9_RFS_VSCALAR] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `d:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REAL_ARITH_TAC);;

let P2B_PROP_9_79_NECK_FIX_FROM_REQ = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_REQ_LRG_BASE_STATEMENT /\ P2B_REQ_LRG_RM_NEAR_STATEMENT
     ==> P2B_PROP_9_79_NECK_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "req") (MP_TAC o MATCH_MP P2B9_NECK_CENTRE_UNIFORM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "cu" o INST_TYPE [`:A`,`:A`])) THEN
  REWRITE_TAC[P2B_PROP_9_79_NECK_FIX_STATEMENT; rfs_strong_neck] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `eps':real`; `a:real`] THEN STRIP_TAC THEN
  USE_THEN "req" (MP_TAC o SPEC `rfs_kreg eps'` o REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(ISPECL [`eps:real`; `eps':real`; `M:real`; `K0:real`; `&1`; `a:real`;
                 `rfs_kreg eps' + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `t:real`; `e:real^3->A`;
    `V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)`;
    `t':real`; `Q':real`; `psi:A->B`] THEN STRIP_TAC THEN
  EXISTS_TAC `(psi:A->B) o (e:real^3->A)` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                 `e:real^3->A`] P2B9_NECK_SUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sup")))) THEN
  MATCH_MP_TAC P2B9_ENECK_CORE THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg eps'`; `M:real`; `K0:real`; `eps:real`; `a:real`;
                        `delta:real`; `eps pow 2`;
                        `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)`; `t:real`; `Q':real`] THEN
  CONJ_TAC THENL [USE_THEN "base" ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d1:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN USE_THEN "sup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "cu" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`eps:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Static necks (one slice).  The same-eps transfer of an eps-neck along a   *)
(* diffeomorphism whose pullback metric is delta-close at the scale R(x)     *)
(* (P2B9_SNECK_CORE, P2B9_OPEN_NECK): the neck case of the open form of MT   *)
(* Prop 9.79.                                                                *)
(* ------------------------------------------------------------------------- *)

let P2B9_SNECK_CORE = prove
 (`!k1 M K0 eps delta d0 top atlas (g:A->real^3^3) x e top' atlas' (g':B->real^3^3)
    psi psi'.
     (!s (G0:real^3->real^3^3) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k1 G0 G1 y <= &1 / &4
         ==> lck_dist2 k1 G0 (\z. G0 z + G2 z - G1 z) y <= M * lck_dist2 k1 G1 G2 y) /\
     &0 <= M /\ k1 = rfs_kreg eps /\
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
     &0 <= d0 /\ d0 <= &1 / &4 /\
     (!y. y IN rfs_neck_dom eps
          ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y <= d0) /\
     (!y0. y0 IN sphere(vec 0,&1) /\ e y0 = x
           ==> lrm_deriv_norm2 0 (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y0
               <= K0 pow 2) /\
     smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas (IMAGE e (rfs_neck_dom eps)) top' atlas'
                (IMAGE psi (IMAGE e (rfs_neck_dom eps))) psi psi' /\
     rfs_mclose (rfs_kreg delta) delta atlas (IMAGE e (rfs_neck_dom eps))
       (\y. mfd_scalar atlas g x %% g y)
       (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y) /\
     &0 < delta /\ delta <= &1 / &10 /\ delta <= eps /\
     &72 * (&1 + abs K0) * delta <= &1 / &2 /\
     (&1 + &72 * (&1 + abs K0) * delta) * (sqrt d0 + sqrt M * delta) +
       &2 * (&72 * (&1 + abs K0) * delta) < eps
     ==> rfs_neck (top',atlas') g' eps (psi x) (psi o e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base") STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k1 = rfs_kreg eps`)) THEN
  SUBGOAL_THEN `rfs_kreg eps <= rfs_kreg delta` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[rfs_neck] (ASSUME
    `rfs_neck (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
              eps x (e:real^3->A)`)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> concl th = `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))`)) THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `m = &72 * (&1 + abs K0) * delta` THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top' atlas' (rfs_neck_dom eps) ((psi:A->B) o (e:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                          `IMAGE (psi:A->B) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
                          `psi':B->A`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `IMAGE (e:real^3->A) (rfs_neck_dom eps)`;
                 `IMAGE (psi:A->B) (IMAGE (e:real^3->A) (rfs_neck_dom eps))`;
                 `psi:A->B`; `psi':B->A`; `g:A->real^3^3`; `g':B->real^3^3`;
                 `R:real`; `R:real`; `rfs_kreg delta`; `delta:real`] P2B9_MCLOSE_PARAM) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))) THEN
  SUBGOAL_THEN
   `lscalar (\z. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) z) y0 = &1 /\
    lscalar (\z. R %% rfs_pullback atlas' ((psi:A->B) o e) (g':B->real^3^3) z) y0 =
    mfd_scalar atlas' g' (psi x) / R`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `rfs_neck_dom eps`; `e:real^3->A`; `R:real`;
                     `y0:real^3`] P2B9_PARAM_LSCALAR_SCALED) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `x:A = e (y0:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `g':B->real^3^3`; `rfs_neck_dom eps`; `(psi:A->B) o (e:real^3->A)`;
                     `R:real`; `y0:real^3`] P2B9_PARAM_LSCALAR_SCALED) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      UNDISCH_TAC `x:A = e (y0:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `G1 = \z. R %% rfs_pullback atlas (e:real^3->A) (g:A->real^3^3) z` THEN
  ABBREV_TAC `G2 = \z. R %% rfs_pullback atlas' ((psi:A->B) o (e:real^3->A))
                                         (g':B->real^3^3) z` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (G1:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (G2:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R' = mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) x)` THEN
  ABBREV_TAC `c = R' / R` THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G1:real^3->real^3^3) G2 y0) <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(delta pow 2)` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg delta) (G1:real^3->real^3^3) G2 y0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) <= m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K0:real`; `rfs_neck_dom eps`; `G1:real^3->real^3^3`;
                   `G2:real^3->real^3^3`; `y0:real^3`] APX_SCALAR_STABILITY_LIP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "lrm_deriv_norm2"))
              (concl th))) THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> x <= b ==> x <= c`) THEN
    REWRITE_TAC[REAL_ARITH `&8 * &3 pow 2 * k * d = (&72 * k) * d`] THEN
    EXPAND_TAC "m" THEN
    REWRITE_TAC[REAL_ARITH `&72 * (&1 + abs K0) * delta = (&72 * (&1 + abs K0)) * delta`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c /\ R' = c * R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Bnd = (&1 + m) * (sqrt d0 + sqrt M * delta) + &2 * m` THEN
  SUBGOAL_THEN `&0 <= Bnd` ASSUME_TAC THENL
   [EXPAND_TAC "Bnd" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
      ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN rfs_neck_dom eps
        ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0)) (\z. c %% (G2:real^3->real^3^3) z) y
            <= Bnd pow 2`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rfs_kreg eps`; `rfs_kreg eps`; `rfs_kreg delta`; `M:real`; `&0`; `&0`;
                   `rfs_neck_dom eps`; `G1:real^3->real^3^3`; `G2:real^3->real^3^3`;
                   `c:real`; `d0:real`; `dd:real`; `y:real^3`] P2B9_NECK_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO; REAL_LE_REFL; REAL_SUB_REFL; REAL_ABS_0] THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV;
        UNDISCH_TAC `!y. y IN rfs_neck_dom eps
                         ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                                       (G1:real^3->real^3^3) y <= d0` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_RID; REAL_POW_ONE;
                                      REAL_MUL_LID; REAL_MUL_RZERO]) THEN
    DISCH_THEN(LABEL_TAC "np") THEN
    MP_TAC(ISPECL [`rfs_kreg eps + 2`; `&0`; `m:real`; `delta:real`; `c:real`; `&0`;
                   `sqrt d0`; `M:real`; `dd:real`] P2B9_BND_ARITH) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_REFL; SQRT_POS_LE; REAL_LT_IMP_LE; REAL_MUL_LZERO;
                    REAL_MUL_RZERO] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg delta) (G1:real^3->real^3^3) G2 y` THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
        ASM_REWRITE_TAC[];
        USE_THEN "dd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_POW_ONE; REAL_MUL_LID;
                REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow (&0)) (\z. c %% (G2:real^3->real^3^3) z) y)
                  <= Bnd` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c * (sqrt d0 + sqrt (M * dd)) + abs (c - &1) * sqrt (&3)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "np" ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lck_dist2 (rfs_kreg eps) (cylinder_flow (&0)) (\z. c %% (G2:real^3->real^3^3) z) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[APX_NECK_CYL_FIELD] THEN MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow (&0)) (\z. c %% (G2:real^3->real^3^3) z) y)
                pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `x:A = e (y0:real^3)`)) THEN
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `Bnd pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN rfs_neck_dom eps`))) THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= x ==> b <= x`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  EXPAND_TAC "G2" THEN REWRITE_TAC[MATRIX_CMUL_ASSOC; FUN_EQ_THM]);;

let P2B9_STATIC_BND = prove
 (`!n m X. &0 <= m /\ &0 <= X
           ==> X + &2 * m <= (&1 + &2 * &1 * m) pow n * (X + (&2 + &4 * &1) * m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * (X + (&2 + &4 * &1) * m)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2B9_SNECK_DATA = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     rfs_neck (top,atlas) g eps x e
     ==> ?d0 K0. &0 <= d0 /\ d0 < eps pow 2 /\
                 (!y. y IN rfs_neck_dom eps
                      ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                            (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y <= d0) /\
                 (!y0. y0 IN sphere(vec 0,&1) /\ e y0 = x
                       ==> lrm_deriv_norm2 0
                             (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y0
                           <= K0 pow 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck; rfs_close_on] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> concl th = `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))`)) THEN
  MAP_EVERY EXISTS_TAC
   [`max d (&0)`;
    `&1 + abs(lrm_deriv_norm2 0
                (\z. mfd_scalar atlas (g:A->real^3^3) x %%
                     rfs_pullback atlas (e:real^3->A) g z) y1)`] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MAX_LT] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
    REWRITE_TAC[REAL_MAX_MAX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y0:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `y0:real^3 = y1` SUBST1_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `e:real^3->A`] THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 + abs x) * abs x ==> x <= (&1 + abs x) pow 2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC]);;

let P2B9_OPEN_NECK = prove
 (`P2B_REQ_LRG_BASE_STATEMENT
   ==> !eps top atlas (g:A->real^3^3) x e.
         &0 < eps /\ eps < &1 / &4 /\ riemannian_metric atlas g /\
         rfs_neck (top,atlas) g eps x e
         ==> ?delta. &0 < delta /\
               !top' atlas' (g':B->real^3^3) psi psi'.
                  smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
                  mfd_diffeo top atlas (IMAGE e (rfs_neck_dom eps)) top' atlas'
                             (IMAGE psi (IMAGE e (rfs_neck_dom eps))) psi psi' /\
                  rfs_mclose (rfs_kreg delta) delta atlas (IMAGE e (rfs_neck_dom eps))
                    (\y. mfd_scalar atlas g x %% g y)
                    (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                  ==> rfs_neck (top',atlas') g' eps (psi x) (psi o e)`,
  REWRITE_TAC[P2B_REQ_LRG_BASE_STATEMENT] THEN DISCH_THEN(LABEL_TAC "req") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "req" (MP_TAC o SPEC `rfs_kreg eps`) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`] P2B9_SNECK_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `K0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "sup") (LABEL_TAC "cb")))))) THEN
  MP_TAC(ISPECL [`sqrt d0`; `eps:real`; `M:real`; `K0:real`; `&1`; `&2`;
                 `rfs_kreg eps + 2`] P2B9_DELTA_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2B9_SNECK_CORE THEN
  MAP_EVERY EXISTS_TAC [`rfs_kreg eps`; `M:real`; `K0:real`; `delta:real`; `d0:real`;
                        `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `psi':B->A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &72 * (&1 + abs K0) * delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `eps pow 2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps pow 2 <= (&1 / &4) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 + &2 * &1 * (&72 * (&1 + abs K0) * delta)) pow (rfs_kreg eps + 2) *
              ((&1 + &72 * (&1 + abs K0) * delta) * (sqrt d0 + sqrt M * delta) +
               (&2 + &4 * &1) * (&72 * (&1 + abs K0) * delta))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2B9_STATIC_BND THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
  ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]);;

