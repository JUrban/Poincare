(* ========================================================================= *)
(* Unit pc_p2c_fl511 (Part 2C, first unit of the flowlim route): MT Thm 5.11 *)
(* on the carrier real^3.  Geometric limits of rescaled time slices of based *)
(* histories with curvature bounds on backward parabolic balls: the          *)
(* derivative bounds of MT Thm 5.9 come from Shi's estimate (P2_THM_3_28,    *)
(* proved as RFA_P2_THM_3_28) applied at scale Q n to the region flows of    *)
(* the persisting balls (regular views, P2C_HISTORY_REGULAR), and the limit  *)
(* from MT Cor 5.10 (P2CK_CG_COMPACT, pc_p2c_cg).                            *)
(* ========================================================================= *)

needs "src/pc_p2c_cg.ml";;
needs "src/pc_p2c_l112.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Slices of histories are compact; curves, lengths and balls               *)
(* of an open submanifold (subtopology top W, restrict_atlas atlas W) with   *)
(* the restricted metric: its balls lie in the balls of the manifold; the    *)
(* derivative of a diffeomorphism of open sets is injective.                 *)
(* ------------------------------------------------------------------------- *)

let P2CW_HIST_COMPACT = prove
 (`!(hs:(A)rfs_history) t. rfs_history_ok hs ==> compact_space (rfs_top_at hs t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_top_at] THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t` THEN
      REWRITE_TAC[rfs_live; rfs_horizon] THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `rfs_slab (hs:(A)rfs_history) t` o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_EMPTY]]);;

let P2CW_C1_CURVE_RESTRICT = prove
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

let P2CW_LENGTH_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) (gamma:real->A) a b.
     smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b
     ==> mfd_length (restrict_atlas atlas W) (restrict_metric atlas W g) gamma a b =
         mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CW_C1_CURVE_RESTRICT) THEN
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

let P2CW_RESTRICT_BALL = prove
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
                 `x:A`; `y:A`; `r:real`] P2C_BALL_CURVE) THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CW_C1_CURVE_RESTRICT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] P2CW_LENGTH_RESTRICT) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The derivative of a diffeomorphism of open sets is injective. *)

let P2CW_DIFFEO_DERIV_INJ = prove
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

(* ------------------------------------------------------------------------- *)
(* The region flow p2c_vfam V W b of a regular view on a                     *)
(* persisting set W, read in the restricted atlas of the last time b: its   *)
(* curvature norm at time s is at most that of the slice at s, and its      *)
(* |nabla^l Rm|^2 at time b is that of the slice at b.                       *)
(* ------------------------------------------------------------------------- *)

let P2CW_VFAM_PULLBACK_LOCAL = prove
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
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
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
         P2C_PULLBACK_METRIC_LOCAL_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN
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

let P2CW_VFAM_RM_NORM_LE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s x.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < s /\ s <= b /\ x IN W
     ==> mfd_rm_norm (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b s) x <=
         p3_vrm V s x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
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
                    (real->A->real^3^3)`; `s:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] P2C_REGULAR_SLICE) THEN
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
      MATCH_MP_TAC MFD_DIFFEO_SYM THEN MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN
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
    MATCH_MP_TAC P2CW_VFAM_PULLBACK_LOCAL THEN EXISTS_TAC `a:real` THEN
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
         APX_PULLBACK_SECTIONAL_GEN) THEN
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
    MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^3) x` o MATCH_MP P2CW_DIFFEO_DERIV_INJ) THEN
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

(* |nabla^l Rm|^2 of the region flow at its last time is that of the slice. *)

let P2CW_VFAM_DERIV_LAST = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b l x.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < b /\ x IN W
     ==> lrm_deriv_norm2 l
           (metric_local (restrict_atlas (rfs_vatlas V b) W)
                         (chart_at (restrict_atlas (rfs_vatlas V b) W) x) (p2c_vfam V W b b))
           (SND(chart_at (restrict_atlas (rfs_vatlas V b) W) x) x) =
         p3_vderiv2 V l b x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x:A`] P2C_REGULAR_SLICE) THEN
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

(* ------------------------------------------------------------------------- *)
(* Shi's estimate (P2_THM_3_28) at scale q, at the centre of a              *)
(* ball of radius A / sqrt q, from the parabolically rescaled flow           *)
(* q g(t / q) (the template of RFA_P2A_REQ_SHI_SCALED, for every order l).  *)
(* ------------------------------------------------------------------------- *)

let P2CW_SHI_SCALED = prove
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
        ASM_SIMP_TAC[P2CU_BALL_SUBSET];
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

(* ------------------------------------------------------------------------- *)
(* The ball of a region manifold W of a regular view around y, of radius r,  *)
(* lies in the slice ball; if the slice ball B(y,2 r) lies in W and the      *)
(* slice is compact, its closure in the region manifold is compact.          *)
(* ------------------------------------------------------------------------- *)

let P2CW_REGION_BALL_COMPACT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W y r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_space top /\
     open_in top W /\ &0 < r /\ mfd_ball (top,atlas) g y (&2 * r) SUBSET W
     ==> compact_in (subtopology top W)
           (subtopology top W closure_of
            mfd_ball (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g) y r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = mfd_ball (subtopology top W,
                            restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) W)
                           (restrict_metric atlas W (g:A->real^3^3)) (y:A) r` THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) y r` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2CW_RESTRICT_BALL THEN ASM_REWRITE_TAC[];
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
           P2CU_BALL_SUBSET) THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(W:A->bool) INTER S = S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) INTER (top closure_of S) = top closure_of S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shi's estimate on regular views (the region flow of the                   *)
(* persisting ball B(x0,4 R / sqrt q) over (a,b], at the points of           *)
(* B(x0,R / sqrt q), compact slice), and MT Thm 5.11.                        *)
(* ------------------------------------------------------------------------- *)

let P2CW_SHI_VIEW = prove
 (`!l K R tau.
     &0 < K /\ &0 < R /\ &0 < tau
     ==> ?C. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) x0 a b q y.
               p2c_regular_view V /\ compact_space (rfs_vtop V b) /\
               x0 IN topspace(rfs_vtop V b) /\ &0 < q /\ a < b /\ tau <= q * (b - a) /\
               rfs_persists V (rfs_vball V b x0 ((&4 * R) * inv(sqrt q))) a b /\
               (!s z. a < s /\ s <= b /\ z IN rfs_vball V b x0 ((&4 * R) * inv(sqrt q))
                      ==> p3_vrm V s z <= K * q) /\
               y IN rfs_vball V b x0 (R * inv(sqrt q))
               ==> p3_vderiv2 V l b y <= C * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `K:real`; `R:real`; `tau:real`] P2CW_SHI_SCALED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x0:A`; `a:real`; `b:real`; `q:real`; `y:A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R * inv(sqrt q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * R) * inv(sqrt q) = &4 * (R * inv(sqrt q))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `r = R * inv(sqrt q)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[P2C_VIEW_EXPAND]) THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(&4 * R) * inv(sqrt q) = &4 * r`]) THEN
  ABBREV_TAC `W = mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) (&4 * r)` THEN
  SUBGOAL_THEN `p2c_vflow (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W a b`
  MP_TAC THENL
   [MATCH_MP_TAC P2C_REGULAR_VFLOW THEN ASM_REWRITE_TAC[P2C_VIEW_EXPAND]; ALL_TAC] THEN
  REWRITE_TAC[p2c_vflow; P2C_VIEW_EXPAND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) r SUBSET W /\
    mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (y:A) (&2 * r) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) (r + &2 * r)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) W b b =
                restrict_metric (rfs_vatlas V b) W (rfs_vmetric V b)`
  ASSUME_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `l:num`; `y:A`]
         P2CW_VFAM_DERIV_LAST) THEN
  ASM_REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
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
    MATCH_MP_TAC P2CW_REGION_BALL_COMPACT THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_metric (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
                        (rfs_vmetric V b)`; `y:A`; `r:real`] P2CU_BALL_SUBSET) THEN
      ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CW_VFAM_RM_NORM_LE THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[P2C_VIEW_EXPAND];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:A) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[]]]);;

(* MT Thm 5.11 on the carrier real^3 from the regularity of history views. *)

let P2CW_THM_5_11 = prove
 (`!u:A->bool. P2C_HISTORY_REGULAR_STATEMENT u ==> P2_THM_5_11_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_TAC THEN
  REWRITE_TAC[P2_THM_5_11_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`; `Q:num->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "base")
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "vol"))) THEN
  SUBGOAL_THEN `!n. p2c_regular_view (rfs_view ((hs:num->(A)rfs_history) n)) /\
                    compact_space (rfs_vtop (rfs_view (hs n)) (t n)) /\
                    (x:num->A) n IN topspace(rfs_vtop (rfs_view (hs n)) (t n)) /\
                    &0 < (Q:num->real) n`
  (LABEL_TAC "nf") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "base" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[P2C_RFS_VIEW_PARTS; P2CW_HIST_COMPACT];
    ALL_TAC] THEN
  MP_TAC(SPEC `u:A->bool` P2CK_CG_COMPACT) THEN REWRITE_TAC[P2C_CG_COMPACT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`\n. rfs_view ((hs:num->(A)rfs_history) n)`; `x:num->A`;
                             `t:num->real`; `Q:num->real`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "nf" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2C_REGULAR_SLICE THEN
    EXISTS_TAC `(x:num->A) n` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `R:real` THEN DISCH_TAC THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN USE_THEN "nf" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    MAP_EVERY X_GEN_TAC [`R:real`; `l:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &4 * R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "per" (MP_TAC o C MP (ASSUME `&0 < &4 * R`) o SPEC `&4 * R`) THEN
    DISCH_THEN(X_CHOOSE_THEN `CA:real` (X_CHOOSE_THEN `dA:real`
      (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`l:num`; `max CA (&1)`; `R:real`; `dA:real`] P2CW_SHI_VIEW) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "sv"))] THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `N:num`] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "nf" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN STRIP_TAC THEN
    USE_THEN "sv" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(x:num->A) n`; `(t:num->real) n - dA * inv((Q:num->real) n)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < dA * inv((Q:num->real) n)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH `t - (t - d) = d`] THEN
      SUBGOAL_THEN `(Q:num->real) n * (dA * inv(Q n)) = dA`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      UNDISCH_TAC `&0 < (Q:num->real) n` THEN CONV_TAC REAL_FIELD;
      MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CA * (Q:num->real) n` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]];
    USE_THEN "vol" MP_TAC THEN REWRITE_TAC[P2C_RFS_VIEW_PARTS]]);;

let P2CW_THM_5_11_ROUTE = prove
 (`!u:A->bool. P2C_THM_5_11_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_THM_5_11_ROUTE_STATEMENT] THEN
  MESON_TAC[P2CW_THM_5_11]);;

