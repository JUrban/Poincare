(* ========================================================================= *)
(* Unit pc_p2c_lrestrict (Part 2C; also used in Part 2B): limits restricted  *)
(* to the joinable class of the base point.  p3_slice_limit, p3_flow_limit   *)
(* and p3_flow_limit_on do not say that the limit manifold is connected.     *)
(* The joinable class C of xl is open and closed; on (subtopology top C,     *)
(* restrict_atlas atlas C) the C^1 curves from points of C, their lengths,   *)
(* distances, closed balls and completeness are those of top, and every      *)
(* point is joinable to xl.  A limit of each kind restricts to C with the    *)
(* same subsequence, the exhaustion W k INTER C and the same maps phi k: the *)
(* lck clauses move to the charts of the restricted atlas by chart           *)
(* independence (P2CA_LCK_CHART_INDEP_C) and P2BL_PB_CHART.                  *)
(* ========================================================================= *)

needs "src/pc_p2c_flasm.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_apx_local.ml";;
needs "src/pc_p2a_par.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The joinable class C of a point x0 (open and closed).  On                 *)
(* the manifold (subtopology top C, restrict_atlas atlas C) the C^1 curves   *)
(* from points of C are those of top (they stay in C), with the same         *)
(* lengths; hence the same joinability, distances and closed balls, and      *)
(* completeness passes to C.                                                 *)
(* ------------------------------------------------------------------------- *)

let P2CO_C1_CURVE_SUBTOP = prove
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

let P2CO_CURVE_IN_CLASS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) x0.
     smooth_manifold_atlas top atlas /\ mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     mfd_joinable (top,atlas) x0 (gamma(&0))
     ==> !s. s IN real_interval[&0,&1] ==> mfd_joinable (top,atlas) x0 (gamma s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
  EXISTS_TAC `(gamma:real->A)(&0)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN
  MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
  UNDISCH_TAC `s IN real_interval[&0,&1]` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let P2CO_CLASS_CURVES = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) x0 (gamma:real->A).
     smooth_manifold_atlas top atlas /\
     mfd_joinable (top,atlas) x0 (gamma(&0))
     ==> (mfd_c1_curve (subtopology top {y | mfd_joinable (top,atlas) x0 y},
                        restrict_atlas atlas {y | mfd_joinable (top,atlas) x0 y}) gamma (&0) (&1)
          <=> mfd_c1_curve (top,atlas) gamma (&0) (&1))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP P2AP_C1_CURVE_RESTRICT) THEN SIMP_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC P2CO_C1_CURVE_SUBTOP THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC P2CO_CURVE_IN_CLASS THEN ASM_REWRITE_TAC[]]);;

let P2CO_CLASS_DIST = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x0 x y.
     smooth_manifold_atlas top atlas /\ mfd_joinable (top,atlas) x0 x
     ==> (mfd_joinable (subtopology top {y | mfd_joinable (top,atlas) x0 y},
                        restrict_atlas atlas {y | mfd_joinable (top,atlas) x0 y}) x y <=>
          mfd_joinable (top,atlas) x y) /\
         mfd_dist (subtopology top {y | mfd_joinable (top,atlas) x0 y},
                   restrict_atlas atlas {y | mfd_joinable (top,atlas) x0 y})
                  (restrict_metric atlas {y | mfd_joinable (top,atlas) x0 y} g) x y =
         mfd_dist (top,atlas) g x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `C = {y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x0 y}` THEN
  SUBGOAL_THEN `open_in top (C:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC MFD_JOINABLE_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!gamma:real->A. gamma(&0) = x
                    ==> (mfd_c1_curve (subtopology (top:A topology) C,
                                       restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) C)
                                      gamma (&0) (&1)
                         <=> mfd_c1_curve (top,atlas) gamma (&0) (&1))`
  (LABEL_TAC "cur") THENL
   [X_GEN_TAC `gamma:real->A` THEN DISCH_TAC THEN EXPAND_TAC "C" THEN
    MATCH_MP_TAC P2CO_CLASS_CURVES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cur" (MP_TAC o SPEC `gamma:real->A`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_dist] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `l:real` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN
  USE_THEN "cur" (MP_TAC o C MP (ASSUME `(gamma:real->A)(&0) = x`) o SPEC `gamma:real->A`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `C:A->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`] P2AP_LENGTH_RESTRICT) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN ASM_MESON_TAC[]);;

let P2CO_CLASS_CBALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x0 x r.
     smooth_manifold_atlas top atlas /\ mfd_joinable (top,atlas) x0 x
     ==> mfd_cball (subtopology top {y | mfd_joinable (top,atlas) x0 y},
                    restrict_atlas atlas {y | mfd_joinable (top,atlas) x0 y})
                   (restrict_metric atlas {y | mfd_joinable (top,atlas) x0 y} g) x r =
         mfd_cball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_cball; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:A` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`; `x:A`; `y:A`] P2CO_CLASS_DIST) THEN
  ASM_SIMP_TAC[]);;

let P2CO_CLASS_CLOSED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) x0.
     smooth_manifold_atlas top atlas
     ==> open_in top {y | mfd_joinable (top,atlas) x0 y} /\
         closed_in top {y | mfd_joinable (top,atlas) x0 y}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MFD_JOINABLE_OPEN] THEN
  REWRITE_TAC[closed_in] THEN ASM_SIMP_TAC[GRGD_JOINABLE_COMPLEMENT_OPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]);;

let P2CO_CLASS_COMPLETE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x0.
     smooth_manifold_atlas top atlas /\ mfd_complete (top,atlas) g
     ==> mfd_complete (subtopology top {y | mfd_joinable (top,atlas) x0 y},
                       restrict_atlas atlas {y | mfd_joinable (top,atlas) x0 y})
                      (restrict_metric atlas {y | mfd_joinable (top,atlas) x0 y} g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_complete] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `r:real`] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2CO_CLASS_CBALL; COMPACT_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN REWRITE_TAC[mfd_complete] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]);;

let P2CO_CLASS_ALL_JOINABLE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) x0 y.
     smooth_manifold_atlas top atlas /\ x0 IN topspace top /\
     y IN topspace (subtopology top {y | mfd_joinable (top,atlas) x0 y})
     ==> mfd_joinable (subtopology top {y | mfd_joinable (top,atlas) x0 y},
                       restrict_atlas atlas {y | mfd_joinable (top,atlas) x0 y}) x0 y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(\x:A. mat 0):A->real^N^N`; `x0:A`; `x0:A`; `y:A`] P2CO_CLASS_DIST) THEN
  ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN SIMP_TAC[]);;

let P2CO_CLASS_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) x0.
     smooth_manifold_atlas top atlas
     ==> connected_space (subtopology top {y | mfd_joinable (top,atlas) x0 y})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x0 y} =
                connected_component_of top (x0:A)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
    ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT] THEN REWRITE_TAC[IN];
    MP_TAC(ISPECL [`top:A topology`; `x0:A`] CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN
    SIMP_TAC[connected_in]]);;

(* ------------------------------------------------------------------------- *)
(* The chart form of a rescaled pullback by a diffeomorphism                 *)
(* f of open sets (P2BL_PB_CHART) is a metric field on the chart images of   *)
(* the source set, and lck distances to it at a point of the source set do  *)
(* not change when the chart at the point is replaced by the chart of the   *)
(* restricted atlas (P2CO_LCK_RESTRICT).                                     *)
(* ------------------------------------------------------------------------- *)

let P2CO_RIEM_FIELD = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) c O.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     open_in top O
     ==> metric_field (IMAGE (SND c) (FST c INTER O)) (metric_local atlas c g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
  EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    SET_TAC[]]);;

let P2CO_CHART_PARAM = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' c.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo top atlas W topX atlasX W' f f' /\ c IN atlas
     ==> mfd_param topX atlasX (IMAGE (SND c) (FST c INTER W)) (f o chart_inv c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `W:B->bool`; `W':A->bool`; `f':A->B`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                    MFD_PARAM_CHART_INV) THEN
      ASM_REWRITE_TAC[PAIR];
      MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_MESON_TAC[mfd_diffeo];
      SET_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]]);;

let P2CO_PB_LOCAL = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' (gX:A->real^3^3) q c z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo top atlas W topX atlasX W' f f' /\ c IN atlas /\
     z IN IMAGE (SND c) (FST c INTER W)
     ==> metric_local atlas c (\x. q %% mfd_pullback_metric atlas atlasX f gX x) z =
         q %% rfs_pullback atlasX (f o chart_inv c) gX z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[METRIC_LOCAL_CMUL] THEN REWRITE_TAC[ETA_AX] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC P2BL_PB_CHART THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `topX:A topology`; `W:B->bool`; `W':A->bool`;
                        `f':A->B`] THEN
  ASM_REWRITE_TAC[]);;

let P2CO_PB_FIELD = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' (gX:A->real^3^3) q c.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo top atlas W topX atlasX W' f f' /\ riemannian_metric atlasX gX /\
     c IN atlas /\ &0 < q
     ==> metric_field (IMAGE (SND c) (FST c INTER W))
                      (metric_local atlas c (\x. q %% mfd_pullback_metric atlas atlasX f gX x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `\z. q %% rfs_pullback (atlasX:((A->bool)#(A->real^3))->bool)
                         ((f:B->A) o chart_inv c) (gX:A->real^3^3) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `topX:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CO_CHART_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `W':A->bool`; `f':A->B`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CO_PB_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `topX:A topology`; `W:B->bool`; `W':A->bool`;
                          `f':A->B`] THEN
    ASM_REWRITE_TAC[]]);;

let P2CO_FD_LOCAL = prove
 (`!(f:real^N->real^M) g O z.
     open O /\ z IN O /\ (!w. w IN O ==> f w = g w)
     ==> frechet_derivative f (at z) = frechet_derivative g (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^N->real^M` THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [open_def]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [MAP_EVERY EXISTS_TAC [`f:real^N->real^M`; `d:real`];
    MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `d:real`]] THEN
  ASM_SIMP_TAC[]);;

let P2CO_RFS_PULLBACK_LOCAL = prove
 (`!atlas (e1:real^N->A) e2 (g:A->real^N^N) O z.
     open O /\ z IN O /\ (!w. w IN O ==> e1 w = e2 w)
     ==> rfs_pullback atlas e1 g z = rfs_pullback atlas e2 g z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback] THEN
  SUBGOAL_THEN `(e1:real^N->A) z = e2 z` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) z)) o
                        (e1:real^N->A)) (at z) =
    frechet_derivative (SND(chart_at atlas (e2 z)) o e2) (at z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CO_FD_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]);;

let P2CO_LCK_RESTRICT = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' (gX:A->real^3^3) (g0:B->real^3^3) q Cs y m.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     mfd_diffeo top atlas W topX atlasX W' f f' /\ riemannian_metric atlasX gX /\
     riemannian_metric atlas g0 /\ &0 < q /\ open_in top Cs /\ y IN W /\ y IN Cs
     ==> lck_dist2 m
           (metric_local (restrict_atlas atlas Cs) (chart_at (restrict_atlas atlas Cs) y)
                         (restrict_metric atlas Cs g0))
           (\z. q %% rfs_pullback atlasX (f o chart_inv (chart_at (restrict_atlas atlas Cs) y))
                                  gX z)
           (SND(chart_at (restrict_atlas atlas Cs) y) y) =
         lck_dist2 m (metric_local atlas (chart_at atlas y) g0)
           (\z. q %% rfs_pullback atlasX (f o chart_inv (chart_at atlas y)) gX z)
           (SND(chart_at atlas y) y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `open_in top (W:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `Cs:B->bool`; `y:B`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->bool` (X_CHOOSE_THEN `ph:B->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[SND] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = \x. q %% mfd_pullback_metric (atlas:((B->bool)#(B->real^3))->bool)
                               (atlasX:((A->bool)#(A->real^3))->bool) (f:B->A) (gX:A->real^3^3) x` THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c P) /\
            metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c (g0:B->real^3^3)) /\
            !z. z IN IMAGE (SND c) (FST c INTER W)
                ==> metric_local atlas c P z =
                    q %% rfs_pullback (atlasX:((A->bool)#(A->real^3))->bool) ((f:B->A) o chart_inv c)
                                      (gX:A->real^3^3) z`
  (LABEL_TAC "chart") THENL
   [X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CO_PB_FIELD THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `topX:A topology`; `W':A->bool`; `f':A->B`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CO_RIEM_FIELD THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC P2CO_PB_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `topX:A topology`; `W:B->bool`; `W':A->bool`;
                            `f':A->B`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (metric_local atlas (U:B->bool,ph:B->real^3) (g0:B->real^3^3))
                          (metric_local atlas (U,ph) P) (ph y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `IMAGE (ph:B->real^3) (U INTER Cs INTER W)` THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (ph:B->real^3) (U INTER Cs INTER W) =
                    IMAGE (SND(U:B->bool,ph)) (FST(U,ph) INTER (Cs INTER W))`
      SUBST1_TAC THENL [REWRITE_TAC[FST; SND; INTER_ASSOC]; ALL_TAC] THEN
      MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `w:B` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `U:B->bool`; `ph:B->real^3`; `Cs:B->bool`; `g0:B->real^3^3`; `w:B`]
                      METRIC_LOCAL_RESTRICT) THEN
        ASM_REWRITE_TAC[IN_INTER];
        REWRITE_TAC[] THEN
        USE_THEN "chart" (MP_TAC o C MP (ASSUME `(U:B->bool,ph:B->real^3) IN atlas`) o
                          SPEC `(U:B->bool,ph:B->real^3)`) THEN
        DISCH_THEN(MP_TAC o SPEC `(ph:B->real^3) w` o last o CONJUNCTS) THEN
        REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC P2CO_RFS_PULLBACK_LOCAL THEN
        EXISTS_TAC `IMAGE (ph:B->real^3) (U INTER Cs)` THEN REPEAT CONJ_TAC THENL
         [SUBGOAL_THEN `IMAGE (ph:B->real^3) (U INTER Cs) =
                        IMAGE (SND(U:B->bool,ph)) (FST(U,ph) INTER Cs)`
          SUBST1_TAC THENL [REWRITE_TAC[FST; SND]; ALL_TAC] THEN
          MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
          MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
          REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `v:B` THEN STRIP_TAC THEN
          REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
          MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `U:B->bool`; `ph:B->real^3`; `Cs:B->bool`; `v:B`]
                        MFDR_CHART_INV_RESTRICT) THEN
          ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (metric_local atlas (chart_at atlas (y:B)) (g0:B->real^3^3))
                          (metric_local atlas (chart_at atlas y) P)
                          (SND(chart_at atlas y) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `P:B->real^3^3`; `(U:B->bool,ph:B->real^3)`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`;
                   `W:B->bool`; `y:B`; `m:num`] P2CA_LCK_CHART_INDEP_C) THEN
    REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "chart" (MP_TAC o C MP (ASSUME
      `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B) IN atlas`) o
      SPEC `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                    (FST(chart_at atlas y) INTER W)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "chart" (MP_TAC o C MP (ASSUME
      `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B) IN atlas`) o
      SPEC `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`) THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The exhaustion and the diffeomorphisms restrict to the                    *)
(* joinable class; restriction theorems for p3_slice_limit and              *)
(* p2c_slice_limit_with.                                                     *)
(* ------------------------------------------------------------------------- *)

let P2CO_EXHAUST_RESTRICT = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) xl (W:num->B->bool).
     smooth_manifold_atlas top atlas /\ xl IN topspace top /\
     (!k. open_in top (W k) /\ xl IN W k /\ compact_in top (top closure_of W k) /\
          top closure_of W k SUBSET W (SUC k)) /\
     UNIONS {W k | k IN (:num)} = topspace top
     ==> (!k. open_in (subtopology top {y | mfd_joinable (top,atlas) xl y})
                      (W k INTER {y | mfd_joinable (top,atlas) xl y}) /\
              xl IN W k INTER {y | mfd_joinable (top,atlas) xl y} /\
              compact_in (subtopology top {y | mfd_joinable (top,atlas) xl y})
                (subtopology top {y | mfd_joinable (top,atlas) xl y} closure_of
                 (W k INTER {y | mfd_joinable (top,atlas) xl y})) /\
              subtopology top {y | mfd_joinable (top,atlas) xl y} closure_of
                (W k INTER {y | mfd_joinable (top,atlas) xl y})
              SUBSET W (SUC k) INTER {y | mfd_joinable (top,atlas) xl y}) /\
         UNIONS {W k INTER {y | mfd_joinable (top,atlas) xl y} | k IN (:num)} =
         topspace (subtopology top {y | mfd_joinable (top,atlas) xl y})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Wk") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `xl:B`]
                P2CO_CLASS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `C = {y:B | mfd_joinable (top,atlas:((B->bool)#(B->real^N))->bool) xl y}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(xl:B) IN C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[IN_ELIM_THM; MFD_JOINABLE_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "Wk" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `C INTER ((W:num->B->bool) k INTER C) = W k INTER C` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `top closure_of ((W:num->B->bool) k INTER C) SUBSET C` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `top closure_of ((W:num->B->bool) k INTER C) SUBSET top closure_of (W k)`
    ASSUME_TAC THENL [MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `C INTER top closure_of ((W:num->B->bool) k INTER C) =
                  top closure_of (W k INTER C)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s c:B->bool. s SUBSET c ==> c INTER s = s`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `(W:num->B->bool) k` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `top closure_of ((W:num->B->bool) k)` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of ((W:num->B->bool) k)` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
    REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_ELIM_THM; IN_UNIV; IN_INTER] THEN MESON_TAC[]]);;

let P2CO_DIFFEO_SUBTOP = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) Cs W topX
    (atlasX:((A->bool)#(A->real^M))->bool) W' (f:B->A) f'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     open_in top Cs /\ mfd_diffeo top atlas W topX atlasX W' f f'
     ==> mfd_diffeo (subtopology top Cs) (restrict_atlas atlas Cs) (W INTER Cs)
                    topX atlasX (IMAGE f (W INTER Cs)) f f'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:B->bool) /\ open_in topX (W':A->bool) /\
                IMAGE (f:B->A) W SUBSET W'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo top (atlas:((B->bool)#(B->real^N))->bool) W topX
                   (atlasX:((A->bool)#(A->real^M))->bool) W' (f:B->A) f'` THEN
    REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> can (find_term ((=) `f:B->A`)) (concl th) &&
                       can (find_term ((=) `continuous_map:(B topology#A topology)->(B->A)->bool`))
                           (concl th))) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (W:B->bool)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `Cs:B->bool`;
                 `topX:A topology`; `atlasX:((A->bool)#(A->real^M))->bool`;
                 `topspace topX:A->bool`; `(W:B->bool) INTER Cs`;
                 `IMAGE (f:B->A) (W INTER Cs)`; `f:B->A`; `f':A->B`]
                APX_MFD_DIFFEO_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; INTER_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W':A->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (f:B->A) W` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_TOPSPACE; RESTRICT_ATLAS_TOPSPACE] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`W:B->bool`; `W':A->bool`] THEN
  ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER]);;

(* One member and one time: the diffeomorphism on W k INTER C and the lck   *)
(* distances at points of K INTER C, from those on W k.                     *)

let P2CO_MEMBER_RESTRICT = prove
 (`!(top:B topology) atlas (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
    Wk (f:B->A) f' (gX:A->real^3^3) (g:B->real^3^3) q xl m.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas topX atlasX /\
     riemannian_metric atlasX gX /\ riemannian_metric atlas g /\ &0 < q /\
     mfd_diffeo top atlas Wk topX atlasX (IMAGE f Wk) f f'
     ==> mfd_diffeo (subtopology top {y | mfd_joinable (top,atlas) xl y})
                    (restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
                    (Wk INTER {y | mfd_joinable (top,atlas) xl y}) topX atlasX
                    (IMAGE f (Wk INTER {y | mfd_joinable (top,atlas) xl y})) f f' /\
         !y. y IN Wk /\ y IN {y | mfd_joinable (top,atlas) xl y}
             ==> lck_dist2 m
                   (metric_local (restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
                      (chart_at (restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y}) y)
                      (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} g))
                   (\z. q %% rfs_pullback atlasX
                               (f o chart_inv
                                  (chart_at (restrict_atlas atlas
                                     {y | mfd_joinable (top,atlas) xl y}) y)) gX z)
                   (SND(chart_at (restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y}) y) y) =
                 lck_dist2 m (metric_local atlas (chart_at atlas y) g)
                   (\z. q %% rfs_pullback atlasX (f o chart_inv (chart_at atlas y)) gX z)
                   (SND(chart_at atlas y) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`]
                P2CO_CLASS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CO_DIFFEO_SUBTOP THEN EXISTS_TAC `IMAGE (f:B->A) Wk` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CO_LCK_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `topX:A topology`; `Wk:B->bool`;
                          `IMAGE (f:B->A) Wk`; `f':A->B`] THEN
    ASM_REWRITE_TAC[]]);;

let P2CO_P3_SLICE_RESTRICT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl.
     (!n s. ~(topspace(rfs_vtop (V n) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)) /\
     p3_slice_limit V x t Q (top,atlas) g xl
     ==> p3_slice_limit V x t Q
           (subtopology top {y | mfd_joinable (top,atlas) xl y},
            restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
           (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} g) xl /\
         connected_space (subtopology top {y | mfd_joinable (top,atlas) xl y})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") MP_TAC) THEN
  REWRITE_TAC[p3_slice_limit] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif")
       (LABEL_TAC "lck"))))))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`;
                 `W:num->B->bool`] P2CO_EXHAUST_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`]
                P2CO_CLASS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                              (rfs_vatlas (V k) (t k)) /\
        riemannian_metric (rfs_vatlas (V k) (t k)) (rfs_vmetric (V k) (t k))`
  (LABEL_TAC "sk") THENL
   [GEN_TAC THEN USE_THEN "sl" MATCH_MP_TAC THEN
    USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                   (rfs_vatlas (V k) (t k)) (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                            CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `xl:B`)) (concl th) &&
      can (find_term ((=) `x:num->A`)) (concl th))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `compact_in:(B)topology->(B->bool)->bool`))
                                 (concl th) &&
      not (can (find_term ((=) `subtopology:(B)topology->(B->bool)->(B)topology`)) (concl th)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2CO_CLASS_CONNECTED] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT];
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; MFD_JOINABLE_REFL];
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CO_CLASS_COMPLETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\k. (W:num->B->bool) k INTER
         {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `phi:num->B->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
    EXISTS_TAC `psi:A->B` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k)`;
                   `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k)`;
                   `g:B->real^3^3`; `(Q:num->real) k`; `xl:B`; `0`] P2CO_MEMBER_RESTRICT) THEN
    USE_THEN "sk" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  USE_THEN "lck" (MP_TAC o C MP (CONJ (ASSUME `compact_in top (K:B->bool)`)
                                      (ASSUME `&0 < eta`)) o
                  SPECL [`K:B->bool`; `m:num`; `eta:real`]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_THEN(LABEL_TAC "k0") THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk")) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k)`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k)`;
                 `g:B->real^3^3`; `(Q:num->real) k`; `xl:B`; `m:num`] P2CO_MEMBER_RESTRICT) THEN
  USE_THEN "sk" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `K:B->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "lk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2CO_SLICE_WITH_RESTRICT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl W phi.
     (!n s. ~(topspace(rfs_vtop (V n) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)) /\
     p2c_slice_limit_with V x t Q (top,atlas) g xl W phi
     ==> p2c_slice_limit_with V x t Q
           (subtopology top {y | mfd_joinable (top,atlas) xl y},
            restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
           (restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} g) xl
           (\k. W k INTER {y | mfd_joinable (top,atlas) xl y}) phi /\
         connected_space (subtopology top {y | mfd_joinable (top,atlas) xl y})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") MP_TAC) THEN
  REWRITE_TAC[p2c_slice_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "lck")))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`;
                 `W:num->B->bool`] P2CO_EXHAUST_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`]
                P2CO_CLASS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                              (rfs_vatlas (V k) (t k)) /\
        riemannian_metric (rfs_vatlas (V k) (t k)) (rfs_vmetric (V k) (t k))`
  (LABEL_TAC "sk") THENL
   [GEN_TAC THEN USE_THEN "sl" MATCH_MP_TAC THEN
    USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                   (rfs_vatlas (V k) (t k)) (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                            CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `xl:B`)) (concl th) &&
      can (find_term ((=) `x:num->A`)) (concl th))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `compact_in:(B)topology->(B->bool)->bool`))
                                 (concl th) &&
      not (can (find_term ((=) `subtopology:(B)topology->(B->bool)->(B)topology`)) (concl th)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2CO_CLASS_CONNECTED] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT];
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; MFD_JOINABLE_REFL];
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
    EXISTS_TAC `psi:A->B` THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k)`;
                   `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k)`;
                   `g:B->real^3^3`; `(Q:num->real) k`; `xl:B`; `0`] P2CO_MEMBER_RESTRICT) THEN
    USE_THEN "sk" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  USE_THEN "lck" (MP_TAC o C MP (CONJ (ASSUME `compact_in top (K:B->bool)`)
                                      (ASSUME `&0 < eta`)) o
                  SPECL [`K:B->bool`; `m:num`; `eta:real`]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_THEN(LABEL_TAC "k0") THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk")) THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k)`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k)`;
                 `g:B->real^3^3`; `(Q:num->real) k`; `xl:B`; `m:num`] P2CO_MEMBER_RESTRICT) THEN
  USE_THEN "sk" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `K:B->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "lk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Ricci flows and flows up to a time restrict to open sets                  *)
(* (charts of the restricted atlas, LRG_RICCI_FLOW_ON_CHART,                 *)
(* P2CA_RICCI_FLOW_ON_CHARTS); restriction theorem for p3_flow_limit.        *)
(* ------------------------------------------------------------------------- *)

let P2CO_RICCI_FLOW_ON_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Cs a b (g:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ open_in top Cs /\ ricci_flow_on (top,atlas) a b g
     ==> ricci_flow_on (subtopology top Cs,restrict_atlas atlas Cs) a b
                       (\s. restrict_metric atlas Cs (g s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CA_RICCI_FLOW_ON_CHARTS THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC `\s. metric_local atlas (U:A->bool,phi:A->real^N) ((g:real->A->real^N^N) s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^N^N`; `(U:A->bool,phi:A->real^N)`]
                    LRG_RICCI_FLOW_ON_CHART) THEN
      ASM_REWRITE_TAC[FST; SND];
      SUBGOAL_THEN `IMAGE (phi:A->real^N) (U INTER Cs) =
                    IMAGE (SND(U:A->bool,phi)) (FST(U,phi) INTER Cs)`
      SUBST1_TAC THENL [REWRITE_TAC[FST; SND]; ALL_TAC] THEN
      MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^N) IN IMAGE (phi:A->real^N) (U INTER Cs)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

let P2CO_FLOW_UPTO_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) Cs a b (g:real->A->real^3^3).
     smooth_manifold_atlas top atlas /\ open_in top Cs /\ rfs_flow_upto (top,atlas) a b g
     ==> rfs_flow_upto (subtopology top Cs,restrict_atlas atlas Cs) a b
                       (\s. restrict_metric atlas Cs (g s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CO_RICCI_FLOW_ON_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(U:A->bool,phi:A->real^3) IN atlas`) o
                SPEC `(U:A->bool,phi:A->real^3)`) THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS IMAGE (phi:A->real^3) U` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN IMAGE (phi:A->real^3) (U INTER Cs)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (phi:A->real^3) U` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `z:real^3`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`))
                                 (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

let P2CO_P3_FLOW_RESTRICT = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl Tl.
     (!n s. ~(topspace(rfs_vtop (V n) s) = {})
            ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)) /\
     p3_flow_limit V x t Q (top,atlas) g xl Tl
     ==> p3_flow_limit V x t Q
           (subtopology top {y | mfd_joinable (top,atlas) xl y},
            restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y})
           (\s. restrict_metric atlas {y | mfd_joinable (top,atlas) xl y} (g s)) xl Tl /\
         connected_space (subtopology top {y | mfd_joinable (top,atlas) xl y})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sl") MP_TAC) THEN
  REWRITE_TAC[p3_flow_limit] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `ts:num->real`
     (X_CHOOSE_THEN `phi:num->B->A`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif")
       (LABEL_TAC "lck")))))))))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`;
                 `W:num->B->bool`] P2CO_EXHAUST_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `xl:B`]
                P2CO_CLASS_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. --Tl < s /\ s <= &0
        ==> riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) ((g:real->B->real^3^3) s)`
  (LABEL_TAC "riem") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "upto" (MP_TAC o SPEC `(--Tl + s) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k s. --((ts:num->real) k) <= s /\ s <= &0
          ==> smooth_manifold_atlas (rfs_vtop ((V:num->(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                 (t k + s / Q k)) (rfs_vatlas (V k) (t k + s / Q k)) /\
              riemannian_metric (rfs_vatlas (V k) (t k + s / Q k))
                                (rfs_vmetric (V k) (t k + s / Q k))`
  (LABEL_TAC "sks") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "sl" MATCH_MP_TAC THEN
    USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o C MP (ASSUME `--((ts:num->real) k) <= s /\ s <= &0`) o
                    SPECL [`k:num`; `s:real`]) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(x:num->A) k` THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s / Q k))
                   (rfs_vatlas (V k) (t k + s / Q k)) (IMAGE ((phi:num->B->A) k) (W k))
                   (phi k) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                            CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `xl:B`)) (concl th) &&
      can (find_term ((=) `x:num->A`)) (concl th))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `compact_in:(B)topology->(B->bool)->bool`))
                                 (concl th) &&
      not (can (find_term ((=) `subtopology:(B)topology->(B->bool)->(B)topology`)) (concl th)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (subtopology (top:B topology)
                       {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}) /\
    smooth_manifold_atlas (subtopology top {y | mfd_joinable (top,atlas) xl y})
                          (restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y}) /\
    xl IN topspace (subtopology top {y | mfd_joinable (top,atlas) xl y}) /\
    connected_space (subtopology top {y | mfd_joinable (top,atlas) xl y}) /\
    (!a. --Tl < a /\ a < &0
         ==> rfs_flow_upto (subtopology top {y | mfd_joinable (top,atlas) xl y},
                            restrict_atlas atlas {y | mfd_joinable (top,atlas) xl y}) a (&0)
                           (\s. restrict_metric atlas {y | mfd_joinable (top,atlas) xl y}
                                                ((g:real->B->real^3^3) s)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
      ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT];
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; MFD_JOINABLE_REFL];
      ASM_SIMP_TAC[P2CO_CLASS_CONNECTED];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CO_FLOW_UPTO_RESTRICT THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "upto" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`\k. (W:num->B->bool) k INTER
         {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `ts:num->real`; `phi:num->B->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN DISCH_TAC THEN
    USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o C MP (ASSUME `--((ts:num->real) k) <= s /\ s <= &0`) o
                    SPECL [`k:num`; `s:real`]) THEN
    EXISTS_TAC `psi:A->B` THEN MATCH_MP_TAC P2CO_DIFFEO_SUBTOP THEN
    EXISTS_TAC `IMAGE ((phi:num->B->A) k) ((W:num->B->bool) k)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sks" (MP_TAC o C MP (ASSUME `--((ts:num->real) k) <= s /\ s <= &0`) o
                    SPECL [`k:num`; `s:real`]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`; `a:real`] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  USE_THEN "lck" (MP_TAC o C MP (CONJ (ASSUME `compact_in top (K:B->bool)`)
                                (CONJ (ASSUME `--Tl < a`) (CONJ (ASSUME `a <= &0`)
                                      (ASSUME `&0 < eta`)))) o
                  SPECL [`K:B->bool`; `m:num`; `eta:real`; `a:real`]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN DISCH_THEN(LABEL_TAC "k0") THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lk"))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--((ts:num->real) k) <= s /\ s <= &0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o C MP (ASSUME `--((ts:num->real) k) <= s /\ s <= &0`) o
                  SPECL [`k:num`; `s:real`]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k + s / Q k)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k + s / Q k)`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) k) (t k + s / Q k)`;
                 `(g:real->B->real^3^3) s`; `(Q:num->real) k`; `xl:B`; `m:num`]
                P2CO_MEMBER_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "sks" (MP_TAC o C MP (ASSUME `--((ts:num->real) k) <= s /\ s <= &0`) o
                    SPECL [`k:num`; `s:real`]) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `K:B->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "lk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

