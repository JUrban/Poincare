(* ========================================================================= *)
(* Unit pc_grg_distcont (Riemannian geometry layer): continuity of the       *)
(* Riemannian distance and the metric balls as a base of the manifold        *)
(* topology.  Convention: for points that cannot be joined, mfd_dist is the  *)
(* fixed value inf {} (the set of lengths is empty), and since joinable      *)
(* classes are open, the distance is continuous on all of topspace x         *)
(* topspace.                                                                 *)
(* ========================================================================= *)

needs "src/pc_grg_dist.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The convention for non-joinable points, Lipschitz bounds, continuity.     *)
(* ------------------------------------------------------------------------- *)

let MFD_DIST_NOT_JOINABLE = prove
 (`!top atlas (g:A->real^N^N) x y.
        ~mfd_joinable (top,atlas) x y ==> mfd_dist (top,atlas) g x y = inf {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_joinable] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_dist] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[]);;

let MFD_DIST_LIPSCHITZ_RIGHT = prove
 (`!top atlas (g:A->real^N^N) x y y'.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable (top,atlas) y y'
        ==> abs(mfd_dist (top,atlas) g x y - mfd_dist (top,atlas) g x y') <=
            mfd_dist (top,atlas) g y y'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (y':A) y` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  ASM_CASES_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y` THENL
   [SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y'` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`; `y':A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y':A`; `y:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `y':A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `~mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y'` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    ASM_SIMP_TAC[MFD_DIST_NOT_JOINABLE; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]]);;

let MFD_DIST_LIPSCHITZ = prove
 (`!top atlas (g:A->real^N^N) x y x' y'.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable (top,atlas) x x' /\ mfd_joinable (top,atlas) y y'
        ==> abs(mfd_dist (top,atlas) g x y - mfd_dist (top,atlas) g x' y') <=
            mfd_dist (top,atlas) g x x' + mfd_dist (top,atlas) g y y'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`; `y':A`] MFD_DIST_LIPSCHITZ_RIGHT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y':A`; `x:A`; `x':A`] MFD_DIST_LIPSCHITZ_RIGHT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y':A`] MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x':A`; `y':A`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MFD_DIST_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> continuous_map (prod_topology top top,euclideanreal)
                           (\(x,y). mfd_dist (top,atlas) g x y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; CONTINUOUS_MAP_TO_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; IN_MBALL;
              REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r / &2`] GRGD_DIST_SMALL_NBHD) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `r / &2`] GRGD_DIST_SMALL_NBHD) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `T2:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(T1:A->bool) CROSS (T2:A->bool)` THEN
  ASM_REWRITE_TAC[OPEN_IN_CROSS; IN_CROSS; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x':A`; `y':A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`; `x':A`; `y':A`] MFD_DIST_LIPSCHITZ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x x' < r / &2 /\
                mfd_dist (top,atlas) g y y' < r / &2`
  MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let MFD_DIST_CONTINUOUS_RIGHT = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> continuous_map (top,euclideanreal) (\y. mfd_dist (top,atlas) g x y)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:A) IN topspace top` THENL
   [SUBGOAL_THEN
     `(\y. mfd_dist (top,atlas) (g:A->real^N^N) x y) =
      (\(x,y). mfd_dist (top,atlas) g x y) o (\y:A. x,y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `prod_topology (top:A topology) top` THEN
    ASM_SIMP_TAC[MFD_DIST_CONTINUOUS; CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_CONST;
                 CONTINUOUS_MAP_ID];
    SUBGOAL_THEN
     `(\y. mfd_dist (top,atlas) (g:A->real^N^N) x y) = (\y. inf {})`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:A` THEN
      MATCH_MP_TAC MFD_DIST_NOT_JOINABLE THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV]]]);;

(* ------------------------------------------------------------------------- *)
(* The metric balls generate the topology of a Hausdorff manifold; on a      *)
(* connected one the distance metrizes the topology.                         *)
(* ------------------------------------------------------------------------- *)

let MFD_OPEN_IN_BALLS = prove
 (`!top atlas (g:A->real^N^N) W.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g
        ==> (open_in top W <=>
             W SUBSET topspace top /\
             !x. x IN W ==> ?r. &0 < r /\ mfd_ball (top,atlas) g x r SUBSET W)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MFD_BALL_NEIGHBOURHOOD_BASE THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(x:A) IN W`)) THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x r` THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL] THEN ASM SET_TAC[]]);;

let MFD_MTOPOLOGY_CONNECTED = prove
 (`!top atlas (g:A->real^N^N) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ x IN topspace top
        ==> mtopology (mfd_metric (top,atlas) g x) = top`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MFD_MTOPOLOGY] THEN
  SUBGOAL_THEN `{y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y} = topspace top`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MFD_JOINABLE_CONNECTED; MFD_JOINABLE_IN_TOPSPACE];
    REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]]);;

