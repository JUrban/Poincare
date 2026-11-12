(* ========================================================================= *)
(* Unit pc_p2c_c1116b (Part 2C): the geometry of MT Claim 11.15              *)
(* (pp. 275-277) for one complete slice of sec >= 0.                         *)
(* A connected manifold minus a point is connected (dimension >= 2), so two  *)
(* points other than y are joined by a connected set at positive distance   *)
(* from y; unit-speed minimizing geodesics; the Toponogov step at equal      *)
(* distances; two minimizing geodesics from y that cross the central sphere *)
(* of an eps-neck either make a small angle (the Toponogov bound) or leave  *)
(* through opposite halves (then the sphere separates their end points).    *)
(* ========================================================================= *)

needs "src/pc_p2c_c1116a.ml";;
needs "src/pc_cmp_tpg.ml";;
needs "src/pc_cmp_busemann.ml";;
needs "src/pc_canon_diam.ml";;
needs "src/pc_p2b_conelib.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_mfd_diff.ml";;
needs "src/pc_grg_distcont.ml";;
needs "src/pc_smt_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A connected manifold of dimension >= 2 minus a point is connected (a      *)
(* chart ball around the point minus the point is connected,                 *)
(* CONNECTED_PUNCTURED_BALL), hence path connected (manifolds are locally    *)
(* path connected), so two points other than y lie in a compact connected    *)
(* set (a path image) at positive distance from y (MT p. 277, last step).    *)
(* ------------------------------------------------------------------------- *)

(* The topological core: an open set B around y with B minus y connected.  *)

let P2FL_DELETE_CONNECTED = prove
 (`!top (B:A->bool) y.
     connected_space top /\ closed_in top {y} /\ open_in top B /\ y IN B /\
     connected_in top (B DELETE y)
     ==> connected_in top (topspace top DELETE y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONNECTED_IN] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`e1:A->bool`; `e2:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (topspace top DELETE (y:A))` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `(s:A->bool) DELETE a = s DIFF {a}`] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:A->bool) SUBSET topspace top /\ (e1:A->bool) SUBSET topspace top /\
                (e2:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `e1 INTER (B DELETE (y:A)) = {} \/ e2 INTER (B DELETE y) = {}` MP_TAC THENL
   [UNDISCH_TAC `connected_in top (B DELETE (y:A))` THEN REWRITE_TAC[CONNECTED_IN] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:A->bool`; `e2:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `connected_space (top:A topology)` THEN REWRITE_TAC[CONNECTED_SPACE_EQ] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`e2 UNION B:A->bool`;
                                  `e1 INTER (topspace top DELETE (y:A))`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`e1 UNION B:A->bool`;
                                  `e2 INTER (topspace top DELETE (y:A))`])] THEN
  ASM_SIMP_TAC[OPEN_IN_UNION; OPEN_IN_INTER] THEN ASM SET_TAC[]);;

(* A chart ball around y minus y is connected. *)

let P2FL_CHART_PUNCTURED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) y.
     2 <= dimindex(:N) /\ smooth_manifold_atlas top atlas /\ y IN topspace top
     ==> ?B. open_in top B /\ y IN B /\ connected_in top (B DELETE y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball((phi:A->real^N) y,r) SUBSET IMAGE phi U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (phi:A->real^N) U)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{x:A | x IN U /\ (phi:A->real^N) x IN ball(phi y,r)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:A | x IN U /\ (phi:A->real^N) x IN ball(phi y,r)} =
                  {x | x IN topspace (subtopology top U) /\ phi x IN ball(phi y,r)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball((phi:A->real^N) y,r)` THEN
    REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bp = {x:A | x IN U /\ (phi:A->real^N) x IN ball(phi y,r)} DELETE y` THEN
  SUBGOAL_THEN `IMAGE (phi:A->real^N) Bp = ball(phi y,r) DELETE phi y` ASSUME_TAC THENL
   [EXPAND_TAC "Bp" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(x:A = y)` THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(w:real^N) IN IMAGE (phi:A->real^N) U` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `chart_inv (U:A->bool,phi:A->real^N) w` THEN ASM_SIMP_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(w:real^N = phi(y:A))` THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Bp:A->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "Bp" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`;
                 `subtopology euclidean (IMAGE (phi:A->real^N) U)`; `Bp:A->bool`]
                HOMEOMORPHIC_MAP_CONNECTEDNESS) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_PUNCTURED_BALL] THEN ASM SET_TAC[]; SIMP_TAC[]]);;

(* A connected manifold minus a point is connected. *)

let P2FL_PUNCTURED_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) y.
     2 <= dimindex(:N) /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     connected_space top /\ y IN topspace top
     ==> connected_in top (topspace top DELETE y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
                P2FL_CHART_PUNCTURED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:A->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2FL_DELETE_CONNECTED THEN EXISTS_TAC `B:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t1_space (top:A topology)` MP_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE]; ALL_TAC] THEN
  REWRITE_TAC[T1_SPACE_CLOSED_IN_SING] THEN ASM_SIMP_TAC[]);;

(* Two points other than y lie in a connected set at positive distance     *)
(* from y.                                                                   *)

let P2FL_AVOID_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) y p q.
     2 <= dimindex(:N) /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ connected_space top /\
     y IN topspace top /\ p IN topspace top /\ q IN topspace top /\ ~(p = y) /\ ~(q = y)
     ==> ?rho P. &0 < rho /\ connected_in top P /\ p IN P /\ q IN P /\
                 !w. w IN P ==> rho <= mfd_dist (top,atlas) g y w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = topspace top DELETE (y:A)` THEN
  SUBGOAL_THEN `connected_in top (W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC P2FL_PUNCTURED_CONNECTED THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[SET_RULE `(s:A->bool) DELETE a = s DIFF {a}`] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    SUBGOAL_THEN `t1_space (top:A topology)` MP_TAC THENL
     [ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE]; ALL_TAC] THEN
    REWRITE_TAC[T1_SPACE_CLOSED_IN_SING] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_connected_space (subtopology top (W:A->bool))` MP_TAC THENL
   [SUBGOAL_THEN `locally_path_connected_space (subtopology top (W:A->bool))` ASSUME_TAC THENL
     [MATCH_MP_TAC LOCALLY_PATH_CONNECTED_SPACE_OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GEO_MANIFOLD_LOCALLY_PATH_CONNECTED THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PATH_CONNECTED_EQ_CONNECTED_SPACE] THEN
    UNDISCH_TAC `connected_in top (W:A->bool)` THEN SIMP_TAC[connected_in];
    ALL_TAC] THEN
  REWRITE_TAC[path_connected_space; TOPSPACE_SUBTOPOLOGY] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:A`; `q:A`]) THEN
  ANTS_TAC THENL [EXPAND_TAC "W" THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `P = IMAGE (h:real->A) (real_interval[&0,&1])` THEN
  SUBGOAL_THEN `compact_in top (P:A->bool) /\ connected_in top P /\ P SUBSET W`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IN_PATH_IMAGE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; CONNECTED_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN P /\ (q:A) IN P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `&0`; EXISTS_TAC `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_compact (IMAGE (\w. mfd_dist (top,atlas) (g:A->real^N^N) y w) P)`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\w. mfd_dist (top,atlas) (g:A->real^N^N) y w) P`
               REAL_COMPACT_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`mfd_dist (top,atlas) (g:A->real^N^N) y w0`; `P:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(w0:A) IN topspace top /\ ~(w0 = y)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (y:A) w0` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `w0:A`] MFD_DIST_EQ_0) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `w0:A`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unit-speed geodesics of a complete slice (all of R, C1 on every interval, *)
(* length b - a), minimizing segments (distances along a minimizing segment  *)
(* are differences of parameters), existence of a minimizing unit-speed      *)
(* segment to every point, and the Toponogov step at equal distances s from  *)
(* the vertex (MT p. 276): d(a,b) <= th s ==> d(x,z)^2 <= (L1 - L2)^2 + th^2 *)
(* L1 L2.                                                                    *)
(* ------------------------------------------------------------------------- *)

let P2FL_UNIT_GEO = prove
 (`!top atlas (g:A->real^N^N) (p:A) u.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p IN topspace top /\ mfd_tnorm g p u = &1
     ==> mfd_geo (top,atlas) g p u (&0) = p /\
         (!s. mfd_geo (top,atlas) g p u s IN topspace top) /\
         (!s. mfd_exp (top,atlas) g p (s % u) = mfd_geo (top,atlas) g p u s) /\
         (!s t. mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u s)
                                         (mfd_geo (top,atlas) g p u t) /\
                mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s)
                         (mfd_geo (top,atlas) g p u t) <= abs(t - s)) /\
         (!a b. a <= b
                ==> mfd_c1_curve (top,atlas) (mfd_geo (top,atlas) g p u) a b /\
                    mfd_length atlas g (mfd_geo (top,atlas) g p u) a b = b - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL CMPB_GEO_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`p:A`; `u:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`;
                 `a:real`; `b:real`] MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`;
                 `a:real`; `&0`] MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RID]);;

(* Along a minimizing unit-speed segment of length L, d(s,t) = t - s. *)

let P2FL_MIN_GEO = prove
 (`!top atlas (g:A->real^N^N) (p:A) u L.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p IN topspace top /\ mfd_tnorm g p u = &1 /\ &0 <= L /\
     mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u L) = L
     ==> !s t. &0 <= s /\ s <= t /\ t <= L
               ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s)
                            (mfd_geo (top,atlas) g p u t) = t - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL P2FL_UNIT_GEO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip") ASSUME_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "lip" (fun th ->
    MP_TAC(SPECL [`&0`; `s:real`] th) THEN MP_TAC(SPECL [`s:real`; `t:real`] th) THEN
    MP_TAC(SPECL [`t:real`; `L:real`] th) THEN MP_TAC(SPECL [`s:real`; `L:real`] th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `mfd_geo (top,atlas) (g:A->real^N^N) p u s`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u L`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u s`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u t`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u L`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* A minimizing unit-speed segment to every point at positive distance. *)

let P2FL_MIN_GEO_EXISTS = prove
 (`!top atlas (g:A->real^N^N) (y:A) q.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     y IN topspace top /\ mfd_joinable (top,atlas) y q /\
     &0 < mfd_dist (top,atlas) g y q
     ==> ?u. mfd_tnorm g y u = &1 /\
             mfd_geo (top,atlas) g y u (mfd_dist (top,atlas) g y q) = q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `q:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) y q` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) y (inv L % v) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  EXISTS_TAC `inv L % (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `inv L % (v:real^N)`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `L:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  MESON_TAC[]);;

(* The Toponogov step: comparison angles at equal distances s. *)

let P2FL_TPG_STEP = prove
 (`!top atlas (g:B->real^3^3) p v1 v2 L1 L2 s th.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     p IN topspace top /\ mfd_tnorm g p v1 = &1 /\ mfd_tnorm g p v2 = &1 /\
     mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p v1 L1) = L1 /\
     mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p v2 L2) = L2 /\
     &0 < s /\ s <= L1 /\ s <= L2 /\ &0 <= th /\
     mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p v1 s) (mfd_geo (top,atlas) g p v2 s)
     <= th * s
     ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p v1 L1)
                  (mfd_geo (top,atlas) g p v2 L2) pow 2
         <= (L1 - L2) pow 2 + th pow 2 * L1 * L2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `v1:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "z1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l1")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `v2:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "z2") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2")))) THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) (mfd_geo (top,atlas) (g:B->real^3^3) p v1 s)
                             (mfd_geo (top,atlas) g p v2 s)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:B` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "l1" (MP_TAC o CONJUNCT1 o SPECL [`s:real`; `&0`]) THEN
      USE_THEN "z1" (fun th -> REWRITE_TAC[th]);
      USE_THEN "l2" (MP_TAC o CONJUNCT1 o SPECL [`&0`; `s:real`]) THEN
      USE_THEN "z2" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:B)` CMP_R1_TOPONOGOV) THEN REWRITE_TAC[CMP_R1_TOPONOGOV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `g:B->real^3^3`; `p:B`; `v1:real^3`; `v2:real^3`;
                             `L1:real`; `L2:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `L1:real`; `s:real`; `L2:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `A = mfd_dist (top,atlas) (g:B->real^3^3) (mfd_geo (top,atlas) g p v1 s)
                           (mfd_geo (top,atlas) g p v2 s)` THEN
  ABBREV_TAC `X = mfd_dist (top,atlas) (g:B->real^3^3) (mfd_geo (top,atlas) g p v1 L1)
                           (mfd_geo (top,atlas) g p v2 L2)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `A pow 2 <= (th * s) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * s * s /\ &0 < &2 * L1 * L2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - th pow 2 / &2 <= (s pow 2 + s pow 2 - A pow 2) / (&2 * s * s)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `A pow 2 <= (th * s) pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - th pow 2 / &2) * (&2 * L1 * L2) <= L1 pow 2 + L2 pow 2 - X pow 2`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Points of a minimizing geodesic in an eps-neck (eps <= 1/100) at distance *)
(* between 40 and 45 neck scales after a point of the central sphere: they   *)
(* lie in the neck with 35 <= abs(sval) <= 46 (APX_NECK_EXIT,                *)
(* APX_NECK_DIST_UPPER/LOWER); two such points on the same side are within   *)
(* 20 scales; points on opposite sides are separated by the central sphere   *)
(* (P2BK_NECK_SIDES).                                                        *)
(* ------------------------------------------------------------------------- *)

let P2FL_NECK_CONSTS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &100
         ==> &99 / &100 <= sqrt(&1 - eps) /\ &1 <= sqrt(&1 + eps) /\
             sqrt(&1 + eps) <= &101 / &100 /\
             &0 <= sqrt(&2) * pi /\ sqrt(&2) * pi <= &9 / &2 /\ &100 <= inv eps`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
    SUBGOAL_THEN `sqrt(&2) <= &1415 / &1000 /\ pi <= &31416 / &10000` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1415 / &1000 * &31416 / &10000` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    SUBGOAL_THEN `inv eps = &1 / eps` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* Two points of the central sphere are within sqrt(1 + eps) sqrt(2) pi      *)
(* neck scales.                                                              *)

let P2FL_NECK_SPHERE_DIST = prove
 (`!top atlas (g:B->real^3^3) eps x0 (e:real^3->B) u w.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x0 e /\ eps < &1 /\
     u IN sphere(vec 0,&1) /\ w IN sphere(vec 0,&1)
     ==> mfd_joinable (top,atlas) (e u) (e w) /\
         mfd_dist (top,atlas) g (e u) (e w) <=
         sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x0)) * (sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN rfs_neck_dom eps /\ (w:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_UNIT_SPHERE_NECK_DOM; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval (u:real^3) = &0 /\ apx_sval (w:real^3) = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_SVAL_UNIT THEN
    UNDISCH_TAC `(u:real^3) IN sphere(vec 0,&1)` THEN
    UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `u:real^3`; `w:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID]);;

(* A point of a minimizing geodesic 40 to 45 scales after the sphere. *)

let P2FL_NECK_GEO_POINT = prove
 (`!top atlas (g:B->real^3^3) eps x0 (e:real^3->B) y v L sg s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps x0 e /\
     y IN topspace top /\ mfd_tnorm g y v = &1 /\ &0 <= L /\
     mfd_dist (top,atlas) g y (mfd_geo (top,atlas) g y v L) = L /\
     &0 <= sg /\ mfd_geo (top,atlas) g y v sg IN IMAGE e (sphere(vec 0,&1)) /\
     sg + &40 * inv(sqrt(mfd_scalar atlas g x0)) <= s /\
     s <= sg + &45 * inv(sqrt(mfd_scalar atlas g x0)) /\ s <= L
     ==> ?w. w IN rfs_neck_dom eps /\ mfd_geo (top,atlas) g y v s = e w /\
             &35 <= abs(apx_sval w) /\ abs(apx_sval w) <= &46`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `l = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v:real^3`] P2FL_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))))) THEN
  USE_THEN "c1" (MP_TAC o SPECL [`sg:real`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v:real^3`; `L:real`] P2FL_MIN_GEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`sg:real`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `mfd_geo (top,atlas) (g:B->real^3^3) y v sg IN IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u0:real^3) IN rfs_neck_dom eps /\ apx_sval u0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[APX_UNIT_SPHERE_NECK_DOM; SUBSET];
      MATCH_MP_TAC APX_SVAL_UNIT THEN UNDISCH_TAC `(u0:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) y v s IN IMAGE (e:real^3->B) (rfs_neck_dom eps)`
  MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x0:B`; `e:real^3->B`; `u0:real^3`;
                   `mfd_geo (top,atlas) (g:B->real^3^3) y v`; `sg:real`; `s:real`]
                  APX_NECK_EXIT) THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO; NOT_IMP; REAL_NOT_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&99 * l <= sqrt(&1 - eps) * l * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&99 / &100) * (l * &100)` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(apx_sval (w:real^3)) < inv eps` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  (* upper bound for the distance gives the lower bound for sval *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `u0:real^3`; `w:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `u0:real^3`; `w:real^3`]
                APX_NECK_DIST_LOWER) THEN
  ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `min (abs(apx_sval (w:real^3))) (&2 * inv eps - abs(apx_sval w)) =
                abs(apx_sval w)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = abs(apx_sval (w:real^3))` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL [EXPAND_TAC "X" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* 40 l <= sqrt(1+eps) l (X + c) *)
    SUBGOAL_THEN `&40 * l <= (sqrt(&1 + eps) * (X + sqrt(&2) * pi)) * l` MP_TAC THENL
     [UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) (e(u0:real^3)) (e w) <=
                   sqrt(&1 + eps) * l * (X + sqrt(&2) * pi)` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3)
                     (mfd_geo (top,atlas) g y v sg) (mfd_geo (top,atlas) g y v s) = s - sg` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ARITH `(a * b) * l = a * l * b`] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sqrt(&1 + eps) * (X + sqrt(&2) * pi) <= &101 / &100 * (X + sqrt(&2) * pi)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* sqrt(1-eps) l X <= 45 l *)
    SUBGOAL_THEN `(sqrt(&1 - eps) * X) * l <= &45 * l` MP_TAC THENL
     [UNDISCH_TAC `sqrt(&1 - eps) * l * X <=
                   mfd_dist (top,atlas) (g:B->real^3^3) (e(u0:real^3)) (e w)` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3)
                     (mfd_geo (top,atlas) g y v sg) (mfd_geo (top,atlas) g y v s) = s - sg` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ARITH `(a * b) * l = a * l * b`] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&99 / &100 * X <= sqrt(&1 - eps) * X` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* Two such points on the same side are within 20 scales. *)

let P2FL_NECK_SAME_SIDE = prove
 (`!top atlas (g:B->real^3^3) eps x0 (e:real^3->B) w1 w2.
     riemannian_metric atlas g /\ &0 < eps /\ eps <= &1 / &100 /\
     rfs_neck (top,atlas) g eps x0 e /\
     w1 IN rfs_neck_dom eps /\ w2 IN rfs_neck_dom eps /\
     &35 <= abs(apx_sval w1) /\ abs(apx_sval w1) <= &46 /\
     &35 <= abs(apx_sval w2) /\ abs(apx_sval w2) <= &46 /\
     (apx_sval w1 < &0 <=> apx_sval w2 < &0)
     ==> mfd_joinable (top,atlas) (e w1) (e w2) /\
         mfd_dist (top,atlas) g (e w1) (e w2) <=
         &20 * inv(sqrt(mfd_scalar atlas g x0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `l = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `w1:real^3`; `w2:real^3`]
                APX_NECK_DIST_UPPER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(apx_sval (w1:real^3) - apx_sval (w2:real^3)) <= &11` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * l * (abs(apx_sval (w1:real^3) - apx_sval (w2:real^3)) +
                                    sqrt(&2) * pi)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `a * l * b = (a * b) * l`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * (&11 + &9 / &2)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* The two half annuli of the neck domain. *)

let P2FL_NECK_HALF = prove
 (`!eps w:real^3.
     w IN rfs_neck_dom eps
     ==> (apx_sval w < &0 ==> w IN annulus (exp(--inv eps / sqrt(&2))) (&1)) /\
         (&0 < apx_sval w ==> w IN annulus (&1) (exp(inv eps / sqrt(&2))))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; apx_sval;
                  REAL_ARITH `--x / y = --(x / y)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^3) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `exp(--(inv eps / sqrt(&2)))` THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `log(norm(w:real^3)) < &0` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `sqrt(&2) * log(norm(w:real^3)) < &0` THEN REWRITE_TAC[REAL_NOT_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`norm(w:real^3)`; `&1`] LOG_MONO_LT) THEN
    ASM_REWRITE_TAC[REAL_LT_01; LOG_1] THEN MESON_TAC[];
    SUBGOAL_THEN `&0 < log(norm(w:real^3))` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < sqrt(&2) * log(norm(w:real^3))` THEN REWRITE_TAC[REAL_NOT_LT] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= s * --x ==> s * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`&1`; `norm(w:real^3)`] LOG_MONO_LT) THEN
    ASM_REWRITE_TAC[REAL_LT_01; LOG_1] THEN MESON_TAC[]]);;

(* Chains of connected components. *)

let P2FL_CC_CHAIN = prove
 (`!top (p:A) q x y a b.
     connected_component_of top x a /\ connected_component_of top y b /\
     connected_component_of top a b /\
     ((x IN connected_component_of top p /\ y IN connected_component_of top q) \/
      (y IN connected_component_of top p /\ x IN connected_component_of top q))
     ==> connected_component_of top p q`,
  REWRITE_TAC[IN] THEN
  MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM]);;

(* Points on opposite sides, joined by connected sets avoiding the central *)
(* sphere to a and b: the sphere separates a and b.                          *)

let P2FL_NECK_OPP_SEP = prove
 (`!top atlas (g:B->real^3^3) eps x0 (e:real^3->B) p0 q0 w1 w2 K1 K2 a b.
     hausdorff_space top /\ connected_space top /\ rfs_neck (top,atlas) g eps x0 e /\
     apx_separates top (IMAGE e (sphere(vec 0,&1))) p0 q0 /\
     w1 IN rfs_neck_dom eps /\ w2 IN rfs_neck_dom eps /\
     apx_sval w1 < &0 /\ &0 < apx_sval w2 /\
     connected_in top K1 /\ K1 INTER IMAGE e (sphere(vec 0,&1)) = {} /\
     e w1 IN K1 /\ a IN K1 /\
     connected_in top K2 /\ K2 INTER IMAGE e (sphere(vec 0,&1)) = {} /\
     e w2 IN K2 /\ b IN K2
     ==> apx_separates top (IMAGE e (sphere(vec 0,&1))) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `w1:real^3`] P2FL_NECK_HALF) THEN
  MP_TAC(ISPECL [`eps:real`; `w2:real^3`] P2FL_NECK_HALF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `p0:B`; `q0:B`] P2BK_NECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ABBREV_TAC `S = IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `T0 = subtopology top (topspace top DIFF S:B->bool)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `((e:real^3->B) w1 IN connected_component_of T0 p0 /\
                 e w2 IN connected_component_of T0 q0) \/
                ((e:real^3->B) w2 IN connected_component_of T0 p0 /\
                 e w1 IN connected_component_of T0 q0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->B) w1 IN IMAGE e (annulus (exp(--inv eps / sqrt(&2))) (&1)) /\
                  (e:real^3->B) w2 IN IMAGE e (annulus (&1) (exp(inv eps / sqrt(&2))))`
    MP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K1:B->bool) SUBSET topspace top DIFF S /\ (K2:B->bool) SUBSET topspace top DIFF S`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `K1:B->bool`] CONNECTED_IN_SUBSET_TOPSPACE) THEN
    MP_TAC(ISPECL [`top:B topology`; `K2:B->bool`] CONNECTED_IN_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component_of T0 ((e:real^3->B) w1) (a:B) /\
                connected_component_of T0 ((e:real^3->B) w2) (b:B)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[connected_component_of] THEN CONJ_TAC THENL
     [EXISTS_TAC `K1:B->bool`; EXISTS_TAC `K2:B->bool`] THEN
    EXPAND_TAC "T0" THEN ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_separates top (S:B->bool) p0 q0` THEN
  REWRITE_TAC[apx_separates] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~connected_component_of T0 (p0:B) q0` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC P2FL_CC_CHAIN THEN
  MAP_EVERY EXISTS_TAC [`(e:real^3->B) w1`; `(e:real^3->B) w2`; `a:B`; `b:B`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Two minimizing unit-speed geodesics from y that meet the central sphere S *)
(* of an eps-neck (eps <= 1/100) and run at least 45 neck scales beyond:     *)
(* either their end points satisfy the Toponogov bound with angle 1/2, d^2   *)
(* <= (L1 - L2)^2 + L1 L2 / 4, or S separates them (MT p. 276, the same-end  *)
(* and opposite-end cases of Claim 11.15).                                   *)
(* ------------------------------------------------------------------------- *)

let P2FL_APX_SEPARATES_SYM = prove
 (`!top (S:A->bool) a b. apx_separates top S a b <=> apx_separates top S b a`,
  REWRITE_TAC[apx_separates] THEN MESON_TAC[CONNECTED_COMPONENT_OF_SYM]);;

(* The diameter bound of the central sphere: at most 5 neck scales. *)

let P2FL_NECK_DELTA0 = prove
 (`!eps l. &0 < eps /\ eps <= &1 / &100 /\ &0 <= l
           ==> sqrt(&1 + eps) * l * (sqrt(&2) * pi) <= &5 * l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * (sqrt(&2) * pi) <= &5` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * &9 / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * l * (sqrt(&2) * pi) =
                (sqrt(&1 + eps) * (sqrt(&2) * pi)) * l` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* Points of a minimizing unit-speed segment are at distance t from p. *)

let P2FL_MIN_GEO_PT = prove
 (`!top atlas (g:A->real^N^N) (p:A) u L t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p IN topspace top /\ mfd_tnorm g p u = &1 /\
     mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u L) = L /\
     &0 <= t /\ t <= L
     ==> mfd_joinable (top,atlas) p (mfd_geo (top,atlas) g p u t) /\
         mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u t) = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`] P2FL_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "z0") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip") ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [USE_THEN "lip" (MP_TAC o CONJUNCT1 o SPECL [`&0`; `t:real`]) THEN
    USE_THEN "z0" (fun th -> REWRITE_TAC[th]);
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `u:real^N`; `L:real`] P2FL_MIN_GEO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `t:real`]) THEN
    USE_THEN "z0" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* The tail of a minimizing geodesic after 40 scales beyond the sphere is a *)
(* connected set that misses the sphere.                                     *)

let P2FL_GEO_TAIL = prove
 (`!top atlas (g:B->real^3^3) eps x0 (e:real^3->B) y v L sg s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps x0 e /\
     y IN topspace top /\ mfd_tnorm g y v = &1 /\ &0 <= L /\
     mfd_dist (top,atlas) g y (mfd_geo (top,atlas) g y v L) = L /\
     &0 <= sg /\ mfd_geo (top,atlas) g y v sg IN IMAGE e (sphere(vec 0,&1)) /\
     sg + &40 * inv(sqrt(mfd_scalar atlas g x0)) <= s /\ s <= L
     ==> connected_in top (IMAGE (mfd_geo (top,atlas) g y v) (real_interval[s,L])) /\
         IMAGE (mfd_geo (top,atlas) g y v) (real_interval[s,L]) INTER
         IMAGE e (sphere(vec 0,&1)) = {} /\
         mfd_geo (top,atlas) g y v s IN IMAGE (mfd_geo (top,atlas) g y v) (real_interval[s,L]) /\
         mfd_geo (top,atlas) g y v L IN IMAGE (mfd_geo (top,atlas) g y v) (real_interval[s,L])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `l = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v:real^3`] P2FL_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lip") (LABEL_TAC "c1"))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v:real^3`; `L:real`] P2FL_MIN_GEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "min") THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[s,L])` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
    USE_THEN "c1" (MP_TAC o C MP (ASSUME `s <= L:real`) o SPECL [`s:real`; `L:real`]) THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `!u. u IN sphere(vec 0,&1)
                    ==> mfd_dist (top,atlas) (g:B->real^3^3) y ((e:real^3->B) u) <= sg + &5 * l`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `mfd_geo (top,atlas) (g:B->real^3^3) y v sg IN
                 IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u0:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x0:B`; `e:real^3->B`; `u0:real^3`; `u:real^3`]
                  P2FL_NECK_SPHERE_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `v:real^3`; `L:real`; `sg:real`] P2FL_MIN_GEO_PT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `(e:real^3->B) u0`; `(e:real^3->B) u`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`eps:real`; `l:real`] P2FL_NECK_DELTA0) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `q:B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "near" (MP_TAC o C MP (ASSUME `(u:real^3) IN sphere(vec 0,&1)`) o
                   SPEC `u:real^3`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v:real^3`; `L:real`; `t:real`] P2FL_MIN_GEO_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) y v t = (e:real^3->B) u` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

(* The dichotomy. *)

let P2FL_NECK_TWO_GEO = prove
 (`!top atlas (g:B->real^3^3) eps x0 (e:real^3->B) p0 q0 y v1 v2 L1 L2 sg1 sg2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ connected_space top /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     &0 < eps /\ eps <= &1 / &100 /\ rfs_neck (top,atlas) g eps x0 e /\
     apx_separates top (IMAGE e (sphere(vec 0,&1))) p0 q0 /\
     y IN topspace top /\ mfd_tnorm g y v1 = &1 /\ mfd_tnorm g y v2 = &1 /\
     mfd_dist (top,atlas) g y (mfd_geo (top,atlas) g y v1 L1) = L1 /\
     mfd_dist (top,atlas) g y (mfd_geo (top,atlas) g y v2 L2) = L2 /\
     &0 <= sg1 /\ &0 <= sg2 /\
     mfd_geo (top,atlas) g y v1 sg1 IN IMAGE e (sphere(vec 0,&1)) /\
     mfd_geo (top,atlas) g y v2 sg2 IN IMAGE e (sphere(vec 0,&1)) /\
     sg1 + &45 * inv(sqrt(mfd_scalar atlas g x0)) <= L1 /\
     sg2 + &45 * inv(sqrt(mfd_scalar atlas g x0)) <= L2
     ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g y v1 L1)
                  (mfd_geo (top,atlas) g y v2 L2) pow 2
         <= (L1 - L2) pow 2 + L1 * L2 / &4 \/
         apx_separates top (IMAGE e (sphere(vec 0,&1)))
                       (mfd_geo (top,atlas) g y v1 L1) (mfd_geo (top,atlas) g y v2 L2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) x0` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `l = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sg1 - sg2) <= &5 * l` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_geo (top,atlas) (g:B->real^3^3) y v1 sg1 IN
                 IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `mfd_geo (top,atlas) (g:B->real^3^3) y v2 sg2 IN
                 IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x0:B`; `e:real^3->B`; `u1:real^3`; `u2:real^3`]
                  P2FL_NECK_SPHERE_DIST) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `v1:real^3`; `L1:real`; `sg1:real`] P2FL_MIN_GEO_PT) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `v2:real^3`; `L2:real`; `sg2:real`] P2FL_MIN_GEO_PT) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool)
                    ((e:real^3->B) u2) (e u1) /\
                  mfd_dist (top,atlas) (g:B->real^3^3) (e u2) (e u1) =
                  mfd_dist (top,atlas) g (e u1) (e u2)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `(e:real^3->B) u1`; `(e:real^3->B) u2`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `(e:real^3->B) u2`; `(e:real^3->B) u1`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`eps:real`; `l:real`] P2FL_NECK_DELTA0) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `st = max sg1 sg2 + &40 * l` THEN
  SUBGOAL_THEN `sg1 + &40 * l <= st /\ st <= sg1 + &45 * l /\ st <= L1 /\
                sg2 + &40 * l <= st /\ st <= sg2 + &45 * l /\ st <= L2 /\ &40 * l <= st`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "st" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `y:B`; `v1:real^3`; `L1:real`;
                 `sg1:real`; `st:real`] P2FL_NECK_GEO_POINT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `y:B`; `v2:real^3`; `L2:real`;
                 `sg2:real`; `st:real`] P2FL_NECK_GEO_POINT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `apx_sval (w1:real^3) < &0 <=> apx_sval (w2:real^3) < &0` THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x0:B`; `e:real^3->B`; `w1:real^3`; `w2:real^3`]
                  P2FL_NECK_SAME_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `v1:real^3`; `v2:real^3`; `L1:real`; `L2:real`; `st:real`;
                   `&1 / &2`] P2FL_TPG_STEP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    DISJ2_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `y:B`; `v1:real^3`; `L1:real`;
                 `sg1:real`; `st:real`] P2FL_GEO_TAIL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x0:B`; `e:real^3->B`; `y:B`; `v2:real^3`; `L2:real`;
                 `sg2:real`; `st:real`] P2FL_GEO_TAIL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(apx_sval (w1:real^3) < &0 /\ &0 < apx_sval (w2:real^3)) \/
                (apx_sval (w2:real^3) < &0 /\ &0 < apx_sval (w1:real^3))`
  STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2FL_NECK_OPP_SEP THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
      `x0:B`; `p0:B`; `q0:B`; `w1:real^3`; `w2:real^3`;
      `IMAGE (mfd_geo (top,atlas) (g:B->real^3^3) y v1) (real_interval[st,L1])`;
      `IMAGE (mfd_geo (top,atlas) (g:B->real^3^3) y v2) (real_interval[st,L2])`] THEN
    ASM_MESON_TAC[];
    ONCE_REWRITE_TAC[P2FL_APX_SEPARATES_SYM] THEN
    MATCH_MP_TAC P2FL_NECK_OPP_SEP THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`; `eps:real`;
      `x0:B`; `p0:B`; `q0:B`; `w2:real^3`; `w1:real^3`;
      `IMAGE (mfd_geo (top,atlas) (g:B->real^3^3) y v2) (real_interval[st,L2])`;
      `IMAGE (mfd_geo (top,atlas) (g:B->real^3^3) y v1) (real_interval[st,L1])`] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for MT Claim 11.15 at one time: in a connected noncompact slice a  *)
(* canonical neighbourhood is a neck or a cap; neck spheres separate         *)
(* (apx_sphere_sep, via the middle annulus of the neck domain); cap facts    *)
(* (positive R, the scalar ratio bound C); scales; a minimizing geodesic     *)
(* from a point of A to a point outside A meets the frontier of A.           *)
(* ------------------------------------------------------------------------- *)

let P2FL_COMPONENT_COMPACT = prove
 (`!top (U:A->bool).
     connected_space top /\ U IN connected_components_of top /\ compact_in top U
     ==> compact_space top`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(U:A->bool) IN connected_components_of top` THEN
  ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; IN_SING] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[compact_space]);;

let P2FL_NECK_OR_CAP = prove
 (`!top atlas (g:A->real^3^3) C eps y U.
     connected_space top /\ ~compact_space top /\
     rfs_canonical_nbhd (top,atlas) g C eps y U
     ==> (?e. rfs_neck (top,atlas) g eps y e /\ U = IMAGE e (rfs_neck_dom eps)) \/
         (?Y. rfs_cap (top,atlas) g C eps U Y /\ y IN Y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_canonical_nbhd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_c_component]);
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_round_component])] THEN
  STRIP_TAC THEN ASM_MESON_TAC[P2FL_COMPONENT_COMPACT]);;

(* The middle annulus lies in the neck domain (the same fact as             *)
(* APX_A25_MID_NECK_DOM of pc_apx_a25, whose load closure is much larger).   *)

let P2FL_MID_NECK_DOM = prove
 (`!eps. &0 < eps /\ eps <= &1 / &100 ==> annulus (&1 / &2) (&2) SUBSET rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN
    SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * eps` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `X = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&2 <= exp X /\ exp(--X) <= &1 / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 <= exp X` ASSUME_TAC THENL
     [MP_TAC(SPEC `X:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBGOAL_THEN `&1 / &2 = inv(&2)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* Neck spheres separate. *)

let P2FL_NECK_SEP = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A).
     apx_sphere_sep top atlas /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100
     ==> apx_separates top (IMAGE e (sphere(vec 0,&1)))
                       (e(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [apx_sphere_sep]) THEN
  REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
  EXISTS_TAC `rfs_neck_dom eps` THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MATCH_MP_TAC P2FL_MID_NECK_DOM THEN ASM_MESON_TAC[rfs_neck]);;

(* Cap facts: R > 0 on U and R(w2) < C R(w1) for w1, w2 in U. *)

let P2FL_CAP_FACTS = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y
     ==> (!w. w IN U ==> &0 < mfd_scalar atlas g w) /\
         (!w1 w2. w1 IN U /\ w2 IN U
                  ==> mfd_scalar atlas g w2 < C * mfd_scalar atlas g w1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))))))) THEN
  ASM_REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`w1:A`; `w2:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) w2 /
                               mfd_scalar atlas g w1`) THEN
  ANTS_TAC THENL
   [MAP_EVERY EXISTS_TAC [`w2:A`; `w1:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `d * mfd_scalar atlas (g:A->real^3^3) w1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]);;

(* Scales: R(a) <= C R(b) gives R(b)^(-1/2) <= sqrt C R(a)^(-1/2). *)

let P2FL_SCALE_RATIO = prove
 (`!a b C. &0 < a /\ &0 < b /\ &0 < C /\ a <= C * b
           ==> inv(sqrt b) <= sqrt C * inv(sqrt a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt a /\ &0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt a <= sqrt C * sqrt b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `inv(sqrt b) * sqrt a = sqrt a / sqrt b` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

(* A minimizing geodesic from a point of A to a point outside A meets the   *)
(* frontier of A.                                                            *)

let P2FL_GEO_CROSS = prove
 (`!top atlas (g:B->real^3^3) y v L (A:B->bool) S.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     y IN topspace top /\ mfd_tnorm g y v = &1 /\ &0 <= L /\
     y IN A /\ ~(mfd_geo (top,atlas) g y v L IN A) /\ top frontier_of A SUBSET S
     ==> ?sg. &0 <= sg /\ sg <= L /\ mfd_geo (top,atlas) g y v sg IN S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `v:real^3`] P2FL_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))))) THEN
  MP_TAC(ISPECL [`top:B topology`;
                 `IMAGE (mfd_geo (top,atlas) (g:B->real^3^3) y v) (real_interval[&0,L])`;
                 `A:B->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,L])` THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                  CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
      USE_THEN "c1" (MP_TAC o C MP (ASSUME `&0 <= L`) o SPECL [`&0`; `L:real`]) THEN
      SIMP_TAC[mfd_c1_curve];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:B` THEN
      ASM_REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
      EXISTS_TAC `mfd_geo (top,atlas) (g:B->real^3^3) y v L` THEN
      ASM_REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN EXISTS_TAC `L:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:B` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `sg:real` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 11.15 at one time (p. 275-277).  In a complete, connected,       *)
(* noncompact slice of sec >= 0 whose neck spheres separate, let y have a    *)
(* (C,eps)-canonical neighbourhood U (eps <= 1/100) and let xl, z be far     *)
(* from y at the scale of R(y), with d(xl,z) beyond the Toponogov bound for  *)
(* angle 1/2.  Then a neck sphere S within distance M R(y)^(-1/2) of y       *)
(* separates xl from z (M = sqrt(1+eps)(1/eps + sqrt(2) pi) + C).            *)
(* ------------------------------------------------------------------------- *)

(* The neck case: y is the centre of an eps-neck. *)

let P2FL_CLAIM_11_15_NECK = prove
 (`!top atlas (g:B->real^3^3) C eps y xl z e M r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     connected_space top /\ apx_sphere_sep top atlas /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     &1 <= C /\ &0 < eps /\ eps <= &1 / &100 /\
     y IN topspace top /\ xl IN topspace top /\ z IN topspace top /\
     rfs_neck (top,atlas) g eps y e /\
     sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi) + C = M /\
     inv(sqrt(mfd_scalar atlas g y)) = r /\
     (M + &45 * sqrt C) * r <= mfd_dist (top,atlas) g y xl /\
     (M + &45 * sqrt C) * r <= mfd_dist (top,atlas) g y z /\
     (mfd_dist (top,atlas) g y xl - mfd_dist (top,atlas) g y z) pow 2 +
     mfd_dist (top,atlas) g y xl * mfd_dist (top,atlas) g y z / &4
     < mfd_dist (top,atlas) g xl z pow 2
     ==> ?S. S SUBSET mfd_cball (top,atlas) g y (M * r) /\ apx_separates top S xl z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= sqrt C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) y` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `r:real`)) THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M * r /\ r <= sqrt C * r /\
                (sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)) * r <= M * r /\
                M * r < (M + &45 * sqrt C) * r` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= (c - &1) * r ==> r <= c * r`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y xl /\
                mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `xl:B`] P2FL_MIN_GEO_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `z:B`] P2FL_MIN_GEO_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) y u1 (&0) = y /\
                mfd_geo (top,atlas) (g:B->real^3^3) y u2 (&0) = y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `y:B`; `u1:real^3`] P2FL_UNIT_GEO);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `y:B`; `u2:real^3`] P2FL_UNIT_GEO)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `y:B`; `e:real^3->B`] P2FL_NECK_SEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:B) IN IMAGE (e:real^3->B) (sphere(vec 0,&1)) /\
                &45 * r <= mfd_dist (top,atlas) (g:B->real^3^3) y xl /\
                &45 * r <= mfd_dist (top,atlas) (g:B->real^3^3) y z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[rfs_neck]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `y:B`; `e:real^3->B`;
                 `(e:real^3->B) (&3 / &4 % basis 1)`; `(e:real^3->B) (&4 / &3 % basis 1)`;
                 `y:B`; `u1:real^3`; `u2:real^3`;
                 `mfd_dist (top,atlas) (g:B->real^3^3) y xl`;
                 `mfd_dist (top,atlas) (g:B->real^3^3) y z`; `&0`; `&0`] P2FL_NECK_TWO_GEO) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID] THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (e:real^3->B) (sphere(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; mfd_cball; IN_ELIM_THM] THEN
  X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `y:B`; `e:real^3->B`; `(e:real^3->B) u`] CANON_NECK_IN_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[APX_UNIT_SPHERE_NECK_DOM; SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The cap case: y lies in the core Y of a (C,eps)-cap U. *)

let P2FL_CLAIM_11_15_CAP = prove
 (`!top atlas (g:B->real^3^3) C eps y xl z U Y M r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     connected_space top /\ apx_sphere_sep top atlas /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     &1 <= C /\ &0 < eps /\ eps <= &1 / &100 /\
     y IN topspace top /\ xl IN topspace top /\ z IN topspace top /\
     rfs_cap (top,atlas) g C eps U Y /\ y IN Y /\
     sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi) + C = M /\
     inv(sqrt(mfd_scalar atlas g y)) = r /\
     (M + &45 * sqrt C) * r <= mfd_dist (top,atlas) g y xl /\
     (M + &45 * sqrt C) * r <= mfd_dist (top,atlas) g y z /\
     (mfd_dist (top,atlas) g y xl - mfd_dist (top,atlas) g y z) pow 2 +
     mfd_dist (top,atlas) g y xl * mfd_dist (top,atlas) g y z / &4
     < mfd_dist (top,atlas) g xl z pow 2
     ==> ?S. S SUBSET mfd_cball (top,atlas) g y (M * r) /\ apx_separates top S xl z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2FL_NECK_CONSTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= sqrt C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`] APX_CAP_CORE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':B` (X_CHOOSE_THEN `e':real^3->B` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`] P2FL_CAP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rpos") (LABEL_TAC "rat")) THEN
  SUBGOAL_THEN `(Y:B->bool) SUBSET top closure_of Y` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN U /\ (z':B) IN U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z':B) IN IMAGE (e':real^3->B) (sphere(vec 0,&1))` MP_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:B->real^3^3) y /\ &0 < mfd_scalar atlas g z'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `r:real`)) THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M * r /\ C * r <= M * r /\ M * r < (M + &45 * sqrt C) * r /\
                &0 <= sqrt C * r` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN U ==> mfd_joinable (top,atlas) (y:B) w /\
                               mfd_dist (top,atlas) (g:B->real^3^3) y w <= M * r`
  (LABEL_TAC "inU") THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`; `y:B`; `w:B`]
                  CANON_CAP_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((xl:B) IN top closure_of Y) /\ ~((z:B) IN top closure_of Y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "inU" (MP_TAC o SPEC `xl:B`); USE_THEN "inU" (MP_TAC o SPEC `z:B`)] THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z')) <= sqrt C * r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand(concl th) = `r:real`)) THEN
    MATCH_MP_TAC P2FL_SCALE_RATIO THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "rat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y xl /\
                mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `xl:B`] P2FL_MIN_GEO_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `z:B`] P2FL_MIN_GEO_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `u1:real^3`; `mfd_dist (top,atlas) (g:B->real^3^3) y xl`;
                 `top closure_of (Y:B->bool)`; `IMAGE (e':real^3->B) (sphere(vec 0,&1))`]
                P2FL_GEO_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `y:B`; `u2:real^3`; `mfd_dist (top,atlas) (g:B->real^3^3) y z`;
                 `top closure_of (Y:B->bool)`; `IMAGE (e':real^3->B) (sphere(vec 0,&1))`]
                P2FL_GEO_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sg1 <= M * r /\ sg2 <= M * r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `y:B`; `u1:real^3`;
                     `mfd_dist (top,atlas) (g:B->real^3^3) y xl`; `sg1:real`]
                    P2FL_MIN_GEO_PT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      USE_THEN "inU" (MP_TAC o SPEC `mfd_geo (top,atlas) (g:B->real^3^3) y u1 sg1`);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `y:B`; `u2:real^3`;
                     `mfd_dist (top,atlas) (g:B->real^3^3) y z`; `sg2:real`]
                    P2FL_MIN_GEO_PT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      USE_THEN "inU" (MP_TAC o SPEC `mfd_geo (top,atlas) (g:B->real^3^3) y u2 sg2`)] THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `z':B`; `e':real^3->B`] P2FL_NECK_SEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sg1 + &45 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z')) <=
                mfd_dist (top,atlas) g y xl /\
                sg2 + &45 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) z')) <=
                mfd_dist (top,atlas) g y z` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `z':B`; `e':real^3->B`;
                 `(e':real^3->B) (&3 / &4 % basis 1)`; `(e':real^3->B) (&4 / &3 % basis 1)`;
                 `y:B`; `u1:real^3`; `u2:real^3`;
                 `mfd_dist (top,atlas) (g:B->real^3^3) y xl`;
                 `mfd_dist (top,atlas) (g:B->real^3^3) y z`; `sg1:real`; `sg2:real`]
                P2FL_NECK_TWO_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (e':real^3->B) (sphere(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `w:B` THEN DISCH_TAC THEN
  USE_THEN "inU" MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* Claim 11.15 at one time. *)

let P2FL_CLAIM_11_15 = prove
 (`!top atlas (g:B->real^3^3) C eps y xl z U M r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     connected_space top /\ ~compact_space top /\ apx_sphere_sep top atlas /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     &1 <= C /\ &0 < eps /\ eps <= &1 / &100 /\
     y IN topspace top /\ xl IN topspace top /\ z IN topspace top /\
     rfs_canonical_nbhd (top,atlas) g C eps y U /\
     sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi) + C = M /\
     inv(sqrt(mfd_scalar atlas g y)) = r /\
     (M + &45 * sqrt C) * r <= mfd_dist (top,atlas) g y xl /\
     (M + &45 * sqrt C) * r <= mfd_dist (top,atlas) g y z /\
     (mfd_dist (top,atlas) g y xl - mfd_dist (top,atlas) g y z) pow 2 +
     mfd_dist (top,atlas) g y xl * mfd_dist (top,atlas) g y z / &4
     < mfd_dist (top,atlas) g xl z pow 2
     ==> ?S. S SUBSET mfd_cball (top,atlas) g y (M * r) /\ apx_separates top S xl z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `C:real`; `eps:real`; `y:B`; `U:B->bool`] P2FL_NECK_OR_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC P2FL_CLAIM_11_15_NECK THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `e:real^3->B`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2FL_CLAIM_11_15_CAP THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `U:B->bool`; `Y:B->bool`] THEN
    ASM_REWRITE_TAC[]]);;

