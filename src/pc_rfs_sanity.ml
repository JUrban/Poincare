(* ========================================================================= *)
(* Unit pc_rfs_sanity: sanity theorems for the surgery layer.  RFS_KREG:     *)
(* rfs_kreg is [1/eps].  RFS_SPHERE_SYSTEM_IMP_SMT: the componentwise        *)
(* sphere-system statement implies SMT_SPHERE_SYSTEM_STATEMENT.              *)
(* RFS_TRIVIAL_CUT_CAP: the empty cut (identity) is cut-and-cap data.        *)
(* RFS_EMPTY_HISTORY: the controlled-history predicate is satisfiable (the   *)
(* empty history, a non-vacuity check only).  RFS_CAP_DIAM_SET,              *)
(* RFS_CAP_DIAM_BOUND: the diameter set of rfs_cap clause (5) ranges over    *)
(* the pairs of points of U only, and a bound on the intrinsic distances in  *)
(* U gives the clause.                                                       *)
(* ========================================================================= *)

needs "src/pc_rfs_assembly.ml";;

prioritize_real();;
type_invention_error := true;;

let RFS_KREG = prove
 (`!eps. &0 < eps ==> &(rfs_kreg eps) = floor(inv eps)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_kreg] THEN
  SUBGOAL_THEN `?k:num. &k <= inv eps /\ inv eps < &k + &1`
   (STRIP_ASSUME_TAC o SELECT_RULE) THENL
   [MP_TAC(SPEC `inv eps` FLOOR_POS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FLOOR];
    CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED]]);;

let RFS_SPHERE_SYSTEM_IMP_SMT = prove
 (`!u:A->bool v:B->bool.
        RFS_SPHERE_SYSTEM_STATEMENT u v ==> SMT_SPHERE_SYSTEM_STATEMENT u v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RFS_SPHERE_SYSTEM_STATEMENT; SMT_SPHERE_SYSTEM_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
    `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
    `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space (topX:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE;
                  PATH_CONNECTED_IMP_CONNECTED_SPACE];
    ALL_TAC] THEN
  MATCH_MP_TAC RFS_COMPONENTS_S3_CONNECTED THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`topZ:B topology`; `atlasZ:((B->bool)#(B->real^3))->bool`;
    `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->B`;
    `cm:num->real^3->B`; `ff:A->B`; `gg:B->A`] THEN
  ASM_SIMP_TAC[RFS_COMPONENTS_SC_CONNECTED; mfd_cut_cap; mfd_cut_spheres; mfd_cut_cores;
               rfs_components_s3]);;

let RFS_TRIVIAL_CUT_CAP = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e cp cm.
        smooth_manifold_atlas top atlas
        ==> mfd_cut_cap top atlas top atlas {} e cp cm (\x. x) (\x. x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_cut_cap; mfd_cut_spheres; mfd_cut_cores] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_0; DIFF_EMPTY] THEN
  REWRITE_TAC[NOT_IN_EMPTY; FINITE_EMPTY] THEN
  MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]);;

let RFS_EMPTY_MANIFOLD = prove
 (`smooth_manifold_atlas (discrete_topology ({}:A->bool))
                         ({}:((A->bool)#(A->real^N))->bool)`,
  REWRITE_TAC[smooth_manifold_atlas; NOT_IN_EMPTY; TOPSPACE_DISCRETE_TOPOLOGY]);;

let RFS_EMPTY_HISTORY = prove
 (`!C eps. ?hs:(A)rfs_history.
        rfs_controlled (C,eps) ((\t. &1),(\t. &1),(\t. &1),(\t. &1)) hs /\
        rfs_extinct hs`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `RfsHistory 0 (\k. &k) (\k. discrete_topology ({}:A->bool))
                         (\k. {}) (\k t (x:A). mat 1:real^3^3)
                         (\k. @ev:(A)rfs_event. T)` THEN
  SUBGOAL_THEN
   `!t. topspace(rfs_top_at (RfsHistory 0 (\k. &k)
                    (\k. discrete_topology ({}:A->bool))
                    (\k. {}) (\k t (x:A). mat 1:real^3^3)
                    (\k. @ev:(A)rfs_event. T)) t) = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfs_top_at; hs_top; COND_ID; TOPSPACE_DISCRETE_TOPOLOGY];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_controlled; rfs_extinct; rfs_history_ok; hs_count; hs_time;
              hs_top; hs_atlas; hs_metric; hs_event; TOPSPACE_DISCRETE_TOPOLOGY] THEN
  REWRITE_TAC[ARITH_RULE `k <= 0 <=> k = 0`; ARITH_RULE `~(1 <= k /\ k = 0)`;
              ARITH_RULE `~(k < 0)`; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[HAUSDORFF_SPACE_DISCRETE_TOPOLOGY; COMPACT_SPACE_DISCRETE_TOPOLOGY;
              FINITE_EMPTY; RFS_EMPTY_MANIFOLD; ADD_CLAUSES; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[ricci_flow_from; ricci_flow_on; riemannian_metric; NOT_IN_EMPTY;
              TOPSPACE_DISCRETE_TOPOLOGY; RFS_EMPTY_MANIFOLD; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[rfs_params; mfd_orientable] THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `{}:((A->bool)#(A->real^3))->bool` THEN
    REWRITE_TAC[UNION_EMPTY; RFS_EMPTY_MANIFOLD; mfd_oriented_atlas; NOT_IN_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_view; rfs_pinched; rfs_canonical_assumption; rfs_noncollapsed] THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* The diameter clause (5) of rfs_cap (MT Def 9.72(5)): its set ranges over  *)
(* the pairs y1, y2 of points of the fixed U (the binders are explicit,      *)
(* since U occurs on both sides of the bar), and bounded intrinsic distances *)
(* in U give the clause for any larger constant.                             *)
(* ------------------------------------------------------------------------- *)

let RFS_CAP_DIAM_SET = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) U z.
        z IN {mfd_dist_in (top,atlas) g U y1 y2 | y1,y2 | y1 IN U /\ y2 IN U} <=>
        ?y1 y2. y1 IN U /\ y2 IN U /\ z = mfd_dist_in (top,atlas) g U y1 y2`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let RFS_CAP_DIAM_BOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) U D c.
        (!y1 y2. y1 IN U /\ y2 IN U ==> mfd_dist_in (top,atlas) g U y1 y2 <= D) /\ D < c
        ==> rfs_sup_lt {mfd_dist_in (top,atlas) g U y1 y2 | y1,y2 | y1 IN U /\ y2 IN U} c`,
  REWRITE_TAC[rfs_sup_lt; RFS_CAP_DIAM_SET] THEN MESON_TAC[]);;

