(* ========================================================================= *)
(* pc_p2b_splitreq (statement and sanity theorems):                          *)
(* P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT, Hamilton's strong maximum principle   *)
(* in dimension 3 (MT Thm 4.18, Cor 4.19), used by Part 2B (Prop 9.83, the   *)
(* asymptotic soliton, Lemma 9.65, Thm 9.64) and proved in pc_rfa_splitend   *)
(* (RFA_P2B_REQ_SMP_SPLIT_PT).  Points of the formulation:                   *)
(* (1) the dichotomy flat or locally split holds at EACH time separately:   *)
(*     an incomplete flow can be flat up to some T0 and split after it, and *)
(*     a flat slice is split only by the flat-chart theorem;                *)
(* (2) a zero of the scalar curvature at (p,t1) makes the flow flat on      *)
(*     (a,t1] (MT Thm 4.18 through the strong maximum principle for R; used *)
(*     by Lemma 9.65);                                                       *)
(* (3) p2b_parallel_on asks the CHART REPRESENTATIVES mfd_vrep to be smooth  *)
(*     (smoothness of the preferred-chart values, mfd_smooth_on atlas W X,   *)
(*     would not do: those values jump where chart_at switches charts).      *)
(* The vocabulary p2b_parallel_on and p2b_locally_split is defined here and  *)
(* used by pc_cmp_pdefs, the Part 2B units and the pc_rfa units.  The needs  *)
(* lines give rfs_flow_upto of pc_p3_defs; its closure has mfd_vrep and      *)
(* mfd_smooth_on of pc_mfd_maps, christoffel of pc_lrg, metric_local,        *)
(* mfd_sectional and mfd_scalar of pc_mfd_riem.                              *)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The vocabulary.  A vector field X (preferred coordinates)                 *)
(* is parallel for g on W if in every chart its representative is smooth    *)
(* and has vanishing covariant derivative; a metric is locally split (a      *)
(* local Riemannian product with a line, MT Cor 4.19) if every point has a   *)
(* parallel unit field on a neighbourhood.                                   *)
(* ------------------------------------------------------------------------- *)

let p2b_parallel_on = new_definition
 `p2b_parallel_on (atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N)
                  (W:B->bool) (X:B->real^N) <=>
    (!c. c IN atlas
         ==> smooth_map_on (IMAGE (SND c) (FST c INTER W)) (mfd_vrep atlas X c)) /\
    !c y z. c IN atlas /\ y IN IMAGE (SND c) (FST c INTER W)
            ==> frechet_derivative (mfd_vrep atlas X c) (at y) z +
                christoffel (metric_local atlas c g) y z (mfd_vrep atlas X c y) = vec 0`;;

let p2b_locally_split = new_definition
 `p2b_locally_split (top:B topology,atlas:((B->bool)#(B->real^N))->bool)
                    (g:B->real^N^N) <=>
    !x. x IN topspace top
        ==> ?W X. open_in top W /\ x IN W /\ p2b_parallel_on atlas g W X /\
                  !y. y IN W ==> X y dot (g y ** X y) = &1`;;

(* ------------------------------------------------------------------------- *)
(* The statement.  A connected (possibly incomplete) flow on (a,b]           *)
(* with sec >= 0.  (i) If some plane at (p,t1) has zero curvature, then at   *)
(* each time t in (a,t1] the slice g(t) is flat or locally split.  (ii) If   *)
(* the scalar curvature vanishes at (p,t1), the flow is flat on (a,t1].      *)
(* Degenerate cases: an empty manifold (no p) and a = t1 (excluded by        *)
(* a < t1) are vacuous; flat flows satisfy both parts; the flow of a         *)
(* shrinking round cylinder S^2 x R satisfies (i) with split slices and (ii) *)
(* vacuously (R > 0); a flow flat on (a,T0] and split on (T0,t1] satisfies   *)
(* (i) time by time.                                                          *)
(* ------------------------------------------------------------------------- *)

let P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT = new_definition
 `P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) a b p t1.
       hausdorff_space top /\ connected_space top /\ rfs_flow_upto (top,atlas) a b g /\
       (!t x u v. a < t /\ t <= b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas (g t) x u v) /\
       a < t1 /\ t1 <= b /\ p IN topspace top
       ==> (!u1 v1. ~collinear {vec 0,u1,v1} /\ mfd_sectional atlas (g t1) p u1 v1 = &0
                    ==> !t. a < t /\ t <= t1
                            ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                                         ==> mfd_sectional atlas (g t) x u v = &0) \/
                                p2b_locally_split (top,atlas) (g t)) /\
           (mfd_scalar atlas (g t1) p = &0
            ==> !t x u v. a < t /\ t <= t1 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> mfd_sectional atlas (g t) x u v = &0)`;;

(* ------------------------------------------------------------------------- *)
(* Sanity.  Euclidean space with its identity chart is locally              *)
(* split by the constant unit field basis 1 (so the vocabulary is           *)
(* satisfiable), and the identity field is not parallel on any nonempty     *)
(* set (so the parallel condition has teeth).                                *)
(* ------------------------------------------------------------------------- *)

let P2BSR_VREP_EUCLID = prove
 (`!X:real^N->real^N.
        mfd_vrep (open_set_atlas (:real^N)) X ((:real^N),(\x:real^N. x)) = X`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; mfd_vrep] THEN X_GEN_TAC `y:real^N` THEN
  SUBGOAL_THEN `chart_inv ((:real^N),(\x:real^N. x)) y = y` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (:real^N)`; `open_set_atlas (:real^N)`;
                   `(:real^N)`; `\x:real^N. x`] CHART_INV) THEN
    SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; RFB_OPEN_SET_ATLAS_CASES; IN_UNIV];
    ALL_TAC] THEN
  SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV] THEN
  MP_TAC(ISPECL [`subtopology euclidean (:real^N)`; `open_set_atlas (:real^N)`;
                 `(:real^N)`; `\x:real^N. x`; `y:real^N`] CHART_JAC_SELF) THEN
  SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; RFB_OPEN_SET_ATLAS_CASES; IN_UNIV]);;

let P2BSR_METRIC_LOCAL_EUCLID = prove
 (`!g:real^N->real^N^N.
        metric_local (open_set_atlas (:real^N)) ((:real^N),(\x:real^N. x)) g = g`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
  MP_TAC(ISPECL [`(:real^N)`; `g:real^N->real^N^N`; `z:real^N`]
                RFB_OPEN_SET_METRIC_LOCAL) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let P2BSR_EUCLID_SPLIT = prove
 (`p2b_locally_split (euclidean:(real^N)topology,open_set_atlas (:real^N))
                     (\x:real^N. mat 1:real^N^N)`,
  REWRITE_TAC[p2b_locally_split; p2b_parallel_on; TOPSPACE_EUCLIDEAN; IN_UNIV;
              RFB_OPEN_SET_ATLAS_CASES; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_UNWIND_THM2; P2BSR_VREP_EUCLID; P2BSR_METRIC_LOCAL_EUCLID] THEN
  X_GEN_TAC `x0:real^N` THEN
  MAP_EVERY EXISTS_TAC [`(:real^N)`; `\x:real^N. basis 1:real^N`] THEN
  REWRITE_TAC[GSYM OPEN_IN; OPEN_UNIV; SMOOTH_MAP_ON_CONST; IN_UNIV;
              FRECHET_DERIVATIVE_CONST_AT; LRG_CHRISTOFFEL_CONST;
              VECTOR_ADD_LID; MATRIX_VECTOR_MUL_LID] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL]);;

let P2BSR_ID_NOT_PARALLEL = prove
 (`!W:real^N->bool.
        ~(W = {})
        ==> ~p2b_parallel_on (open_set_atlas (:real^N)) (\x:real^N. mat 1:real^N^N)
                             W (\x. x)`,
  SUBGOAL_THEN `!y:real^N. frechet_derivative (\x:real^N. x) (at y) = (\h. h)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2b_parallel_on; RFB_OPEN_SET_ATLAS_CASES; IMP_CONJ;
                  RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2; P2BSR_VREP_EUCLID;
                  P2BSR_METRIC_LOCAL_EUCLID; LRG_CHRISTOFFEL_CONST; VECTOR_ADD_RID;
                  IMAGE_ID; INTER_UNIV] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^N`) THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL]);;

