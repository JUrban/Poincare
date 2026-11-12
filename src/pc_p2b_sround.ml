(* ========================================================================= *)
(* pc_p2b_sround: the route of SPLIT_ROUND.  From the inputs X0, THM_9_11,   *)
(* P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT, ANCIENT_COMPACT and                 *)
(* P2B_REQ_S2_ENTROPY_STATEMENT, and the statement                           *)
(* P2B_REQ_CYL_FROM_LEAF_STATEMENT (pc_p2b_cylleafreq), a split class flow   *)
(* is, up to every time s0 < b, the round cylinder model.  Steps: the        *)
(* shifted flow g(. + b - 1) is a kappa-solution                             *)
(* (P2B_GSPLIT_SLICE_BOUND_ROUTE); its asymptotic soliton (THM_9_11) carries *)
(* the limit Y of the splitting field at time 0 (P2BPL_LIMIT_FIELD); the     *)
(* limit flow is split by Y at every time (P2BRD_LIMIT_GSPLIT), so           *)
(* P2B_GSPLIT_SLICE_BOUND_ROUTE bounds R on the soliton slice and            *)
(* P2B_SHRINKER_SPLIT_CYL gives its model map; P2BKL_LEAF_ROUND (with the    *)
(* S^2 entropy statement) gives the round leaf data, and                     *)
(* P2B_REQ_CYL_FROM_LEAF_STATEMENT the cylinder model.                       *)
(* Main theorems: P2BRD_SPLIT_ROUND_FROM_CYL                                 *)
(*   |- !w. P2B_REQ_CYL_FROM_LEAF_STATEMENT w ==>                            *)
(*          P2B_SPLIT_ROUND_ROUTE_STATEMENT w,                               *)
(* and with P2B_CYL_FROM_LEAF (pc_p2b_cylleaf)                               *)
(*   P2B_SPLIT_ROUND_ROUTE |- !w. P2B_SPLIT_ROUND_ROUTE_STATEMENT w.         *)
(* ========================================================================= *)

needs "src/pc_p2b_x0r.ml";;
needs "src/pc_p2b_shrinkcl.ml";;
needs "src/pc_p2b_rmhalf.ml";;
needs "src/pc_p2b_parlim.ml";;
needs "src/pc_p2b_parfield.ml";;
needs "src/pc_p2b_parons.ml";;
needs "src/pc_p2c_blowup2.ml";;
needs "src/pc_rfa_mfd.ml";;
needs "src/pc_rfa_split.ml";;
needs "src/pc_rfa_secpres.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2c_views.ml";;
needs "src/pc_p2b_shsplit.ml";;
needs "src/pc_p2b_kleaf.ml";;
needs "src/pc_p2b_cylleafreq.ml";;
needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_p2b_s2entreq.ml";;
needs "src/pc_p2b_cylleaf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The kappa-solution, limits in two forms, subsequences.                    *)
(* ========================================================================= *)

(* P2BRD.R1 The split ancient flow shifted to end at s1 < b is a           *)
(* kappa-solution: bounded slices (P2B_GSPLIT_SLICE_BOUND_ROUTE with       *)
(* ANCIENT_COMPACT, P2BPL_POINT_LIMIT and P2BPL_ORBIT_LIMIT),              *)
(* abs Rm <= R/2 (sec >= 0) and P2BSK_KSOL_SHIFT.                          *)

let P2BRD_KSOL_OF_SPLIT = prove
 (`!w:B->bool.
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b (X:B->real^3) s1.
           p2b_ancflow0 kappa (top,atlas) g b /\ p2b_gsplit (top,atlas) g {s | s < b} X /\
           s1 < b
           ==> p2b_kappa_solution kappa (top,atlas) (\t. g(t + s1))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BSK_KSOL_SHIFT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `w:B->bool` P2B_GSPLIT_SLICE_BOUND_ROUTE) THEN
  REWRITE_TAC[P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT; P2B_GSPLIT_SLICE_BOUND_STATEMENT] THEN
  ASM_REWRITE_TAC[P2BPL_POINT_LIMIT; P2BPL_ORBIT_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `g:real->B->real^3^3`; `b:real`; `X:B->real^3`; `s:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K:real`) THEN
  UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
  REWRITE_TAC[p2b_ancflow0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `K / &2` THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) x / &2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!s x u v. s < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                           ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) s) x u v` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a <= k ==> a / &2 <= k / &2`) THEN ASM_SIMP_TAC[]]);;

(* P2BRD.R2 Uniqueness of limits measured in two positive definite forms:  *)
(* if c n % z n converges to Y1 in the G1-form and, along a subsequence r,  *)
(* to Y2 in the G2-form, then Y1 = Y2.                                      *)

let P2BRD_FORM_LIMIT = prove
 (`!(G:real^3^3) (w:num->real^3) Y.
     (!v. ~(v = vec 0) ==> &0 < v dot (G ** v)) /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> (w n - Y) dot (G ** (w n - Y)) < e)
     ==> (w --> Y) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC o MATCH_MP RFA_POSDEF_LOWER) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m * e pow 2`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `N <= n:num`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(w:num->real^3) n - Y`) THEN
  SUBGOAL_THEN `&0 <= norm((w:num->real^3) n - Y)` MP_TAC THENL [REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SPEC_TAC(`norm((w:num->real^3) n - Y)`,`d:real`) THEN
  SPEC_TAC(`((w:num->real^3) n - Y) dot (G ** (w n - Y))`,`q:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `m * d pow 2 < m * e pow 2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `2` REAL_POW_LT2_REV) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BRD_LIMIT_UNIQUE_SUB = prove
 (`!(w:num->real^3) r Y1 Y2.
     (!m n. m < n ==> r m < r n) /\ (w --> Y1) sequentially /\ ((w o r) --> Y2) sequentially
     ==> Y1 = Y2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `(w:num->real^3) o (r:num->num)` THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC LIM_SUBSEQUENCE THEN ASM_REWRITE_TAC[]);;

(* P2BRD.R3 The limit field is parallel for every slice of the flow limit: *)
(* P2BPL_LIMIT_FIELD at time 0 gives Y along sub; at a time s < 1 it         *)
(* gives Y_s along a further subsequence of the slice limit at s (taken     *)
(* along the same indices); the vectors z with dphi z = X(phi y) are the    *)
(* same (dphi injective), so the two limits agree: Y_s = Y.  Hence the      *)
(* flow limit is split by Y on s < 1.                                       *)

let P2BRD_DIFF_UNIQUE = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) top1 (atlas1:((A->bool)#(A->real^3))->bool)
    W W' (f:B->A) f' y z z'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top1 atlas1 /\
     mfd_diffeo top atlas W top1 atlas1 W' f f' /\ y IN W /\
     mfd_differential atlas atlas1 f y z = mfd_differential atlas atlas1 f y z'
     ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `top1:A topology`;
                 `atlas1:((A->bool)#(A->real^3))->bool`; `W:B->bool`; `W':A->bool`;
                 `f:B->A`; `f':A->B`; `y:B`] P2BPL_DIFF_SURJ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `mfd_differential (atlas:((B->bool)#(B->real^3))->bool) (atlas1:((A->bool)#(A->real^3))->bool) (f:B->A) y`
               LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The same statement as P2BX1_PARALLEL_ON_SUBSET of pc_p2b_x1, which this  *)
(* unit does not load (pc_p2b_x1 uses SPLIT_ROUND).                         *)

let P2BRD_PARALLEL_ON_SUBSET = prove
 (`!(atlas:((B->bool)#(B->real^N))->bool) g W W' (X:B->real^N).
     p2b_parallel_on atlas g W X /\ W' SUBSET W ==> p2b_parallel_on atlas g W' X`,
  REWRITE_TAC[p2b_parallel_on] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) (FST c INTER W)` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2BRD_SUBSEQ_SHIFT = prove
 (`!sub N0 Ns. p3_subseq sub
               ==> p3_subseq (\n. (sub(n + Ns) + N0) - Ns) /\
                   !n. ((sub(n + Ns) + N0) - Ns) + Ns = sub(n + Ns) + N0`,
  REWRITE_TAC[p3_subseq] THEN BETA_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. Ns <= (sub:num->num)(n + Ns)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + Ns:num` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(sub:num->num)(m + Ns) < sub(n + Ns)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `m:num` (ASSUME `!n. Ns <= (sub:num->num)(n + Ns)`)) THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. Ns <= (sub:num->num)(n + Ns)`)) THEN ARITH_TAC;
    GEN_TAC THEN MP_TAC(SPEC `n:num` (ASSUME `!n. Ns <= (sub:num->num)(n + Ns)`)) THEN
    ARITH_TAC]);;

(* ========================================================================= *)
(* g(s) X is constant in s; R > 0 in the class.                              *)
(* ========================================================================= *)

(* P2BRD.R5 Facts of a split class flow used by the assembly: the Ricci     *)
(* matrix kills a parallel field, so g(s) X does not depend on s (d/ds g =  *)
(* -2 Ric); and R > 0 everywhere at every time (the class has a point with  *)
(* abs Rm > 0 at every time, abs Rm <= R/2 by sec >= 0, and the strong      *)
(* maximum principle RFA_SCALAR_STRONG_SEC).                                *)

let P2BRD_PAR_RICCI_MATRIX_ZERO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (X:A->real^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ x IN topspace top
     ==> mfd_ricci_matrix atlas g x ** X x = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_ricci_matrix atlas (g:A->real^N^N) x ** (X:A->real^N) x`; `i:num`]
                DOT_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `basis i:real^N`; `(X:A->real^N) x`] P2BKL_MFD_RICCI_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_ricci atlas (g:A->real^N^N) x (basis i) ((X:A->real^N) x) =
                mfd_ricci atlas g x (X x) (basis i)` SUBST1_TAC THENL
   [REWRITE_TAC[mfd_ricci] THEN MATCH_MP_TAC LRICCI_SYM THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                      (FST(chart_at atlas x))` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BX0R_PAR_RICCI_ZERO THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

let P2BRD_FLOW_FIELD_CONST = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:real->A->real^N^N) a b (X:A->real^N) s s' y.
     ricci_flow_on (top,atlas) a b g /\
     (!r. a < r /\ r < b ==> p2b_parallel_on atlas (g r) (topspace top) X) /\
     a < s /\ s < b /\ a < s' /\ s' < b /\ y IN topspace top
     ==> g s y ** X y = g s' y ** X y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `!r. a < r /\ r < b
                    ==> mfd_ricci_matrix atlas ((g:real->A->real^N^N) r) y ** (X:A->real^N) y =
                        vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BRD_PAR_RICCI_MATRIX_ZERO THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. ((g:real->A->real^N^N) r y ** (X:A->real^N) y)$i`; `real_interval(a,b)`]
                HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN
     `&0 = sum(1..dimindex(:N))
               (\j. (--(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) r) y$i$j) *
                    (X:A->real^N) y$j)`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `sum(1..dimindex(:N))
            (\j. mfd_ricci_matrix atlas ((g:real->A->real^N^N) r) y$i$j * (X:A->real^N) y$j) =
        (mfd_ricci_matrix atlas (g r) y ** X y)$i`
      MP_TAC THENL [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot]; ALL_TAC] THEN
      ASM_SIMP_TAC[VEC_COMPONENT] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN DISCH_THEN SUBST1_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_derivative"))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (fun th -> MP_TAC(SPEC `s:real` th) THEN
                                               MP_TAC(SPEC `s':real` th))) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REAL_ARITH_TAC);;

(* The same statement as P2BX1_SCALAR_POS of pc_p2b_x1 (proved there by the *)
(* SMP splitting), which this unit does not load: pc_p2b_x1 uses SPLIT_ROUND. *)
(* Here by the strong maximum principle RFA_SCALAR_STRONG_SEC.             *)

let P2BRD_ANC_SCALAR_POS = prove
 (`!kappa top atlas (g:real->B->real^3^3) b t x.
     p2b_ancflow0 kappa (top,atlas) g b /\ t < b /\ x IN topspace top
     ==> &0 < mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow0] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t - &1` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_rm_norm")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (t - &2) b (g:real->B->real^3^3)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) (t - &1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) (t - &2) b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r y u v. r < b /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) r) y u v`
  (LABEL_TAC "sec") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) (t - &1)) x0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) (t - &1)`; `x0:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `t - &2`; `b:real`;
                 `g:real->B->real^3^3`; `t - &1`; `x0:B`] RFA_SCALAR_STRONG_SEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:real`; `y:B`] THEN STRIP_TAC THEN
      MATCH_MP_TAC RFA_SECMIN_NONNEG THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The flow limit is split by the time-0 limit field.                        *)
(* ========================================================================= *)

(* P2BRD.R6 Helpers of LIMIT_GSPLIT: facts of a slice limit; agreement of *)
(* two limit fields read off the same vectors z (dphi_n z = X(phi_n y),     *)
(* unique for large n) in two positive definite forms; the slice limit of a *)
(* flow limit at a time s along the indices sub(n + Ns) + N0.               *)

let P2BRD_SLICE_FACTS = prove
 (`!V x t Q (top:B topology) atlas (g:B->real^3^3) xl W (phi:num->B->A).
     p2c_slice_limit_with V x t Q (top,atlas) g xl W phi
     ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         (!k. ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k))
                               (IMAGE (phi k) (W k)) (phi k) psi) /\
         (!k. IMAGE (phi k) (W k) SUBSET topspace (rfs_vtop (V k) (t k))) /\
         (!y. y IN topspace top ==> ?n1. !n. n1 <= n ==> y IN W n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_slice_limit_with] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `k:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_diffeo")) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP OPEN_IN_SUBSET);
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`{y:B}`; `0`; `&1`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
    ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n1:num` THEN REWRITE_TAC[SING_SUBSET] THEN
    MESON_TAC[]]);;

let P2BRD_FIELD_AGREE = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (top1:A topology) atlas1
    (f:num->B->A) (q:num->real) (X:A->real^3) y n1 (G0:real^3^3) Gs Y0 Y1 (sub2:num->num).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top1 atlas1 /\
     (!n. n1 <= n ==> ?W W' f'. mfd_diffeo top atlas W top1 atlas1 W' (f n) f' /\ y IN W) /\
     (!v. ~(v = vec 0) ==> &0 < v dot (G0 ** v)) /\
     (!v. ~(v = vec 0) ==> &0 < v dot (Gs ** v)) /\
     (!m n. m < n ==> sub2 m < sub2 n) /\
     (!e. &0 < e
          ==> ?n0. !n. n0 <= n
                       ==> ?z. mfd_differential atlas atlas1 (f n) y z = X(f n y) /\
                               (inv(sqrt(q n)) % z - Y0) dot
                               (G0 ** (inv(sqrt(q n)) % z - Y0)) < e) /\
     (!e. &0 < e
          ==> ?n0. !n. n0 <= n
                       ==> ?z. mfd_differential atlas atlas1 (f(sub2 n)) y z = X(f(sub2 n) y) /\
                               (inv(sqrt(q(sub2 n))) % z - Y1) dot
                               (Gs ** (inv(sqrt(q(sub2 n))) % z - Y1)) < e)
     ==> Y0 = Y1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "c0") (LABEL_TAC "c1")))))))) THEN
  SUBGOAL_THEN `!n (z:real^3) (z':real^3). n1 <= n /\
                         mfd_differential (atlas:((B->bool)#(B->real^3))->bool)
                           (atlas1:((A->bool)#(A->real^3))->bool) ((f:num->B->A) n) (y:B) z =
                         (X:A->real^3)(f n y) /\
                         mfd_differential atlas atlas1 (f n) y z' = X(f n y)
                         ==> z = z'`
  (LABEL_TAC "un") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "dif" (MP_TAC o C MATCH_MP (ASSUME `n1 <= n:num`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `Wn:B->bool` (X_CHOOSE_THEN `Wn':A->bool`
      (X_CHOOSE_THEN `fn':A->B` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC P2BRD_DIFF_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
                          `Wn:B->bool`; `Wn':A->bool`; `(f:num->B->A) n`; `fn':A->B`; `y:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = \n. inv(sqrt((q:num->real) n)) %
                      (@z:real^3. mfd_differential (atlas:((B->bool)#(B->real^3))->bool)
                                    (atlas1:((A->bool)#(A->real^3))->bool) ((f:num->B->A) n)
                                    (y:B) z = (X:A->real^3)(f n y))` THEN
  SUBGOAL_THEN `!n (z:real^3). n1 <= n /\
                      mfd_differential (atlas:((B->bool)#(B->real^3))->bool)
                        (atlas1:((A->bool)#(A->real^3))->bool) ((f:num->B->A) n) (y:B) z =
                      (X:A->real^3)(f n y)
                      ==> (w:num->real^3) n = inv(sqrt((q:num->real) n)) % z`
  (LABEL_TAC "wz") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "w" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    USE_THEN "un" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SELECT_CONV THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= (sub2:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((w:num->real^3) --> Y0) sequentially` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BRD_FORM_LIMIT THEN EXISTS_TAC `G0:real^3^3` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "c0" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN EXISTS_TAC `n0 + n1:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "wz" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((w:num->real^3) o (sub2:num->num)) --> Y1) sequentially` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BRD_FORM_LIMIT THEN EXISTS_TAC `Gs:real^3^3` THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "c1" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN EXISTS_TAC `n0 + n1:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "wz" (MP_TAC o SPECL [`(sub2:num->num) n`; `z:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `n:num` (ASSUME `!n. n <= (sub2:num->num) n`)) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BRD_LIMIT_UNIQUE_SUB THEN
  MAP_EVERY EXISTS_TAC [`w:num->real^3`; `sub2:num->num`] THEN ASM_REWRITE_TAC[]);;

let P2BRD_SLICE_AT_SUB = prove
 (`!V x t Q (top:B topology) atlas (g:real->B->real^3^3) xl W (phi:num->B->A) sub N0 s.
     p2c_flow_limit_with V x t Q {s | s < &1} (top,atlas) g xl W phi /\ s < &1 /\
     riemannian_metric atlas (g s) /\ p3_subseq sub
     ==> ?Ns. p2c_slice_limit_with (\n. V(sub(n + Ns) + N0)) (\n. x(sub(n + Ns) + N0))
                (\n. t(sub(n + Ns) + N0) + s / Q(sub(n + Ns) + N0)) (\n. Q(sub(n + Ns) + N0))
                (top,atlas) (g s) xl (\n. W(sub(n + Ns) + N0)) (\n. phi(sub(n + Ns) + N0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `{s:real | s < &1}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `s:real`]
                P2BX0R_FLOW_TO_SLICE_AT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ns:num` ASSUME_TAC) THEN EXISTS_TAC `Ns:num` THEN
  MP_TAC(SPECL [`sub:num->num`; `N0:num`; `Ns:num`] P2BRD_SUBSEQ_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BU_SLICE_LIMIT_SUBSEQ o C CONJ
    (ASSUME `p3_subseq (\n. ((sub:num->num)(n + Ns) + N0) - Ns)`) o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2c_slice_limit_with"))
          (concl th))) THEN
  REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[]);;

(* P2BRD.R4 The flow limit is split by the time-0 limit field.  For each   *)
(* time s < 1: the slice limit at s along the indices sub(n + Ns) + N0       *)
(* (P2BRD_SLICE_AT_SUB), P2BPL_LIMIT_FIELD there gives a parallel unit      *)
(* field Ys of g(s) along a further subsequence sub2, and Ys = Y because    *)
(* both are limits of the same rescaled vectors z (P2BRD_FIELD_AGREE).      *)

let P2BRD_LIMIT_GSPLIT = prove
 (`!V x t Q (top:B topology) atlas (g:real->B->real^3^3) xl W (phi:num->B->A)
    (top1:A topology) atlas1 (X:A->real^3) N0 sub (Y:B->real^3).
     p2c_flow_limit_with V x t Q {s | s < &1} (top,atlas) g xl W phi /\
     smooth_manifold_atlas top1 atlas1 /\
     (!s. s < &1 ==> riemannian_metric atlas (g s)) /\
     (!n s. s < &1
            ==> rfs_vtop (V n) (t n + s / Q n) = top1 /\
                rfs_vatlas (V n) (t n + s / Q n) = atlas1 /\
                riemannian_metric atlas1 (rfs_vmetric (V n) (t n + s / Q n)) /\
                p2b_parallel_on atlas1 (rfs_vmetric (V n) (t n + s / Q n)) (topspace top1) X /\
                (!y. y IN topspace top1
                     ==> X y dot (rfs_vmetric (V n) (t n + s / Q n) y ** X y) = &1)) /\
     p3_subseq sub /\
     (!K e. compact_in top K /\ &0 < e
            ==> ?n0. !n. n0 <= n
                   ==> !y. y IN K
                       ==> ?z. mfd_differential atlas atlas1 (phi (sub n + N0)) y z =
                               X (phi (sub n + N0) y) /\
                               (inv(sqrt(Q(sub n + N0))) % z - Y y) dot
                               (g (&0) y ** (inv(sqrt(Q(sub n + N0))) % z - Y y)) < e)
     ==> p2b_gsplit (top,atlas) g {s | s < &1} Y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rm") (CONJUNCTS_THEN2 (LABEL_TAC "vw")
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0")))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k) ((t:num->real) k + s / (Q:num->real) k) = top1 /\
        rfs_vatlas (V k) (t k + s / Q k) = atlas1`
  (LABEL_TAC "vt") THENL
   [GEN_TAC THEN
    USE_THEN "vw" (MP_TAC o C MATCH_MP (ASSUME `s < &1`) o SPECL [`k:num`; `s:real`]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `sub:num->num`; `N0:num`; `s:real`] P2BRD_SLICE_AT_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ns:num` (LABEL_TAC "sl")) THEN
  SUBGOAL_THEN
   `!n. IMAGE ((phi:num->B->A)((sub:num->num)(n + Ns) + N0)) ((W:num->B->bool)(sub(n + Ns) + N0))
          SUBSET topspace top1 /\
        (?psi. mfd_diffeo top (atlas:((B->bool)#(B->real^3))->bool) (W(sub(n + Ns) + N0))
                 top1 (atlas1:((A->bool)#(A->real^3))->bool)
                 (IMAGE (phi(sub(n + Ns) + N0)) (W(sub(n + Ns) + N0))) (phi(sub(n + Ns) + N0)) psi)`
  (LABEL_TAC "im") THENL
   [GEN_TAC THEN USE_THEN "sl" (MP_TAC o BETA_RULE o MATCH_MP P2BRD_SLICE_FACTS) THEN
    USE_THEN "vt" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN topspace top
        ==> ?n1. !n. n1 <= n ==> y IN (W:num->B->bool)((sub:num->num)(n + Ns) + N0)`
  (LABEL_TAC "ev") THENL
   [USE_THEN "sl" (MP_TAC o BETA_RULE o MATCH_MP P2BRD_SLICE_FACTS) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* P2BPL_LIMIT_FIELD at time s *)
  MP_TAC(ISPECL [`UNIV:A->bool`; `UNIV:B->bool`] P2BPL_LIMIT_FIELD) THEN
  REWRITE_TAC[P2BPL_LIMIT_FIELD_STATEMENT] THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
           ((sub:num->num)(n + Ns) + N0)`;
    `\n. (x:num->A) ((sub:num->num)(n + Ns) + N0)`;
    `\n. (t:num->real) ((sub:num->num)(n + Ns) + N0) + s / (Q:num->real) (sub(n + Ns) + N0)`;
    `\n. (Q:num->real) ((sub:num->num)(n + Ns) + N0)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) s`; `xl:B`;
    `\n. (W:num->B->bool) ((sub:num->num)(n + Ns) + N0)`;
    `\n. (phi:num->B->A) ((sub:num->num)(n + Ns) + N0)`;
    `\n:num. (X:A->real^3)`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [USE_THEN "sl" (fun th -> REWRITE_TAC[th]) THEN X_GEN_TAC `n:num` THEN
    USE_THEN "vw" (MP_TAC o C MATCH_MP (ASSUME `s < &1`) o
      SPECL [`(sub:num->num)(n + Ns) + N0`; `s:real`]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "im" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BRD_PARALLEL_ON_SUBSET THEN EXISTS_TAC `topspace top1:A->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `Ys:B->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs")))))) THEN
  (* Ys = Y *)
  SUBGOAL_THEN `!y. y IN topspace top ==> (Y:B->real^3) y = Ys y` (LABEL_TAC "ag") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "ev" (MP_TAC o C MATCH_MP (ASSUME `(y:B) IN topspace top`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
    MATCH_MP_TAC P2BRD_FIELD_AGREE THEN
    MAP_EVERY EXISTS_TAC
     [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `top1:A topology`;
      `atlas1:((A->bool)#(A->real^3))->bool`;
      `\n. (phi:num->B->A)((sub:num->num)(n + Ns) + N0)`;
      `\n. (Q:num->real)((sub:num->num)(n + Ns) + N0)`; `X:A->real^3`; `y:B`; `n1:num`;
      `(g:real->B->real^3^3) (&0) y`; `(g:real->B->real^3^3) s y`; `sub2:num->num`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "im" (X_CHOOSE_TAC `psi:A->B` o CONJUNCT2 o SPEC `n:num`) THEN
      MAP_EVERY EXISTS_TAC
       [`(W:num->B->bool)((sub:num->num)(n + Ns) + N0)`;
        `IMAGE ((phi:num->B->A)((sub:num->num)(n + Ns) + N0)) (W(sub(n + Ns) + N0))`;
        `psi:A->B`] THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) (&0)`; `y:B`] RIEMANNIAN_METRIC_POS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "rm" MATCH_MP_TAC THEN REAL_ARITH_TAC; SIMP_TAC[]];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) s`; `y:B`] RIEMANNIAN_METRIC_POS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ASM_MESON_TAC[p3_subseq];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "c0" (MP_TAC o SPECL [`{y:B}`; `e:real`]) THEN
      REWRITE_TAC[COMPACT_IN_SING; IN_SING; FORALL_UNWIND_THM2] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN EXISTS_TAC `n0:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n + Ns:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "cs" (MP_TAC o SPECL [`{y:B}`; `e:real`]) THEN
      REWRITE_TAC[COMPACT_IN_SING; IN_SING; FORALL_UNWIND_THM2] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "vt" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BPF_PARALLEL_ON_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `Ys:B->real^3`] THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "ag" (MP_TAC o C MATCH_MP (ASSUME `(y:B) IN topspace top`)) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Shifted class flow, views, times, lorient, soliton model.                 *)
(* ========================================================================= *)

(* P2BRD.R7 Pieces of the route: the time shift of a Ricci flow; the split  *)
(* class flow shifted by b - 1 (so it lives on t < 1 and its views t <= 0   *)
(* are earlier slices); the views of p2b_kview; the times of THM_9_11; the  *)
(* local orientability of a slice limit; the soliton model                 *)
(* (P2B_GSPLIT_SLICE_BOUND_ROUTE for the split limit flow gives R bounded, *)
(* then P2B_SHRINKER_SPLIT_CYL).                                           *)

let P2BRD_RF_SHIFT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:real->A->real^N^N) a b s1.
     ricci_flow_on (top,atlas) (a + s1) (b + s1) g
     ==> ricci_flow_on (top,atlas) a b (\t. g(t + s1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `--s1:real` o MATCH_MP RICCI_FLOW_TRANSLATE) THEN
  REWRITE_TAC[REAL_ARITH `(x + s1) + --s1 = x`; REAL_ARITH `t - --s1 = t + s1`]);;

let P2BRD_SHIFTED_CLASS = prove
 (`!kappa top atlas (g:real->B->real^3^3) b (X:B->real^3).
     p2b_ancflow0 kappa (top,atlas) g b /\ p2b_gsplit (top,atlas) g {s | s < b} X
     ==> hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
         (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) (\t. g(t + (b - &1)))) /\
         (!s. s < &1 ==> mfd_complete (top,atlas) (g(s + (b - &1)))) /\
         riemannian_metric atlas (g(b - &1)) /\ mfd_complete (top,atlas) (g(b - &1)) /\
         p2b_parallel_on atlas (g(b - &1)) (topspace top) X /\
         (!y. y IN topspace top ==> X y dot (g(b - &1) y ** X y) = &1) /\
         (!s. s < &1
              ==> riemannian_metric atlas (g(s + (b - &1))) /\
                  p2b_parallel_on atlas (g(s + (b - &1))) (topspace top) X /\
                  (!y. y IN topspace top ==> X y dot (g(s + (b - &1)) y ** X y) = &1)) /\
         (!s y. s < &1 /\ y IN topspace top
                ==> g(s + (b - &1)) y ** X y = g(b - &1) y ** X y) /\
         (!s y. s < &1 /\ y IN topspace top ==> &0 < mfd_scalar atlas (g(s + (b - &1))) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "gs" o REWRITE_RULE[p2b_gsplit; IN_ELIM_THM])) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_ancflow0]) THEN
  SUBGOAL_THEN `!s. s < b ==> riemannian_metric atlas ((g:real->B->real^3^3) s)`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `b - &1` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on")) (concl th))) THEN
    REWRITE_TAC[REAL_ARITH `b - &1 < b`] THEN SIMP_TAC[ricci_flow_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BRD_RF_SHIFT THEN
    REWRITE_TAC[REAL_ARITH `&1 + b - &1 = b`] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    USE_THEN "rm" MATCH_MP_TAC THEN REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    USE_THEN "gs" (MP_TAC o SPEC `b - &1`) THEN REWRITE_TAC[REAL_ARITH `b - &1 < b`] THEN
    SIMP_TAC[];
    USE_THEN "gs" (MP_TAC o SPEC `b - &1`) THEN REWRITE_TAC[REAL_ARITH `b - &1 < b`] THEN
    SIMP_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s + (b - &1) < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "gs" (MP_TAC o C MATCH_MP (ASSUME `s + (b - &1) < b`) o SPEC `s + (b - &1)`) THEN
    USE_THEN "rm" (MP_TAC o C MATCH_MP (ASSUME `s + (b - &1) < b`) o SPEC `s + (b - &1)`) THEN
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BRD_FLOW_FIELD_CONST THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `b - &2 - abs s`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "gs" (MP_TAC o SPEC `r:real`) THEN
      ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BRD_ANC_SCALAR_POS THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2BRD_KVIEW_AT = prove
 (`!top atlas (g:real->B->real^3^3) s.
     s <= &0
     ==> rfs_vtop (p2b_kview (top,atlas) g) s = top /\
         rfs_vatlas (p2b_kview (top,atlas) g) s = atlas /\
         rfs_vmetric (p2b_kview (top,atlas) g) s = g s`,
  SIMP_TAC[p2b_kview; rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric; IN_ELIM_THM]);;

let P2BRD_TAU_FACTS = prove
 (`!tau:num->real N.
     (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k)
     ==> (!e. &0 < e ==> ?n0. !n. n0 <= n ==> inv(tau(n + N)) < e) /\
         (!Tm. ?n0. !n. n0 <= n ==> --(tau(n + N)) < Tm) /\
         (!k. --(tau k) <= &0 /\ --(tau k) < &1) /\
         (!n s. s < &1 ==> --(tau n) + s / inv(tau n) < &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inf")) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "inf" (X_CHOOSE_TAC `n0:num` o SPEC `inv e`) THEN EXISTS_TAC `n0:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_SIMP_TAC[REAL_LT_INV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `Tm:real` THEN USE_THEN "inf" (X_CHOOSE_TAC `n0:num` o SPEC `--Tm`) THEN
    EXISTS_TAC `n0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + N:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_INV_INV] THEN
    MATCH_MP_TAC(REAL_ARITH `s * t < &1 * t ==> --t + s * t < &0`) THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]]);;

let P2BRD_LIMIT_LORIENT = prove
 (`!V x t Q (top:B topology) atlas (g0:B->real^3^3) xl W (phi:num->B->B) (top1:B topology)
    atlas1.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. rfs_vtop (V n) (t n) = top1 /\ rfs_vatlas (V n) (t n) = atlas1) /\
     hausdorff_space top1 /\ smooth_manifold_atlas top1 atlas1 /\ p2b_lorient top1 atlas1
     ==> p2b_lorient top atlas`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B_LORIENT_EMBED_CORE2 THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->B`; `\k:num. (top1:B topology)`;
                        `\k:num. (atlas1:((B->bool)#(B->real^3))->bool)`] THEN
  UNDISCH_TAC `p2c_slice_limit_with V x t Q (top,atlas) (g0:B->real^3^3) xl W (phi:num->B->B)` THEN
  ASM_REWRITE_TAC[p2c_slice_limit_with] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (W:num->B->bool) k` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]);;

let P2BRD_SOLITON_MODEL = prove
 (`!w:B->bool.
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) (f:real->B->real) (Y:B->real^3) xl.
           p2b_ancflow0 kappa (top,atlas) g (&1) /\
           (!s. s < &1 ==> p2b_shrinker (top,atlas) (\x. inv(&1 - s) %% g s x) (f s)) /\
           p2b_gsplit (top,atlas) g {s | s < &1} Y /\ p2b_lorient top atlas /\
           xl IN topspace top
           ==> ?p lam. &0 < lam /\
                   IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
                   (!y. ~(y = vec 0)
                        ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
                   (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
                   (!y. ~(y = vec 0)
                        ==> rfs_pullback atlas p (g(&0)) y = lam %% cylinder_flow (&0) y) /\
                   (!y. ~(y = vec 0)
                        ==> Y(p y) =
                            mfd_differential (open_set_atlas {z:real^3 | ~(z = vec 0)}) atlas p y
                                             (inv(sqrt(&2 * lam)) % y))`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `w:B->bool` P2B_SHRINKER_SPLIT_CYL) THEN
  REWRITE_TAC[P2B_SHRINKER_SPLIT_CYL_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `(f:real->B->real) (&0)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_ancflow0]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_shrinker")) (concl th))) THEN
    REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX];
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LT_01];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!s x u v. s < &1 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                           ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) s) x u v` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_01];
    MP_TAC(SPEC `w:B->bool` P2B_GSPLIT_SLICE_BOUND_ROUTE) THEN
    REWRITE_TAC[P2B_GSPLIT_SLICE_BOUND_ROUTE_STATEMENT; P2B_GSPLIT_SLICE_BOUND_STATEMENT] THEN
    ASM_REWRITE_TAC[P2BPL_POINT_LIMIT; P2BPL_ORBIT_LIMIT] THEN
    DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                               `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                               `&1`; `Y:B->real^3`; `&0`]) THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BRD_ANC_SCALAR_POS THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    UNDISCH_TAC `p2b_gsplit (top,atlas) (g:real->B->real^3^3) {s | s < &1} Y` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    UNDISCH_TAC `p2b_gsplit (top,atlas) (g:real->B->real^3^3) {s | s < &1} Y` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* The main theorem, conditional on P2B_REQ_CYL_FROM_LEAF_STATEMENT.         *)
(* ========================================================================= *)

(* P2BRD.R8 The route of SPLIT_ROUND, conditional on                       *)
(* P2B_REQ_CYL_FROM_LEAF_STATEMENT (proved in pc_p2b_cylleaf).  For a      *)
(* split class flow g on s < b: g1 = g(. + b - 1) is a kappa-solution      *)
(* (P2BRD_KSOL_OF_SPLIT); THM_9_11 gives a flow limit of its views on      *)
(* s < 1 with the shrinker equation; the slice at 0                        *)
(* (P2BX0R_FLOW_TO_SLICE_AT) carries the limit Y of X (P2BPL_LIMIT_FIELD); *)
(* the flow limit is split by Y (P2BRD_LIMIT_GSPLIT), so                   *)
(* P2B_GSPLIT_SLICE_BOUND_ROUTE and P2B_SHRINKER_SPLIT_CYL give the        *)
(* soliton model (p, lam) (P2BRD_SOLITON_MODEL); P2BKL_LEAF_ROUND with the *)
(* S^2 entropy statement gives the round leaf data of g1 with reference    *)
(* metric g(b - 1); P2B_REQ_CYL_FROM_LEAF_STATEMENT gives the cylinder     *)
(* model of g1(. + s0 - (b - 1)) = g(. + s0).                              *)

let P2BRD_SPLIT_ROUND_FROM_CYL = prove
 (`!w:B->bool.
     P2B_REQ_CYL_FROM_LEAF_STATEMENT w ==> P2B_SPLIT_ROUND_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_SPLIT_ROUND_ROUTE_STATEMENT; P2B_SPLIT_ROUND_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "cyl") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "t911")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "anc") (LABEL_TAC "ent"))))) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `X:B->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "af") (CONJUNCTS_THEN2 (LABEL_TAC "lo")
    (LABEL_TAC "gsp"))) THEN
  X_GEN_TAC `s0:real` THEN DISCH_TAC THEN
  (* the shifted class flow g1 = g(. + b - 1) on t < 1 *)
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `X:B->real^3`] P2BRD_SHIFTED_CLASS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rf1")
    (CONJUNCTS_THEN2 (LABEL_TAC "cp1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rpu")
    (CONJUNCTS_THEN2 (LABEL_TAC "fc") (LABEL_TAC "rpos")))))))))))) THEN
  SUBGOAL_THEN
   `!s. s < &1 ==> p2b_parallel_on atlas ((g:real->B->real^3^3)(s + (b - &1))) (topspace top) X`
  (LABEL_TAC "par1") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "rpu" (MP_TAC o C MATCH_MP (ASSUME `s < &1`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* g1 is a kappa-solution *)
  MP_TAC(SPEC `w:B->bool` P2BRD_KSOL_OF_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                             `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                             `b:real`; `X:B->real^3`; `b - &1`]) THEN
  ASM_REWRITE_TAC[REAL_ARITH `b - &1 < b`] THEN DISCH_TAC THEN
  (* THM_9_11 *)
  USE_THEN "t911" (MP_TAC o GEN_REWRITE_RULE I [P2B_THM_9_11_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                             `atlas:((B->bool)#(B->real^3))->bool`;
                             `\t. (g:real->B->real^3^3)(t + (b - &1))`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->real` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `f:real->B->real` STRIP_ASSUME_TAC))))))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2C_FLOW_LIMIT_ON_WITH] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_flow_limit_on")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` (LABEL_TAC "fl"))) THEN
  SUBGOAL_THEN `!s. s < &1 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`
  (LABEL_TAC "rml") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BKL_RF_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `&1`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2b_ancflow0 kappa (top',atlas') (g':real->B->real^3^3) (&1)` THEN
    SIMP_TAC[p2b_ancflow0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xl:B) IN topspace top'` ASSUME_TAC THENL
   [USE_THEN "fl" (MP_TAC o GEN_REWRITE_RULE I [p2c_flow_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the times *)
  MP_TAC(SPEC `tau:num->real` P2BRD_TAU_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "tf") THEN
  SUBGOAL_THEN `!k. --((tau:num->real) k) <= &0 /\ --(tau k) < &1` (LABEL_TAC "tn") THENL
   [USE_THEN "tf" (MP_TAC o SPEC `0`) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* the slice limit at time 0 *)
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + (b - &1)))`;
                 `q:num->B`; `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`;
                 `{s:real | s < &1}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`]
                P2BX0R_FLOW_TO_SLICE_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN USE_THEN "rml" MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "sl0")) THEN
  USE_THEN "tf" (STRIP_ASSUME_TAC o SPEC `N:num`) THEN
  SUBGOAL_THEN
   `!n. rfs_vtop (p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + (b - &1))))
                 (--((tau:num->real)(n + N))) = top /\
        rfs_vatlas (p2b_kview (top,atlas) (\t. g(t + (b - &1)))) (--(tau(n + N))) = atlas /\
        rfs_vmetric (p2b_kview (top,atlas) (\t. g(t + (b - &1)))) (--(tau(n + N))) =
        g(--(tau(n + N)) + (b - &1)) /\
        --(tau(n + N)) < &1`
  (LABEL_TAC "vw0") THENL
   [GEN_TAC THEN USE_THEN "tn" (STRIP_ASSUME_TAC o SPEC `n + N:num`) THEN
    ASM_SIMP_TAC[P2BRD_KVIEW_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. IMAGE ((phi:num->B->B)(n + N)) ((W:num->B->bool)(n + N)) SUBSET topspace top`
  (LABEL_TAC "im0") THENL
   [GEN_TAC THEN USE_THEN "sl0" (MP_TAC o BETA_RULE o MATCH_MP P2BRD_SLICE_FACTS) THEN
    USE_THEN "vw0" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* P2BPL_LIMIT_FIELD at time 0: the limit field Y *)
  MP_TAC(ISPECL [`UNIV:B->bool`; `UNIV:B->bool`] P2BPL_LIMIT_FIELD) THEN
  REWRITE_TAC[P2BPL_LIMIT_FIELD_STATEMENT] THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`\n:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + (b - &1)))`;
    `\n. (q:num->B)(n + N)`; `\n. --((tau:num->real)(n + N))`; `\n. inv((tau:num->real)(n + N))`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `(g':real->B->real^3^3) (&0)`;
    `xl:B`; `\n. (W:num->B->bool)(n + N)`; `\n. (phi:num->B->B)(n + N)`;
    `\n:num. (X:B->real^3)`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [USE_THEN "sl0" (fun th -> REWRITE_TAC[th]) THEN X_GEN_TAC `n:num` THEN
    USE_THEN "vw0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "vw0" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `n:num`) THEN
    DISCH_TAC THEN
    USE_THEN "rpu" (MP_TAC o C MATCH_MP (ASSUME `--((tau:num->real)(n + N)) < &1`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "im0" (MP_TAC o SPEC `n:num`) THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BRD_PARALLEL_ON_SUBSET THEN EXISTS_TAC `topspace top:B->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `Y:B->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0")))))) THEN
  USE_THEN "c0" (LABEL_TAC "c0a" o REWRITE_RULE[P2B_KVIEW_SLICE]) THEN
  (* the flow limit is split by Y *)
  MP_TAC(ISPECL [`\k:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + (b - &1)))`;
                 `q:num->B`; `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `X:B->real^3`;
                 `N:num`; `sub:num->num`; `Y:B->real^3`] P2BRD_LIMIT_GSPLIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN DISCH_TAC THEN
    USE_THEN "tf" (MP_TAC o C MATCH_MP (ASSUME `s < &1`) o SPECL [`n:num`; `s:real`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `N:num`) THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[P2BRD_KVIEW_AT; REAL_LT_IMP_LE] THEN
    USE_THEN "rpu" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* the soliton model *)
  MP_TAC(SPEC `w:B->bool` P2BRD_SOLITON_MODEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                             `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                             `f:real->B->real`; `Y:B->real^3`; `xl:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BRD_LIMIT_LORIENT THEN
    MAP_EVERY EXISTS_TAC
     [`\n:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + (b - &1)))`;
      `\n. (q:num->B)(n + N)`; `\n. --((tau:num->real)(n + N))`;
      `\n. inv((tau:num->real)(n + N))`; `(g':real->B->real^3^3) (&0)`; `xl:B`;
      `\n. (W:num->B->bool)(n + N)`; `\n. (phi:num->B->B)(n + N)`;
      `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->B` (X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC)) THEN
  (* P2BKL_LEAF_ROUND: the round leaf data of g1 *)
  MP_TAC(ISPECL [`w:B->bool`;
                 `\n:num. p2b_kview (top,atlas) (\t. (g:real->B->real^3^3)(t + (b - &1)))`;
                 `\n. (q:num->B)(n + N)`; `\n. --((tau:num->real)(n + N))`;
                 `\n. inv((tau:num->real)(n + N))`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`;
                 `\n. (W:num->B->bool)(n + N)`; `\n. (phi:num->B->B)(n + N)`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t. (g:real->B->real^3^3)(t + (b - &1))`; `(g:real->B->real^3^3)(b - &1)`;
                 `&1`; `X:B->real^3`; `sub:num->num`; `Y:B->real^3`; `p:real^3->B`; `lam:real`]
                P2BKL_LEAF_ROUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2b_gsplit (top',atlas') (g':real->B->real^3^3) {s | s < &1} Y` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:B->bool` (X_CHOOSE_THEN `h0:B->real` (X_CHOOSE_THEN `u0:real`
    (X_CHOOSE_THEN `psi1:real^3->B` (X_CHOOSE_THEN `psi1':B->real^3` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `topspace (subtopology top (lvs_set V0 h0 u0)) = lvs_set (V0:B->bool) h0 u0`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC(SET_RULE `(s:B->bool) SUBSET t ==> t INTER s = s`) THEN
    MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?psi1 psi1'. mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                   (sphere(vec 0,&1)) (subtopology top (lvs_set V0 h0 u0))
                   (lvs_atlas top (atlas:((B->bool)#(B->real^3))->bool) V0 h0 u0)
                   (lvs_set V0 h0 u0) psi1 psi1'`
  ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`psi1:real^3->B`; `psi1':B->real^3`] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* P2B_REQ_CYL_FROM_LEAF_STATEMENT: the cylinder model *)
  USE_THEN "cyl" (MP_TAC o GEN_REWRITE_RULE I [P2B_REQ_CYL_FROM_LEAF_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `\t. (g:real->B->real^3^3)(t + (b - &1))`;
                             `(g:real->B->real^3^3)(b - &1)`; `&1`; `X:B->real^3`;
                             `V0:B->bool`; `h0:B->real`; `u0:real`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s0 - (b - &1)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The route theorem, with P2B_CYL_FROM_LEAF (pc_p2b_cylleaf) for            *)
(* P2B_REQ_CYL_FROM_LEAF_STATEMENT.                                          *)
(* ========================================================================= *)

let P2B_SPLIT_ROUND_ROUTE = prove
 (`!w:B->bool. P2B_SPLIT_ROUND_ROUTE_STATEMENT w`,
  MESON_TAC[P2BRD_SPLIT_ROUND_FROM_CYL; P2B_CYL_FROM_LEAF]);;

