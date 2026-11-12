(* ========================================================================= *)
(* pc_p2a_flow: the flow level of the Part 2A L-geometry, first file.        *)
(* MT Ch 7 for Ricci flows that are complete with bounded curvature on       *)
(* [a,b] (p2a_cbflow of pc_p2a_fldefs): FL1 P2A_FLOW_PROPER (generic in N: R *)
(* bounded below, the metric comparison MT (7.1), distance along piecewise   *)
(* C^1 curves, closed balls of the complete metric at b), the                *)
(* admissible-curve existence lemma for connected flows, rescaling of        *)
(* complete flows of bounded curvature and FL7 P2A_FLOW_SCALING (N = 3,      *)
(* through FL0 = P2AW_FLOW_VIEW_3).                                          *)
(* ========================================================================= *)

needs "src/pc_p2a_fldefs.ml";;
needs "src/pc_p2a_wk1.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_p2a_c712.ml";;

prioritize_real();;
type_invention_error := true;;

(* Assumption selection by constant name (a bare quotation of a polymorphic *)
(* constant has fresh type variables and would not match).                  *)

let p2au_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* ------------------------------------------------------------------------- *)
(* Basic facts on complete flows of bounded curvature (generic in N): the    *)
(* components of p2a_cbflow, the scalar curvature bound abs R <= n(n-1)      *)
(* abs Rm (P2AZ_MFD_SCALAR_ABS of pc_p2a_smz, made dimension-generic with    *)
(* the same proof), R and Ric bounded on M x [a,b], and MT (7.1) relative to *)
(* the top time b (from RFA_UPTO_QFORM_EQUIV of pc_rfa_slmfd).               *)
(* ------------------------------------------------------------------------- *)

let P2AU_CBFLOW_FACTS = prove
 (`!top atlas a b (g:real->A->real^N^N).
     p2a_cbflow (top,atlas) a b g
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ a < b /\
         ricci_flow_on (top,atlas) a b g /\ ricci_flow_from (top,atlas) a b g /\
         p2a_flow_upto (top,atlas) a b g /\
         (!t. a <= t /\ t <= b ==> riemannian_metric atlas (g t)) /\
         (!t. a <= t /\ t <= b ==> mfd_complete (top,atlas) (g t)) /\
         (?K. &0 <= K /\
              !t y. a <= t /\ t <= b /\ y IN topspace top
                    ==> mfd_rm_norm atlas (g t) y <= K)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_cbflow] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2a_flow_upto]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a < t /\ t < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `max (&0) K` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* abs R <= n(n-1) abs Rm: R is the trace of Ric in an orthonormal frame     *)
(* (LRG_FRAME, P2B_LSCALAR_FRAME), and abs Ric(e,e) <= (n-1) abs Rm          *)
(* (P2AP_MFD_RICCI_ABS).  The proof of P2AZ_MFD_SCALAR_ABS with N generic.   *)

let P2AU_MFD_SCALAR_ABS = prove
 (`!top atlas (g:A->real^N^N) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> abs(mfd_scalar atlas g y) <=
         &(dimindex(:N) * (dimindex(:N) - 1)) * mfd_rm_norm atlas g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                             (G:real^N->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) y IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `G:real^N->real^N^N`;
                 `SND(c:(A->bool)#(A->real^N)) y`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:A->real^N^N) y = transp(M:real^N^N) ** M` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^N^N) y =
    sum(1..dimindex(:N))
       (\j. mfd_ricci atlas g y (matrix_inv(M:real^N^N) ** basis j) (matrix_inv M ** basis j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_scalar; mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_LSCALAR_FRAME THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                 (\j. &(dimindex(:N) - 1) * mfd_rm_norm atlas (g:A->real^N^N) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y:A`; `matrix_inv(M:real^N^N) ** basis j`] P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`transp(M:real^N^N) ** M`; `M:real^N^N`; `j:num`; `j:num`]
                  P2B_FRAME_ORTHO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]]);;

(* The 3-d form of pc_p2a_smz is an instance.                                *)

let P2AU_MFD_SCALAR_ABS_3 = prove
 (`!top atlas (g:A->real^3^3) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> abs(mfd_scalar atlas g y) <= &6 * mfd_rm_norm atlas g y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AU_MFD_SCALAR_ABS) THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* R and Ric are bounded on M x [a,b].                                       *)

let P2AU_CBFLOW_CURV = prove
 (`!top atlas a b (g:real->A->real^N^N).
     p2a_cbflow (top,atlas) a b g
     ==> ?K. &0 <= K /\
             (!t y. a <= t /\ t <= b /\ y IN topspace top
                    ==> --(&(dimindex(:N) * (dimindex(:N) - 1)) * K) <=
                        mfd_scalar atlas (g t) y) /\
             (!t y w. a <= t /\ t <= b /\ y IN topspace top
                      ==> abs(mfd_ricci atlas (g t) y w w) <=
                          (&(dimindex(:N) - 1) * K) * (w dot (g t y ** w)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN STRIP_TAC THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x y z. abs x <= y /\ y <= z ==> --z <= x`) THEN
    EXISTS_TAC `&(dimindex(:N) * (dimindex(:N) - 1)) *
                mfd_rm_norm atlas ((g:real->A->real^N^N) t) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AU_MFD_SCALAR_ABS THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N) - 1) * mfd_rm_norm atlas ((g:real->A->real^N^N) t) y *
                (w dot (g t y ** w))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AP_MFD_RICCI_ABS THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_SIMP_TAC[]]]]);;

(* MT (7.1) relative to the top time: g(b) <= E g(t) for a < t <= b.         *)

let P2AU_CBFLOW_QFORM_TOP = prove
 (`!top atlas a b (g:real->A->real^N^N).
     p2a_cbflow (top,atlas) a b g
     ==> ?E. &1 <= E /\
             !t y w. a < t /\ t <= b /\ y IN topspace top
                     ==> w dot (g b y ** w) <= E * (w dot (g t y ** w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_CURV) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  ABBREV_TAC `Kr = &(dimindex(:N) - 1) * K` THEN
  SUBGOAL_THEN `&0 <= Kr` ASSUME_TAC THENL
   [EXPAND_TAC "Kr" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  EXISTS_TAC `exp(&2 * Kr * (b - a))` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`; `w:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `y:A`; `t:real`; `Kr:real`; `w:real^N`]
                RFA_UPTO_QFORM_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `p2a_flow_upto (top,atlas) a b (g:real->A->real^N^N)` THEN
      REWRITE_TAC[p2a_flow_upto] THEN SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        p2au_mentions "mfd_ricci" th && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REAL_ARITH `!x y z. y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Curves that are piecewise C^1 in every chart (the corner condition of    *)
(* p2a_pc1 for a constant atlas) are C^1 curves (mfd_c1_curve) on every     *)
(* subinterval without corners inside, and the distance between two of      *)
(* their points is at most the integral of any majorant of the lengths of   *)
(* the corner-free pieces (split at the finitely many corners;              *)
(* MFD_DIST_LE_LENGTH, MFD_DIST_TRIANGLE).  Generic in N.                   *)
(* ------------------------------------------------------------------------- *)

(* The neighbourhood form of continuity (clause 4 of p2a_adm) gives         *)
(* continuity on every subinterval.                                          *)

let P2AU_CONT_MAP_INTERVAL = prove
 (`!top (gamma:real->A) a b c d.
     a <= c /\ d <= b /\
     (!s. a <= s /\ s <= b ==> gamma s IN topspace top) /\
     (!s0 O. a <= s0 /\ s0 <= b /\ open_in top O /\ gamma s0 IN O
             ==> ?e. &0 < e /\ !s. a <= s /\ s <= b /\ abs(s - s0) < e ==> gamma s IN O)
     ==> continuous_map (subtopology euclideanreal (real_interval[c,d]),top) gamma`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `O:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `u0:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u0:real`; `O:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `real_interval(u0 - e,u0 + e) INTER real_interval[c,d]` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `real_interval(u0 - e,u0 + e)` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL];
    REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTER; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The times in [e1,e2] at which the curve lies in an open set are          *)
(* relatively open (as GRGD_CURVE_TIMES_OPEN_IN, from continuity only).      *)

let P2AU_TIMES_OPEN_IN = prove
 (`!top (gamma:real->A) e1 e2 W.
     continuous_map (subtopology euclideanreal (real_interval[e1,e2]),top) gamma /\
     open_in top W
     ==> open_in (subtopology euclidean (interval[lift e1,lift e2]))
                 {s | s IN interval[lift e1,lift e2] /\ gamma(drop s) IN W}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (interval[lift e1,lift e2]),top)
                               ((gamma:real->A) o drop)` MP_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[GSYM CONTINUOUS_MAP_DROP_EQ_GEN];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `W:A->bool` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] OPEN_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM]);;

(* No corner inside (e1,e2): a C^1 curve on [e1,e2] (GRGD_C1_LOCAL with the *)
(* one-sided sets at the ends and the two-sided sets inside).               *)

let P2AU_PIECE_C1 = prove
 (`!top atlas (gamma:real->A) b0 P e1 e2.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     (!s. &0 <= s /\ s <= b0 ==> gamma s IN topspace top) /\
     (!s0 O. &0 <= s0 /\ s0 <= b0 /\ open_in top O /\ gamma s0 IN O
             ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= b0 /\ abs(s - s0) < d ==> gamma s IN O) /\
     (!s0 c. &0 < s0 /\ s0 <= b0 /\ c IN atlas /\ gamma s0 IN FST c
             ==> ?d. &0 < d /\
                     continuously_differentiable 1
                       {s | s0 - d <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s))) /\
                     continuously_differentiable 1
                       {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b0 /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s))) /\
                     (~(s0 IN P)
                      ==> continuously_differentiable 1
                            {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                                 &0 < drop s /\ drop s <= b0 /\ gamma(drop s) IN FST c}
                            (\s. SND c (gamma(drop s))))) /\
     &0 < e1 /\ e1 < e2 /\ e2 <= b0 /\ (!s. e1 < s /\ s < e2 ==> ~(s IN P))
     ==> mfd_c1_curve (top,atlas) gamma e1 e2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pc") STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[e1,e2]),top)
                               (gamma:real->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_CONT_MAP_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b0:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_c1_curve] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in top (FST(c:(A->bool)#(A->real^N)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[GRGD_ATLAS_CHART]; ALL_TAC] THEN
  MATCH_MP_TAC GRGD_C1_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`e1:real`; `e2:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AU_TIMES_OPEN_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `e1 <= drop x /\ drop x <= e2 /\
                (gamma:real->A)(drop x) IN FST(c:(A->bool)#(A->real^N))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `x IN {s | s IN interval[lift e1,lift e2] /\
                          (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "pc" (MP_TAC o SPECL [`drop x`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "L") (CONJUNCTS_THEN2 (LABEL_TAC "R") (LABEL_TAC "T"))))) THEN
  EXISTS_TAC `{s | s IN interval[lift e1,lift e2] /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))} INTER
              ball(x:real^1,d)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC P2AU_TIMES_OPEN_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `drop x = e1` THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{s | drop x <= drop s /\ drop s <= drop x + d /\ drop s <= b0 /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; IN_BALL;
                DIST_REAL; GSYM drop] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `drop x = e2` THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{s | drop x - d <= drop s /\ drop s <= drop x /\ &0 < drop s /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; IN_BALL;
                DIST_REAL; GSYM drop] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `{s | drop x - d <= drop s /\ drop s <= drop x + d /\ &0 < drop s /\
                   drop s <= b0 /\
                   (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; IN_BALL;
                DIST_REAL; GSYM drop] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "T" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The distance bound along a piecewise C^1 curve, by induction on the      *)
(* number of corners inside the interval.                                   *)

let P2AU_PIECEWISE_DIST = prove
 (`!top atlas (G:A->real^N^N) (gamma:real->A) b0 P w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     (!s. &0 <= s /\ s <= b0 ==> gamma s IN topspace top) /\
     (!s0 O. &0 <= s0 /\ s0 <= b0 /\ open_in top O /\ gamma s0 IN O
             ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= b0 /\ abs(s - s0) < d ==> gamma s IN O) /\
     FINITE P /\
     (!s0 c. &0 < s0 /\ s0 <= b0 /\ c IN atlas /\ gamma s0 IN FST c
             ==> ?d. &0 < d /\
                     continuously_differentiable 1
                       {s | s0 - d <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s))) /\
                     continuously_differentiable 1
                       {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b0 /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s))) /\
                     (~(s0 IN P)
                      ==> continuously_differentiable 1
                            {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                                 &0 < drop s /\ drop s <= b0 /\ gamma(drop s) IN FST c}
                            (\s. SND c (gamma(drop s))))) /\
     (!c d. &0 < c /\ c < d /\ d <= b0 /\ mfd_c1_curve (top,atlas) gamma c d
            ==> mfd_length atlas G gamma c d <= real_integral (real_interval[c,d]) w) /\
     (!c d. &0 < c /\ c <= d /\ d <= b0 ==> w real_integrable_on real_interval[c,d])
     ==> !e1 e2. &0 < e1 /\ e1 <= e2 /\ e2 <= b0
                 ==> mfd_joinable (top,atlas) (gamma e1) (gamma e2) /\
                     mfd_dist (top,atlas) G (gamma e1) (gamma e2) <=
                     real_integral (real_interval[e1,e2]) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pc") (CONJUNCTS_THEN2 (LABEL_TAC "len")
     (LABEL_TAC "int")))))))) THEN
  SUBGOAL_THEN
   `!n e1 e2. CARD {s | s IN P /\ e1 < s /\ s < e2} = n /\
              &0 < e1 /\ e1 <= e2 /\ e2 <= b0
              ==> mfd_joinable (top,atlas) ((gamma:real->A) e1) (gamma e2) /\
                  mfd_dist (top,atlas) (G:A->real^N^N) (gamma e1) (gamma e2) <=
                  real_integral (real_interval[e1,e2]) w`
  (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`e1:real`; `e2:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `e1:real = e2` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
    SUBGOAL_THEN `(gamma:real->A) e2 IN topspace top` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL; REAL_INTEGRAL_REFL; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 < e2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `?c. c IN P /\ e1 < c /\ c < e2` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `FINITE {s | s IN P /\ e1 < s /\ s < e2}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:real->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "IH" (MP_TAC o SPEC `CARD {s | s IN P /\ e1 < s /\ s < c}`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM] THEN
      CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[REAL_LT_REFL];
      DISCH_THEN(MP_TAC o SPECL [`e1:real`; `c:real`])] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "IH" (MP_TAC o SPEC `CARD {s | s IN P /\ c < s /\ s < e2}`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `n:num`)) (concl th))) THEN
      MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM] THEN
      CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[REAL_LT_REFL];
      DISCH_THEN(MP_TAC o SPECL [`c:real`; `e2:real`])] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) c` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (G:A->real^N^N) ((gamma:real->A) e1) (gamma c) +
                mfd_dist (top,atlas) G (gamma c) (gamma e2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real->real`; `e1:real`; `e2:real`; `c:real`]
                  REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN USE_THEN "int" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) e1 e2` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_PIECE_C1 THEN
    MAP_EVERY EXISTS_TAC [`b0:real`; `P:real->bool`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length atlas (G:A->real^N^N) (gamma:real->A) e1 e2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
    USE_THEN "len" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* FL1 (MT p. 149-150, (7.1) and the energy bound in the proof of Lemma     *)
(* 7.2).  For an admissible curve of the flow view with L-length L, on      *)
(* every corner-free piece the g(b)-speed is at most sqrt(E)                *)
(* (h + s^(-1/2)) / 2 with h = L-integrand + C sqrt(s) >= 0, so             *)
(* the g(b)-distance between two points of the curve is at most sqrt(E)     *)
(* (L + C tau sqrt(tau) + 2 sqrt(tau)) / 2; the curve stays in a            *)
(* closed g(b)-ball around p, compact by completeness at b.  Generic in N.  *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_VIEW_PARTS = prove
 (`!top atlas J (g:real->A->real^N^N) t.
     p2a_vtop (p2a_flow_view (top,atlas) J g) t =
     (if t IN J then top else discrete_topology {}) /\
     p2a_vatlas (p2a_flow_view (top,atlas) J g) t = atlas /\
     p2a_vmetric (p2a_flow_view (top,atlas) J g) t = g t`,
  REWRITE_TAC[p2a_flow_view; p2a_vtop; p2a_vatlas; p2a_vmetric]);;

let P2AU_FLOW_VTOP = prove
 (`!top atlas a b (g:real->A->real^N^N) t.
     a <= t /\ t <= b
     ==> p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) g) t = top`,
  SIMP_TAC[P2AU_FLOW_VIEW_PARTS; IN_REAL_INTERVAL]);;

(* p2a_pc1 for a flow view: the atlas condition of the one-sided sets is    *)
(* trivially true.                                                           *)

let P2AU_PC1_FLOW = prove
 (`!top atlas J (g:real->A->real^N^N) tt gamma a0 b0 P.
     p2a_pc1 (p2a_flow_view (top,atlas) J g) tt gamma a0 b0 P <=>
     FINITE P /\
     !s0 c. a0 < s0 /\ s0 <= b0 /\ c IN atlas /\ gamma s0 IN FST c
            ==> ?d. &0 < d /\
                    continuously_differentiable 1
                      {s | s0 - d <= drop s /\ drop s <= s0 /\ a0 < drop s /\
                           gamma(drop s) IN FST c}
                      (\s. SND c (gamma(drop s))) /\
                    continuously_differentiable 1
                      {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b0 /\
                           gamma(drop s) IN FST c}
                      (\s. SND c (gamma(drop s))) /\
                    (~(s0 IN P)
                     ==> continuously_differentiable 1
                           {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                                a0 < drop s /\ drop s <= b0 /\ gamma(drop s) IN FST c}
                           (\s. SND c (gamma(drop s))))`,
  REWRITE_TAC[p2a_pc1; P2AU_FLOW_VIEW_PARTS]);;

(* The admissible curves of a flow view at backward times in (0, b - a).    *)

let P2AU_ADM_FLOW = prove
 (`!top atlas a b (g:real->A->real^N^N) p tau gamma.
     tau < b - a /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma
     ==> &0 < tau /\ gamma(&0) = p /\
         (!s. &0 <= s /\ s <= tau ==> gamma s IN topspace top) /\
         (!s0 O. &0 <= s0 /\ s0 <= tau /\ open_in top O /\ gamma s0 IN O
                 ==> ?d. &0 < d /\
                         !s. &0 <= s /\ s <= tau /\ abs(s - s0) < d ==> gamma s IN O) /\
         (?P. FINITE P /\
              !s0 c. &0 < s0 /\ s0 <= tau /\ c IN atlas /\ gamma s0 IN FST c
                     ==> ?d. &0 < d /\
                             continuously_differentiable 1
                               {s | s0 - d <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                                    gamma(drop s) IN FST c}
                               (\s. SND c (gamma(drop s))) /\
                             continuously_differentiable 1
                               {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= tau /\
                                    gamma(drop s) IN FST c}
                               (\s. SND c (gamma(drop s))) /\
                             (~(s0 IN P)
                              ==> continuously_differentiable 1
                                    {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                                         &0 < drop s /\ drop s <= tau /\
                                         gamma(drop s) IN FST c}
                                    (\s. SND c (gamma(drop s))))) /\
         (\s. sqrt s * (mfd_scalar atlas (g(b - s)) (gamma s) +
                        mfd_speed atlas (g(b - s)) gamma (&0) tau s pow 2))
         real_integrable_on real_interval[&0,tau] /\
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau =
         real_integral (real_interval[&0,tau])
           (\s. sqrt s * (mfd_scalar atlas (g(b - s)) (gamma s) +
                          mfd_speed atlas (g(b - s)) gamma (&0) tau s pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= tau
        ==> p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N))
                     (b - s) = top`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AU_FLOW_VTOP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N))
                    b (gamma:real->A) tau =
    (\s. sqrt s * (mfd_scalar atlas (g(b - s)) (gamma s) +
                   mfd_speed atlas (g(b - s)) gamma (&0) tau s pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2a_L_integrand; P2AU_FLOW_VIEW_PARTS]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2a_adm] o check (p2au_mentions "p2a_adm")) THEN
  ASM_REWRITE_TAC[P2AU_PC1_FLOW; p2a_L_length] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && p2au_mentions "topspace" th &&
      not (p2au_mentions "open_in" th) && not (p2au_mentions "p2a_smooth" th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `O:A->bool`] o check (fun th ->
      is_forall(concl th) && p2au_mentions "open_in" th)) THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `P:real->bool` THEN ASM_REWRITE_TAC[]]);;

(* AM-GM: x <= (sqrt s x^2 + 1/sqrt s)/2.                                   *)

let P2AU_AMGM = prove
 (`!x s. &0 < s ==> x <= (sqrt s * x pow 2 + inv(sqrt s)) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt s` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt s * x pow 2 + inv(sqrt s) - &2 * x =
                (sqrt s * x - &1) pow 2 / sqrt s` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < sqrt s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (sqrt s * x - &1) pow 2 / sqrt s` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The integral of s^(-1/2) over [e1,e2] with e1 > 0.                       *)

let P2AU_INV_SQRT_INTEGRAL = prove
 (`!e1 e2. &0 < e1 /\ e1 <= e2
           ==> ((\s. inv(sqrt s)) has_real_integral (&2 * sqrt e2 - &2 * sqrt e1))
               (real_interval[e1,e2])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. &2 * sqrt s`; `\s. inv(sqrt s)`; `e1:real`; `e2:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt x) = &2 * inv(&2 * sqrt x)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt x` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT]);;

(* Comparison of integrals off the end points.                              *)

let P2AU_REAL_INTEGRAL_LE_INTERIOR = prove
 (`!f g c d.
     f real_integrable_on real_interval[c,d] /\ g real_integrable_on real_interval[c,d] /\
     (!x. c < x /\ x < d ==> f x <= g x)
     ==> real_integral (real_interval[c,d]) f <= real_integral (real_interval[c,d]) g`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f' = \x. if x = c \/ x = d then g x else (f:real->real) x` THEN
  SUBGOAL_THEN `real_negligible {c,d}` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NEGLIGIBLE_INSERT; REAL_NEGLIGIBLE_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN real_interval[c,d] DIFF {c,d} ==> (f':real->real) x = f x`
  ASSUME_TAC THENL
   [EXPAND_TAC "f'" THEN REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[c,d]) f = real_integral (real_interval[c,d]) f'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{c:real,d}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `{c:real,d}`; `real_interval[c,d]`]
                  REAL_INTEGRABLE_SPIKE) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "f'" THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The distance bound along admissible curves of a flow view and FL1.       *)
(* ------------------------------------------------------------------------- *)

let P2AU_ADM_DIST = prove
 (`!top atlas a b (g:real->A->real^N^N).
     p2a_cbflow (top,atlas) a b g
     ==> ?D0 D1. &0 <= D0 /\ &0 <= D1 /\
           !p tau gamma e1 e2.
              tau < b - a /\
              p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
              &0 < e1 /\ e1 <= e2 /\ e2 <= tau
              ==> mfd_joinable (top,atlas) (gamma e1) (gamma e2) /\
                  mfd_dist (top,atlas) (g b) (gamma e1) (gamma e2) <=
                  D0 * (p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                     b gamma tau + D1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_CURV) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `E:real` STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_QFORM_TOP) THEN
  ABBREV_TAC `C = &(dimindex(:N) * (dimindex(:N) - 1)) * K` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `sqrt E / &2` THEN
  EXISTS_TAC `C * (b - a) * sqrt(b - a) + &2 * sqrt(b - a)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; SQRT_POS_LE]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `tau:real`; `gamma:real->A`; `e1:real`; `e2:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `p:A`; `tau:real`; `gamma:real->A`] P2AU_ADM_FLOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `P:real->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
  ABBREV_TAC
   `f = \s. sqrt s * (mfd_scalar atlas ((g:real->A->real^N^N)(b - s)) ((gamma:real->A) s) +
                      mfd_speed atlas (g(b - s)) gamma (&0) tau s pow 2)` THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= tau ==> --(C * sqrt s) <= (f:real->real) s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "f" THEN
    SUBGOAL_THEN `--C <= mfd_scalar atlas ((g:real->A->real^N^N)(b - s)) ((gamma:real->A) s)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        p2au_mentions "mfd_scalar" th && is_forall(concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `mfd_speed atlas ((g:real->A->real^N^N)(b - s)) (gamma:real->A) (&0) tau s`
                REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&0 <= sqrt s` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `--(C * x) <= x * (r + q) <=> &0 <= x * (r + C + q)`] THEN
    REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h = \s. (f:real->real) s + C * sqrt s` THEN
  SUBGOAL_THEN `!c d. real_interval[c,d] SUBSET real_interval[&0,tau]
                      ==> (h:real->real) real_integrable_on real_interval[c,d]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[&0,tau]` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[ETA_AX; REAL_CONTINUOUS_ON_SQRT];
    ALL_TAC] THEN
  ABBREV_TAC `w = \s. sqrt E * ((h:real->real) s + inv(sqrt s)) / &2` THEN
  SUBGOAL_THEN `!c d. &0 < c /\ c <= d /\ d <= tau
                      ==> (w:real->real) real_integrable_on real_interval[c,d]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_integrable_on] THEN
      EXISTS_TAC `&2 * sqrt d - &2 * sqrt c` THEN
      MATCH_MP_TAC P2AU_INV_SQRT_INTEGRAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the bound on a corner-free piece *)
  SUBGOAL_THEN
   `!c d. &0 < c /\ c < d /\ d <= tau /\ mfd_c1_curve (top,atlas) (gamma:real->A) c d
          ==> mfd_length atlas ((g:real->A->real^N^N) b) gamma c d <=
              real_integral (real_interval[c,d]) w`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:real`; `d:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC P2AU_REAL_INTEGRAL_LE_INTERIOR THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s /\ s < tau` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`; `c:real`; `d:real`;
                   `&0`; `tau:real`; `s:real`] P2A_VELOCITY_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `v = mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)
                                 (&0) tau s` THEN
    SUBGOAL_THEN
     `v dot ((g:real->A->real^N^N) b ((gamma:real->A) s) ** v) <=
      E * (v dot (g (b - s) (gamma s) ** v))` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `E:real`)) (concl th) && is_forall(concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= v dot ((g:real->A->real^N^N) (b - s) ((gamma:real->A) s) ** v)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `x = mfd_speed atlas ((g:real->A->real^N^N) (b - s)) (gamma:real->A) (&0) tau s` THEN
    SUBGOAL_THEN
     `mfd_speed atlas ((g:real->A->real^N^N) b) (gamma:real->A) c d s <= sqrt E * x`
    ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN REWRITE_TAC[mfd_speed] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt s * x pow 2 <= (h:real->real) s` ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN EXPAND_TAC "f" THEN EXPAND_TAC "x" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `--C <= mfd_scalar atlas ((g:real->A->real^N^N)(b - s)) ((gamma:real->A) s)`
      MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          p2au_mentions "mfd_scalar" th && is_forall(concl th))) THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= sqrt s` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
                                               ALL_TAC] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= sqrt s * (mfd_scalar atlas ((g:real->A->real^N^N)(b - s))
                                    ((gamma:real->A) s) + C)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`x:real`; `s:real`] P2AU_AMGM) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt E * x` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) b`; `gamma:real->A`; `tau:real`; `P:real->bool`;
                 `w:real->real`] P2AU_PIECEWISE_DIST) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real`; `e2:real`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[e1,e2]) w` THEN ASM_REWRITE_TAC[] THEN
  (* the integral of w over [e1,e2] *)
  SUBGOAL_THEN `real_integral (real_interval[e1,e2]) w =
                sqrt E / &2 * (real_integral (real_interval[e1,e2]) h +
                               (&2 * sqrt e2 - &2 * sqrt e1))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `((\s. inv(sqrt s)) has_real_integral (&2 * sqrt e2 - &2 * sqrt e1))
                    (real_interval[e1,e2])` ASSUME_TAC THENL
     [MATCH_MP_TAC P2AU_INV_SQRT_INTEGRAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real->real) real_integrable_on real_interval[e1,e2]` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[REAL_ARITH `sqrt E * (x + y) / &2 = sqrt E / &2 * (x + y)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN
    ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 * y = x / &2 * y`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
                  MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* int_e1^e2 h <= int_0^tau h = L + C int sqrt <= L + C tau sqrt tau *)
  SUBGOAL_THEN `real_integral (real_interval[e1,e2]) h <=
                real_integral (real_interval[&0,tau]) h` ASSUME_TAC THENL
   [SUBGOAL_THEN `!c d. &0 <= c /\ c <= d /\ d <= tau
                        ==> &0 <= real_integral (real_interval[c,d]) h` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
          can (find_term (fun t -> t = `f:real->real`)) (concl th) && is_forall(concl th) &&
          can (find_term (fun t -> t = `C:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real->real`; `&0`; `tau:real`; `e1:real`] REAL_INTEGRAL_COMBINE) THEN
    MP_TAC(ISPECL [`h:real->real`; `e1:real`; `tau:real`; `e2:real`] REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y z. &0 <= x /\ &0 <= z ==> y <= x + y + z`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[&0,tau]) h <=
                real_integral (real_interval[&0,tau]) f + C * tau * sqrt tau`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `real_integral (real_interval[&0,tau]) h =
                  real_integral (real_interval[&0,tau]) f +
                  real_integral (real_interval[&0,tau]) (\s. C * sqrt s)` SUBST1_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[ETA_AX; REAL_CONTINUOUS_ON_SQRT];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,tau]) (\s. C * sqrt tau)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC[ETA_AX; REAL_CONTINUOUS_ON_SQRT];
        X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt tau <= sqrt(b - a) /\ &0 <= sqrt e1 /\ sqrt e2 <= sqrt tau`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_MONO_LE) THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C * tau * sqrt tau <= C * (b - a) * sqrt(b - a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The g(b)-distance from the base point to the points of an admissible     *)
(* curve is bounded in terms of its L-length.                                *)

let P2AU_ADM_PDIST = prove
 (`!top atlas a b (g:real->A->real^N^N).
     p2a_cbflow (top,atlas) a b g
     ==> ?D0 D1. &0 <= D0 /\ &0 <= D1 /\
           !p tau gamma s.
              tau < b - a /\
              p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
              &0 <= s /\ s <= tau
              ==> mfd_joinable (top,atlas) p (gamma s) /\
                  mfd_dist (top,atlas) (g b) p (gamma s) <=
                  D0 * (p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                     b gamma tau + D1) + &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D1:real` STRIP_ASSUME_TAC) o
              MATCH_MP P2AU_ADM_DIST) THEN
  MAP_EVERY EXISTS_TAC [`D0:real`; `D1:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `tau:real`; `gamma:real->A`; `s:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `p:A`; `tau:real`; `gamma:real->A`] P2AU_ADM_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhand(concl th) = `(gamma:real->A)(&0)`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
    SUBGOAL_THEN `(gamma:real->A) tau IN topspace top` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `tau:real`; `gamma:real->A`; `tau:real`; `tau:real`] o
      check (fun th -> can (find_term (fun t -> t = `D0:real`)) (concl th) &&
                       is_forall(concl th))) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; MFD_DIST_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `mfd_ball (top,atlas) ((g:real->A->real^N^N) b) p (&1)`]
    o check (fun th -> can (find_term (fun t -> t = `open_in:(A)topology->(A->bool)->bool`))
                           (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; MFD_BALL_OPEN; MFD_CENTRE_IN_BALL; REAL_LT_01];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e1 = min (s / &2) (d / &2)` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= s /\ e1 < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) e1 IN mfd_ball (top,atlas) ((g:real->A->real^N^N) b) p (&1)`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `tau:real`; `gamma:real->A`; `e1:real`; `s:real`] o
    check (fun th -> can (find_term (fun t -> t = `D0:real`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) ((g:real->A->real^N^N) b) p ((gamma:real->A) e1) +
              mfd_dist (top,atlas) (g b) (gamma e1) (gamma s)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* FL1: curves of bounded L-length from (p,b) stay in a compact set.        *)

let P2AU_FLOW_PROPER = prove
 (`!(u:A->bool) (n:N->bool). P2A_FLOW_PROPER_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_FLOW_PROPER_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `p:A`; `Lb:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D1:real` STRIP_ASSUME_TAC) o
              MATCH_MP P2AU_ADM_PDIST) THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) ((g:real->A->real^N^N) b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `mfd_cball (top,atlas) ((g:real->A->real^N^N) b) p (D0 * (abs Lb + D1) + &1)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) ((g:real->A->real^N^N) b)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau:real`; `gamma:real->A`] THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:A`; `tau:real`; `gamma:real->A`; `s:real`] o
    check (fun th -> can (find_term (fun t -> t = `D0:real`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `D0 * (p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b])
                      (g:real->A->real^N^N)) b (gamma:real->A) tau + D1) + &1` THEN
  ASM_REWRITE_TAC[REAL_LE_RADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Admissibility and L-length depend only on the curve on the parameter     *)
(* interval (any view, generic in N).                                       *)
(* ------------------------------------------------------------------------- *)

let P2AU_ADM_CONG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) gamma'.
     p2a_adm V tt x b gamma /\ (!s. &0 <= s /\ s <= b ==> gamma' s = gamma s)
     ==> p2a_adm V tt x b gamma' /\
         p2a_L_length V tt gamma' b = p2a_L_length V tt gamma b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma':real->A) b`;
    `&0`; `b:real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IE") (LABEL_TAC "LE"))] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[p2a_L_length] THEN USE_THEN "LE" (SUBST1_TAC o SYM) THEN REFL_TAC] THEN
  UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) tt x b (gamma:real->A)` THEN
  REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma':real->A)(&0) = x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      can (find_term (fun t -> t = `gamma':real->A`)) (concl th) && is_forall(concl th))) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tau0:real`; `O:A->bool`] o check (fun th ->
      can (find_term (fun t -> t = `O:A->bool`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    EXISTS_TAC `P:real->bool` THEN
    UNDISCH_TAC `p2a_pc1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                           (real->A->real^N^N)) tt (gamma:real->A) (&0) b P` THEN
    REWRITE_TAC[p2a_pc1] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L")
      (CONJUNCTS_THEN2 (LABEL_TAC "R") (LABEL_TAC "T")))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "L" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma':real->A)(drop s) = gamma(drop s)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[];
      USE_THEN "R" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma':real->A)(drop s) = gamma(drop s)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN USE_THEN "T" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma':real->A)(drop s) = gamma(drop s)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    USE_THEN "IE" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Parabolic rescaling g'(t) = q g(t/q) of complete flows of bounded        *)
(* curvature (generic in N, 2 <= n): ricci_flow_from and p2a_flow_upto      *)
(* (RICCI_FLOW_RESCALE plus the smooth extensions through the affine time   *)
(* change RFB_SMOOTH_TIME_AFFINE), completeness (MFD_COMPLETE_SCALE) and    *)
(* the curvature bound K / q (RFA_MFD_RM_NORM_CMUL_LE).                     *)
(* ------------------------------------------------------------------------- *)

let P2AU_SCALE_TIME = prove
 (`!q t x. &0 < q
           ==> (x < inv q * t <=> q * x < t) /\ (x <= inv q * t <=> q * x <= t) /\
               (inv q * t < x <=> t < q * x) /\ (inv q * t <= x <=> t <= q * x) /\
               inv q * t = t / q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv q * t = t / q` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

let P2AU_RICCI_FLOW_FROM_RESCALE = prove
 (`!top atlas a b (g:real->A->real^N^N) q.
     ricci_flow_from (top,atlas) a b g /\ &0 < q
     ==> ricci_flow_from (top,atlas) (q * a) (q * b) (\t x. q %% g (t / q) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RICCI_FLOW_RESCALE] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(q * a) / q = a` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
    is_forall(concl th) && p2au_mentions "smooth_map_on" th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fm:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `q * e` THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                q % (Fm:real^(1,N)finite_sum->real^(N,N)finite_prod)
                      (pastecart (lift(inv q * drop(fstcart z) + &0)) (sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC RFB_SMOOTH_TIME_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`a - e:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
    ASM_SIMP_TAC[P2AU_SCALE_TIME] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_ADD_RID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv q * t`; `y:real^N`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `vectorize:real^N^N->real^(N,N)finite_prod`))
      (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[P2AU_SCALE_TIME]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL] THEN ASM_SIMP_TAC[P2AU_SCALE_TIME; ETA_AX]]);;

let P2AU_FLOW_UPTO_RESCALE = prove
 (`!top atlas a b (g:real->A->real^N^N) q.
     p2a_flow_upto (top,atlas) a b g /\ &0 < q
     ==> p2a_flow_upto (top,atlas) (q * a) (q * b) (\t x. q %% g (t / q) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_flow_upto] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RICCI_FLOW_RESCALE] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(q * b) / q = b` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN; ricci_flow_on]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o check (fun th ->
    is_forall(concl th) && p2au_mentions "smooth_map_on" th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `q * e` THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                q % (Fx:real^(1,N)finite_sum->real^(N,N)finite_prod)
                      (pastecart (lift(inv q * drop(fstcart z) + &0)) (sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MATCH_MP_TAC RFB_SMOOTH_TIME_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b + e:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
    ASM_SIMP_TAC[P2AU_SCALE_TIME] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_ADD_RID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`inv q * t`; `y:real^N`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `vectorize:real^N^N->real^(N,N)finite_prod`))
      (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[P2AU_SCALE_TIME]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL] THEN ASM_SIMP_TAC[P2AU_SCALE_TIME; ETA_AX]]);;

(* Parabolic rescaling of a complete flow of bounded curvature.              *)

let P2AU_CBFLOW_RESCALE = prove
 (`!top atlas a b (g:real->A->real^N^N) q.
     2 <= dimindex(:N) /\ p2a_cbflow (top,atlas) a b g /\ &0 < q
     ==> p2a_cbflow (top,atlas) (q * a) (q * b) (\t x. q %% g (t / q) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  REWRITE_TAC[p2a_cbflow] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL; P2AU_RICCI_FLOW_FROM_RESCALE; P2AU_FLOW_UPTO_RESCALE] THEN
  SUBGOAL_THEN `!t. q * a <= t /\ t <= q * b ==> a <= t / q /\ t / q <= b`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= t / q /\ t / q <= b` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N)(t / q)`; `q:real`] MFD_COMPLETE_SCALE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC[];
    EXISTS_TAC `K / q` THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= t / q /\ t / q <= b` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `q:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_MFD_RM_NORM_CMUL_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the rescaling of curves (generic in N): C^1 under a linear     *)
(* change of the parameter, the scalar curvature of q g, the velocity of    *)
(* gamma(s/q) at points where gamma is differentiable in a chart.           *)
(* ------------------------------------------------------------------------- *)

let P2AU_CD1_LINEAR_REPARAM = prove
 (`!(f:real^1->real^N) S Tt c.
     continuously_differentiable 1 S f /\ (!y. y IN Tt ==> c % y IN S)
     ==> continuously_differentiable 1 Tt (\y. f(c % y))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f':real^1->real^1->real^N` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^1 h:real^1. (f':real^1->real^1->real^N) (c % y) (c % h)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\y:real^1. (f:real^1->real^N)(c % y)) = f o (\y. c % y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h:real^1. (f':real^1->real^1->real^N) (c % y) (c % h)) =
                  f' (c % y) o (\h. c % h)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `S:real^1->bool` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ASM SET_TAC[]]];
    X_GEN_TAC `h:real^1` THEN
    SUBGOAL_THEN `(\y:real^1. (f':real^1->real^1->real^N) (c % y) (c % h)) =
                  (\x. f' x (c % h)) o (\y. c % y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SCALING];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^1->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

(* The scalar curvature of q g is R / q.                                     *)

let P2AU_MFD_SCALAR_CMUL = prove
 (`!top atlas (G:A->real^N^N) q y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     y IN topspace top /\ &0 < q
     ==> mfd_scalar atlas (\x. q %% G x) y = mfd_scalar atlas G y / q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar; METRIC_LOCAL_CMUL] THEN
  MATCH_MP_TAC LSCALAR_SCALE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                    (FST(chart_at atlas y))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (G:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* The chart curve of gamma(s/q) and its velocity at s, where the chart     *)
(* curve of gamma has derivative v at s/q.                                   *)

let P2AU_VELOCITY_RESCALE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) q s a b v.
     &0 < q /\ a < s / q /\ s / q < b /\
     ((\x. SND(chart_at atlas (gamma(s / q))) (gamma(drop x))) has_vector_derivative v)
       (at (lift(s / q)))
     ==> mfd_velocity atlas (\r. gamma(r / q)) (q * a) (q * b) s = inv q % v /\
         mfd_velocity atlas gamma a b (s / q) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q * a < s /\ s < q * b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `a < s / q` THEN UNDISCH_TAC `s / q < b` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_velocity] THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `lift(s / q) IN interior(interval[lift a,lift b])` ASSUME_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_DERIVATIVE_WITHIN_INTERIOR] THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `lift s IN interior(interval[lift(q * a),lift(q * b)])` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_DERIVATIVE_WITHIN_INTERIOR] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  SUBGOAL_THEN
   `(\x. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A)(s / q)))
           (gamma(drop x / q))) =
    (\x. SND(chart_at atlas (gamma(s / q))) (gamma(drop x))) o (\x. inv q % x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_CMUL] THEN X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % inv q % (v:real^N)) =
                (\h. drop h % v) o (\h. inv q % h)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_CMUL; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
    SUBGOAL_THEN `inv q % lift s = lift(s / q)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM LIFT_CMUL; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM has_vector_derivative]]);;

(* At a time u of (0,b0) off the corner set the chart curve in the          *)
(* preferred chart at gamma(u) has a two-sided derivative.                   *)

let P2AU_PC1_DIFF_AT = prove
 (`!top atlas (gamma:real->A) b0 P u.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     (!s. &0 <= s /\ s <= b0 ==> gamma s IN topspace top) /\
     (!s0 O. &0 <= s0 /\ s0 <= b0 /\ open_in top O /\ gamma s0 IN O
             ==> ?d. &0 < d /\ !s. &0 <= s /\ s <= b0 /\ abs(s - s0) < d ==> gamma s IN O) /\
     (!s0 c. &0 < s0 /\ s0 <= b0 /\ c IN atlas /\ gamma s0 IN FST c
             ==> ?d. &0 < d /\
                     continuously_differentiable 1
                       {s | s0 - d <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s))) /\
                     continuously_differentiable 1
                       {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b0 /\
                            gamma(drop s) IN FST c}
                       (\s. SND c (gamma(drop s))) /\
                     (~(s0 IN P)
                      ==> continuously_differentiable 1
                            {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                                 &0 < drop s /\ drop s <= b0 /\ gamma(drop s) IN FST c}
                            (\s. SND c (gamma(drop s))))) /\
     &0 < u /\ u < b0 /\ ~(u IN P)
     ==> ?v. ((\x. SND(chart_at atlas (gamma u)) (gamma(drop x))) has_vector_derivative v)
             (at (lift u))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ct") (CONJUNCTS_THEN2 (LABEL_TAC "pc") STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) u)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN atlas /\ (gamma:real->A) u IN FST c /\
                open_in top (FST c)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) u`] CHART_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
                    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    ALL_TAC] THEN
  USE_THEN "pc" (MP_TAC o SPECL [`u:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N` (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  DISCH_THEN(MP_TAC o SPEC `lift u`) THEN
  REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "ct" (MP_TAC o SPECL [`u:real`; `FST(c:(A->bool)#(A->real^N))`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (min d d1) (min u (b0 - u))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= d /\ e <= d1 /\ e <= u /\ e <= b0 - u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. SND(c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop x)))
                differentiable (at (lift u))`
  (fun th -> MESON_TAC[th; VECTOR_DERIVATIVE_WORKS]) THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `(f':real^1->real^1->real^N) (lift u)` THEN
  SUBGOAL_THEN `ball(lift u,e) SUBSET
                {s | u - d <= drop s /\ drop s <= u + d /\ &0 < drop s /\ drop s <= b0 /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1. SND(c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
                 `(f':real^1->real^1->real^N) (lift u)`; `lift u`; `ball(lift u,e)`]
                HAS_DERIVATIVE_WITHIN_OPEN) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `{s | u - d <= drop s /\ drop s <= u + d /\ &0 < drop s /\ drop s <= b0 /\
                   (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Rescaling of admissible curves (MT Lemma 6.72): for the flow view of     *)
(* g'(t) = q g(t/q) on [q a, q b], base time q b, the curve gamma(s/q) on   *)
(* [0, q tau] is admissible when gamma is (given the smooth points of the   *)
(* rescaled view, FL0) and has L-length sqrt(q) L(gamma). Generic in N.     *)
(* ------------------------------------------------------------------------- *)

(* Division by q > 0 preserves the window inequalities.                     *)

let P2AU_DIV_LE_IMP = prove
 (`!q x y d. &0 < q
             ==> (x - q * d <= y ==> x / q - d <= y / q) /\
                 (y <= x + q * d ==> y / q <= x / q + d) /\
                 (y <= x ==> y / q <= x / q) /\
                 (y <= q * x ==> y / q <= x) /\
                 (&0 < y ==> &0 < y / q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `x / q - d = (x - q * d) / q /\ x / q + d = (x + q * d) / q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_DIV]]);;

(* p2a_pc1 of flow views under the reparametrization s -> s/q.               *)

let P2AU_PC1_RESCALE = prove
 (`!top atlas J (g:real->A->real^N^N) tt J' (g':real->A->real^N^N) tt'
    (gamma:real->A) b0 P q.
     &0 < q /\ p2a_pc1 (p2a_flow_view (top,atlas) J g) tt gamma (&0) b0 P
     ==> p2a_pc1 (p2a_flow_view (top,atlas) J' g') tt' (\s. gamma(s / q)) (&0) (q * b0)
                 (IMAGE (\x. q * x) P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2AU_PC1_FLOW] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pc"))) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  USE_THEN "pc" (MP_TAC o SPECL [`s0 / q`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "L") (CONJUNCTS_THEN2 (LABEL_TAC "R") (LABEL_TAC "T"))))) THEN
  EXISTS_TAC `q * d` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  SUBGOAL_THEN
   `(\s:real^1. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s / q))) =
    (\y. (\s. SND c (gamma(drop s))) (inv q % y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DROP_CMUL] THEN GEN_TAC THEN
    REWRITE_TAC[real_div] THEN REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. inv q * x = x / q` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2AU_CD1_LINEAR_REPARAM THEN
    EXISTS_TAC `{s | s0 / q - d <= drop s /\ drop s <= s0 / q /\ &0 < drop s /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM; DROP_CMUL] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`q:real`; `s0:real`; `drop(y:real^1)`; `d:real`] P2AU_DIV_LE_IMP) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC P2AU_CD1_LINEAR_REPARAM THEN
    EXISTS_TAC `{s | s0 / q <= drop s /\ drop s <= s0 / q + d /\ drop s <= b0 /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM; DROP_CMUL] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`q:real`; `s0:real`; `drop(y:real^1)`; `d:real`] P2AU_DIV_LE_IMP) THEN
    MP_TAC(SPECL [`q:real`; `b0:real`; `drop(y:real^1)`; `d:real`] P2AU_DIV_LE_IMP) THEN
    MP_TAC(SPECL [`q:real`; `drop(y:real^1)`; `s0:real`; `d:real`] P2AU_DIV_LE_IMP) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `~((s0 / q) IN (P:real->bool))` ASSUME_TAC THENL
     [UNDISCH_TAC `~((s0:real) IN IMAGE (\x. q * x) P)` THEN
      REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `s0 / q`) THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    USE_THEN "T" (MP_TAC o C MP (ASSUME `~((s0 / q) IN (P:real->bool))`)) THEN
    DISCH_TAC THEN MATCH_MP_TAC P2AU_CD1_LINEAR_REPARAM THEN
    EXISTS_TAC `{s | s0 / q - d <= drop s /\ drop s <= s0 / q + d /\ &0 < drop s /\
                     drop s <= b0 /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM; DROP_CMUL] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`q:real`; `s0:real`; `drop(y:real^1)`; `d:real`] P2AU_DIV_LE_IMP) THEN
    MP_TAC(SPECL [`q:real`; `b0:real`; `drop(y:real^1)`; `d:real`] P2AU_DIV_LE_IMP) THEN
    ASM_SIMP_TAC[]]);;

(* The L-integrand of gamma(s/q) at a point s where the chart curve of gamma *)
(* is differentiable at s/q.                                                 *)

let P2AU_LINT_RESCALE = prove
 (`!top atlas a b (g:real->A->real^N^N) q tau (gamma:real->A) s v.
     p2a_cbflow (top,atlas) a b g /\ &0 < q /\ tau < b - a /\
     &0 < s / q /\ s / q < tau /\ gamma(s / q) IN topspace top /\
     ((\x. SND(chart_at atlas (gamma(s / q))) (gamma(drop x))) has_vector_derivative v)
       (at (lift(s / q)))
     ==> p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[q * a,q * b])
                                        (\t x. q %% g (t / q) x))
                         (q * b) (\r. gamma(r / q)) (q * tau) s =
         sqrt q / q *
         p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau
                         (s / q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  REWRITE_TAC[p2a_L_integrand; P2AU_FLOW_VIEW_PARTS] THEN
  SUBGOAL_THEN `(q * b - s) / q = b - s / q` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `G = (g:real->A->real^N^N) (b - s / q)` THEN
  SUBGOAL_THEN `riemannian_metric atlas (G:A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `G:A->real^N^N`;
                 `q:real`; `(gamma:real->A)(s / q)`] P2AU_MFD_SCALAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GRGD_SPEED_SCALE] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`; `q:real`; `s:real`;
                 `&0`; `tau:real`; `v:real^N`] P2AU_VELOCITY_RESCALE) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_speed] THEN
  ABBREV_TAC `X = v dot ((G:A->real^N^N) ((gamma:real->A)(s / q)) ** v)` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(inv q % v) dot ((G:A->real^N^N) ((gamma:real->A)(s / q)) ** (inv q % v)) =
                inv q pow 2 * X` SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(inv q pow 2 * X) = inv q * sqrt X` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt s = sqrt q * sqrt(s / q)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < q` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt q pow 2 = q /\ sqrt X pow 2 = X /\ &0 < sqrt q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD);;

(* Rescaling of admissible curves and of their L-length.                      *)

let P2AU_ADM_RESCALE = prove
 (`!top atlas a b (g:real->A->real^N^N) q p tau (gamma:real->A).
     p2a_cbflow (top,atlas) a b g /\ &0 < q /\ tau < b - a /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     (!s. &0 < s /\ s <= q * tau
          ==> p2a_smooth (p2a_flow_view (top,atlas) (real_interval[q * a,q * b])
                                        (\t x. q %% g (t / q) x))
                         (gamma(s / q)) (q * b - s))
     ==> p2a_adm (p2a_flow_view (top,atlas) (real_interval[q * a,q * b])
                                (\t x. q %% g (t / q) x))
                 (q * b) p (q * tau) (\s. gamma(s / q)) /\
         p2a_L_length (p2a_flow_view (top,atlas) (real_interval[q * a,q * b])
                                     (\t x. q %% g (t / q) x))
                      (q * b) (\s. gamma(s / q)) (q * tau) =
         sqrt q * p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `p:A`; `tau:real`; `gamma:real->A`] P2AU_ADM_FLOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "top") (CONJUNCTS_THEN2 (LABEL_TAC "ct") (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `P:real->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pc")))
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `p2a_pc1 (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N))
                        b (gamma:real->A) (&0) tau P` ASSUME_TAC THENL
   [REWRITE_TAC[P2AU_PC1_FLOW] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the integrand and its integral *)
  ABBREV_TAC `f = p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a,b])
                    (g:real->A->real^N^N)) b (gamma:real->A) tau` THEN
  SUBGOAL_THEN `(f has_real_integral
                 p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^N^N)) b (gamma:real->A) tau)
                (real_interval[&0,tau])` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[p2a_L_length; GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    UNDISCH_TAC `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b])
                   (g:real->A->real^N^N)) b p tau (gamma:real->A)` THEN
    REWRITE_TAC[p2a_adm] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[q * a,q * b])
                       (\t x. q %% (g:real->A->real^N^N) (t / q) x))
                     (q * b) (\r. (gamma:real->A)(r / q)) (q * tau)
     has_real_integral
     sqrt q * p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b gamma tau)
    (real_interval[&0,q * tau])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `\x. sqrt q / q * (f:real->real)(inv q * x)` THEN
    EXISTS_TAC `{&0,q * tau} UNION IMAGE (\x. q * x) (P:real->bool)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_NEGLIGIBLE_FINITE THEN
      ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_INSERT; FINITE_EMPTY];
      X_GEN_TAC `s:real` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL; IN_IMAGE;
                  DE_MORGAN_THM; NOT_EXISTS_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `inv q * s = s / q` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~((s / q) IN (P:real->bool))` ASSUME_TAC THENL
       [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s / q` o check (fun th ->
          is_forall(concl th) && p2au_mentions "IN" th &&
          can (find_term (fun t -> t = `P:real->bool`)) (concl th) &&
          not (p2au_mentions "continuously_differentiable" th))) THEN
        ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < s / q /\ s / q < tau` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_MUL_LZERO] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `tau:real`; `P:real->bool`; `s / q`]
                    P2AU_PC1_DIFF_AT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
      EXPAND_TAC "f" THEN MATCH_MP_TAC P2AU_LINT_RESCALE THEN
      EXISTS_TAC `v:real^N` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "top" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `sqrt q * p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b])
                      (g:real->A->real^N^N)) b (gamma:real->A) tau =
                    sqrt q / q *
                    (inv(abs(inv q)) * p2a_L_length (p2a_flow_view (top,atlas)
                      (real_interval[a,b]) g) b gamma tau)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_INV] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`] THEN
        UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
      SUBGOAL_THEN `real_interval[&0,q * tau] = IMAGE (\x. inv(inv q) * x) (real_interval[&0,tau])`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_INV; IMAGE_STRETCH_REAL_INTERVAL] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_INTERVAL_EQ_EMPTY; REAL_MUL_RZERO] THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_STRETCH THEN ASM_REWRITE_TAC[REAL_INV_EQ_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [p2a_L_length] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    ASM_REWRITE_TAC[]] THEN
  (* admissibility *)
  REWRITE_TAC[p2a_adm] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL];
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN ASM_MESON_TAC[real_div; REAL_MUL_LZERO];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `q * a <= q * b - s /\ q * b - s <= q * b` ASSUME_TAC THENL
     [SUBGOAL_THEN `q * tau < q * (b - a)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_LMUL]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2AU_FLOW_VTOP] THEN USE_THEN "top" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `q * a <= q * b - tau0 /\ q * b - tau0 <= q * b` ASSUME_TAC THENL
     [SUBGOAL_THEN `q * tau < q * (b - a)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_LMUL]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `open_in (p2a_vtop (p2a_flow_view (top,atlas) (real_interval[q * a,q * b])
                   (\t x. q %% (g:real->A->real^N^N) (t / q) x)) (q * b - tau0)) O` THEN
    ASM_SIMP_TAC[P2AU_FLOW_VTOP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= tau0 / q /\ tau0 / q <= tau` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "ct" (MP_TAC o SPECL [`tau0 / q`; `O:A->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(\s. (gamma:real->A)(s / q)) tau0 IN O` THEN REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q * d` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s / q - tau0 / q = (s - tau0) / q` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < q ==> abs q = q`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `IMAGE (\x. q * x) (P:real->bool)` THEN
    MATCH_MP_TAC P2AU_PC1_RESCALE THEN
    MAP_EVERY EXISTS_TAC [`real_interval[a,b]`; `g:real->A->real^N^N`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A C^1 path from p to q padded by constant pieces (the smoothstep         *)
(* 3u^2 - 2u^3 makes the velocity vanish at both ends), and the chart       *)
(* windows of the reparametrized path s -> c4((s^2 - t1)/(tau - t1)).       *)
(* Generic in N.                                                            *)
(* ------------------------------------------------------------------------- *)

let P2AU_VELOCITY_CONST = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (x:A) a b t.
     a < b /\ t IN real_interval[a,b] ==> mfd_velocity atlas (\s. x) a b t = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_velocity] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; HAS_VECTOR_DERIVATIVE_CONST]);;

let P2AU_C1_PATH_PAD = prove
 (`!top atlas (c:real->A) p q.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     mfd_c1_curve (top,atlas) c (&0) (&1) /\ c(&0) = p /\ c(&1) = q
     ==> mfd_c1_curve (top,atlas)
           (\u. if u <= &0 then p
                else if u <= &1 then c(&3 * u pow 2 - &2 * u pow 3) else q)
           (-- &1) (&2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c4 = \u. if u <= &0 then (p:A)
                       else if u <= &1 then (c:real->A)(&3 * u pow 2 - &2 * u pow 3)
                       else q` THEN
  SUBGOAL_THEN `(p:A) IN topspace top /\ (q:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(c:real->A)(&0) = p` THEN DISCH_THEN(SUBST1_TAC o SYM);
      UNDISCH_TAC `(c:real->A)(&1) = q` THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the smoothstep and its derivative *)
  SUBGOAL_THEN
   `!s. s IN real_interval[&0,&1]
        ==> (\u. &3 * u pow 2 - &2 * u pow 3) s IN real_interval[&0,&1] /\
            ((\u. &3 * u pow 2 - &2 * u pow 3) has_real_derivative
             (\u. &6 * u - &6 * u pow 2) s) (atreal s within real_interval[&0,&1])`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(SPEC `s:real` GRGD_SMOOTHSTEP_RANGE) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\u. &6 * u - &6 * u pow 2) real_continuous_on real_interval[&0,&1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[real_differentiable_on] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `&6 - &12 * x` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!u. u IN real_interval[-- &1,&0] ==> (c4:real->A) u = (\s. p) u) /\
                (!u. u IN real_interval[&0,&1]
                     ==> c4 u = ((c:real->A) o (\u. &3 * u pow 2 - &2 * u pow 3)) u) /\
                (!u. u IN real_interval[&1,&2] ==> c4 u = (\s. q) u)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c4" THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_CASES_TAC `u = &0` THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `~(u <= &0)` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `u = &1` THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `~(u <= &0) /\ ~(u <= &1)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (c4:real->A) (-- &1) (&0) /\
                mfd_c1_curve (top,atlas) c4 (&0) (&1) /\
                mfd_c1_curve (top,atlas) c4 (&1) (&2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                     `\s:real. (p:A)`; `-- &1`; `&0`] MFD_C1_CURVE_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC MFD_C1_CURVE_CONST THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                     `(c:real->A) o (\u. &3 * u pow 2 - &2 * u pow 3)`; `&0`; `&1`]
                    MFD_C1_CURVE_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`; `\u. &6 * u - &6 * u pow 2`] THEN
      ASM_REWRITE_TAC[REAL_POS];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                     `\s:real. (q:A)`; `&1`; `&2`] MFD_C1_CURVE_EQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC MFD_C1_CURVE_CONST THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* velocities at the junctions *)
  SUBGOAL_THEN
   `mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (c4:real->A) (-- &1) (&0) (&0) =
      vec 0 /\
    mfd_velocity atlas c4 (&0) (&1) (&0) = vec 0 /\
    mfd_velocity atlas c4 (&0) (&1) (&1) = vec 0 /\
    mfd_velocity atlas c4 (&1) (&2) (&1) = vec 0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`; `\s:real. (p:A)`;
                     `-- &1`; `&0`; `&0`] GRGD_VELOCITY_EQ) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC P2AU_VELOCITY_CONST THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                     `(c:real->A) o (\u. &3 * u pow 2 - &2 * u pow 3)`;
                     `&0`; `&1`; `&0`] GRGD_VELOCITY_EQ) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c:real->A`;
                     `&0`; `&1`; `\u. &3 * u pow 2 - &2 * u pow 3`;
                     `\u. &6 * u - &6 * u pow 2`; `&0`; `&1`; `&0`] GRGD_VELOCITY_REPARAM) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LT_01] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[VECTOR_MUL_LZERO];
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                     `(c:real->A) o (\u. &3 * u pow 2 - &2 * u pow 3)`;
                     `&0`; `&1`; `&1`] GRGD_VELOCITY_EQ) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c:real->A`;
                     `&0`; `&1`; `\u. &3 * u pow 2 - &2 * u pow 3`;
                     `\u. &6 * u - &6 * u pow 2`; `&0`; `&1`; `&1`] GRGD_VELOCITY_REPARAM) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LT_01] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[VECTOR_MUL_LZERO];
      MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`; `\s:real. (q:A)`;
                     `&1`; `&2`; `&1`] GRGD_VELOCITY_EQ) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC P2AU_VELOCITY_CONST THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (c4:real->A) (-- &1) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_JOIN THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_C1_CURVE_JOIN THEN EXISTS_TAC `&1` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                 `-- &1`; `&1`; `\t:real. t`; `\t:real. &1`; `&0`; `&1`; `&1`]
                GRGD_VELOCITY_REPARAM) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LT_01; HAS_REAL_DERIVATIVE_ID] THEN
  ANTS_TAC THENL [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c4:real->A) o (\t. t) = c4` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chart windows of a C^1 curve c4 on [-1,2] reparametrized affinely,       *)
(* s -> c4((s - A)/(B - A)) for s near [A,B]: in one chart the chart        *)
(* curve is differentiable with a continuous derivative (the input of       *)
(* P2A_CHART_CURVE_SEG).  Generic in N.                                     *)
(* ------------------------------------------------------------------------- *)

let P2AU_PATH_WINDOW = prove
 (`!top atlas (c4:real->A) A B s0.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     mfd_c1_curve (top,atlas) c4 (-- &1) (&2) /\ A < B /\ A <= s0 /\ s0 <= B
     ==> ?d (U:A->bool) (phi:A->real^N) (sol:real^1->real^N).
            &0 < d /\ (U,phi) IN atlas /\
            !s. abs(s - s0) < d
                ==> c4((s - A) / (B - A)) IN U /\
                    sol(lift s) = phi(c4((s - A) / (B - A))) /\
                    sol differentiable (at (lift s)) /\
                    (\v. vector_derivative sol (at v)) continuous (at (lift s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < B - A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (s0 - A) / (B - A) /\ (s0 - A) / (B - A) <= &1` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `u0 = (s0 - A) / (B - A)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c4:real->A) u0 IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `-- &1`; `&2`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `k = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((c4:real->A) u0)` THEN
  SUBGOAL_THEN `(k:(A->bool)#(A->real^N)) IN atlas /\ (c4:real->A) u0 IN FST k /\
                open_in top (FST k)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c4:real->A) u0`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    ALL_TAC] THEN
  ABBREV_TAC `Sk = {x | x IN interval[lift(-- &1),lift(&2)] /\
                        (c4:real->A)(drop x) IN FST (k:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 Sk (\x. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)(drop x)))`
  MP_TAC THENL
   [EXPAND_TAC "Sk" THEN
    UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (c4:real->A) (-- &1) (&2)` THEN
    REWRITE_TAC[mfd_c1_curve] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable; CONTINUOUSLY_DIFFERENTIABLE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "C"))) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(lift u0,r) SUBSET Sk` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                   `-- &1`; `&2`; `FST(k:(A->bool)#(A->real^N))`] GRGD_CURVE_TIMES_OPEN_IN) THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SK"))) THEN
    SUBGOAL_THEN `lift u0 IN (O:real^1->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `lift u0 IN Sk` MP_TAC THENL
       [EXPAND_TAC "Sk" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "SK" SUBST1_TAC THEN SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    UNDISCH_TAC `open(O:real^1->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `lift u0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e (&1 / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SK" SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `x IN ball(lift u0,min e (&1 / &2))` THEN
      REWRITE_TAC[IN_BALL; IN_INTERVAL_1; LIFT_DROP; DIST_REAL; GSYM drop] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      UNDISCH_TAC `x IN ball(lift u0,min e (&1 / &2))` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(lift u0,r)
        ==> ((\x. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)(drop x))) has_derivative
             (f':real^1->real^1->real^N) x) (at x) /\
            (\y. f' y (vec 1)) continuous (at x)`
  (LABEL_TAC "BALL") THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)(drop x))`;
                     `(f':real^1->real^1->real^N) x`; `x:real^1`; `ball(lift u0,r)`]
                    HAS_DERIVATIVE_WITHIN_OPEN) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `Sk:real^1->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "D" MATCH_MP_TAC THEN ASM SET_TAC[];
      USE_THEN "C" (MP_TAC o SPEC `vec 1:real^1`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\y. (f':real^1->real^1->real^N) y (vec 1)) continuous_on ball(lift u0,r)`
      MP_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Sk:real^1->bool` THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  (* the affine reparametrization *)
  ABBREV_TAC `gm = \v:real^1. inv(B - A) % (v - lift A)` THEN
  SUBGOAL_THEN `!v:real^1. (gm:real^1->real^1) v = lift((drop v - A) / (B - A))`
  ASSUME_TAC THENL
   [EXPAND_TAC "gm" THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_SUB; LIFT_DROP] THEN
    GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^1. ((gm:real^1->real^1) has_derivative (\h. inv(B - A) % h)) (at v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gm" THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    MP_TAC(ISPECL [`\v:real^1. v`; `\h:real^1. h`; `\v:real^1. lift A`;
                   `\h:real^1. vec 0:real^1`; `at (v:real^1)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. abs(drop v - s0) < r * (B - A) ==> (gm:real^1->real^1) v IN ball(lift u0,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_BALL; DIST_LIFT] THEN
    EXPAND_TAC "u0" THEN
    SUBGOAL_THEN `(s0 - A) / (B - A) - (drop v - A) / (B - A) = (s0 - drop v) / (B - A)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < B - A` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the vector derivative of sol in the window *)
  SUBGOAL_THEN
   `!v. abs(drop v - s0) < r * (B - A)
        ==> ((\v. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)((drop v - A) / (B - A))))
             has_vector_derivative
             (inv(B - A) % (f':real^1->real^1->real^N) ((gm:real^1->real^1) v) (vec 1)))
            (at v)`
  (LABEL_TAC "VD") THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\v. SND (k:(A->bool)#(A->real^N)) ((c4:real->A)((drop v - A) / (B - A)))) =
      (\x. SND k (c4(drop x))) o (gm:real^1->real^1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN
     `(\h:real^1. drop h % inv(B - A) % (f':real^1->real^1->real^N) ((gm:real^1->real^1) v)
                    (vec 1)) =
      f' (gm v) o (\h. inv(B - A) % h)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
      SUBGOAL_THEN `linear((f':real^1->real^1->real^N) ((gm:real^1->real^1) v))` ASSUME_TAC THENL
       [USE_THEN "BALL" (MP_TAC o SPEC `(gm:real^1->real^1) v`) THEN
        ANTS_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (find_term (fun t -> t = `ball(lift u0,r)`)) (concl th) &&
            not (p2au_mentions "has_derivative" th))) THEN
          ASM_REWRITE_TAC[];
          SIMP_TAC[has_derivative]];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(B - A) % (h:real^1) = (inv(B - A) * drop h) % vec 1` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM LIFT_EQ_CMUL; LIFT_DROP]; ALL_TAC] THEN
      ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "BALL" (MP_TAC o SPEC `(gm:real^1->real^1) v`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `ball(lift u0,r)`)) (concl th) &&
        not (p2au_mentions "has_derivative" th))) THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `r * (B - A)` THEN EXISTS_TAC `FST(k:(A->bool)#(A->real^N))` THEN
  EXISTS_TAC `SND(k:(A->bool)#(A->real^N))` THEN
  EXISTS_TAC `\v:real^1. SND(k:(A->bool)#(A->real^N)) ((c4:real->A)((drop v - A) / (B - A)))` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; PAIR] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th ->
      can (find_term (fun t -> t = `gm:real^1->real^1`)) (concl th) &&
      can (find_term (fun t -> t = `ball(lift u0,r)`)) (concl th) &&
      not (p2au_mentions "has_derivative" th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lift((s - A) / (B - A)) IN Sk` MP_TAC THENL
     [ASM SET_TAC[]; EXPAND_TAC "Sk" THEN SIMP_TAC[IN_ELIM_THM; LIFT_DROP]];
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % inv(B - A) %
                (f':real^1->real^1->real^N) ((gm:real^1->real^1) (lift s)) (vec 1)` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN USE_THEN "VD" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\v:real^1. inv(B - A) % (f':real^1->real^1->real^N) ((gm:real^1->real^1) v)
                                          (vec 1)` THEN
    EXISTS_TAC `r * (B - A) - abs(s - s0)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      USE_THEN "VD" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN
    SUBGOAL_THEN `(\v:real^1. (f':real^1->real^1->real^N) ((gm:real^1->real^1) v) (vec 1)) =
                  (\y. f' y (vec 1)) o gm` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      ASM_MESON_TAC[];
      USE_THEN "BALL" (MP_TAC o SPEC `(gm:real^1->real^1) (lift s)`) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]; SIMP_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* On a connected manifold every point is reached by an admissible curve of *)
(* the flow view at every backward time in (0, b - a): the constant curve   *)
(* at p near tau = 0 (P2A_CONST_SMALL_TIME), then a padded C^1 path from    *)
(* p to q (MFD_JOINABLE_CONNECTED, P2AU_C1_PATH_PAD), glued chart piece by  *)
(* chart piece (P2A_CHART_CURVE_SEG, P2A_SEG_GLUE) by a supremum argument.  *)
(* Generic in N, given the region clauses of FL0.                           *)
(* ------------------------------------------------------------------------- *)

let P2AU_ADM_EXISTS = prove
 (`!top atlas a b (g:real->A->real^N^N) p q tau.
     p2a_cbflow (top,atlas) a b g /\ connected_space top /\
     p IN topspace top /\ q IN topspace top /\ &0 < tau /\ tau < b - a /\
     p2a_svs (p2a_flow_view (top,atlas) (real_interval[a,b]) g) /\
     (!W a' b'. open_in top W /\ a <= a' /\ a' < b' /\ b' <= b
                ==> p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b]) g) W a' b')
     ==> ?gamma. p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
                 gamma tau = q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "REG")))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  ABBREV_TAC `V = p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^N^N)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (topspace top:A->bool) a b` ASSUME_TAC THENL
   [USE_THEN "REG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; REAL_LE_REFL];
    ALL_TAC] THEN
  (* the constant curve near tau = 0 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `b:real`; `p:A`; `topspace top:A->bool`; `a:real`]
                P2A_CONST_SMALL_TIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `Kr:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `t1 = min (t0 / &2) (tau / &2)` THEN
  SUBGOAL_THEN `&0 < t1 /\ t1 < t0 /\ t1 < tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the padded path *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`; `q:A`]
                MFD_JOINABLE_CONNECTED) THEN
  ASM_REWRITE_TAC[mfd_joinable] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c:real->A`;
                 `p:A`; `q:A`] P2AU_C1_PATH_PAD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c4 = \u. if u <= &0 then (p:A)
                       else if u <= &1 then (c:real->A)(&3 * u pow 2 - &2 * u pow 3)
                       else q` THEN
  DISCH_TAC THEN
  ABBREV_TAC `A = sqrt t1` THEN ABBREV_TAC `B = sqrt tau` THEN
  SUBGOAL_THEN `&0 < A /\ A < B /\ A pow 2 = t1 /\ B pow 2 = tau` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `gamma = \sigma. (c4:real->A)((sqrt sigma - A) / (B - A))` THEN
  EXISTS_TAC `gamma:real->A` THEN
  SUBGOAL_THEN `(gamma:real->A) tau = q` ASSUME_TAC THENL
   [EXPAND_TAC "gamma" THEN EXPAND_TAC "c4" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(sqrt tau - A) / (B - A) = &1` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!sigma. &0 <= sigma /\ sigma <= t1 ==> (gamma:real->A) sigma = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `sigma:real` THEN STRIP_TAC THEN EXPAND_TAC "gamma" THEN EXPAND_TAC "c4" THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(sqrt sigma - A) / (B - A) <= &0` (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `&0 < B - A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
    EXPAND_TAC "A" THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - y <= &0`) THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the supremum argument over the s-parameter *)
  ABBREV_TAC `Ts = {s | A <= s /\ s <= B /\ p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p (s pow 2) (gamma:real->A)}` THEN
  SUBGOAL_THEN `(A:real) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `b:real`; `p:A`; `t1:real`; `\s:real. (p:A)`;
                   `gamma:real->A`] P2AU_ADM_CONG) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Ts:real->bool = {}) /\ (!s. s IN Ts ==> s <= B)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "Ts" THEN SIMP_TAC[IN_ELIM_THM]]; ALL_TAC] THEN
  ABBREV_TAC `ss = sup (Ts:real->bool)` THEN
  SUBGOAL_THEN `A <= ss /\ ss <= B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN CONJ_TAC THENL
     [MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `c4:real->A`;
                 `A:real`; `B:real`; `ss:real`] P2AU_PATH_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `sol:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "WIN"))))))) THEN
  SUBGOAL_THEN `?s1. s1 IN Ts /\ ss - d < s1` (X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC SUP_APPROACH THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `A <= s1 /\ s1 <= B /\ p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p (s1 pow 2) (gamma:real->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s1:real) IN Ts` THEN EXPAND_TAC "Ts" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 <= ss` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s1:real = B` THENL
   [UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p (s1 pow 2) (gamma:real->A)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s2 = min B (ss + d / &2)` THEN
  SUBGOAL_THEN `s1 < s2 /\ s2 <= B /\ s2 <= ss + d / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ U INTER topspace top = U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool),(phi:A->real^N)`] GRGD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `B < sqrt(b - a)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the chart segment on [s1^2, s2^2] *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `b:real`; `topspace top:A->bool`; `a:real`; `b:real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`; `s1:real`; `s2:real`;
                 `max (ss - d) (&0)`; `min (ss + d) (sqrt(b - a))`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[P2AU_FLOW_VIEW_PARTS] THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MAX_LT] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_MAX_LT; REAL_LT_MIN] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < b - a` MP_TAC THENL
       [SUBGOAL_THEN `s pow 2 < sqrt(b - a) pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_SUB_LT]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `seg = \tau'. chart_inv ((U:A->bool),(phi:A->real^N))
                                     ((sol:real^1->real^N)(lift(sqrt tau')))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `!tau'. s1 pow 2 <= tau' /\ tau' <= s2 pow 2
                       ==> (seg:real->A) tau' = gamma tau'` ASSUME_TAC THENL
   [X_GEN_TAC `tau':real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= tau'` ASSUME_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s1 /\ &0 <= s2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s1 <= sqrt tau' /\ sqrt tau' <= s2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; ARITH_EQ];
      ALL_TAC] THEN
    USE_THEN "WIN" (MP_TAC o SPEC `sqrt tau'`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    EXPAND_TAC "seg" THEN EXPAND_TAC "gamma" THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool),(phi:A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `b:real`; `p:A`; `seg:real->A`; `gamma:real->A`;
                 `\tau'. if tau' <= s1 pow 2 then (gamma:real->A) tau' else seg tau'`;
                 `s2 pow 2`; `s1 pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[];
      X_GEN_TAC `tau':real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau' = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) b p (s2 pow 2) (gamma:real->A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `b:real`; `p:A`; `s2 pow 2`;
                   `\tau'. if tau' <= s1 pow 2 then (gamma:real->A) tau' else seg tau'`;
                   `gamma:real->A`] P2AU_ADM_CONG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `tau':real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s2:real) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 <= ss` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s2:real = B` ASSUME_TAC THENL
   [UNDISCH_TAC `min B (ss + d / &2) = s2` THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) b p (s2 pow 2) (gamma:real->A)` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* FL7 (MT Lemmas 6.72, 6.75, Cor 6.74) at N = 3: the sets of L-lengths     *)
(* of the two views correspond under x -> sqrt(Q) x (admissible curves      *)
(* rescale both ways, P2AU_ADM_RESCALE with Q and with 1/Q), they are       *)
(* nonempty (P2AU_ADM_EXISTS, connectedness) and bounded below              *)
(* (P2AU_L_LOWER), so the infima rescale and lx is invariant.               *)
(* ------------------------------------------------------------------------- *)

let P2AU_INF_LMUL = prove
 (`!s c. &0 < c /\ ~(s = {}) /\ (?m. !x. x IN s ==> m <= x)
         ==> inf (IMAGE (\x. c * x) s) = c * inf s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INF_UNIQUE THEN X_GEN_TAC `d:real` THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SUBGOAL_THEN `!x. d <= c * x <=> d / c <= x` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real->bool`; `d / c`] REAL_LE_INF_EQ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* L-lengths of admissible curves of the flow view are bounded below.      *)

let P2AU_L_LOWER = prove
 (`!top atlas a b (g:real->A->real^N^N).
     p2a_cbflow (top,atlas) a b g
     ==> ?C. &0 <= C /\
             !p tau gamma.
                tau < b - a /\
                p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma
                ==> --(C * tau * sqrt tau) <=
                    p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                 b gamma tau`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_CURV) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  EXISTS_TAC `&(dimindex(:N) * (dimindex(:N) - 1)) * K` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `tau:real`; `gamma:real->A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `p:A`; `tau:real`; `gamma:real->A`] P2AU_ADM_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,tau])
                (\s:real. --((&(dimindex(:N) * (dimindex(:N) - 1)) * K) * sqrt tau))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--(&(dimindex(:N) * (dimindex(:N) - 1)) * K) <=
                mfd_scalar atlas ((g:real->A->real^N^N)(b - s)) ((gamma:real->A) s)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      p2au_mentions "mfd_scalar" th && is_forall(concl th) &&
      can (find_term (fun t -> t = `K:real`)) (concl th))) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt s /\ sqrt s <= sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE]; ALL_TAC] THEN
  MP_TAC(SPEC `mfd_speed atlas ((g:real->A->real^N^N)(b - s)) (gamma:real->A) (&0) tau s`
              REAL_LE_POW_2) THEN
  ABBREV_TAC `C = &(dimindex(:N) * (dimindex(:N) - 1)) * K` THEN
  ABBREV_TAC `R = mfd_scalar atlas ((g:real->A->real^N^N)(b - s)) ((gamma:real->A) s)` THEN
  ABBREV_TAC `v = mfd_speed atlas ((g:real->A->real^N^N)(b - s)) (gamma:real->A) (&0) tau s
                  pow 2` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt s * (R + C + v)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * sqrt s <= C * sqrt tau` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Undoing a rescaling.                                                       *)

let P2AU_RESCALE_INV = prove
 (`!(g:real->A->real^N^N) Q.
     &0 < Q
     ==> (\t x. inv Q %% (\t x. Q %% g (t / Q) x) (t / inv Q) x) = g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
  SUBGOAL_THEN `inv Q * Q = &1 /\ t / inv Q / Q = t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_CMUL_LID]);;

(* FL7 at N = 3.                                                             *)

let P2AU_FLOW_SCALING = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_SCALING_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2A_FLOW_SCALING_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `Q:real`; `tau:real`; `q:A`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AU_CBFLOW_FACTS) THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) (Q * a) (Q * b) (\t x. Q %% (g:real->A->real^3^3) (t / Q) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AU_CBFLOW_RESCALE THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`u:A->bool`; `n:3->bool`] P2AW_FLOW_VIEW_3) THEN
  REWRITE_TAC[P2A_FLOW_VIEW_STATEMENT] THEN DISCH_THEN(LABEL_TAC "FL0") THEN
  USE_THEN "FL0" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `a:real`; `b:real`; `g:real->A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "REG")
    (CONJUNCTS_THEN2 (LABEL_TAC "SM") (K ALL_TAC)))) THEN
  USE_THEN "FL0" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `Q * a`; `Q * b`; `\t x. Q %% (g:real->A->real^3^3) (t / Q) x`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "SM'") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `&0 < Q * tau /\ Q * tau < Q * b - Q * a` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_SUB_LDISTRIB; REAL_LT_LMUL_EQ]; ALL_TAC] THEN
  ABBREV_TAC `S = {p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a,b])
                      (g:real->A->real^3^3)) b gamma tau | gamma |
                   p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
                   gamma tau = q}` THEN
  SUBGOAL_THEN
   `{p2a_L_length (p2a_flow_view (top,atlas) (real_interval[Q * a,Q * b])
                    (\t x. Q %% (g:real->A->real^3^3) (t / Q) x)) (Q * b) gamma (Q * tau) | gamma |
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[Q * a,Q * b])
                (\t x. Q %% g (t / Q) x)) (Q * b) p (Q * tau) gamma /\
     gamma (Q * tau) = q} =
    IMAGE (\x. sqrt Q * x) S`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Q * a`; `Q * b`;
                     `\t x. Q %% (g:real->A->real^3^3) (t / Q) x`; `inv Q`; `p:A`; `Q * tau`;
                     `gamma':real->A`] P2AU_ADM_RESCALE) THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; P2AU_RESCALE_INV] THEN
      SUBGOAL_THEN `inv Q * Q * a = a /\ inv Q * Q * b = b /\ inv Q * Q * tau = tau`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "SM" MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `p2a_adm (p2a_flow_view (top,atlas) (real_interval[Q * a,Q * b])
                         (\t x. Q %% (g:real->A->real^3^3) (t / Q) x)) (Q * b) p (Q * tau)
                         (gamma':real->A)` THEN
          REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `s / inv Q` o check (fun th ->
            p2au_mentions "topspace" th && is_forall(concl th) &&
            not (p2au_mentions "open_in" th))) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[real_div; REAL_INV_INV] THEN
            SUBGOAL_THEN `&0 <= s * Q /\ s * Q <= tau * Q` MP_TAC THENL
             [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
              ASM_REAL_ARITH_TAC;
              REAL_ARITH_TAC];
            ALL_TAC] THEN
          SUBGOAL_THEN `Q * b - s / inv Q IN real_interval[Q * a,Q * b]` ASSUME_TAC THENL
           [REWRITE_TAC[IN_REAL_INTERVAL; real_div; REAL_INV_INV] THEN
            SUBGOAL_THEN `s * Q <= tau * Q` MP_TAC THENL
             [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            SUBGOAL_THEN `&0 <= s * Q` MP_TAC THENL
             [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            ASM_REAL_ARITH_TAC;
            ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS]];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      STRIP_TAC THEN
      ABBREV_TAC `LQ = p2a_L_length (p2a_flow_view (top,atlas) (real_interval[Q * a,Q * b])
                (\t x. Q %% (g:real->A->real^3^3) (t / Q) x)) (Q * b) gamma' (Q * tau)` THEN
      EXISTS_TAC `sqrt(inv Q) * LQ` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC; GSYM SQRT_MUL] THEN
        ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; SQRT_1; REAL_MUL_LID];
        ALL_TAC] THEN
      EXISTS_TAC `\s. (gamma':real->A)(s / inv Q)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[real_div; REAL_INV_INV] THEN
      SUBGOAL_THEN `tau * Q = Q * tau` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                     `g:real->A->real^3^3`; `Q:real`; `p:A`; `tau:real`; `gamma:real->A`]
                    P2AU_ADM_RESCALE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "SM'" MATCH_MP_TAC THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b])
                         (g:real->A->real^3^3)) b p tau (gamma:real->A)` THEN
          REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `s / Q` o check (fun th ->
            p2au_mentions "topspace" th && is_forall(concl th) &&
            not (p2au_mentions "open_in" th))) THEN
          ANTS_TAC THENL
           [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `b - s / Q IN real_interval[a,b]` ASSUME_TAC THENL
           [REWRITE_TAC[IN_REAL_INTERVAL] THEN
            SUBGOAL_THEN `&0 <= s / Q /\ s / Q <= tau` MP_TAC THENL
             [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
              ASM_REAL_ARITH_TAC];
            ASM_REWRITE_TAC[P2AU_FLOW_VIEW_PARTS]];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      STRIP_TAC THEN EXISTS_TAC `\s. (gamma:real->A)(s / Q)` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(Q * tau) / Q = tau` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lx; p2a_Lx] THEN ASM_REWRITE_TAC[] THEN
  (* nonempty and bounded below *)
  SUBGOAL_THEN `~(S:real->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `q:A`; `tau:real`] P2AU_ADM_EXISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. !x. x IN S ==> m <= x` ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o MATCH_MP P2AU_L_LOWER o
      check (fun th -> p2au_mentions "p2a_cbflow" th &&
                       not (can (find_term (fun t -> t = `Q:real`)) (concl th)))) THEN
    EXISTS_TAC `--(C * tau * sqrt tau)` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P2AU_INF_LMUL; SQRT_POS_LT] THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&0 < sqrt Q /\ &0 < sqrt tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < sqrt Q` THEN UNDISCH_TAC `&0 < sqrt tau` THEN CONV_TAC REAL_FIELD);;

