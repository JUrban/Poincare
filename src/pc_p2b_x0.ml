(* ========================================================================= *)
(* pc_p2b_x0: X0 of the Part 2B chain, MT Prop 9.11 split at infinity, i.e.  *)
(* P2B_SPLIT_AT_INFINITY_STATEMENT of pc_p2b_chainstmts, from the            *)
(* limit-geometry statements of pc_lim_stmts and ANCIENT_COMPACT             *)
(* (P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT, pc_p2b_defs).  Main theorems:     *)
(*   P2BX0_SPLIT_BODY: LIM_DIST, LIM_BALL, LIM_KNC, LIM_CURV (instances     *)
(*     w w), LIM_FLOW_COMPLETE_BACK w and ANCIENT_COMPACT w give            *)
(*     P2B_SPLIT_AT_INFINITY_STATEMENT w;                                   *)
(*   P2B_SPLIT_AT_INFINITY_ROUTE_LIM: the five LIM instances give           *)
(*     P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT w.                             *)
(*                                                                           *)
(* Proof.  For an ancient flow g on s < b (p2b_ancflow0) and points pp k    *)
(* with R d(p,pp k)^2 -> infinity at time s0: picked points q0 k            *)
(* (P2BX0_PICKED_POINTS, R <= 4 R(q0 k) on balls of radius                  *)
(* A / sqrt(R(q0 k))); along a subsequence, almost-line pairs at scale      *)
(* 1 / sqrt(R) (P2BX0_ALMOST_PAIRS: segments from p converge at time 1,     *)
(* Toponogov twice); the limit of the views rescaled by Q k = R(s0,q k)     *)
(* at times s0 + s/Q k, s <= 0 (P2BX0_LIMIT_EXISTS: ANCIENT_COMPACT on the  *)
(* shifted flows, restriction of every per-Tl limit to the joinable class  *)
(* of xl by P2CO_P3_FLOW_RESTRICT of pc_p2c_lrestrict, one limit on s <= 0  *)
(* by P2BX0_FLOW_LIMIT_DIAG, conversion to the views by                     *)
(* P2BX0_FLOW_LIMIT_WITH_CONG); its properties (X0.6: sec >= 0 and          *)
(* R(0,xl) = 1 from LIM_CURV, completeness from LIM_FLOW_COMPLETE_BACK,     *)
(* R(0,.) <= 4 from the picked balls, R nondecreasing in s, abs Rm <= 2,    *)
(* dR/ds >= 0, kappa-noncollapsing from LIM_KNC); a line at time 0 (exact  *)
(* pairs by P2BX0_LIMIT_PAIRS on LIM_DIST and LIM_BALL, then                *)
(* P2BX0_LINE_FROM_PAIRS); the splitting field X at time 0 (CMP_R3_SPLIT);  *)
(* X unit and parallel at every s <= 0 (P2BX0_TIME_INVARIANCE: kernel of    *)
(* Ric by backward continuous induction with the P-field family of          *)
(* RFA_PARALLEL_CHART, d/dt of the family = 0).                            *)
(*                                                                           *)
(* Duplication note: P2BX0_SUBSEQ_COMPOSE has the statement and proof of    *)
(* P2AK_SUBSEQ_O of pc_p2a_l72d.ml, which is outside this closure (it pulls *)
(* 22 more files, about 29K lines).  P2BX0_SUBSEQ_GE is MONOTONE_BIGGER for *)
(* p3_subseq, P2BX0_DIST_QUAD is MFD_DIST_LIPSCHITZ on a connected          *)
(* manifold, P2BX0_MONO_DERIV_NONNEG is REAL_DERIVATIVE_POS_RIGHT_MAXIMUM   *)
(* for a function nondecreasing up to s, P2BX0_FLOW_UPTO_SHIFT is          *)
(* RICCI_FLOW_TRANSLATE plus P2CF_RFO_UPTO.                                 *)
(*                                                                           *)
(* The chart kit for parallel fields is in pc_p2b_parkit and abs Rm <= R/2   *)
(* is in pc_p2b_rmhalf, so that pc_p2b_kfl and other users can load them     *)
(* without this unit.                                                        *)
(* ========================================================================= *)

needs "src/pc_p2b_parkit.ml";;
needs "src/pc_p2b_rmhalf.ml";;
needs "src/pc_p2b_flatfwd.ml";;
needs "src/pc_rfa_p3alg.ml";;
needs "src/pc_rfa_tmaxp.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_rfa_splitend.ml";;
let p2bx0_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := p2bx0_saved_interface;;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_cmp_soul.ml";;
needs "src/pc_cmp_split.ml";;
needs "src/pc_cmp_tpg.ml";;
needs "src/pc_lim_stmts.ml";;
needs "src/pc_apx_scal.ml";;
needs "src/pc_p2c_lrestrict.ml";;

prioritize_real();;
type_invention_error := true;;

(* X0.1 Point picking (MT Lemma 9.37, Cor 9.38) in maximisation form: on a  *)
(* Riemannian manifold with compact closed balls, for f continuous and      *)
(* positive, y0 and r > 0, a maximum point q of f(y)(r - d(y0,y))^2 on the  *)
(* closed ball has f(q) >= f(y0), d(y0,q) < r, f <= 4 f(q) on the ball      *)
(* about q of radius rho = (r - d(y0,q))/2, and r^2 f(y0) <= 4 rho^2 f(q).   *)

let P2BX0_POINT_PICK = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) y0 r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\
     continuous_map (top,euclideanreal) f /\ (!y. y IN topspace top ==> &0 <= f y) /\
     y0 IN topspace top /\ &0 < f y0 /\ &0 < r
     ==> ?q. mfd_joinable (top,atlas) y0 q /\ mfd_dist (top,atlas) g y0 q < r /\
             f y0 <= f q /\
             r pow 2 * f y0 <= (r - mfd_dist (top,atlas) g y0 q) pow 2 * f q /\
             !y. mfd_joinable (top,atlas) q y /\
                 mfd_dist (top,atlas) g q y < (r - mfd_dist (top,atlas) g y0 q) / &2
                 ==> f y <= &4 * f q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K = mfd_cball (top,atlas) (g:A->real^N^N) (y0:A) r` THEN
  SUBGOAL_THEN `compact_in (top:A topology) K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    UNDISCH_TAC `mfd_complete (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                              (g:A->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN K <=> mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) y0 y /\
                   mfd_dist (top,atlas) (g:A->real^N^N) y0 y <= r`
  (LABEL_TAC "K") THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (top:A topology,euclideanreal)
                   (\y. mfd_dist (top,atlas) (g:A->real^N^N) y0 y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`] MFD_DIST_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\y. mfd_dist (top,atlas) (g:A->real^N^N) y0 y) =
      (\(x,y). mfd_dist (top,atlas) g x y) o (\y:A. (y0:A),y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `prod_topology (top:A topology) top` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
    ASM_REWRITE_TAC[ETA_AX; CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  ABBREV_TAC
   `Fp = \y. (f:A->real) y * (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 y) pow 2` THEN
  SUBGOAL_THEN `continuous_map (top:A topology,euclideanreal) Fp` ASSUME_TAC THENL
   [EXPAND_TAC "Fp" THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN K` ASSUME_TAC THENL
   [USE_THEN "K" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (Fp:A->real) K` REAL_COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max"))) THEN
  EXISTS_TAC `q:A` THEN
  USE_THEN "K" (MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:A) IN topspace top /\ (y0:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^N^N) y0 q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fp:A->real) y0 <= Fp q` MP_TAC THENL
   [USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "Fp" THEN ASM_SIMP_TAC[MFD_DIST_REFL; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (f:A->real) q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y. y IN topspace top ==> &0 <= (f:A->real) y`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `(f:A->real) y0 * r pow 2 <=
                   f q * (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 q) pow 2` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_NOT_LE] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y0 q < r` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(f:A->real) y0 * r pow 2 <=
                 f q * (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 q) pow 2` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; REAL_NOT_LE] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `dq = mfd_dist (top,atlas) (g:A->real^N^N) y0 q` THEN
  SUBGOAL_THEN `(r - dq) pow 2 <= r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(f:A->real) q * (r - dq) pow 2 <= f q * r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:A->real) y0 * r pow 2 <= f q * r pow 2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW_LT];
    UNDISCH_TAC `(f:A->real) y0 * r pow 2 <= f q * (r - dq) pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) y0 y`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y0 y <= dq + mfd_dist (top,atlas) g q y`
  ASSUME_TAC THENL
   [EXPAND_TAC "dq" THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^N^N) q y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fp:A->real) y <= Fp q` MP_TAC THENL
   [USE_THEN "max" MATCH_MP_TAC THEN USE_THEN "K" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "Fp" THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `rho = (r - dq) / &2` THEN
  SUBGOAL_THEN `&0 < rho /\ r - dq = &2 * rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rho <= r - mfd_dist (top,atlas) (g:A->real^N^N) y0 y` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 2 <= (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 y) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (f:A->real) y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!y. y IN topspace top ==> &0 <= (f:A->real) y`) (concl th))) THEN
    ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real) y * rho pow 2 <=
                f y * (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 y) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real) y * rho pow 2 <= (&4 * f q) * rho pow 2` MP_TAC THENL
   [UNDISCH_TAC `(f:A->real) y * (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 y) pow 2 <=
                 f q * (r - dq) pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:A->real) y * rho pow 2 <=
                 f y * (r - mfd_dist (top,atlas) (g:A->real^N^N) y0 y) pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW_LT]);;

(* X0.2a A nonnegative symmetric bilinear form is bounded by its trace in a *)
(* G-orthonormal frame times the G-norm squared: with f i = M^-1 e_i and    *)
(* c = M x, B(x,x) <= (sum_i B(f i,f i)) (c dot c).  Proof: x = sum c_i f_i, *)
(* B(x,x) = sum c_i B(x,f i) <= sqrt B(x,x) sum abs(c_i) sqrt B(f i,f i)     *)
(* (Cauchy-Schwarz for B, P2BFF_PSD_CS) <= sqrt B(x,x) norm c sqrt(trace)    *)
(* (Cauchy-Schwarz in R^N).                                                 *)

let P2BX0_PSD_FRAME_BOUND = prove
 (`!(B:real^N->real^N->real) (M:real^N^N) x.
     (!u. &0 <= B u u) /\ (!u v. B u v = B v u) /\ (!v. linear (\u. lift(B u v))) /\
     invertible M
     ==> B x x <=
         sum(1..dimindex(:N))
            (\i. B (matrix_inv M ** basis i) (matrix_inv M ** basis i)) *
         ((M ** x) dot (M ** x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "sym")
    (CONJUNCTS_THEN2 (LABEL_TAC "lin") ASSUME_TAC))) THEN
  ABBREV_TAC `c:real^N = (M:real^N^N) ** (x:real^N)` THEN
  ABBREV_TAC `Tr = sum(1..dimindex(:N))
                      (\i. (B:real^N->real^N->real) (matrix_inv(M:real^N^N) ** basis i)
                                                    (matrix_inv M ** basis i))` THEN
  SUBGOAL_THEN `&0 <= Tr` ASSUME_TAC THENL
   [EXPAND_TAC "Tr" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x = vsum(1..dimindex(:N)) (\i. (c:real^N)$i % (matrix_inv(M:real^N^N) ** basis i))`
  (LABEL_TAC "xexp") THENL
   [SUBGOAL_THEN `(x:real^N) = matrix_inv(M:real^N^N) ** (c:real^N)` SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z:real^N. matrix_inv(M:real^N^N) ** z`;
                   `\i. (c:real^N)$i % (basis i:real^N)`; `1..dimindex(:N)`] LINEAR_VSUM) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FINITE_NUMSEG; BASIS_EXPANSION; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a w. (B:real^N->real^N->real) (a % w) x = a * B w x` (LABEL_TAC "cmul") THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "lin" (MP_TAC o MATCH_MP LINEAR_CMUL o SPEC `x:real^N`) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real`; `w:real^N`]) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(B:real^N->real^N->real) x x =
    sum(1..dimindex(:N)) (\i. (c:real^N)$i * B x (matrix_inv(M:real^N^N) ** basis i))`
  (LABEL_TAC "Bsum") THENL
   [USE_THEN "xexp" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THEN
    MP_TAC(ISPECL [`\u:real^N. lift((B:real^N->real^N->real) u x)`;
                   `\i. (c:real^N)$i % (matrix_inv(M:real^N^N) ** basis i)`;
                   `1..dimindex(:N)`] LINEAR_VSUM) THEN
    ANTS_TAC THENL [USE_THEN "lin" (fun th -> REWRITE_TAC[th; FINITE_NUMSEG]); ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    REWRITE_TAC[LIFT_DROP; DROP_VSUM; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "cmul" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sym" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(B:real^N->real^N->real) x x <=
    sqrt(B x x) *
    sum(1..dimindex(:N))
       (\i. abs((c:real^N)$i) *
            sqrt(B (matrix_inv(M:real^N^N) ** basis i) (matrix_inv M ** basis i)))`
  ASSUME_TAC THENL
   [USE_THEN "Bsum" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `abs((B:real^N->real^N->real) x (matrix_inv(M:real^N^N) ** basis i)) <=
      sqrt(B x x) * sqrt(B (matrix_inv M ** basis i) (matrix_inv M ** basis i))`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN
      MP_TAC(ISPEC `B:real^N->real^N->real` P2BFF_PSD_CS) THEN
      ANTS_TAC THENL
       [USE_THEN "pos" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "sym" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "lin" (fun th -> REWRITE_TAC[th]);
        DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `matrix_inv(M:real^N^N) ** basis i`]) THEN
        REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((c:real^N)$i) *
                abs((B:real^N->real^N->real) x (matrix_inv(M:real^N^N) ** basis i))` THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((c:real^N)$i) *
                (sqrt((B:real^N->real^N->real) x x) *
                 sqrt(B (matrix_inv(M:real^N^N) ** basis i) (matrix_inv M ** basis i)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "Bsum" (K ALL_TAC) THEN REMOVE_THEN "xexp" (K ALL_TAC) THEN
  REMOVE_THEN "cmul" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
       (\i. abs((c:real^N)$i) *
            sqrt((B:real^N->real^N->real) (matrix_inv(M:real^N^N) ** basis i)
                                          (matrix_inv M ** basis i))) <=
    norm c * sqrt Tr`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`(lambda i. abs((c:real^N)$i)):real^N`;
      `(lambda i. sqrt((B:real^N->real^N->real) (matrix_inv(M:real^N^N) ** basis i)
                                                 (matrix_inv M ** basis i))):real^N`]
     NORM_CAUCHY_SCHWARZ) THEN
    MATCH_MP_TAC(MESON[] `(a:real) = a' /\ (b:real) = b' /\ (d:real) = d' ==> a <= b * d ==> a' <= b' * d'`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA];
      REWRITE_TAC[vector_norm] THEN AP_TERM_TAC THEN REWRITE_TAC[dot] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[vector_norm] THEN AP_TERM_TAC THEN REWRITE_TAC[dot] THEN
      EXPAND_TAC "Tr" THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
      MATCH_MP_TAC SQRT_POW_2 THEN USE_THEN "pos" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  ABBREV_TAC `b = (B:real^N->real^N->real) x x` THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN USE_THEN "pos" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THENL
   [UNDISCH_TAC `b = &0` THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[DOT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b <= norm(c:real^N) * sqrt Tr` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt b * sqrt b <= sqrt b * (norm(c:real^N) * sqrt Tr)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sqrt b * sum(1..dimindex(:N))
                    (\i. abs((c:real^N)$i) *
                         sqrt((B:real^N->real^N->real) (matrix_inv(M:real^N^N) ** basis i)
                                                       (matrix_inv M ** basis i)))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE]];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b pow 2 <= (norm(c:real^N) * sqrt Tr) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_POW_MUL; NORM_POW_2] THEN REAL_ARITH_TAC);;

(* X0.2c R is nondecreasing in time at each point where dR/ds >= 0          *)
(* (derivatives from RFA_MFD_SCALAR_EVOLUTION, HAS_REAL_DERIVATIVE_         *)
(* INCREASING_IMP on [s1,s2]).                                              *)

let P2BX0_SCALAR_MONO = prove
 (`!top atlas a b (g:real->A->real^N^N) x s1 s2.
     ricci_flow_on (top,atlas) a b g /\ a < s1 /\ s1 <= s2 /\ s2 < b /\
     x IN topspace top /\
     (!s dR. s1 <= s /\ s <= s2 /\
             ((\t. mfd_scalar atlas (g t) x) has_real_derivative dR) (atreal s)
             ==> &0 <= dR)
     ==> mfd_scalar atlas (g s1) x <= mfd_scalar atlas (g s2) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?D. !t. a < t /\ t < b
            ==> ((\s. mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                 ((g:real->A->real^N^N) s) x) has_real_derivative D t)
                (atreal t)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `t:real`; `x:A`]
                  RFA_MFD_SCALAR_EVOLUTION) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                 ((g:real->A->real^N^N) s) x`;
                 `D:real->real`; `real_interval[s1,s2]`; `s1:real`; `s2:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* X0.5 The diagonal lemma: limits p3_flow_limit for every Tl > 0 (each    *)
(* with its own W, ts, phi) give, along a subsequence, one limit            *)
(* p2c_flow_limit_with on s <= 0: W from Tl = 1, phi j from Tl = j + 1 at   *)
(* an index sub j beyond the thresholds of the test data of level j.        *)

let P2BX0_EVENTUALLY_UPTO = prove
 (`!(P:num->num->bool) j.
     (!m. m <= j ==> ?k0. !k. k0 <= k ==> P m k)
     ==> ?k0. !k m. k0 <= k /\ m <= j ==> P m k`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE] THEN MESON_TAC[];
    DISCH_THEN(LABEL_TAC "H") THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN USE_THEN "H" MATCH_MP_TAC THEN
      UNDISCH_TAC `m <= (j:num)` THEN ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `k1:num`)] THEN
    USE_THEN "H" (MP_TAC o SPEC `SUC j`) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_TAC `k2:num`) THEN EXISTS_TAC `k1 + k2:num` THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `m <= (j:num) \/ m = SUC j` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `m <= SUC j` THEN ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k1 + k2 <= (k:num)` THEN ARITH_TAC;
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      UNDISCH_TAC `k1 + k2 <= (k:num)` THEN ARITH_TAC]]);;

(* A strictly increasing sequence above given thresholds. *)

let P2BX0_SUBSEQ_ABOVE = prove
 (`!kap:num->num. ?sub. p3_subseq sub /\ !j. kap j <= sub j`,
  GEN_TAC THEN EXISTS_TAC `\j. j + nsum(0..j) (kap:num->num)` THEN
  REWRITE_TAC[p3_subseq] THEN CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN ARITH_TAC;
    INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN ARITH_TAC]);;

(* X0.5 (continued) the diagonal lemma itself.                               *)

let P2BX0_FLOW_LIMIT_DIAG = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl.
     (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top,atlas) g xl Tl)
     ==> ?sub W phi. p3_subseq sub /\
                     p2c_flow_limit_with (\k. V (sub k)) (x o sub) (t o sub) (Q o sub)
                                         {s | s <= &0} (top,atlas) g xl W phi`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. p3_flow_limit (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) x t Q (top:B topology,atlas) g xl (&n + &1)`
  MP_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3_flow_limit] THEN DISCH_THEN(LABEL_TAC "pl") THEN
  SUBGOAL_THEN
   `hausdorff_space (top:B topology) /\
    smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
    (xl:B) IN topspace top /\ (!k. &0 < (Q:num->real) k)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "pl" (MP_TAC o SPEC `0`) THEN SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "pl" (MP_TAC o GEN `n:num` o last o CONJUNCTS o SPEC `n:num`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `WW:num->num->B->bool` (X_CHOOSE_THEN `TS:num->num->real`
    (X_CHOOSE_THEN `PH:num->num->B->A` (LABEL_TAC "data")))) THEN
  (* Monotonicity and compact exhaustion for WW 0. *)
  SUBGOAL_THEN
   `(!k. open_in (top:B topology) (WW 0 k) /\ (WW:num->num->B->bool) 0 k SUBSET WW 0 (SUC k)) /\
    UNIONS {WW 0 k | k IN (:num)} = topspace top /\
    (!k. compact_in top (top closure_of WW 0 k)) /\
    (!k. WW 0 k SUBSET top closure_of WW 0 k)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "data" (MP_TAC o SPEC `0`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!k. (WW:num->num->B->bool) 0 k SUBSET top closure_of WW 0 k`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  (* Thresholds of level j. *)
  SUBGOAL_THEN
   `!j. ?k0. !k m. k0 <= k /\ m <= j
                   ==> top closure_of (WW:num->num->B->bool) 0 j SUBSET WW j k /\
                       --((TS:num->num->real) j k) <= --(&j) /\
                       !s y. --(&j) <= s /\ s <= &0 /\ y IN top closure_of WW 0 j
                             ==> lck_dist2 m
                                   (metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas y) ((g:real->B->real^3^3) s))
                                   (\z. (Q:num->real) k %%
                                        rfs_pullback
                                          (rfs_vatlas (V k) (t k + s / Q k))
                                          ((PH:num->num->B->A) j k o
                                           chart_inv (chart_at atlas y))
                                          (rfs_vmetric (V k) (t k + s / Q k)) z)
                                   (SND(chart_at atlas y) y) < inv(&j + &1)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC(REWRITE_RULE[] (ISPEC
      `\m k. top closure_of (WW:num->num->B->bool) 0 j SUBSET WW j k /\
             --((TS:num->num->real) j k) <= --(&j) /\
             !s y. --(&j) <= s /\ s <= &0 /\ y IN top closure_of WW 0 j
                   ==> lck_dist2 m
                         (metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas y) ((g:real->B->real^3^3) s))
                         (\z. (Q:num->real) k %%
                              rfs_pullback
                                (rfs_vatlas (V k) (t k + s / Q k))
                                ((PH:num->num->B->A) j k o chart_inv (chart_at atlas y))
                                (rfs_vmetric (V k) (t k + s / Q k)) z)
                         (SND(chart_at atlas y) y) < inv(&j + &1)` P2BX0_EVENTUALLY_UPTO)) THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "data" (MP_TAC o last o CONJUNCTS o SPEC `j:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`top closure_of (WW:num->num->B->bool) 0 j`; `m:num`;
                               `inv(&j + &1)`; `--(&j)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `j:num` REAL_POS) THEN
      SIMP_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:num->num` (LABEL_TAC "kap")) THEN
  MP_TAC(SPEC `kap:num->num` P2BX0_SUBSEQ_ABOVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`sub:num->num`; `(WW:num->num->B->bool) 0`; `\j. (PH:num->num->B->A) j (sub j)`] THEN
  ASM_REWRITE_TAC[p2c_flow_limit_with; o_THM; IN_ELIM_THM; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `(WW:num->num->B->bool) 0`; `K:B->bool`]
                P2B_COMPACT_IN_EXHAUST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `j0:num`) THEN
  MP_TAC(SPEC `--a:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `Na:num`) THEN
  MP_TAC(SPEC `eta:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ne:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `j0 + m + Na + Ne:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(K:B->bool) SUBSET (WW:num->num->B->bool) 0 j` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(WW:num->num->B->bool) 0 j0` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `(WW:num->num->B->bool) 0` P2B_EXHAUST_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    UNDISCH_TAC `j0 + m + Na + Ne <= (j:num)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(kap:num->num) j <= (sub:num->num) j /\ m <= (j:num)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `j0 + m + Na + Ne <= (j:num)` THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "kap" (MP_TAC o SPECL [`j:num`; `(sub:num->num) j`; `0`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  USE_THEN "kap" (MP_TAC o SPECL [`j:num`; `(sub:num->num) j`; `m:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "close"))) THEN
  SUBGOAL_THEN `--(&j) <= a` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `--a <= &Na /\ &Na <= &j ==> --(&j) <= a`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `j0 + m + Na + Ne <= (j:num)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> s <= &0` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET {s:real | s <= &0}` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "data" (MP_TAC o SPEC `j:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`(sub:num->num) j`; `s:real`] o
               el 5 o CONJUNCTS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN EXISTS_TAC `psi:A->B` THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`(WW:num->num->B->bool) j (sub j)`;
                          `IMAGE ((PH:num->num->B->A) j (sub j)) (WW j (sub j))`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `top closure_of (WW:num->num->B->bool) 0 j` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&j + &1)` THEN CONJ_TAC THENL
   [USE_THEN "close" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]; ASM SET_TAC[]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&Ne)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(Ne = 0)` THEN UNDISCH_TAC `j0 + m + Na + Ne <= (j:num)` THEN
    ARITH_TAC]);;

(* X0.4b Views that agree at the times t k + s / Q k, s in J, have the same *)
(* limits p2c_flow_limit_with on J.                                         *)

let P2BX0_FLOW_LIMIT_WITH_CONG = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V' x t t' Q J (top:B topology) atlas g xl W phi.
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!k s. s IN J
            ==> rfs_vtop (V' k) (t' k + s / Q k) = rfs_vtop (V k) (t k + s / Q k) /\
                rfs_vatlas (V' k) (t' k + s / Q k) = rfs_vatlas (V k) (t k + s / Q k) /\
                rfs_vmetric (V' k) (t' k + s / Q k) = rfs_vmetric (V k) (t k + s / Q k))
     ==> p2c_flow_limit_with V' x t' Q J (top,atlas) g xl W phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "cong")) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> (s:real) IN J` (LABEL_TAC "inJ") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET (J:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] o
    check (fun th -> is_forall(concl th) &&
                     length(fst(strip_forall(concl th))) = 5)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REMOVE_THEN "k0" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "cl"))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "cong" (MP_TAC o SPECL [`k:num`; `s:real`]) THEN
    ANTS_TAC THENL [USE_THEN "inJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    USE_THEN "cong" (MP_TAC o SPECL [`k:num`; `s:real`]) THEN
    ANTS_TAC THENL [USE_THEN "inJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* X0.4c A Ricci flow on (c,b) shifted by an interior time s0 is a flow up  *)
(* to 0 on (a,0] whenever c < s0 + a (RICCI_FLOW_TRANSLATE, then            *)
(* P2CF_RFO_UPTO of pc_p2c_fview).                                          *)

let P2BX0_FLOW_UPTO_SHIFT = prove
 (`!top atlas c b (g:real->A->real^3^3) a s0.
     ricci_flow_on (top,atlas) c b g /\ c < s0 + a /\ a < &0 /\ s0 < b
     ==> rfs_flow_upto (top,atlas) a (&0) (\t. g(s0 + t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (c - s0) (b - s0)
                  (\t. (g:real->A->real^3^3) (s0 + t))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(c - s0 = c + --s0) /\ (b - s0 = b + --s0) /\
      (\t. (g:real->A->real^3^3) (s0 + t)) = (\t. g (t - --s0))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC; REAL_ARITH_TAC;
        ABS_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
      MATCH_MP_TAC RICCI_FLOW_TRANSLATE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CF_RFO_UPTO THEN
  MAP_EVERY EXISTS_TAC [`c - s0:real`; `b - s0:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* X0.1b The picked points along pp k (MT Prop 9.39, first step): from      *)
(* R(pp k) d(p,pp k)^2 -> infinity, points q k with R(q k) >= R(pp k),      *)
(* R(q k) > 0, R(q k) d(p,q k)^2 -> infinity, and for every A eventually    *)
(* R <= 4 R(q k) on the ball about q k of radius A / sqrt R(q k).            *)

let P2BX0_PICKED_POINTS = prove
 (`!top atlas (g:A->real^N^N) p (pp:num->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\
     continuous_map (top,euclideanreal) (mfd_scalar atlas g) /\
     (!y. y IN topspace top ==> &0 <= mfd_scalar atlas g y) /\
     (?x. x IN topspace top /\ &0 < mfd_scalar atlas g x) /\
     p IN topspace top /\ (!k. pp k IN topspace top) /\
     (!M. ?N. !k. N <= k
                  ==> M < mfd_scalar atlas g (pp k) * mfd_dist (top,atlas) g p (pp k) pow 2)
     ==> ?q:num->A. (!k. q k IN topspace top /\ &0 < mfd_scalar atlas g (q k) /\
                  mfd_scalar atlas g (pp k) <= mfd_scalar atlas g (q k)) /\
             (!M. ?N. !k. N <= k
                          ==> M < mfd_scalar atlas g (q k) *
                                  mfd_dist (top,atlas) g p (q k) pow 2) /\
             (!A. ?N. !k y. N <= k /\
                            y IN mfd_ball (top,atlas) g (q k)
                                          (A * inv(sqrt(mfd_scalar atlas g (q k))))
                            ==> mfd_scalar atlas g y <= &4 * mfd_scalar atlas g (q k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nonneg")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `xp:A` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "div")))))))))) THEN
  ABBREV_TAC `R = mfd_scalar (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
  ABBREV_TAC `d = mfd_dist (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                           (g:A->real^N^N)` THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) x y`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?q. q IN topspace top /\ &0 < (R:A->real) q /\ R((pp:num->A) k) <= R q /\
            (&0 < R(pp k) /\ &0 < d p (pp k)
             ==> d (pp k) q < d p (pp k) / &2 /\
                 (d p (pp k) / &2) pow 2 * R(pp k) <=
                 (d p (pp k) / &2 - d (pp k) q) pow 2 * R q /\
                 !y. mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) q y /\
                     d q y < (d p (pp k) / &2 - d (pp k) q) / &2
                     ==> R y <= &4 * R q)`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `&0 < (R:A->real)((pp:num->A) k) /\ &0 < (d:A->A->real) p (pp k)` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `R:A->real`; `(pp:num->A) k`;
                     `(d:A->A->real) p ((pp:num->A) k) / &2`] P2BX0_POINT_PICK) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `q:A` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_CASES_TAC `&0 < (R:A->real)((pp:num->A) k)` THENL
       [EXISTS_TAC `(pp:num->A) k` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_MESON_TAC[];
        EXISTS_TAC `xp:A` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 <= (R:A->real)((pp:num->A) k)` MP_TAC THENL
         [USE_THEN "nonneg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->A` (LABEL_TAC "q") o REWRITE_RULE[SKOLEM_THM]) THEN
  EXISTS_TAC `q:num->A` THEN
  CONJ_TAC THENL [USE_THEN "q" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  (* Eventually R(pp k) > 0 and d p (pp k) > 0, with the picking facts. *)
  SUBGOAL_THEN
   `!M. ?N. !k. N <= k
                ==> M < (R:A->real)((pp:num->A) k) * (d:A->A->real) p (pp k) pow 2 /\
                    &0 < R(pp k) /\ &0 < d p (pp k)`
  (LABEL_TAC "div2") THENL
   [X_GEN_TAC `M:real` THEN USE_THEN "div" (MP_TAC o SPEC `abs M`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (R:A->real)((pp:num->A) k)` ASSUME_TAC THENL
     [USE_THEN "nonneg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (d:A->A->real) p ((pp:num->A) k)` ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (R:A->real)((pp:num->A) k) * (d:A->A->real) p (pp k) pow 2`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < (R:A->real)((pp:num->A) k) * (d:A->A->real) p (pp k) pow 2` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
      REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < (R:A->real)((pp:num->A) k) * (d:A->A->real) p (pp k) pow 2` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; REAL_LT_REFL]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `M:real` THEN USE_THEN "div2" (MP_TAC o SPEC `&4 * abs M`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "q" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(d:A->A->real) p ((pp:num->A) k) / &2 <= d p ((q:num->A) k)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(d:A->A->real) p ((pp:num->A) k) <= d p ((q:num->A) k) + d (q k) (pp k)`
      MP_TAC THENL
       [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(d:A->A->real) ((q:num->A) k) ((pp:num->A) k) = d (pp k) (q k)`
      SUBST1_TAC THENL
       [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (d:A->A->real) p ((pp:num->A) k) / &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `((d:A->A->real) p ((pp:num->A) k) / &2) pow 2 <= d p ((q:num->A) k) pow 2`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(R:A->real)((pp:num->A) k) * ((d:A->A->real) p (pp k) / &2) pow 2 <=
      R((q:num->A) k) * d p (q k) pow 2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `&4 * abs M < (R:A->real)((pp:num->A) k) * (d:A->A->real) p (pp k) pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `A:real` THEN USE_THEN "div2" (MP_TAC o SPEC `&16 * A pow 2`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "q" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `rho = ((d:A->A->real) p ((pp:num->A) k) / &2 - d (pp k) ((q:num->A) k)) / &2` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `y IN mfd_ball (top,atlas) (g:A->real^N^N) ((q:num->A) k)
                             (A * inv (sqrt ((R:A->real) (q k))))` THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `&4`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `A * inv(sqrt((R:A->real)((q:num->A) k)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt((R:A->real)((q:num->A) k))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
  ASM_CASES_TAC `A <= &0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `(d:A->A->real) p ((pp:num->A) k) / &2 - d (pp k) ((q:num->A) k) = &2 * rho`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "rho" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `((d:A->A->real) p ((pp:num->A) k) / &2) pow 2 * (R:A->real)(pp k) <=
               (&2 * rho) pow 2 * R ((q:num->A) k)` THEN
  UNDISCH_TAC `&16 * A pow 2 < (R:A->real)((pp:num->A) k) * (d:A->A->real) p (pp k) pow 2` THEN
  REAL_ARITH_TAC);;

(* X0.2d / X0.3 The hypotheses of ANCIENT_COMPACT for the shifted flows     *)
(* g(s0 + t), t <= 0, based at the picked points q k with Q k = R(s0,q k):  *)
(* flows up to 0 and complete slices; abs Rm <= 2 Q k on the balls of        *)
(* radius A / sqrt Q k for all earlier times (R <= 4 Q k there at s0,        *)
(* R nondecreasing in time, abs Rm <= R/2); the volume at radius             *)
(* (1/2) / sqrt Q k from kappa-noncollapsing (abs Rm <= 4 Q k on the         *)
(* parabolic ball).                                                          *)

let P2BX0_CURV_ON_BALLS = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) A N.
     p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\
     (!k. q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
     (!k y. N <= k /\
            y IN mfd_ball (top,atlas) (g s0) (q k) (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
            ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q k))
     ==> !k s y. N <= k /\ s <= s0 /\
                 y IN mfd_ball (top,atlas) (g s0) (q k)
                                (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                 ==> mfd_rm_norm atlas (g s) y <= &2 * mfd_scalar atlas (g s0) (q k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "q") (LABEL_TAC "ball")))) THEN
  REWRITE_TAC[p2b_ancflow0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nonflat")
    (CONJUNCTS_THEN2 (LABEL_TAC "drds") (LABEL_TAC "knc")))))))))) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) ((q:num->B) k)
                             (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_on (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (s - &1) b
                  (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
    riemannian_metric atlas ((g:real->B->real^3^3) s)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                               (s - &1) b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) y / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) s) y <= mfd_scalar atlas (g s0) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `s - &1`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s':real`; `dR:real`] THEN STRIP_TAC THEN
      USE_THEN "drds" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`s':real`; `y:B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_scalar atlas ((g:real->B->real^3^3) s0) y <=
    &4 * mfd_scalar atlas (g s0) ((q:num->B) k)`
  MP_TAC THENL
   [USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_scalar atlas ((g:real->B->real^3^3) s) y <= mfd_scalar atlas (g s0) y` THEN
  REAL_ARITH_TAC);;

let P2BX0_ANCIENT_HYPS = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B).
     p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\
     (!k. q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
     (!A. ?N. !k y. N <= k /\
                    y IN mfd_ball (top,atlas) (g s0) (q k)
                                  (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                    ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q k))
     ==> (!k. hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. g(s0 + t))) /\
              (!t. t <= &0 ==> mfd_complete (top,atlas) (g(s0 + t))) /\
              q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
         (!A a. &0 < A /\ a < &0
                ==> ?CA N. !k s y. N <= k /\ a <= s /\ s <= &0 /\
                                   y IN mfd_ball (top,atlas) (g(s0 + &0)) (q k)
                                          (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                                   ==> mfd_rm_norm atlas
                                         (g(s0 + s / mfd_scalar atlas (g s0) (q k))) y <=
                                       CA * mfd_scalar atlas (g s0) (q k)) /\
         (?r0 kappa' N. &0 < r0 /\ &0 < kappa' /\
            !k. N <= k
                ==> ?v. mfd_has_volume (top,atlas) (g(s0 + &0))
                          (mfd_ball (top,atlas) (g(s0 + &0)) (q k)
                             (r0 * inv(sqrt(mfd_scalar atlas (g s0) (q k))))) v /\
                        kappa' * (r0 * inv(sqrt(mfd_scalar atlas (g s0) (q k)))) pow 3 <= v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "anc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "q") (LABEL_TAC "ball")))) THEN
  USE_THEN "anc" (MP_TAC o REWRITE_RULE[p2b_ancflow0]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nonflat")
    (CONJUNCTS_THEN2 (LABEL_TAC "drds") (LABEL_TAC "knc")))))))))) THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "rf" (MP_TAC o SPEC `s0 - &1`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. (g:real->B->real^3^3)(s0 + t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX0_FLOW_UPTO_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`s0 + a - &1`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t <= &0 ==> mfd_complete (top,atlas) ((g:real->B->real^3^3)(s0 + t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "comp" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`A:real`; `a:real`] THEN STRIP_TAC THEN
    USE_THEN "ball" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
    MAP_EVERY EXISTS_TAC [`&2`; `N:num`] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `y:B`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `b:real`; `s0:real`; `q:num->B`; `A:real`; `N:num`]
                  P2BX0_CURV_ON_BALLS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`
    ASSUME_TAC THENL [USE_THEN "q" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> s0 + x <= s0`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  USE_THEN "ball" (X_CHOOSE_TAC `N:num` o SPEC `&1`) THEN
  MAP_EVERY EXISTS_TAC [`&1 / &2`; `kappa:real`; `N:num`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)` THEN
  SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
   [EXPAND_TAC "Qk" THEN USE_THEN "q" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  ABBREV_TAC `r = &1 / &2 * inv(sqrt Qk)` THEN
  SUBGOAL_THEN `&0 < r /\ inv(r pow 2) = &4 * Qk /\ r <= &1 * inv(sqrt Qk)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    SUBGOAL_THEN `&0 < sqrt Qk` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `&0 < Qk` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "knc" (MP_TAC o SPEC `r:real`) THEN
  REWRITE_TAC[rfs_flow_view] THEN REWRITE_TAC[rfs_kappa_noncollapsed] THEN
  DISCH_THEN(MP_TAC o SPECL [`s0:real`; `(q:num->B) k`; `r:real`]) THEN
  REWRITE_TAC[rfs_flow_view; rfs_vball; rfs_parabolic_exists; rfs_persists; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s < b` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rf" (MP_TAC o SPEC `s0 - &1`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[ricci_flow_on]] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * Qk` THEN CONJ_TAC THENL
     [EXPAND_TAC "Qk" THEN
      MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:real->B->real^3^3`; `b:real`; `s0:real`; `q:num->B`; `&1`; `N:num`]
                    P2BX0_CURV_ON_BALLS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0) ((q:num->B) k) r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

(* X0.10d The time derivative of Gamma(u, W) vanishes for a field W that is *)
(* parallel for G t (LCHRISTOFFEL_EVOLUTION; the three nabla Ric terms vanish *)
(* by P2BX0_NABLA_RIC_W12 and P2BX0_NABLA_W_RIC).                          *)

let P2BX0_DGAMMA_PAR = prove
 (`!U a b (G:real->real^N->real^N^N) t y u (W:real^N->real^N).
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel (G t) z w (W z) = vec 0)
     ==> ((\s. christoffel (G (drop s)) y u (W y)) has_vector_derivative vec 0) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`; `t:real`;
                 `y:real^N`; `u:real^N`; `(W:real^N->real^N) y`] LCHRISTOFFEL_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `w:real^N = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
  SUBGOAL_THEN `(G:real->real^N->real^N^N) t y ** w = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `lric2`)) (concl th) = false &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lnabla")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `lnabla 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y
        (\m. if m = 1 then (W:real^N->real^N) y else if m = 2 then basis k else u) = &0 /\
      lnabla 2 (G t) (lric2 (G t)) y
        (\m. if m = 1 then u else if m = 2 then basis k else W y) = &0 /\
      lnabla 2 (G t) (lric2 (G t)) y
        (\m. if m = 1 then u else if m = 2 then W y else basis k) = &0`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX0_NABLA_RIC_W12 THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `W:real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX0_NABLA_W_RIC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX0_NABLA_RIC_W12 THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `W:real^N->real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
                LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `w:real^N = matrix_inv((G:real->real^N->real^N^N) t y) ** (G t y ** w)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

(* X0.10e A smooth space-time family Y(t,z) that is parallel for G t in z  *)
(* at every time has a time derivative that is parallel for G t: d/dt of    *)
(* the parallel equation, with the mixed partials of LRG_TIME_SPACE_SWAP,   *)
(* the product rule LRG_HAS_DERIVATIVE_LINFAM in t and P2BX0_DGAMMA_PAR.    *)

let P2BX0_LRICCI_FLOW_SUBSET = prove
 (`!U V a b (G:real->real^N->real^N^N).
     lricci_flow U a b G /\ open V /\ V SUBSET U ==> lricci_flow V a b G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let P2BX0_SLICE_SMOOTH_OPEN = prove
 (`!(Y:real^(1,N)finite_sum->real^P) Wb t0.
     open Wb /\ smooth_map_on Wb Y
     ==> open {x:real^N | pastecart (lift t0) x IN Wb} /\
         smooth_map_on {x:real^N | pastecart (lift t0) x IN Wb}
                       (\x. Y(pastecart (lift t0) x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^N | pastecart (lift t0) x IN Wb}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:real^N. (Y:real^(1,N)finite_sum->real^P) (pastecart (lift t0) x)) =
                Y o (\x. pastecart (lift t0) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `Wb:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

let P2BX0_DT_PARALLEL = prove
 (`!U a b (G:real->real^N->real^N^N) (Y:real^(1,N)finite_sum->real^N) Wb t0 z0 w.
     lricci_flow U a b G /\ open Wb /\ Wb SUBSET interval(lift a,lift b) PCROSS U /\
     smooth_map_on Wb Y /\ pastecart (lift t0) z0 IN Wb /\
     (!t z v. pastecart (lift t) z IN Wb
              ==> frechet_derivative (\x. Y(pastecart (lift t) x)) (at z) v +
                  christoffel (G t) z v (Y(pastecart (lift t) z)) = vec 0)
     ==> frechet_derivative
           (\x. frechet_derivative Y (at (pastecart (lift t0) x))
                                   (pastecart (lift(&1)) (vec 0))) (at z0) w +
         christoffel (G t0) z0 w
           (frechet_derivative Y (at (pastecart (lift t0) z0))
                                 (pastecart (lift(&1)) (vec 0))) = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "par")))))) THEN
  SUBGOAL_THEN `a < t0 /\ t0 < b /\ (z0:real^N) IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `Wb SUBSET interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `pastecart (lift t0) (z0:real^N)`) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [USE_THEN "rf" (fun th -> MESON_TAC[REWRITE_RULE[lricci_flow] th]); ALL_TAC] THEN
  (* The slice at t0 is parallel on U0. *)
  ABBREV_TAC `U0 = (U:real^N->bool) INTER {x:real^N | pastecart (lift t0) x IN Wb}` THEN
  MP_TAC(ISPECL [`Y:real^(1,N)finite_sum->real^N`; `Wb:real^(1,N)finite_sum->bool`; `t0:real`]
                P2BX0_SLICE_SMOOTH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (U0:real^N->bool) /\ (z0:real^N) IN U0 /\ U0 SUBSET U`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U0" THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER; IN_ELIM_THM; INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U0:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`; `t0:real`;
                 `z0:real^N`; `w:real^N`; `\x:real^N. (Y:real^(1,N)finite_sum->real^N)
                                                      (pastecart (lift t0) x)`]
                P2BX0_DGAMMA_PAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX0_LRICCI_FLOW_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{x:real^N | pastecart (lift t0) x IN Wb}` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "U0" THEN REWRITE_TAC[INTER_SUBSET];
      MAP_EVERY X_GEN_TAC [`z:real^N`; `v:real^N`] THEN DISCH_TAC THEN
      USE_THEN "par" MATCH_MP_TAC THEN UNDISCH_TAC `(z:real^N) IN U0` THEN
      EXPAND_TAC "U0" THEN SIMP_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative; VECTOR_MUL_RZERO] THEN DISCH_TAC THEN
  (* B: the product rule in time. *)
  SUBGOAL_THEN
   `(Y:real^(1,N)finite_sum->real^N) differentiable at (pastecart (lift t0) z0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Wb:real^(1,N)finite_sum->bool`; `Y:real^(1,N)finite_sum->real^N`;
                   `pastecart (lift t0) (z0:real^N)`; `pastecart (lift t0) (z0:real^N)`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1 v:real^N. christoffel ((G:real->real^N->real^N^N) (drop s)) z0 w v`;
                 `\s:real^1. (Y:real^(1,N)finite_sum->real^N) (pastecart s z0)`;
                 `\s':real^1. frechet_derivative (Y:real^(1,N)finite_sum->real^N)
                                (at (pastecart (lift t0) z0)) (pastecart s' (vec 0))`;
                 `interval(lift a,lift b)`; `lift t0`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop s)`; `z0:real^N`]
                    LRG_CHRISTOFFEL_LINEAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "rf" (MP_TAC o REWRITE_RULE[lricci_flow]) THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                     `t0:real`; `z0:real^N`; `w:real^N`; `basis i:real^N`]
                    LRG_FLOW_GAMMA_VDERIV) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC LRG_HAS_DERIVATIVE_TIME_CURVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) o check
    (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "drop")) (concl th) &&
               can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel"))
                   (concl th) &&
               can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative"))
                   (concl th))) THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN DISCH_TAC THEN
  (* A: the mixed partials. *)
  MP_TAC(ISPECL [`Wb:real^(1,N)finite_sum->bool`; `Y:real^(1,N)finite_sum->real^N`;
                 `t0:real`; `z0:real^N`; `w:real^N`] LRG_TIME_SPACE_SWAP) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  (* phi = A + B vanishes near lift t0. *)
  SUBGOAL_THEN
   `((\s:real^1. frechet_derivative (\x. (Y:real^(1,N)finite_sum->real^N) (pastecart s x))
                                    (at z0) w +
                 christoffel ((G:real->real^N->real^N^N) (drop s)) z0 w (Y(pastecart s z0)))
     has_derivative (\h. vec 0)) (at (lift t0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\s:real^1. vec 0:real^N` THEN
    UNDISCH_TAC `open (Wb:real^(1,N)finite_sum->bool)` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift t0) (z0:real^N)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (s:real^1) (z0:real^N) IN Wb` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; DIST_PASTECART_CANCEL] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "par" (MP_TAC o SPECL [`drop s`; `z0:real^N`; `w:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP]; REWRITE_TAC[LIFT_DROP] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s:real^1. frechet_derivative (\x. (Y:real^(1,N)finite_sum->real^N) (pastecart s x))
                                    (at z0) w +
                 christoffel ((G:real->real^N->real^N^N) (drop s)) z0 w (Y(pastecart s z0)))
     has_derivative
     (\h. drop h % frechet_derivative
                     (\x. frechet_derivative Y (at (pastecart (lift t0) x))
                                             (pastecart (lift(&1)) (vec 0))) (at z0) w +
          christoffel (G t0) z0 w
            (frechet_derivative Y (at (pastecart (lift t0) z0)) (pastecart h (vec 0)))))
     (at (lift t0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s:real^1. frechet_derivative (\x. (Y:real^(1,N)finite_sum->real^N) (pastecart s x))
                                   (at z0) w +
                christoffel ((G:real->real^N->real^N^N) (drop s)) z0 w (Y(pastecart s z0))`;
    `\h:real^1. drop h % frechet_derivative
                  (\x. frechet_derivative (Y:real^(1,N)finite_sum->real^N)
                         (at (pastecart (lift t0) x)) (pastecart (lift(&1)) (vec 0))) (at z0) w +
                christoffel ((G:real->real^N->real^N^N) t0) z0 w
                  (frechet_derivative Y (at (pastecart (lift t0) z0)) (pastecart h (vec 0)))`;
    `\h:real^1. vec 0:real^N`; `lift t0`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]);;

(* X0.10f Two linearly independent vectors annihilated by the curvature    *)
(* force R = 0 in dimension 3: for any w, R(u,v)w is G-orthogonal to e1 and *)
(* e2 (metric antisymmetry), hence a multiple of n = G^-1 (e1 x e2), and   *)
(* G-orthogonal to n.                                                       *)


let P2BX0_PERP2_CROSS = prove
 (`!e1 e2 z:real^3.
     ~collinear {vec 0,e1,e2} /\ z dot e1 = &0 /\ z dot e2 = &0
     ==> ?c. z = c % (e1 cross e2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(e1 cross e2 = vec 0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CROSS_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `collinear {vec 0, e1 cross e2, z:real^3}` MP_TAC THENL
   [REWRITE_TAC[GSYM CROSS_EQ_0] THEN
    SUBGOAL_THEN `(e1 cross e2) cross (z:real^3) = (e1 dot z) % e2 - (e2 dot z) % e1`
    SUBST1_TAC THENL [VEC3_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COLLINEAR_LEMMA] THEN STRIP_TAC THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]]);;

let P2BX0_TWO_KILLED_RIEMANN0 = prove
 (`!U (G:real^3->real^3^3) y e1 e2.
     metric_field U G /\ y IN U /\ ~collinear {vec 0,e1,e2} /\
     (!u v. lriemann G y u v e1 = vec 0) /\ (!u v. lriemann G y u v e2 = vec 0)
     ==> !u v w. lriemann G y u v w = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n:real^3. (G:real^3->real^3^3) y ** n = e1 cross e2` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `matrix_inv((G:real^3->real^3^3) y) ** (e1 cross e2)` THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(G:real^3->real^3^3) y ** n = e1 cross e2` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[CROSS_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n dot (e1 cross e2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`]
                  LRG_METRIC_POS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Any R(u,v)w is a multiple of n. *)
  SUBGOAL_THEN `!u v w. ?c. lriemann (G:real^3->real^3^3) y u v w = c % n` (LABEL_TAC "mult") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`e1:real^3`; `e2:real^3`;
                   `(G:real^3->real^3^3) y ** lriemann G y u v w`] P2BX0_PERP2_CROSS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THENL
       [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                       `v:real^3`; `w:real^3`; `e1:real^3`] LRIEMANN_METRIC_ANTISYM);
        MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                       `v:real^3`; `w:real^3`; `e2:real^3`] LRIEMANN_METRIC_ANTISYM)] THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_NEG_0];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN EXISTS_TAC `c:real` THEN
    MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c * (n dot (e1 cross e2)) = &0 ==> c = &0` (LABEL_TAC "canc") THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  (* R(u,v)n = 0. *)
  SUBGOAL_THEN `!u v. lriemann (G:real^3->real^3^3) y u v n = vec 0` (LABEL_TAC "n0") THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "mult" (X_CHOOSE_TAC `c:real` o SPECL [`u:real^3`; `v:real^3`; `n:real^3`]) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                   `v:real^3`; `n:real^3`; `n:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x = --x ==> x = &0`)) THEN
    DISCH_THEN(fun th -> USE_THEN "canc" (MP_TAC o C MATCH_MP th)) THEN
    SIMP_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  USE_THEN "mult" (X_CHOOSE_TAC `c:real` o SPECL [`u:real^3`; `v:real^3`; `w:real^3`]) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`;
                 `v:real^3`; `w:real^3`; `n:real^3`] LRIEMANN_METRIC_ANTISYM) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_NEG_0; MATRIX_VECTOR_MUL_RMUL;
                  DOT_RMUL] THEN
  DISCH_THEN(fun th -> USE_THEN "canc" (MP_TAC o C MATCH_MP th)) THEN
  SIMP_TAC[VECTOR_MUL_LZERO]);;

(* X0.10g Pointwise algebra.  P-field of a kernel vector of Ric: if Ric(v,.) *)
(* = 0 then the raised P(v,.) is (R/2) v, so the normalised P-field at v is *)
(* v for a unit v.  One-dimensional kernel: with the rank-one identity of P  *)
(* and R > 0, a kernel vector is a multiple of a unit kernel vector n.      *)

let P2BX0_PFIELD_KER = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U /\ (!w. lricci G y v w = &0)
     ==> matrix_inv(G y) **
         ((lambda k. lpcurv G y (\m. if m = 1 then v else basis k)):real^N) =
         (lscalar G y / &2) % v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`; `w:real^N`]
                RFA_PFIELD_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `matrix_inv((G:real^N->real^N^N) y) **
                  ((lambda k. lpcurv G y (\m. if m = 1 then v else basis k)):real^N)`]
                LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`; `v:real^N`]
                LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lpcurv; lmetric2; lric2; MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BX0_NFIELD_KER = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U /\ (!w. lricci G y v w = &0) /\ &0 < lscalar G y /\
     v dot (G y ** v) = &1
     ==> inv(sqrt((matrix_inv(G y) **
                   ((lambda k. lpcurv G y (\m. if m = 1 then v else basis k)):real^N)) dot
                  (G y ** (matrix_inv(G y) **
                   ((lambda k. lpcurv G y (\m. if m = 1 then v else basis k)):real^N))))) %
         (matrix_inv(G y) **
          ((lambda k. lpcurv G y (\m. if m = 1 then v else basis k)):real^N)) = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`]
                P2BX0_PFIELD_KER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `c = lscalar (G:real^N->real^N^N) y / &2` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; REAL_MUL_RID] THEN
  SUBGOAL_THEN `sqrt(c * c) = c` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let P2BX0_KER_RIC_MULT = prove
 (`!U (G:real^N->real^N^N) y v n.
     metric_field U G /\ y IN U /\
     (!u w. lpcurv G y (\m. u) * lpcurv G y (\m. w) =
            lpcurv G y (\m. if m = 1 then u else w) pow 2) /\
     &0 < lscalar G y /\
     (!w. lricci G y v w = &0) /\ (!w. lricci G y n w = &0) /\ n dot (G y ** n) = &1
     ==> v = (v dot (G y ** n)) % n`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `cc = (v:real^N) dot ((G:real^N->real^N^N) y ** n)` THEN
  ABBREV_TAC `e:real^N = v - cc % n` THEN
  SUBGOAL_THEN `!w. lricci (G:real^N->real^N^N) y e w = &0` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN
    SUBGOAL_THEN `e:real^N = &1 % v + --cc % n`
    SUBST1_TAC THENL [EXPAND_TAC "e" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `&1`; `v:real^N`;
                   `--cc:real`; `n:real^N`; `w:real^N`]
                  RFA_LRICCI_LCOMB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e dot ((G:real^N->real^N^N) y ** n) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lpcurv (G:real^N->real^N^N) y (\m. e) = lscalar G y / &2 * (e dot (G y ** e)) /\
    lpcurv G y (\m. n) = lscalar G y / &2 /\
    lpcurv G y (\m. if m = 1 then e else n) = &0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[lpcurv; lmetric2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e dot ((G:real^N->real^N^N) y ** e) = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`e:real^N`; `n:real^N`] o check (fun th ->
      can (term_match [] `!u w. lpcurv (G:real^N->real^N^N) y (\m. u) * lpcurv G y (\m. w) =
                                lpcurv G y (\m. if m = 1 then u else w) pow 2`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_RZERO; REAL_ENTIRE] THEN
    SUBGOAL_THEN `~(lscalar (G:real^N->real^N^N) y / &2 = &0)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e:real^N = vec 0` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `e:real^N`]
                  LRG_METRIC_POS) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  EXPAND_TAC "e" THEN EXPAND_TAC "cc" THEN VECTOR_ARITH_TAC);;

(* The unit length of a moving vector Y(t) for G t: d/dt <Y, G Y> = 0 gives  *)
(* <dY/dt, G Y> = Ric(Y,Y) (LRG_HAS_DERIVATIVE_DOT_MATVEC, LRG_FLOW_VDERIV). *)

let P2BX0_UNIT_DT = prove
 (`!U a b (G:real->real^N->real^N^N) (Y:real^(1,N)finite_sum->real^N) t0 z0 d.
     lricci_flow U a b G /\ a < t0 /\ t0 < b /\ z0 IN U /\
     Y differentiable at (pastecart (lift t0) z0) /\ &0 < d /\
     (!t. abs(t - t0) < d
          ==> Y(pastecart (lift t) z0) dot (G t z0 ** Y(pastecart (lift t) z0)) = &1)
     ==> frechet_derivative Y (at (pastecart (lift t0) z0)) (pastecart (lift(&1)) (vec 0)) dot
         (G t0 z0 ** Y(pastecart (lift t0) z0)) =
         lricci (G t0) z0 (Y(pastecart (lift t0) z0)) (Y(pastecart (lift t0) z0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  ABBREV_TAC `M = (lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t0) z0
                                                 (basis i) (basis j)):real^N^N` THEN
  ABBREV_TAC `D' = \s':real^1. frechet_derivative (Y:real^(1,N)finite_sum->real^N)
                                 (at (pastecart (lift t0) z0)) (pastecart s' (vec 0))` THEN
  SUBGOAL_THEN
   `((\z:real^1. lift((Y:real^(1,N)finite_sum->real^N) (pastecart z z0) dot
                      ((G:real->real^N->real^N^N) (drop z) z0 ** Y (pastecart z z0))))
     has_derivative
     (\w. lift((D':real^1->real^N) w dot (G t0 z0 ** Y(pastecart (lift t0) z0)) +
               Y(pastecart (lift t0) z0) dot
               (matrify(drop w % (vectorize:real^N^N->real^(N,N)finite_prod) M) **
                Y(pastecart (lift t0) z0) +
                G t0 z0 ** D' w)))) (at (lift t0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s:real^1. (G:real->real^N->real^N^N) (drop s) z0`;
                   `\h:real^1. drop h % (vectorize:real^N^N->real^(N,N)finite_prod) M`;
                   `\s:real^1. (Y:real^(1,N)finite_sum->real^N) (pastecart s z0)`;
                   `D':real^1->real^N`;
                   `\s:real^1. (Y:real^(1,N)finite_sum->real^N) (pastecart s z0)`;
                   `D':real^1->real^N`;
                   `lift t0`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                     `t0:real`; `z0:real^N`] LRG_FLOW_VDERIV) THEN
      ASM_REWRITE_TAC[has_vector_derivative];
      EXPAND_TAC "D'" THEN MATCH_MP_TAC LRG_HAS_DERIVATIVE_TIME_CURVE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z:real^1. lift((Y:real^(1,N)finite_sum->real^N) (pastecart z z0) dot
                      ((G:real->real^N->real^N^N) (drop z) z0 ** Y (pastecart z z0))))
     has_derivative (\h. vec 0)) (at (lift t0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\z:real^1. lift(&1)`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s`) THEN REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(s:real^1,lift t0) < d` THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^1. lift((Y:real^(1,N)finite_sum->real^N) (pastecart z z0) dot
                     ((G:real->real^N->real^N^N) (drop z) z0 ** Y (pastecart z z0)))`;
    `\w:real^1. lift((D':real^1->real^N) w dot
                     ((G:real->real^N->real^N^N) t0 z0 ** Y(pastecart (lift t0) z0)) +
                     Y(pastecart (lift t0) z0) dot
                     (matrify(drop w % (vectorize:real^N^N->real^(N,N)finite_prod) M) **
                      Y(pastecart (lift t0) z0) +
                      G t0 z0 ** D' w))`;
    `\h:real^1. vec 0:real^1`; `lift t0`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  EXPAND_TAC "D'" THEN EXPAND_TAC "M" THEN
  REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID; MATRIFY_VECTORIZE; DOT_RADD] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t0`; `z0:real^N`;
                 `(Y:real^(1,N)finite_sum->real^N) (pastecart (lift t0) z0)`;
                 `(Y:real^(1,N)finite_sum->real^N) (pastecart (lift t0) z0)`] LRG_HDOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t0`; `z0:real^N`;
                 `(Y:real^(1,N)finite_sum->real^N) (pastecart (lift t0) z0)`;
                 `frechet_derivative (Y:real^(1,N)finite_sum->real^N)
                    (at (pastecart (lift t0) z0)) (pastecart (lift(&1)) (vec 0))`]
                LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* X0.10h The time derivative of a space-time family of unit parallel fields *)
(* vanishes when R > 0: d/dt Y is parallel (P2BX0_DT_PARALLEL), so R(.,.)    *)
(* kills Y and d/dt Y; two independent killed vectors give R = 0            *)
(* (P2BX0_TWO_KILLED_RIEMANN0), so d/dt Y = mu Y, and the unit length gives  *)
(* mu = Ric(Y,Y) = 0 (P2BX0_UNIT_DT).                                       *)

(* P2BX0_LRICCI_PAR is in pc_p2b_parkit.                                    *)

let P2BX0_DT_ZERO = prove
 (`!U a b (G:real->real^3->real^3^3) (Y:real^(1,3)finite_sum->real^3) Wb t0 z0.
     lricci_flow U a b G /\ open Wb /\ Wb SUBSET interval(lift a,lift b) PCROSS U /\
     smooth_map_on Wb Y /\ pastecart (lift t0) z0 IN Wb /\
     (!t z v. pastecart (lift t) z IN Wb
              ==> frechet_derivative (\x. Y(pastecart (lift t) x)) (at z) v +
                  christoffel (G t) z v (Y(pastecart (lift t) z)) = vec 0) /\
     (!t z. pastecart (lift t) z IN Wb
            ==> Y(pastecart (lift t) z) dot (G t z ** Y(pastecart (lift t) z)) = &1) /\
     &0 < lscalar (G t0) z0
     ==> frechet_derivative Y (at (pastecart (lift t0) z0)) (pastecart (lift(&1)) (vec 0)) =
         vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par")
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `a < t0 /\ t0 < b /\ (z0:real^3) IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `Wb SUBSET interval(lift a,lift b) PCROSS (U:real^3->bool)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `pastecart (lift t0) (z0:real^3)`) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (U:real^3->bool) /\ metric_field U ((G:real->real^3->real^3^3) t0)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "rf" (fun th -> ASM_MESON_TAC[REWRITE_RULE[lricci_flow] th]); ALL_TAC] THEN
  ABBREV_TAC `U0 = (U:real^3->bool) INTER {x:real^3 | pastecart (lift t0) x IN Wb}` THEN
  MP_TAC(ISPECL [`Y:real^(1,3)finite_sum->real^3`; `Wb:real^(1,3)finite_sum->bool`; `t0:real`]
                P2BX0_SLICE_SMOOTH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Wb:real^(1,3)finite_sum->bool`; `Y:real^(1,3)finite_sum->real^3`;
                 `pastecart (lift(&1)) (vec 0:real^3)`] SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\p. frechet_derivative (Y:real^(1,3)finite_sum->real^3) (at p)
                                         (pastecart (lift(&1)) (vec 0:real^3))`;
                 `Wb:real^(1,3)finite_sum->bool`; `t0:real`] P2BX0_SLICE_SMOOTH_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (U0:real^3->bool) /\ (z0:real^3) IN U0 /\ U0 SUBSET U /\
                U0 SUBSET {x:real^3 | pastecart (lift t0) x IN Wb}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U0" THEN ASM_SIMP_TAC[OPEN_INTER; IN_INTER; IN_ELIM_THM; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U0 ((G:real->real^3->real^3^3) t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U0 (\x:real^3. (Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) x)) /\
    smooth_map_on U0 (\x:real^3. frechet_derivative (Y:real^(1,3)finite_sum->real^3)
                                   (at (pastecart (lift t0) x)) (pastecart (lift(&1)) (vec 0)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | pastecart (lift t0) x IN Wb}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z w. z IN U0
          ==> frechet_derivative (\x:real^3. (Y:real^(1,3)finite_sum->real^3)
                                             (pastecart (lift t0) x)) (at z) w +
              christoffel ((G:real->real^3->real^3^3) t0) z w (Y(pastecart (lift t0) z)) =
              vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "par" MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN U0` THEN EXPAND_TAC "U0" THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z w. z IN U0
          ==> frechet_derivative
                (\x:real^3. frechet_derivative (Y:real^(1,3)finite_sum->real^3)
                              (at (pastecart (lift t0) x)) (pastecart (lift(&1)) (vec 0)))
                (at z) w +
              christoffel ((G:real->real^3->real^3^3) t0) z w
                (frechet_derivative Y (at (pastecart (lift t0) z))
                                      (pastecart (lift(&1)) (vec 0))) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX0_DT_PARALLEL THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `a:real`; `b:real`;
                          `Wb:real^(1,3)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN U0` THEN EXPAND_TAC "U0" THEN SIMP_TAC[IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u v. lriemann ((G:real->real^3->real^3^3) t0) z0 u v
             ((Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) z0)) = vec 0) /\
    (!u v. lriemann (G t0) z0 u v
             (frechet_derivative Y (at (pastecart (lift t0) z0))
                                   (pastecart (lift(&1)) (vec 0))) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MP_TAC(ISPECL [`U0:real^3->bool`; `(G:real->real^3->real^3^3) t0`;
                     `\x:real^3. (Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) x)`;
                     `z0:real^3`; `u:real^3`; `v:real^3`] P2BX0_LRIEMANN_PARALLEL);
      MP_TAC(ISPECL [`U0:real^3->bool`; `(G:real->real^3->real^3^3) t0`;
                     `\x:real^3. frechet_derivative (Y:real^(1,3)finite_sum->real^3)
                                  (at (pastecart (lift t0) x)) (pastecart (lift(&1)) (vec 0))`;
                     `z0:real^3`; `u:real^3`; `v:real^3`] P2BX0_LRIEMANN_PARALLEL)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) z0) = vec 0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "unit" (MP_TAC o SPECL [`t0:real`; `z0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `collinear {vec 0, (Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) z0),
               frechet_derivative Y (at (pastecart (lift t0) z0))
                                    (pastecart (lift(&1)) (vec 0))}`
  THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`U0:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `z0:real^3`;
                   `(Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) z0)`;
                   `frechet_derivative (Y:real^(1,3)finite_sum->real^3)
                      (at (pastecart (lift t0) z0)) (pastecart (lift(&1)) (vec 0))`]
                  P2BX0_TWO_KILLED_RIEMANN0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < lscalar ((G:real->real^3->real^3^3) t0) z0` THEN
    ASM_REWRITE_TAC[lscalar; lricci; VEC_COMPONENT; SUM_0; REAL_MUL_RZERO; REAL_LT_REFL]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_LEMMA]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
  (* d/dt Y = c Y: c = Ric(Y,Y) = 0 by the unit length *)
  MP_TAC(ASSUME `open (Wb:real^(1,3)finite_sum->bool)`) THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t0) (z0:real^3)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `Y:real^(1,3)finite_sum->real^3`; `t0:real`; `z0:real^3`; `r:real`]
                P2BX0_UNIT_DT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Wb:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "unit" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DOT_LMUL] THEN
  MP_TAC(ISPECL [`U0:real^3->bool`; `(G:real->real^3->real^3^3) t0`;
                 `\x:real^3. (Y:real^(1,3)finite_sum->real^3) (pastecart (lift t0) x)`;
                 `z0:real^3`] P2BX0_LRICCI_PAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "unit" (MP_TAC o SPECL [`t0:real`; `z0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID]);;

(* X0.10i Tools for the time invariance: the normalised P-field p2bx0_nf   *)
(* (the field of RFA_PARALLEL_CHART), constancy in time from a vanishing    *)
(* time derivative, the parallel property at every time t in (a,0] (from    *)
(* RFA_PARALLEL_CHART and RFA_PARALLEL_CHART_END), space-time smoothness    *)
(* and unit length on a box where P(v,v) > 0, and such a box around a point *)
(* where P(v,v) > 0 (from RFA_UPTO_BOX).                                     *)

let p2bx0_nf = new_definition
 `p2bx0_nf (G:real^N->real^N^N) (b:real^N) (w:real^N) =
    inv(sqrt((matrix_inv(G w) **
              ((lambda k. lpcurv G w (\m. if m = 1 then b else basis k)):real^N)) dot
             (G w ** (matrix_inv(G w) **
              ((lambda k. lpcurv G w (\m. if m = 1 then b else basis k)):real^N))))) %
    (matrix_inv(G w) ** ((lambda k. lpcurv G w (\m. if m = 1 then b else basis k)):real^N))`;;

let P2BX0_TIME_CONST = prove
 (`!(Y:real^(1,N)finite_sum->real^P) s t1 t2 z.
     open s /\ smooth_map_on s Y /\ t1 <= t2 /\
     (!t. t1 <= t /\ t <= t2 ==> pastecart (lift t) z IN s) /\
     (!t. t1 < t /\ t < t2
          ==> frechet_derivative Y (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0)) =
              vec 0)
     ==> Y(pastecart (lift t2) z) = Y(pastecart (lift t1) z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "seg") (LABEL_TAC "dz"))))) THEN
  MP_TAC(ISPECL [`\x:real^1. (Y:real^(1,N)finite_sum->real^P) (pastecart x z)`;
                 `lift t1`; `lift t2`; `{lift t1,lift t2}`;
                 `(Y:real^(1,N)finite_sum->real^P) (pastecart (lift t1) z)`]
                HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^1. (Y:real^(1,N)finite_sum->real^P) (pastecart x z)) =
                    Y o (\x. pastecart x z)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^(1,N)finite_sum->bool` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
        X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
        USE_THEN "seg" (MP_TAC o SPEC `drop x`) THEN
        REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_INTERVAL_1; DE_MORGAN_THM; LIFT_DROP] THEN
      STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `t1 < drop x /\ drop x < t2` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `~(x = lift t1)` THEN UNDISCH_TAC `~(x = lift t2)` THEN
        REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `pastecart (x:real^1) (z:real^N) IN s` ASSUME_TAC THENL
       [USE_THEN "seg" (MP_TAC o SPEC `drop x`) THEN
        REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(Y:real^(1,N)finite_sum->real^P) differentiable at (pastecart x z)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `s:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`Y:real^(1,N)finite_sum->real^P`; `x:real^1`; `z:real^N`]
                    LRG_HAS_DERIVATIVE_TIME_CURVE) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
      SUBGOAL_THEN `pastecart (h:real^1) (vec 0:real^N) =
                    drop h % pastecart (lift(&1)) (vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL; REAL_MUL_RID;
                    LIFT_DROP];
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL
        (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]) THEN
      USE_THEN "dz" (MP_TAC o SPEC `drop x`) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t2`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL]);;

(* The P-field is parallel at every time t in (a,0] where sec_min = 0.    *)

let P2BX0_NF_PAR_AT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a c t N v y u.
     rfs_flow_upto (top,atlas) a (&0) g /\ c IN atlas /\ a < t /\ t <= &0 /\
     (!s x. a < s /\ s <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g s) x = &0) /\
     open N /\ N SUBSET IMAGE (SND c) (FST c) /\
     (!y. y IN N ==> &0 < lpcurv (metric_local atlas c (g t)) y (\m. v)) /\ y IN N
     ==> frechet_derivative (\w. p2bx0_nf (metric_local atlas c (g t)) v w) (at y) u +
         christoffel (metric_local atlas c (g t)) y u
                     (p2bx0_nf (metric_local atlas c (g t)) v y) = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx0_nf] THEN
  ASM_CASES_TAC `t = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                   `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `N:real^3->bool`;
                   `v:real^3`; `y:real^3`; `u:real^3`] RFA_PARALLEL_CHART_END) THEN
    ASM_REWRITE_TAC[lcovd];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `t:real`; `N:real^3->bool`;
                 `v:real^3`; `y:real^3`; `u:real^3`] RFA_PARALLEL_CHART) THEN
  REWRITE_TAC[lcovd] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto];
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Space-time smoothness and unit length of the P-field family of a smooth  *)
(* metric family Gb on a box where P(v,v) > 0.                               *)

let P2BX0_NF_SMOOTH = prove
 (`!N ta tb (Gb:real->real^N->real^N^N) v.
     lrg_lsmooth N ta tb Gb /\
     (!t y. ta < t /\ t < tb /\ y IN N ==> &0 < lpcurv (Gb t) y (\m. v))
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS N)
           (\p. p2bx0_nf (Gb (drop(fstcart p))) v (sndcart p)) /\
         (!t y. ta < t /\ t < tb /\ y IN N
                ==> p2bx0_nf (Gb t) v y dot (Gb t y ** p2bx0_nf (Gb t) v y) = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t y. ta < t /\ t < tb /\ y IN N
          ==> ~(matrix_inv((Gb:real->real^N->real^N^N) t y) **
                ((lambda k. lpcurv (Gb t) y (\m. if m = 1 then v else basis k)):real^N) =
                vec 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`N:real^N->bool`; `(Gb:real->real^N->real^N^N) t`; `y:real^N`;
                   `v:real^N`; `v:real^N`] RFA_PFIELD_DOT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[lrg_lsmooth]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO; COND_ID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (N:real^N->bool)`;
                   `\p. (Gb:real->real^N->real^N^N) (drop(fstcart p)) (sndcart p)`;
                   `\p. matrix_inv((Gb:real->real^N->real^N^N) (drop(fstcart p)) (sndcart p)) **
                        ((lambda k. lpcurv (Gb (drop(fstcart p))) (sndcart p)
                                      (\m. if m = 1 then v else basis k)):real^N)`]
                  RFA_SMOOTH_GNORMALIZE_GEN) THEN
    REWRITE_TAC[p2bx0_nf] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[lrg_lsmooth; OPEN_PCROSS; OPEN_INTERVAL];
      UNDISCH_TAC `lrg_lsmooth N ta tb (Gb:real->real^N->real^N^N)` THEN
      REWRITE_TAC[lrg_lsmooth; o_DEF] THEN SIMP_TAC[];
      MATCH_MP_TAC RFA_LSMOOTH_PFIELD THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                  FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `N:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[lrg_lsmooth];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx0_nf] THEN
    MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[lrg_lsmooth]]);;

(* A box around (b,z) where P(v,v) > 0, inside the smooth extension Gb of    *)
(* RFA_UPTO_BOX.                                                             *)

let P2BX0_PBOX = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) c z v.
     rfs_flow_upto (top,atlas) a b g /\ c IN atlas /\ z IN IMAGE (SND c) (FST c) /\
     &0 < lpcurv (metric_local atlas c (g b)) z (\m. v)
     ==> ?d (Gb:real->real^3->real^3^3).
           &0 < d /\ a <= b - d /\ ball(z,d) SUBSET IMAGE (SND c) (FST c) /\
           lrg_lsmooth (ball(z,d)) (b - d) (b + d) Gb /\
           (!t. t <= b ==> Gb t = metric_local atlas c (g t)) /\
           (!t y. b - d < t /\ t < b + d /\ y IN ball(z,d)
                  ==> &0 < lpcurv (Gb t) y (\m. v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `z:real^3`] RFA_UPTO_BOX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `f = \p:real^(1,3)finite_sum.
                    lpcurv ((Gb:real->real^3->real^3^3) (drop(fstcart p))) (sndcart p) (\m. v)` THEN
  SUBGOAL_THEN `(lift o (f:real^(1,3)finite_sum->real)) continuous (at (pastecart (lift b) z))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`ball(z:real^3,d0)`; `b - d0`; `b + d0`; `Gb:real->real^3->real^3^3`;
                   `\m:num. (v:real^3)`] RFA_LSMOOTH_LPCURV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) (z:real^3)`) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at; o_THM; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^(1,3)finite_sum->real) (pastecart (lift b) z)`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "econt"))) THEN
  EXISTS_TAC `min d0 e / &2` THEN EXISTS_TAC `Gb:real->real^3->real^3^3` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:real^3,d0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_LSMOOTH_SUB THEN
    MAP_EVERY EXISTS_TAC [`ball(z:real^3,d0)`; `b - d0`; `b + d0`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "econt" (MP_TAC o SPEC `pastecart (lift t) (y:real^3)`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `dist(lift t,lift b) + dist(y:real^3,z)` THEN
      CONJ_TAC THENL [REWRITE_TAC[DIST_PASTECART_LE]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN ball(z,min d0 e / &2)` THEN REWRITE_TAC[IN_BALL; DIST_LIFT] THEN
      MP_TAC(ISPECL [`z:real^3`; `y:real^3`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "f" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      REAL_ARITH_TAC]]);;

(* X0.10j Left openness: if v lies in the kernel of Ric(t0) at z and is     *)
(* unit for g(t0), then the same holds at z for all t in (t0 - d,t0].  The   *)
(* P-field family Yb of b0 = v on a box where P(v,v) > 0 is parallel at every *)
(* time (P2BX0_NF_PAR_AT), so its time derivative vanishes (P2BX0_DT_ZERO),  *)
(* Yb(t,z) = Yb(t0,z) = v (P2BX0_TIME_CONST, P2BX0_NFIELD_KER), and Yb(t,.)  *)
(* parallel gives Ric(t)(v,.) = 0 (P2BX0_LRICCI_PAR).                        *)

let P2BX0_KER_LEFT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a c z v t0.
     rfs_flow_upto (top,atlas) a (&0) g /\ c IN atlas /\
     (!t x. a < t /\ t <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     (!t y. a < t /\ t <= &0 /\ y IN IMAGE (SND c) (FST c)
            ==> &0 < lscalar (metric_local atlas c (g t)) y) /\
     z IN IMAGE (SND c) (FST c) /\ a < t0 /\ t0 <= &0 /\
     (!w. lricci (metric_local atlas c (g t0)) z v w = &0) /\
     v dot (metric_local atlas c (g t0) z ** v) = &1
     ==> ?d. &0 < d /\
             !t. t0 - d < t /\ t <= t0
                 ==> (!w. lricci (metric_local atlas c (g t)) z v w = &0) /\
                     v dot (metric_local atlas c (g t) z ** v) = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "scal")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ker0") (LABEL_TAC "unit0"))))))))) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a (&0) (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) a t0 (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_CASES_TAC `t0 = &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t <= &0
        ==> metric_field (IMAGE (SND c) (FST c))
                         (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` MP_TAC THENL
     [ASM_CASES_TAC `t = &0` THENL
       [ASM_MESON_TAC[rfs_flow_upto];
        UNDISCH_TAC `ricci_flow_on (top,atlas) a (&0) (g:real->A->real^3^3)` THEN
        REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lpcurv (metric_local atlas c ((g:real->A->real^3^3) t0)) z (\m. v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[lpcurv; lmetric2; lric2] THEN
    USE_THEN "ker0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "unit0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "scal" (MP_TAC o SPECL [`t0:real`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `t0:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `z:real^3`; `v:real^3`]
                P2BX0_PBOX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gb") (LABEL_TAC "ppos")))))))) THEN
  MP_TAC(ISPECL [`ball(z:real^3,d)`; `t0 - d`; `t0 + d`; `Gb:real->real^3->real^3^3`;
                 `v:real^3`] P2BX0_NF_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ppos" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nfunit")) THEN
  (* parallel at every time t in (t0 - d,t0] on ball(z,d) *)
  SUBGOAL_THEN
   `!t y u. t0 - d < t /\ t <= t0 /\ y IN ball(z:real^3,d)
            ==> frechet_derivative
                  (\w. p2bx0_nf (metric_local atlas c ((g:real->A->real^3^3) t)) v w) (at y) u +
                christoffel (metric_local atlas c (g t)) y u
                            (p2bx0_nf (metric_local atlas c (g t)) v y) = vec 0`
  (LABEL_TAC "par") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX0_NF_PAR_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `ball(z:real^3,d)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN
      USE_THEN "gb" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "ppos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the time derivative of the family vanishes at times t < t0 *)
  SUBGOAL_THEN
   `!t y. t0 - d < t /\ t < t0 /\ y IN ball(z:real^3,d)
          ==> frechet_derivative
                (\p. p2bx0_nf ((Gb:real->real^3->real^3^3) (drop(fstcart p))) v (sndcart p))
                (at (pastecart (lift t) y)) (pastecart (lift(&1)) (vec 0)) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX0_DT_ZERO THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `&0`;
      `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
      `interval(lift(t0 - d),lift t0) PCROSS ball(z:real^3,d)`] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL];
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(z:real^3,d)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^3`; `u:real^3`] THEN STRIP_TAC THEN
      USE_THEN "gb" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "par" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^3`] THEN STRIP_TAC THEN
      USE_THEN "gb" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "nfunit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "scal" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* the value at (t0,z) is v *)
  SUBGOAL_THEN `p2bx0_nf ((Gb:real->real^3->real^3^3) t0) v z = v` ASSUME_TAC THENL
   [USE_THEN "gb" (MP_TAC o SPEC `t0:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2bx0_nf] THEN
    MATCH_MP_TAC P2BX0_NFIELD_KER THEN EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  (* Yb(t,z) = Yb(t0,z) = v *)
  SUBGOAL_THEN `p2bx0_nf (metric_local atlas c ((g:real->A->real^3^3) t)) v z = v` ASSUME_TAC THENL
   [USE_THEN "gb" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL
     [`\p. p2bx0_nf ((Gb:real->real^3->real^3^3) (drop(fstcart p))) v (sndcart p)`;
      `interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(z:real^3,d)`; `t:real`; `t0:real`;
      `z:real^3`] P2BX0_TIME_CONST) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`ball(z:real^3,d)`; `metric_local atlas c ((g:real->A->real^3^3) t)`;
                   `\w. p2bx0_nf (metric_local atlas c ((g:real->A->real^3^3) t)) v w`;
                   `z:real^3`] P2BX0_LRICCI_PAR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "gb" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MP_TAC(ISPECL
         [`\p. p2bx0_nf ((Gb:real->real^3->real^3^3) (drop(fstcart p))) v (sndcart p)`;
          `interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(z:real^3,d)`; `t:real`]
          P2BX0_SLICE_SMOOTH_OPEN) THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL; FSTCART_PASTECART;
                     SNDCART_PASTECART; LIFT_DROP] THEN
        STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `{x:real^3 | pastecart (lift t) x IN
                               interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(z,d)}` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
        GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "par" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    SUBGOAL_THEN
     `p2bx0_nf ((Gb:real->real^3->real^3^3) t) v z dot
      (Gb t z ** p2bx0_nf (Gb t) v z) = &1`
    MP_TAC THENL
     [USE_THEN "nfunit" MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "gb" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* X0.10k Right closedness (continuity in time at interior times), the      *)
(* backward continuous induction on (-inf,b], and the kernel property for   *)
(* all t <= 0: if v is in the kernel of Ric(0) at z and unit for g(0), then *)
(* the same holds for every t <= 0.                                          *)

let P2BX0_CONT_RIGHT_EQ = prove
 (`!f t0 d c.
     f real_continuous (atreal t0) /\ &0 < d /\ (!t. t0 < t /\ t < t0 + d ==> f t = c)
     ==> f t0 = c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `(f:real->real) real_continuous (atreal t0)` THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `abs((f:real->real) t0 - c)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 + min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 + min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let P2BX0_LSMOOTH_TCONT = prove
 (`!U ta tb (Fq:real->real^N->real) t y.
     smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                   (\p. lift(Fq (drop(fstcart p)) (sndcart p))) /\
     open U /\ ta < t /\ t < tb /\ y IN U
     ==> (\s. Fq s y) real_continuous atreal t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  SUBGOAL_THEN `lift o (\s. (Fq:real->real^N->real) s y) o drop =
                (\p. lift(Fq (drop(fstcart p)) (sndcart p))) o (\x:real^1. pastecart x y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_PASTECART THEN REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]);;

let P2BX0_KER_RIGHT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a c z v ts.
     ricci_flow_on (top,atlas) a (&0) g /\ c IN atlas /\ z IN IMAGE (SND c) (FST c) /\
     a < ts /\ ts < &0 /\
     (!t. ts < t /\ t <= &0
          ==> (!w. lricci (metric_local atlas c (g t)) z v w = &0) /\
              v dot (metric_local atlas c (g t) z ** v) = &1)
     ==> (!w. lricci (metric_local atlas c (g ts)) z v w = &0) /\
         v dot (metric_local atlas c (g ts) z ** v) = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "after")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`] LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lrg_lsmooth (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)) a (&0)
                (\t. metric_local atlas c ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `lricci_flow (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)) a (&0)
                  (\t. metric_local atlas c ((g:real->A->real^3^3) t))` THEN
    REWRITE_TAC[lricci_flow; lrg_lsmooth] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lrg_lsmooth]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`\s. lricci (metric_local atlas (c:(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3) s)) z v w`;
                   `ts:real`; `--ts`; `&0`] P2BX0_CONT_RIGHT_EQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `&0`;
                     `\s y. lricci (metric_local atlas (c:(A->bool)#(A->real^3))
                                    ((g:real->A->real^3^3) s)) y v w`;
                     `ts:real`; `z:real^3`] P2BX0_LSMOOTH_TCONT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `&0`;
                     `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                     `v:real^3`; `w:real^3`] LRG_LSMOOTH_LRICCI) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "after" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    MP_TAC(ISPECL [`\s. (v:real^3) dot (metric_local atlas (c:(A->bool)#(A->real^3))
                                         ((g:real->A->real^3^3) s) z ** v)`;
                   `ts:real`; `--ts`; `&1`] P2BX0_CONT_RIGHT_EQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `--(&2) * lricci (metric_local atlas (c:(A->bool)#(A->real^3))
                                     ((g:real->A->real^3^3) ts)) z v v` THEN
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`; `a:real`; `&0`;
                     `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
                     `ts:real`; `z:real^3`; `v:real^3`] RFA_GQFORM_DERIV) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "after" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]]);;

(* Backward continuous induction on (-inf,b].                                *)

let P2BX0_BACKWARD_INDUCT = prove
 (`!P b. P b /\
         (!t. t <= b /\ P t ==> ?d. &0 < d /\ !s. t - d < s /\ s <= t ==> P s) /\
         (!t. t < b /\ (!s. t < s /\ s <= b ==> P s) ==> P t)
         ==> !t. t <= b ==> P t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "left")
    (LABEL_TAC "right"))) THEN
  X_GEN_TAC `t0:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `S = {s:real | t0 <= s /\ s <= b /\ ~P s}` THEN
  ABBREV_TAC `m = sup S` THEN
  SUBGOAL_THEN `~(S:real->bool = {}) /\ (!s. s IN S ==> s <= b)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN `t0 <= m /\ m <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL];
      USE_THEN "lub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. m < s /\ s <= b ==> (P:real->bool) s` (LABEL_TAC "above") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real) IN S` MP_TAC THENL
     [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> USE_THEN "ub" (MP_TAC o C MATCH_MP th)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real->bool) m` ASSUME_TAC THENL
   [ASM_CASES_TAC `m:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "right" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "above" ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "left" (MP_TAC o SPEC `m:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "below"))) THEN
  SUBGOAL_THEN `!s. s IN S ==> s <= m - d` MP_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `~(m - d < s) ==> s <= m - d`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real->bool) s` MP_TAC THENL
     [ASM_CASES_TAC `s <= m` THENL
       [USE_THEN "below" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "above" MATCH_MP_TAC THEN
        UNDISCH_TAC `(s:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `(s:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> USE_THEN "lub" (MP_TAC o C MATCH_MP th)) THEN ASM_REAL_ARITH_TAC);;

(* The kernel property for all t <= 0.                                       *)

let P2BX0_KER_ALL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) c z v.
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\ c IN atlas /\
     (!t x. t <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     (!t y. t <= &0 /\ y IN IMAGE (SND c) (FST c)
            ==> &0 < lscalar (metric_local atlas c (g t)) y) /\
     z IN IMAGE (SND c) (FST c) /\
     (!w. lricci (metric_local atlas c (g(&0))) z v w = &0) /\
     v dot (metric_local atlas c (g(&0)) z ** v) = &1
     ==> !t. t <= &0
             ==> (!w. lricci (metric_local atlas c (g t)) z v w = &0) /\
                 v dot (metric_local atlas c (g t) z ** v) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. (!w. lricci (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))
                     z v w = &0) /\
         v dot (metric_local atlas c (g t) z ** v) = &1`; `&0`] P2BX0_BACKWARD_INDUCT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX0_KER_LEFT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `t - &1`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX0_KER_RIGHT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `t - &1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `rfs_flow_upto (top,atlas) (t - &1) (&0) (g:real->A->real^3^3)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]];
      REAL_ARITH_TAC]]);;

(* X0.10m The parallel property at a time s < 0 from the kernel property:   *)
(* near y0 the P-field Nf of b0 = Xc(y0) is a smooth unit parallel field    *)
(* (P2BX0_NF_LOCAL); the rank-one identity of P (RFA_RANK1_POINT) gives      *)
(* Xc = e Nf with e = <Xc,Nf> (P2BX0_KER_RIC_MULT), e^2 = 1 and e(y0) = 1,   *)
(* so Xc = Nf near y0 and Xc is parallel at y0.                              *)

let P2BX0_NF_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a c s y0 b0.
     rfs_flow_upto (top,atlas) a (&0) g /\ c IN atlas /\ a < s /\ s <= &0 /\
     (!t x. a < t /\ t <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     y0 IN IMAGE (SND c) (FST c) /\
     &0 < lpcurv (metric_local atlas c (g s)) y0 (\m. b0)
     ==> ?d. &0 < d /\ ball(y0,d) SUBSET IMAGE (SND c) (FST c) /\
             smooth_map_on (ball(y0,d)) (\w. p2bx0_nf (metric_local atlas c (g s)) b0 w) /\
             (!y u. y IN ball(y0,d)
                    ==> frechet_derivative (\w. p2bx0_nf (metric_local atlas c (g s)) b0 w)
                                           (at y) u +
                        christoffel (metric_local atlas c (g s)) y u
                                    (p2bx0_nf (metric_local atlas c (g s)) b0 y) = vec 0) /\
             (!y. y IN ball(y0,d)
                  ==> p2bx0_nf (metric_local atlas c (g s)) b0 y dot
                      (metric_local atlas c (g s) y **
                       p2bx0_nf (metric_local atlas c (g s)) b0 y) = &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) a s (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_CASES_TAC `s = &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `&0`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[rfs_flow_upto]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `s:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `y0:real^3`; `b0:real^3`]
                P2BX0_PBOX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gb") (LABEL_TAC "ppos")))))))) THEN
  MP_TAC(ISPECL [`ball(y0:real^3,d)`; `s - d`; `s + d`; `Gb:real->real^3->real^3^3`;
                 `b0:real^3`] P2BX0_NF_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ppos" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nfunit")) THEN
  SUBGOAL_THEN `(Gb:real->real^3->real^3^3) s = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) s)` (LABEL_TAC "gbs")
  THENL [USE_THEN "gb" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "gbs" (SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL
     [`\p. p2bx0_nf ((Gb:real->real^3->real^3^3) (drop(fstcart p))) b0 (sndcart p)`;
      `interval(lift(s - d),lift(s + d)) PCROSS ball(y0:real^3,d)`; `s:real`]
      P2BX0_SLICE_SMOOTH_OPEN) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL; FSTCART_PASTECART;
                 SNDCART_PASTECART; LIFT_DROP] THEN
    STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^3 | pastecart (lift s) x IN
                           interval(lift(s - d),lift(s + d)) PCROSS ball(y0,d)}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX0_NF_PAR_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `ball(y0:real^3,d)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `y':real^3` THEN DISCH_TAC THEN
    USE_THEN "gbs" (SUBST1_TAC o SYM) THEN USE_THEN "ppos" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "gbs" (SUBST1_TAC o SYM) THEN
    USE_THEN "nfunit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2BX0_PAR_FROM_KER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a c
    (Xc:real^3->real^3) s y0.
     rfs_flow_upto (top,atlas) a (&0) g /\ c IN atlas /\ a < s /\ s < &0 /\
     (!t x. a < t /\ t <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     (!y. y IN IMAGE (SND c) (FST c) ==> &0 < lscalar (metric_local atlas c (g s)) y) /\
     smooth_map_on (IMAGE (SND c) (FST c)) Xc /\
     (!y w. y IN IMAGE (SND c) (FST c)
            ==> lricci (metric_local atlas c (g s)) y (Xc y) w = &0) /\
     (!y. y IN IMAGE (SND c) (FST c)
          ==> Xc y dot (metric_local atlas c (g s) y ** Xc y) = &1) /\
     y0 IN IMAGE (SND c) (FST c)
     ==> !u. frechet_derivative Xc (at y0) u +
             christoffel (metric_local atlas c (g s)) y0 u (Xc y0) = vec 0`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) s)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "scal")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ker")
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") ASSUME_TAC))))))))) THEN
  X_GEN_TAC `u:real^3` THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a (&0) (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                             (G:real^3->real^3^3)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) s)` MP_TAC THENL
     [UNDISCH_TAC `ricci_flow_on (top,atlas) a (&0) (g:real->A->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  (* the P-field of b0 = Xc y0 near y0 *)
  SUBGOAL_THEN `&0 < lpcurv (G:real^3->real^3^3) y0 (\m. (Xc:real^3->real^3) y0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[lpcurv; lmetric2; lric2] THEN
    USE_THEN "ker" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`)]) THEN
    USE_THEN "unit" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`)]) THEN
    USE_THEN "scal" (MP_TAC o SPEC `y0:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `a:real`; `c:(A->bool)#(A->real^3)`; `s:real`; `y0:real^3`;
                 `(Xc:real^3->real^3) y0`] P2BX0_NF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRY(USE_THEN "sec" ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Nf = \w. p2bx0_nf (G:real^3->real^3^3) ((Xc:real^3->real^3) y0) w` THEN
  SUBGOAL_THEN `!w. p2bx0_nf (G:real^3->real^3^3) ((Xc:real^3->real^3) y0) w =
                    (Nf:real^3->real^3) w`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Nf" THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "npar") (LABEL_TAC "nunit")))))) THEN
  SUBGOAL_THEN `metric_field (ball(y0:real^3,d)) (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  (* Ric(Nf,.) = 0 and the rank-one identity on the ball *)
  SUBGOAL_THEN `!y w. y IN ball(y0:real^3,d)
                      ==> lricci (G:real^3->real^3^3) y ((Nf:real^3->real^3) y) w = &0`
  (LABEL_TAC "nker") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(y0:real^3,d)`; `G:real^3->real^3^3`; `Nf:real^3->real^3`; `y:real^3`]
                  P2BX0_LRICCI_PAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "npar" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(y0:real^3,d)
        ==> (!u w. lpcurv (G:real^3->real^3^3) y (\m. u) * lpcurv G y (\m. w) =
                   lpcurv G y (\m. if m = 1 then u else w) pow 2)`
  (LABEL_TAC "rank1") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y IN FST c /\
                  SND c (chart_inv c y) = y` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                   `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `s:real`;
                   `chart_inv (c:(A->bool)#(A->real^3)) y`; `s - a`] RFA_RANK1_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        CONV_TAC SYM_CONV THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        CONV_TAC SYM_CONV THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* Xc = e Nf with e = <Xc, G Nf> *)
  SUBGOAL_THEN
   `!y. y IN ball(y0:real^3,d)
        ==> (Xc:real^3->real^3) y =
            (Xc y dot ((G:real^3->real^3^3) y ** (Nf:real^3->real^3) y)) % Nf y`
  (LABEL_TAC "mult") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX0_KER_RIC_MULT THEN
    EXISTS_TAC `ball(y0:real^3,d)` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rank1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "scal" MATCH_MP_TAC THEN ASM SET_TAC[];
      GEN_TAC THEN USE_THEN "ker" MATCH_MP_TAC THEN ASM SET_TAC[];
      GEN_TAC THEN USE_THEN "nker" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "nunit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Nf y0 = Xc y0 *)
  SUBGOAL_THEN `(Nf:real^3->real^3) y0 = Xc y0` ASSUME_TAC THENL
   [EXPAND_TAC "Nf" THEN REWRITE_TAC[p2bx0_nf] THEN MATCH_MP_TAC P2BX0_NFIELD_KER THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "ker" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "scal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "unit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* continuity of e at y0 *)
  SUBGOAL_THEN
   `(\y. lift((Xc:real^3->real^3) y dot ((G:real^3->real^3^3) y ** (Nf:real^3->real^3) y)))
    continuous (at y0)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    MP_TAC(ISPECL [`G:real^3->real^3^3`;
                   `frechet_derivative ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                        (G:real^3->real^3^3)) (at y0)`;
                   `Xc:real^3->real^3`; `frechet_derivative (Xc:real^3->real^3) (at y0)`;
                   `Nf:real^3->real^3`; `frechet_derivative (Nf:real^3->real^3) (at y0)`;
                   `y0:real^3`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field];
        EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `ball(y0:real^3,d)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL]];
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at; DIST_LIFT] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(Nf:real^3->real^3) y0 = Xc y0`] THEN
  USE_THEN "unit" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `(y0:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`)]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "econt"))) THEN
  (* Xc = Nf on ball(y0, min r d) *)
  SUBGOAL_THEN `!y. y IN ball(y0:real^3,min r d) ==> (Xc:real^3->real^3) y = Nf y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN ball(y0,d)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `e = (Xc:real^3->real^3) y dot ((G:real^3->real^3^3) y ** (Nf:real^3->real^3) y)` THEN
    SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
     [USE_THEN "econt" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Xc:real^3->real^3) y = e % (Nf:real^3->real^3) y` ASSUME_TAC THENL
     [USE_THEN "mult" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e * e = &1` ASSUME_TAC THENL
     [USE_THEN "unit" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `(Xc:real^3->real^3) y = e % (Nf:real^3->real^3) y`)) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
      USE_THEN "nunit" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `e = &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `(e - &1) * (e + &1) = &0` MP_TAC THENL
       [UNDISCH_TAC `e * e = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (Xc:real^3->real^3) (at y0) =
                frechet_derivative (Nf:real^3->real^3) (at y0)` SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `ball(y0:real^3,min r d)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SYM(ASSUME `(Nf:real^3->real^3) y0 = Xc y0`)] THEN
  USE_THEN "npar" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]);;

(* X0.10n Assembly of the time invariance: if sec_min = 0 and R > 0 at all  *)
(* times s <= 0 and X is a unit parallel field for g(0), then X is a unit   *)
(* parallel field for every g(s), s <= 0 (p2b_gsplit on s <= 0).            *)

let P2BX0_GSPLIT_FROM_KER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) X.
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!t x. t <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0) /\
     (!t x. t <= &0 /\ x IN topspace top ==> &0 < mfd_scalar atlas (g t) x) /\
     p2b_parallel_on atlas (g(&0)) (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g(&0) y ** X y) = &1)
     ==> p2b_gsplit (top,atlas) g {s | s <= &0} X`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "sec")
    (CONJUNCTS_THEN2 (LABEL_TAC "scal") (CONJUNCTS_THEN2 (LABEL_TAC "par0")
    (LABEL_TAC "unit0"))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "upto" (MP_TAC o SPEC `--(&1)`) THEN REWRITE_TAC[REAL_ARITH `--(&1) < &0`] THEN
    MESON_TAC[rfs_flow_upto; ricci_flow_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t <= &0 ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "upto" (MP_TAC o SPEC `t - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `t = &0` THENL [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
          ==> chart_inv (c:(A->bool)#(A->real^3)) y IN topspace top /\
              chart_inv c y IN FST c /\ SND c (chart_inv c y) = y`
  (LABEL_TAC "cinv") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> IMAGE (SND c) (FST c INTER topspace top) =
            IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`
  (LABEL_TAC "img") THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t c y. t <= &0 /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
            ==> &0 < lscalar (metric_local atlas c ((g:real->A->real^3^3) t)) y`
  (LABEL_TAC "cscal") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`; `y:real^3`]
                  P2BX0_LSCALAR_CHART) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "scal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "cinv" (MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the chart representatives at time 0 *)
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas (X:A->real^3) c) /\
            (!y z. y IN IMAGE (SND c) (FST c)
                   ==> frechet_derivative (mfd_vrep atlas X c) (at y) z +
                       christoffel (metric_local atlas c ((g:real->A->real^3^3) (&0))) y z
                                   (mfd_vrep atlas X c y) = vec 0)`
  (LABEL_TAC "rep0") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "par0" (MP_TAC o REWRITE_RULE[p2b_parallel_on]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c y t. c IN atlas /\ y IN IMAGE (SND c) (FST c) /\ t <= &0
            ==> (!w. lricci (metric_local atlas c ((g:real->A->real^3^3) t)) y
                            (mfd_vrep atlas (X:A->real^3) c y) w = &0) /\
                mfd_vrep atlas X c y dot
                (metric_local atlas c (g t) y ** mfd_vrep atlas X c y) = &1`
  (LABEL_TAC "kerall") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                               (metric_local atlas c ((g:real->A->real^3^3) (&0)))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) (&0))` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "rep0" (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `c:(A->bool)#(A->real^3)`; `y:real^3`;
                   `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3)) y`] P2BX0_KER_ALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "cscal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                       `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) (&0))`;
                       `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`; `y:real^3`]
                      P2BX0_LRICCI_PAR) THEN
        ASM_SIMP_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `(g:real->A->real^3^3) (&0)`; `X:A->real^3`; `c:(A->bool)#(A->real^3)`;
                       `y:real^3`] P2BX0_VREP_DOT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        USE_THEN "unit0" MATCH_MP_TAC THEN
        USE_THEN "cinv" (MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `y:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
     [USE_THEN "par0" ACCEPT_TAC; USE_THEN "unit0" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2b_parallel_on] THEN CONJ_TAC THENL
     [USE_THEN "par0" (MP_TAC o CONJUNCT1 o REWRITE_RULE[p2b_parallel_on]) THEN SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "rep0" (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `s - &1`; `c:(A->bool)#(A->real^3)`;
                   `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`; `s:real`; `y:real^3`]
                  P2BX0_PAR_FROM_KER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "cscal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        USE_THEN "kerall" (MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `y':real^3`; `s:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        REPEAT STRIP_TAC THEN
        USE_THEN "kerall" (MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `y':real^3`; `s:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      SIMP_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) s`; `X:A->real^3`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`] P2BX0_VREP_DOT) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "kerall" (MP_TAC o SPECL [`chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                                       `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                                       `s:real`]) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_REAL_ARITH_TAC]);;

(* X0.10o The hypotheses of P2BX0_GSPLIT_FROM_KER on the limit: a parallel *)
(* field gives a zero plane at time 0, hence sec_min = 0 at all times      *)
(* (RFA_SECMIN_ZERO_UPTO); R > 0 at all times from R(xl,0) = 1, by          *)
(* RFA_SCALAR_ZERO_UPTO, FLAT_FORWARD and continuity at time 0.             *)

let P2BX0_NONCOLLINEAR_EXISTS = prove
 (`!e:real^3. ~(e = vec 0) ==> ?u. ~collinear {vec 0,u,e}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CROSS_EQ_0] THEN
  SUBGOAL_THEN `(basis 1:real^3) cross e = vec 0 /\ (basis 2:real^3) cross e = vec 0
                ==> e = vec 0` ASSUME_TAC THENL [VEC3_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let P2BX0_PAR_SEC_ZERO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) X p u.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ p IN topspace top
     ==> mfd_sectional atlas g p u (X p) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (SND c) (FST c INTER topspace top) =
                IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC `p2b_parallel_on atlas (g:A->real^3^3) (topspace top) X` THEN
  REWRITE_TAC[p2b_parallel_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`)
    (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c))
                             (metric_local atlas c (g:A->real^3^3))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`;
                 `SND (c:(A->bool)#(A->real^3)) p`; `u:real^3`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3)) (SND c p)`]
                P2BX0_LRIEMANN_PARALLEL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `X:A->real^3`; `p:A`]
                P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[mfd_sectional; lsectional; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO;
                  real_div; REAL_MUL_LZERO]);;

let P2BX0_SECMIN_ZERO_ALL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) X.
     connected_space top /\ ~(topspace top = {}) /\
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s y u v. s <= &0 /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g s) y u v) /\
     p2b_parallel_on atlas (g(&0)) (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g(&0) y ** X y) = &1)
     ==> !t x. t <= &0 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "sec")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unit0")))))) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) (&0))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "upto" (MP_TAC o SPEC `--(&1)`) THEN REWRITE_TAC[REAL_ARITH `--(&1) < &0`] THEN
    MESON_TAC[rfs_flow_upto; ricci_flow_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((X:A->real^3) p = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "unit0" (MP_TAC o SPEC `p:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `(X:A->real^3) p` P2BX0_NONCOLLINEAR_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real^3`) THEN
  SUBGOAL_THEN `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) (&0)) p =
                &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_SECMIN_NONNEG THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_sectional (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) (&0)) p u ((X:A->real^3) p)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC P2BX0_PAR_SEC_ZERO THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `t - &1`; `&0`;
                 `g:real->A->real^3^3`; `p:A`] RFA_SECMIN_ZERO_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT STRIP_TAC THEN
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2BX0_SCALAR_LEFT_LIMIT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a x t1.
     rfs_flow_upto (top,atlas) a (&0) g /\ x IN topspace top /\ t1 < &0 /\
     (!t. t1 <= t /\ t < &0 ==> mfd_scalar atlas (g t) x = &0)
     ==> mfd_scalar atlas (g(&0)) x = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`;
                 `SND (c:(A->bool)#(A->real^3)) x`] RFA_UPTO_BOX) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gb:real->real^3->real^3^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\p. lift(lscalar ((Gb:real->real^3->real^3^3) (drop(fstcart p))) (sndcart p))`;
                 `interval(lift(&0 - d),lift(&0 + d)) PCROSS ball(SND (c:(A->bool)#(A->real^3)) x,d)`;
                 `max t1 (--(d / &2))`; `&0`; `SND (c:(A->bool)#(A->real^3)) x`]
                RFA_ZERO_LEFT_LIMIT) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC LRG_LSMOOTH_LSCALAR THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(Gb:real->real^3->real^3^3) t = metric_local atlas c ((g:real->A->real^3^3) t)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (term_match [] `!t. t1 <= t /\ t < &0 ==> mfd_scalar atlas ((g:real->A->real^3^3) t) (x:A) = &0`)
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[mfd_scalar] THEN SIMP_TAC[LIFT_NUM]];
    SUBGOAL_THEN `(Gb:real->real^3->real^3^3) (&0) = metric_local atlas c ((g:real->A->real^3^3) (&0))`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_scalar; GSYM LIFT_NUM; LIFT_EQ]]);;

(* X0.10p R > 0 at all times s <= 0 of the limit, and the time invariance  *)
(* of the parallel field (X0.10): X unit and parallel for g(0) is unit and  *)
(* parallel for every g(s), s <= 0.                                          *)

let P2BX0_SCALAR_POS_ALL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) xl K.
     hausdorff_space top /\ connected_space top /\
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s. s <= &0 ==> mfd_complete (top,atlas) (g s)) /\
     (!s y u v. s <= &0 /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g s) y u v) /\
     (!s y. s <= &0 /\ y IN topspace top ==> mfd_rm_norm atlas (g s) y <= K) /\
     xl IN topspace top /\ mfd_scalar atlas (g(&0)) xl = &1
     ==> !t x. t <= &0 /\ x IN topspace top ==> &0 < mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "rm")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) (t - &1) (&0) (g:real->A->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (t - &1) (&0) (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) (t - &1) t (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_CASES_TAC `t = &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`t - &1`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `!s y. s <= &0 /\ y IN topspace top
                      ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                            ((g:real->A->real^3^3) s) y`
  (LABEL_TAC "smin") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT STRIP_TAC THEN
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      USE_THEN "smin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN topspace top
                    ==> mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                   ((g:real->A->real^3^3) t) y = &0`
  (LABEL_TAC "zero") THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `t - &1`; `t:real`;
                   `g:real->A->real^3^3`; `x:A`] RFA_SCALAR_ZERO_UPTO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "smin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC th THEN
                           ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) (&0)) xl =
                &0` MP_TAC THENL
   [ASM_CASES_TAC `t = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "zero" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `t - &1`; `&0`;
                   `g:real->A->real^3^3`; `t:real`; `K:real`] P2B_FLAT_FORWARD_BODY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "comp" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    MATCH_MP_TAC P2BX0_SCALAR_LEFT_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `t - &1`; `t:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2BX0_TIME_INVARIANCE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) X xl K.
     hausdorff_space top /\ connected_space top /\
     (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
     (!s. s <= &0 ==> mfd_complete (top,atlas) (g s)) /\
     (!s y u v. s <= &0 /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g s) y u v) /\
     (!s y. s <= &0 /\ y IN topspace top ==> mfd_rm_norm atlas (g s) y <= K) /\
     xl IN topspace top /\ mfd_scalar atlas (g(&0)) xl = &1 /\
     p2b_parallel_on atlas (g(&0)) (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g(&0) y ** X y) = &1)
     ==> p2b_gsplit (top,atlas) g {s | s <= &0} X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX0_GSPLIT_FROM_KER THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SECMIN_ZERO_ALL THEN EXISTS_TAC `X:A->real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC P2BX0_SCALAR_POS_ALL THEN
    MAP_EVERY EXISTS_TAC [`xl:A`; `K:real`] THEN ASM_REWRITE_TAC[]]);;

(* X0.8a A line from pairs: if for every A > 0 there are a, b with           *)
(* d(xl,a) = d(xl,b) = A and d(a,b) = 2A, then the complete connected        *)
(* manifold contains a line through xl: the segments from xl to a and to b   *)
(* (CMPSO_SEGMENT) satisfy d(geo u s, geo w t) = s + t, and the limits of     *)
(* the two families of segments (CMPSO_LIMIT_RAY) are two rays with the same *)
(* property.                                                                  *)

let P2BX0_PAIR_SEGMENTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) xl a b L.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ xl IN topspace top /\
     a IN topspace top /\ b IN topspace top /\ &0 < L /\
     mfd_dist (top,atlas) g xl a = L /\ mfd_dist (top,atlas) g xl b = L /\
     mfd_dist (top,atlas) g a b = &2 * L
     ==> ?u w. mfd_tnorm g xl u = &1 /\ mfd_tnorm g xl w = &1 /\
               (!s. &0 <= s /\ s <= L
                    ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl u s) = s) /\
               (!s. &0 <= s /\ s <= L
                    ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl w s) = s) /\
               (!s t. &0 <= s /\ s <= L /\ &0 <= t /\ t <= L
                      ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u s)
                                                 (mfd_geo (top,atlas) g xl w t) = s + t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:A = xl) /\ ~(b:A = xl)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `xl:A`] MFD_DIST_REFL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `b:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "du")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `a:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw")))) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `w:real^N`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inu")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lipu")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inw")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lipw")))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N) xl u s` THEN
  ABBREV_TAC `z = mfd_geo (top,atlas) (g:A->real^N^N) xl w t` THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (z:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN EXPAND_TAC "z" THEN
    USE_THEN "inu" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "inw" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) xl y = s` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN USE_THEN "du" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) xl z = t` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN USE_THEN "dw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) z a <= L - t` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_geo (top,atlas) (g:A->real^N^N) xl w L = a`)) THEN
    USE_THEN "lipw" (MP_TAC o SPECL [`t:real`; `L:real`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y b <= L - s` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_geo (top,atlas) (g:A->real^N^N) xl u L = b`)) THEN
    USE_THEN "lipu" (MP_TAC o SPECL [`s:real`; `L:real`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) y z <= s + t` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y:A`; `xl:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `y:A`; `xl:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s + t <= mfd_dist (top,atlas) (g:A->real^N^N) y z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `z:A`; `b:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `y:A`; `b:A`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `z:A`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `y:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* X0.8b The line from pairs (P2BX0_LINE_FROM_PAIRS): rays u0, w0 from xl   *)
(* as limits of the two families of segments,                               *)
(* d(geo u0 s, geo w0 t) = s + t, and the line lam t = geo u0 t (t >= 0),   *)
(* geo w0 (-t) (t < 0).                                                     *)

(* The four-point distance bound on a connected manifold (MFD_DIST_       *)
(* LIPSCHITZ with all points joinable).                                     *)

let P2BX0_DIST_QUAD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) P P' Q Q'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     P IN topspace top /\ P' IN topspace top /\ Q IN topspace top /\ Q' IN topspace top
     ==> abs(mfd_dist (top,atlas) g P Q - mfd_dist (top,atlas) g P' Q') <=
         mfd_dist (top,atlas) g P P' + mfd_dist (top,atlas) g Q Q'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_LIPSCHITZ THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
  ASM_REWRITE_TAC[]);;

let P2BX0_LINE_FROM_PAIRS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) xl.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ xl IN topspace top /\
     (!A. &0 < A
          ==> ?a b. a IN topspace top /\ b IN topspace top /\
                    mfd_dist (top,atlas) g xl a = A /\ mfd_dist (top,atlas) g xl b = A /\
                    mfd_dist (top,atlas) g a b = &2 * A)
     ==> ?lam. !s t. lam s IN topspace top /\
                     mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pairs"))))))) THEN
  SUBGOAL_THEN
   `?(u:num->real^N) (w:num->real^N).
      !n. mfd_tnorm (g:A->real^N^N) xl (u n) = &1 /\ mfd_tnorm g xl (w n) = &1 /\
          (!s. &0 <= s /\ s <= &n + &1
               ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl (u n) s) = s) /\
          (!s. &0 <= s /\ s <= &n + &1
               ==> mfd_dist (top,atlas) g xl (mfd_geo (top,atlas) g xl (w n) s) = s) /\
          (!s t. &0 <= s /\ s <= &n + &1 /\ &0 <= t /\ t <= &n + &1
                 ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl (u n) s)
                                            (mfd_geo (top,atlas) g xl (w n) t) = s + t)`
  (X_CHOOSE_THEN `u:num->real^N` (X_CHOOSE_THEN `w:num->real^N` (LABEL_TAC "seg"))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "pairs" (MP_TAC o SPEC `&n + &1`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC P2BX0_PAIR_SEGMENTS THEN MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v r. mfd_tnorm (g:A->real^N^N) xl v = &1
                      ==> mfd_geo (top,atlas) g xl v r IN topspace top`
  (LABEL_TAC "geoin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `xl:A`; `v:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `u:num->real^N`; `\n:num. &n + &1`] CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (X_CHOOSE_THEN `sub1:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rayu") (LABEL_TAC "convu")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `xl:A`; `\n:num. (w:num->real^N) (sub1 n)`; `\n:num. &(sub1 n) + &1`]
                CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      can (term_match [] `!n:num. n <= (sub1:num->num) n`) (concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^N` (X_CHOOSE_THEN `sub2:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rayw") (LABEL_TAC "convw")))))) THEN
  SUBGOAL_THEN
   `!s t. &0 <= s /\ &0 <= t
          ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u0 s)
                                     (mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t) = s + t`
  (LABEL_TAC "opp") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    ABBREV_TAC `D = mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl u0 s)
                                           (mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t)` THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ABBREV_TAC `e = abs(D - (s + t)) / &4` THEN
    SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "convu" (MP_TAC o SPECL [`s:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
    USE_THEN "convw" (MP_TAC o SPECL [`t:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
    MP_TAC(SPEC `s + t:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
    ABBREV_TAC `n = N1 + N2 + N3:num` THEN
    SUBGOAL_THEN `N2 <= n /\ N1 <= (sub2:num->num) n /\ s + t <= &((sub1:num->num) (sub2 n))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `n <= (sub2:num->num) n /\ (sub2 n) <= (sub1:num->num) (sub2 n)`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "n" THEN ARITH_TAC;
        UNDISCH_TAC `n <= (sub2:num->num) n` THEN EXPAND_TAC "n" THEN ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N3` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `n <= (sub2:num->num) n` THEN
        UNDISCH_TAC `(sub2:num->num) n <= (sub1:num->num) (sub2 n)` THEN
        EXPAND_TAC "n" THEN ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "n1" (MP_TAC o SPEC `(sub2:num->num) n`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "n2" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_TAC] THEN
    USE_THEN "seg" (MP_TAC o SPEC `(sub1:num->num) ((sub2:num->num) n)`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`] o check (fun th ->
      can (term_match [] `!s t. &0 <= s /\ s <= x /\ &0 <= t /\ t <= x ==> P s t`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 s`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl (u((sub1:num->num) ((sub2:num->num) n))) s`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl (w((sub1:num->num) ((sub2:num->num) n))) t`]
                  P2BX0_DIST_QUAD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `\t. if &0 <= t then mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t
                  else mfd_geo (top,atlas) g xl w0 (--t)` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN REWRITE_TAC[] THEN
  USE_THEN "rayu" (STRIP_ASSUME_TAC o REWRITE_RULE[cmp_ray]) THEN
  USE_THEN "rayw" (STRIP_ASSUME_TAC o REWRITE_RULE[cmp_ray]) THEN
  ASM_CASES_TAC `&0 <= s` THEN ASM_CASES_TAC `&0 <= t` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[];
    ASM_SIMP_TAC[] THEN
    USE_THEN "opp" (MP_TAC o SPECL [`s:real`; `--t`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. &0 <= t ==> mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t IN topspace top`)
            (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl w0 (--s)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) xl u0 t`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "opp" (MP_TAC o SPECL [`t:real`; `--s`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_REAL_ARITH_TAC;
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. &0 <= t ==> mfd_geo (top,atlas) (g:A->real^N^N) xl w0 t IN topspace top`)
            (concl th))) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`--s`; `--t`] o check (fun th ->
      can (term_match [] `!s t. &0 <= s /\ &0 <= t
             ==> mfd_joinable (top,atlas) (mfd_geo (top,atlas) (g:A->real^N^N) xl w0 s)
                   (mfd_geo (top,atlas) g xl w0 t) /\
                 mfd_dist (top,atlas) g (mfd_geo (top,atlas) g xl w0 s)
                   (mfd_geo (top,atlas) g xl w0 t) = abs(t - s)`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC]);;

(* X0.8c Pairs at exact distance from approximate pairs in a compact set:   *)
(* F(y,z) = d(y,z) - 2|d(xl,y) - A| - 2|d(xl,z) - A| attains its maximum on   *)
(* K x K; approximate pairs give max F >= 2A, and the triangle inequality    *)
(* gives F <= 2A - |d(xl,y) - A| - |d(xl,z) - A|.                              *)

let P2BX0_PAIRS_FROM_SUP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) xl K A.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     xl IN topspace top /\ compact_in top K /\ &0 < A /\
     (!e. &0 < e
          ==> ?y z. y IN K /\ z IN K /\
                    abs(mfd_dist (top,atlas) g xl y - A) < e /\
                    abs(mfd_dist (top,atlas) g xl z - A) < e /\
                    &2 * A - e < mfd_dist (top,atlas) g y z)
     ==> ?a b. a IN K /\ b IN K /\
               mfd_dist (top,atlas) g xl a = A /\ mfd_dist (top,atlas) g xl b = A /\
               mfd_dist (top,atlas) g a b = &2 * A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "appr"))))))) THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  ABBREV_TAC
   `Fp = \p:A#A. mfd_dist (top,atlas) (g:A->real^N^N) (FST p) (SND p) -
                 &2 * abs(mfd_dist (top,atlas) g xl (FST p) - A) -
                 &2 * abs(mfd_dist (top,atlas) g xl (SND p) - A)` THEN
  SUBGOAL_THEN `continuous_map (prod_topology top top,euclideanreal) (\p:A#A. --((Fp:A#A->real) p))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN EXPAND_TAC "Fp" THEN
    REWRITE_TAC[] THEN REPEAT
     (MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC) THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`] MFD_DIST_CONTINUOUS) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM];
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      SUBGOAL_THEN `(\p:A#A. mfd_dist (top,atlas) (g:A->real^N^N) xl (FST p)) =
                    (\y. mfd_dist (top,atlas) g xl y) o FST` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[CONTINUOUS_MAP_FST] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      SUBGOAL_THEN `(\p:A#A. mfd_dist (top,atlas) (g:A->real^N^N) xl (SND p)) =
                    (\y. mfd_dist (top,atlas) g xl y) o SND` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND] THEN MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((K:A->bool) CROSS K = {})` ASSUME_TAC THENL
   [USE_THEN "appr" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PAIR_THM; IN_CROSS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`prod_topology (top:A topology) top`; `\p:A#A. --((Fp:A#A->real) p)`;
                 `(K:A->bool) CROSS K`] RFA_CMAP_COMPACT_MIN) THEN
  ASM_REWRITE_TAC[COMPACT_IN_CROSS] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "max")))) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * A <= (Fp:A#A->real) (a,b)` ASSUME_TAC THENL
   [ABBREV_TAC `m = (Fp:A#A->real) (a,b)` THEN
    MATCH_MP_TAC(REAL_ARITH `~(x < y) ==> y <= x`) THEN DISCH_TAC THEN
    USE_THEN "appr" (MP_TAC o SPEC `(&2 * A - m) / &5`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `&2 * A - &5 * ((&2 * A - m) / &5) < (Fp:A#A->real) (y,z)` ASSUME_TAC THENL
     [EXPAND_TAC "Fp" THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "max" (MP_TAC o SPECL [`y:A`; `z:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) a b <=
                mfd_dist (top,atlas) g xl a + mfd_dist (top,atlas) g xl b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `xl:A`; `b:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `a:A`; `xl:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&2 * A <= (Fp:A#A->real) (a,b)` THEN EXPAND_TAC "Fp" THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* X0.8d Exact pairs in the limit from approximate pairs in the views, by    *)
(* LIM_BALL (the view points at rescaled distance A lie in phi k (K INTER    *)
(* W k)), LIM_DIST (rescaled distances converge on K) and                     *)
(* P2BX0_PAIRS_FROM_SUP.                                                      *)

let P2BX0_LIMIT_PAIRS = prove
 (`!(u:A->bool) (w:B->bool)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (x:num->A) t Q J (top:B topology) atlas g (xl:B) W phi s A.
     LIM_DIST_STATEMENT u w /\ LIM_BALL_STATEMENT u w /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!n tau. ~(topspace(rfs_vtop (V n) tau) = {})
              ==> smooth_manifold_atlas (rfs_vtop (V n) tau) (rfs_vatlas (V n) tau) /\
                  riemannian_metric (rfs_vatlas (V n) tau) (rfs_vmetric (V n) tau)) /\
     (!k. hausdorff_space (rfs_vtop (V k) (t k + s / Q k))) /\
     s IN J /\ connected_space top /\ riemannian_metric atlas (g s) /\
     mfd_complete (top,atlas) (g s) /\ &0 < A /\
     (!e. &0 < e
          ==> ?N. !k. N <= k
                  ==> ?a b. mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                          rfs_vatlas (V k) (t k + s / Q k)) (x k) a /\
                            mfd_joinable (rfs_vtop (V k) (t k + s / Q k),
                                          rfs_vatlas (V k) (t k + s / Q k)) (x k) b /\
                            sqrt(Q k) *
                            mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                      rfs_vatlas (V k) (t k + s / Q k))
                                     (rfs_vmetric (V k) (t k + s / Q k)) (x k) a = A /\
                            sqrt(Q k) *
                            mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                      rfs_vatlas (V k) (t k + s / Q k))
                                     (rfs_vmetric (V k) (t k + s / Q k)) (x k) b = A /\
                            &2 * A - e <=
                            sqrt(Q k) *
                            mfd_dist (rfs_vtop (V k) (t k + s / Q k),
                                      rfs_vatlas (V k) (t k + s / Q k))
                                     (rfs_vmetric (V k) (t k + s / Q k)) a b)
     ==> ?a b. a IN topspace top /\ b IN topspace top /\
               mfd_dist (top,atlas) (g s) xl a = A /\ mfd_dist (top,atlas) (g s) xl b = A /\
               mfd_dist (top,atlas) (g s) a b = &2 * A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "views"))))))))))) THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                xl IN topspace top /\ (!k. &0 < (Q:num->real) k) /\
                (!k. (phi:num->B->A) k xl = x k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  USE_THEN "L2" (MP_TAC o REWRITE_RULE[LIM_BALL_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->A`; `s:real`; `A + &1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:B->bool` (X_CHOOSE_THEN `k0:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball")))) THEN
  ABBREV_TAC `K = {xl:B} UNION K0` THEN
  SUBGOAL_THEN `compact_in (top:B topology) K /\ (xl:B) IN K /\ K0 SUBSET K /\
                K SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[COMPACT_IN_SING];
      SET_TAC[];
      SET_TAC[];
      REWRITE_TAC[UNION_SUBSET; SING_SUBSET] THEN ASM_MESON_TAC[compact_in]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `xl:B`; `K:B->bool`; `A:real`]
                P2BX0_PAIRS_FROM_SUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "L1" (MP_TAC o REWRITE_RULE[LIM_DIST_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
      `W:num->B->bool`; `phi:num->B->A`; `s:real`; `K:B->bool`; `e / &3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "dist")) THEN
    USE_THEN "views" (MP_TAC o SPEC `e / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "vN")) THEN
    USE_THEN "vN" (MP_TAC o SPEC `k0 + k1 + N:num`) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `k = k0 + k1 + N:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(k0:num) <= k /\ (k1:num) <= k` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt((Q:num->real) k)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:A) IN IMAGE ((phi:num->B->A) k) (K0 INTER W k) /\
                  (b:A) IN IMAGE (phi k) (K0 INTER W k)`
    MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `z:B` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`y:B`; `z:B`] THEN
    SUBGOAL_THEN `(y:B) IN K /\ (z:B) IN K` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `y:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `xl:B`; `z:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "dist" (MP_TAC o SPECL [`k:num`; `y:B`; `z:B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` (X_CHOOSE_THEN `b:B` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:B`; `b:B`] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* X0.8e Toponogov in the form used for the line (MT Thm 5.35): angle     *)
(* comparison along two minimising geodesics from p with cleared           *)
(* denominators (CMPAN_TOPONOGOV_GEN), and the far pair at x: if the        *)
(* segments from p to x and to a far point y start close (distance <= eta  *)
(* at time 1) and d(p,y) >= K d(p,x), then near x there are a, b at         *)
(* distance r from x with d(a,b)^2 >= 2 r^2 (1 - (1 - c K) / (1 + K)),       *)
(* c = 1 - eta^2 / 2 (comparison at p, then at x).                          *)

let P2BX0_TOPO_GEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p u v L1 L2 s1 s2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     p IN topspace top /\ mfd_tnorm g p u = &1 /\ mfd_tnorm g p v = &1 /\
     &0 < L1 /\ &0 < L2 /\
     mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u L1) = L1 /\
     mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p v L2) = L2 /\
     &0 < s1 /\ s1 <= L1 /\ &0 < s2 /\ s2 <= L2
     ==> (s1 pow 2 + s2 pow 2 -
          mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s1)
                                 (mfd_geo (top,atlas) g p v s2) pow 2) * (L1 * L2) <=
         (L1 pow 2 + L2 pow 2 -
          mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u L1)
                                 (mfd_geo (top,atlas) g p v L2) pow 2) * (s1 * s2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `v:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ev") ASSUME_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eu") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`; `v:real^N`; `L1:real`; `L2:real`] CMPAN_TOPONOGOV_GEN) THEN
  USE_THEN "eu" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:real`; `L1:real`; `s2:real`; `L2:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `X = s1 pow 2 + s2 pow 2 -
                  mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u s1)
                                         (mfd_geo (top,atlas) (g:A->real^N^N) p v s2) pow 2` THEN
  ABBREV_TAC `Y = L1 pow 2 + L2 pow 2 -
                  mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u L1)
                                         (mfd_geo (top,atlas) (g:A->real^N^N) p v L2) pow 2` THEN
  SUBGOAL_THEN `&0 < &2 * s1 * s2 /\ &0 < &2 * L1 * L2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `X * (L1 * L2) = (X / (&2 * s1 * s2)) * ((&2 * s1 * s2) * (L1 * L2)) /\
                Y * (s1 * s2) = (Y / (&2 * L1 * L2)) * ((&2 * s1 * s2) * (L1 * L2))`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `&0 < &2 * s1 * s2` THEN UNDISCH_TAC `&0 < &2 * L1 * L2` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

(* X0.8f The algebra of the far pair (MT Thm 5.35): from the comparison at  *)
(* p (D^2 <= dx^2 + dy^2 - (2 - eta^2) dx dy) and at x ((2R - d2) dx D <=    *)
(* (dx^2 + D^2 - dy^2) R, R = r^2, d2 = d(a,b)^2) follows                      *)
(* R K (4 - eta^2) <= (1 + K) d2 when dy >= K dx, K >= 2, eta^2 K <= 1.       *)

let P2BX0_FAR_ALGEBRA = prove
 (`!d2 R D dx dy eta K.
     &1 <= dx /\ &2 <= K /\ K * dx <= dy /\ &0 <= eta /\ eta pow 2 * K <= &1 /\
     &0 < R /\ &0 <= d2 /\ dy - dx <= D /\ D <= dx + dy /\
     (&2 * R - d2) * (dx * D) <= (dx pow 2 + D pow 2 - dy pow 2) * R /\
     D pow 2 <= dx pow 2 + dy pow 2 - (&2 - eta pow 2) * dx * dy
     ==> R * K * (&4 - eta pow 2) <= (&1 + K) * d2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < dx /\ &0 < dy /\ &0 < D /\ &0 <= eta pow 2 /\ eta pow 2 <= &1 / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * dx <= K * dx` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `eta pow 2 * &2 <= eta pow 2 * K` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* (c): (2R - d2) D <= N R with N = 2 dx - (2 - eta^2) dy *)
  SUBGOAL_THEN `(&2 * R - d2) * D <= (&2 * dx - (&2 - eta pow 2) * dy) * R` ASSUME_TAC THENL
   [SUBGOAL_THEN `dx * ((&2 * R - d2) * D) <= dx * ((&2 * dx - (&2 - eta pow 2) * dy) * R)`
    MP_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(dx pow 2 + D pow 2 - dy pow 2) * R` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(&2 * R - d2) * (dx * D) <= (dx pow 2 + D pow 2 - dy pow 2) * R` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(dx pow 2 + D pow 2 - dy pow 2) * R <=
                  (&2 * dx pow 2 - (&2 - eta pow 2) * dx * dy) * R` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* N < 0 *)
  SUBGOAL_THEN `&2 * dx - (&2 - eta pow 2) * dy < &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 / &2 * dy <= (&2 - eta pow 2) * dy` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * dx <= K * dx` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* d2 > 2R *)
  SUBGOAL_THEN `&0 <= d2 - &2 * R` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(x < &0) ==> &0 <= x`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&2 * R - d2) * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * dx - (&2 - eta pow 2) * dy) * R < &0` MP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC(REAL_ARITH
        `&0 < R /\ R * N < R * &0 ==> R * N < &0`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* (f), (g) *)
  SUBGOAL_THEN `(d2 - &2 * R) * D <= (d2 - &2 * R) * (dx + dy)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `R * (&4 - eta pow 2) * dy <= d2 * (dx + dy)` ASSUME_TAC THENL
   [UNDISCH_TAC `(d2 - &2 * R) * D <= (d2 - &2 * R) * (dx + dy)` THEN
    UNDISCH_TAC `(&2 * R - d2) * D <= (&2 * dx - (&2 - eta pow 2) * dy) * R` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* (h), (i) *)
  SUBGOAL_THEN `(R * K * (&4 - eta pow 2)) * (dx + dy) <= ((&1 + K) * d2) * (dx + dy)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + K) * R * (&4 - eta pow 2) * dy` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(R * (&4 - eta pow 2)) * (K * (dx + dy)) <=
                    (R * (&4 - eta pow 2)) * ((&1 + K) * dy)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      SUBGOAL_THEN `(&1 + K) * (R * (&4 - eta pow 2) * dy) <= (&1 + K) * (d2 * (dx + dy))`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    SUBGOAL_THEN `&0 < dx + dy` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ]]);;

(* X0.8g The far pair at x = geo p u dx (comparison at p, then at x).        *)

let P2BX0_FAR_PAIR = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p u v dx dy eta K r.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     p IN topspace top /\ mfd_tnorm g p u = &1 /\ mfd_tnorm g p v = &1 /\
     &1 <= dx /\ &2 <= K /\ K * dx <= dy /\ &0 <= eta /\ eta pow 2 * K <= &1 /\
     (!s. &0 <= s /\ s <= dx
          ==> mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u s) = s) /\
     (!s. &0 <= s /\ s <= dy
          ==> mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p v s) = s) /\
     mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u (&1))
                            (mfd_geo (top,atlas) g p v (&1)) <= eta /\
     &0 < r /\ r <= dx
     ==> ?a b. mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u dx) a /\
               mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u dx) b /\
               mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u dx) a = r /\
               mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u dx) b = r /\
               r pow 2 * K * (&4 - eta pow 2) <=
               (&1 + K) * mfd_dist (top,atlas) g a b pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN topspace top /\ y IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w s. mfd_tnorm (g:A->real^N^N) p w = &1
                      ==> mfd_geo (top,atlas) g p w s IN topspace top`
  (LABEL_TAC "geoin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `x = mfd_geo (top,atlas) (g:A->real^N^N) p u dx` THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N) p v dy` THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (y:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN CONJ_TAC THEN
    USE_THEN "geoin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= dy` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * dx <= K * dx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p x = dx /\
                mfd_dist (top,atlas) g p y = dy`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "y" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!s. &0 <= s /\ s <= dx
           ==> mfd_dist (top,atlas) (g:A->real^N^N) (p:A)
                 (mfd_geo (top,atlas) g p (u:real^N) s) = s`) (concl th)));
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!s. &0 <= s /\ s <= dy
           ==> mfd_dist (top,atlas) (g:A->real^N^N) (p:A)
                 (mfd_geo (top,atlas) g p (v:real^N) s) = s`) (concl th)))] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* comparison at p *)
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^N^N) x y` THEN
  SUBGOAL_THEN `D pow 2 <= dx pow 2 + dy pow 2 - (&2 - eta pow 2) * dx * dy` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `u:real^N`; `v:real^N`; `dx:real`; `dy:real`; `&1`; `&1`]
                  P2BX0_TOPO_GEO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `d1 = mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g p u (&1))
                                             (mfd_geo (top,atlas) g p v (&1))` THEN
    SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
     [EXPAND_TAC "d1" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "join" MATCH_MP_TAC THEN CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `d1 pow 2 <= eta pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 - eta pow 2) * (dx * dy) <= (&1 pow 2 + &1 pow 2 - d1 pow 2) * (dx * dy)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* triangle bounds for D *)
  SUBGOAL_THEN `dy - dx <= D /\ D <= dx + dy` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `x:A`; `y:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `p:A`; `y:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* segments from x *)
  SUBGOAL_THEN `~(p:A = x) /\ ~(y:A = x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 * dx <= K * dx` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x p = dx` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `p:A`] MFD_DIST_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `p:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w1:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw1"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `y:A`] CMPSO_SEGMENT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w2:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw2"))))) THEN
  MAP_EVERY EXISTS_TAC [`mfd_geo (top,atlas) (g:A->real^N^N) x w1 r`;
                        `mfd_geo (top,atlas) (g:A->real^N^N) x w2 r`] THEN
  SUBGOAL_THEN `r <= D` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * dx <= K * dx` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x (mfd_geo (top,atlas) g x w1 r) = r /\
                mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x w2 r) = r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "dw1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "dw2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w s. mfd_tnorm (g:A->real^N^N) x w = &1
                      ==> mfd_geo (top,atlas) g x w s IN topspace top`
  (LABEL_TAC "geoinx") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "geoinx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "geoinx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* comparison at x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `w1:real^N`; `w2:real^N`; `dx:real`; `D:real`; `r:real`; `r:real`]
                P2BX0_TOPO_GEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BX0_FAR_ALGEBRA THEN
  MAP_EVERY EXISTS_TAC [`D:real`; `dx:real`; `dy:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT];
    REWRITE_TAC[REAL_LE_POW_2];
    UNDISCH_TAC
     `(r pow 2 + r pow 2 -
       mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x w1 r)
                (mfd_geo (top,atlas) g x w2 r) pow 2) * (dx * D) <=
      (dx pow 2 + D pow 2 - dy pow 2) * (r * r)` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* X0.8h Subsequence helpers: a strictly increasing refinement of a        *)
(* sequence of indices with n <= sub n, composition, and a strictly        *)
(* increasing subsequence along which a divergent real sequence exceeds    *)
(* n + 1.                                                                    *)

let P2BX0_SUBSEQ_MONO = prove
 (`!sub:num->num. (!n. n <= sub n) ==> ?rho. p3_subseq (sub o rho) /\ !n. n <= rho n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(prove_recursive_functions_exist num_RECURSION
    `(rho:num->num) 0 = 0 /\ !k. rho(SUC k) = (sub:num->num)(rho k) + 1`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rho:num->num` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3_subseq; o_THM] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) (rho(k:num)) + 1` o check (fun th ->
      can (term_match [] `!n:num. n <= (sub:num->num) n`) (concl th))) THEN
    ARITH_TAC;
    INDUCT_TAC THEN ASM_REWRITE_TAC[LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(rho:num->num) n` o check (fun th ->
      can (term_match [] `!n:num. n <= (sub:num->num) n`) (concl th))) THEN
    UNDISCH_TAC `n <= (rho:num->num) n` THEN ARITH_TAC]);;

let P2BX0_SUBSEQ_COMPOSE = prove
 (`!(r:num->num) t. p3_subseq r /\ p3_subseq t ==> p3_subseq (r o t)`,
  REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[]);;

let P2BX0_SUBSEQ_GE = prove
 (`!sub:num->num. p3_subseq sub ==> !n. n <= sub n`,
  REWRITE_TAC[p3_subseq; MONOTONE_BIGGER]);;

let P2BX0_SUBSEQ_DIVERGE = prove
 (`!f:num->real. (!M. ?N. !n. N <= n ==> M < f n)
                 ==> ?sub. p3_subseq sub /\ !n. &n + &1 <= f (sub n)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `NN:real->num`) THEN
  MP_TAC(SPEC `\j:num. (NN:real->num) (&j + &1)` P2BX0_SUBSEQ_ABOVE) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sub:num->num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* X0.8i The arithmetic of the parameters of the far pair: with             *)
(* ep = min (e / A) 1, K = max 2 (2 / ep), eta^2 K = 1, the bound           *)
(* (A / sqrt lam)^2 K (4 - eta^2) <= (1 + K) d^2 gives 2A - e <= sqrt lam d.  *)

let P2BX0_PAIR_PARAMS = prove
 (`!A e. &0 < A /\ &0 < e
         ==> ?ep K. &0 < ep /\ ep <= &1 /\ A * ep <= e /\ &2 <= K /\ &2 <= K * ep`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min (e / A) (&1)` THEN
  EXISTS_TAC `max (&2) (&2 / min (e / A) (&1))` THEN
  ABBREV_TAC `ep = min (e / A) (&1)` THEN
  SUBGOAL_THEN `&0 < ep /\ ep <= &1 /\ A * ep <= e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_01];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * e / A` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / ep * ep` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

let P2BX0_PAIR_ARITH = prove
 (`!A e lam d K eta ep.
     &0 < A /\ &0 < e /\ &0 < lam /\ &0 <= d /\ &0 < ep /\ ep <= &1 /\ A * ep <= e /\
     &2 <= K /\ &2 <= K * ep /\ eta pow 2 * K = &1 /\
     (A / sqrt lam) pow 2 * K * (&4 - eta pow 2) <= (&1 + K) * d pow 2
     ==> &2 * A - e <= sqrt lam * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A / sqrt lam) pow 2 = A pow 2 / lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_DIV; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `A pow 2 * (&4 - &3 * ep) <= lam * d pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `A pow 2 * (&4 * K - &1) <= lam * ((&1 + K) * d pow 2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(A pow 2 / lam) * (&4 * K - &1) <= (&1 + K) * d pow 2` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        SUBGOAL_THEN `(A / sqrt lam) pow 2 * K * (&4 - eta pow 2) =
                      (A / sqrt lam) pow 2 * (&4 * K - &1)` (fun th -> REWRITE_TAC[GSYM th]) THENL
         [UNDISCH_TAC `eta pow 2 * K = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `(a / b) * c = (a * c) / b`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(A pow 2 * (&4 - &3 * ep)) * (&1 + K) <= A pow 2 * (&4 * K - &1)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(&4 - &3 * ep) * (&1 + K) <= &4 * K - &1` MP_TAC THENL
       [SUBGOAL_THEN `ep * &1 <= ep * K` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        DISCH_TAC THEN
        SUBGOAL_THEN `A pow 2 * ((&4 - &3 * ep) * (&1 + K)) <= A pow 2 * (&4 * K - &1)`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
          REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(A pow 2 * (&4 - &3 * ep)) * (&1 + K) <= (lam * d pow 2) * (&1 + K)`
    MP_TAC THENL
     [UNDISCH_TAC `A pow 2 * (&4 * K - &1) <= lam * ((&1 + K) * d pow 2)` THEN
      UNDISCH_TAC `(A pow 2 * (&4 - &3 * ep)) * (&1 + K) <= A pow 2 * (&4 * K - &1)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 + K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 * A - e <= &0` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A pow 2 * (&4 - &3 * ep)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&2 * A - e) pow 2 <= (A * (&2 - ep)) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A pow 2 * ep pow 2 <= A pow 2 * ep` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

(* X0.8j Almost-line pairs along a sequence going to infinity (MT Thm 5.35, *)
(* distance form): if d(p,x n) -> infinity and lam n d(p,x n)^2 -> infinity, *)
(* then along a subsequence, for every A, e > 0 and all large n there are a, *)
(* b with sqrt(lam) d(x,a) = sqrt(lam) d(x,b) = A and sqrt(lam) d(a,b) >=    *)
(* 2A - e.  Segments from p to the x n (CMPSO_SEGMENT) converge at time 1    *)
(* (CMPSO_LIMIT_RAY); for x n and a far x n' the far pair (P2BX0_FAR_PAIR)   *)
(* at scale r = A / sqrt(lam) gives the pair (P2BX0_PAIR_ARITH).             *)

let P2BX0_ALMOST_PAIRS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p (x:num->A) (lam:num->real).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g y u v) /\
     p IN topspace top /\ (!n. x n IN topspace top) /\ (!n. &0 < lam n) /\
     (!M. ?N. !n. N <= n ==> M < mfd_dist (top,atlas) g p (x n)) /\
     (!M. ?N. !n. N <= n ==> M < lam n * mfd_dist (top,atlas) g p (x n) pow 2)
     ==> ?sub. p3_subseq sub /\
               !A e. &0 < A /\ &0 < e
                     ==> ?N. !n. N <= n
                             ==> ?a b. mfd_joinable (top,atlas) (x(sub n)) a /\
                                       mfd_joinable (top,atlas) (x(sub n)) b /\
                                       sqrt(lam(sub n)) *
                                       mfd_dist (top,atlas) g (x(sub n)) a = A /\
                                       sqrt(lam(sub n)) *
                                       mfd_dist (top,atlas) g (x(sub n)) b = A /\
                                       &2 * A - e <=
                                       sqrt(lam(sub n)) * mfd_dist (top,atlas) g a b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sec")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xin")
    (CONJUNCTS_THEN2 (LABEL_TAC "lpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "far") (LABEL_TAC "scale"))))))))))) THEN
  SUBGOAL_THEN `!y z. y IN topspace top /\ z IN topspace top
                      ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y z`
  (LABEL_TAC "join") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* a subsequence with d(p, x(sigma n)) >= n + 1 *)
  MP_TAC(ISPEC `\n. mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) n)`
                P2BX0_SUBSEQ_DIVERGE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [USE_THEN "far" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sig"))) THEN
  (* segments from p *)
  SUBGOAL_THEN
   `?un:num->real^N.
      !n. mfd_tnorm (g:A->real^N^N) p (un n) = &1 /\
          mfd_geo (top,atlas) g p (un n) (mfd_dist (top,atlas) g p (x((sigma:num->num) n))) =
          x(sigma n) /\
          !s. &0 <= s /\ s <= mfd_dist (top,atlas) g p (x(sigma n))
              ==> mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p (un n) s) = s`
  (X_CHOOSE_THEN `un:num->real^N` (LABEL_TAC "un")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `(x:num->A) ((sigma:num->num) n)`] CMPSO_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN USE_THEN "sig" (MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && rhs(concl th) = `p:A`)) THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `p:A`] MFD_DIST_REFL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      MESON_TAC[]];
    ALL_TAC] THEN
  (* convergence of the segments at fixed times *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `un:num->real^N`;
                 `\n. mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) n))`]
                CMPSO_LIMIT_RAY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "sig" (MP_TAC o SPEC `n:num`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N` (X_CHOOSE_THEN `sub1:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))))) THEN
  MP_TAC(ISPEC `sub1:num->num` P2BX0_SUBSEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rho"))) THEN
  EXISTS_TAC `(sigma:num->num) o (sub1:num->num) o (rho:num->num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A:real`; `e:real`] P2BX0_PAIR_PARAMS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `eta = inv(sqrt K)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta pow 2 * K = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt K` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`&1`; `eta / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "scale" (MP_TAC o SPEC `A pow 2`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k:num. k <= (sigma:num->num) k` (LABEL_TAC "sigge") THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k <= (sub1:num->num) ((rho:num->num) k)` (LABEL_TAC "srge") THENL
   [GEN_TAC THEN USE_THEN "rho" (MP_TAC o SPEC `k:num`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `(rho:num->num) k` o check (fun th ->
      aconv (concl th) `!n:num. n <= (sub1:num->num) n`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = (sub1:num->num) ((rho:num->num) n)` THEN
  ABBREV_TAC `dx = mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m))` THEN
  MP_TAC(SPEC `K * dx` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `M0:num`) THEN
  ABBREV_TAC `n2 = M0 + N1 + n:num` THEN
  ABBREV_TAC `m2 = (sub1:num->num) ((rho:num->num) n2)` THEN
  ABBREV_TAC `dy = mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m2))` THEN
  SUBGOAL_THEN `n <= m:num /\ n2 <= m2:num /\ N1 <= n:num /\ N2 <= n:num /\ N1 <= n2:num /\ M0 <= n2:num`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` (ASSUME `!k:num. k <= (sub1:num->num) ((rho:num->num) k)`)) THEN
    MP_TAC(SPEC `n2:num` (ASSUME `!k:num. k <= (sub1:num->num) ((rho:num->num) k)`)) THEN
    REWRITE_TAC[ASSUME `(sub1:num->num) ((rho:num->num) n) = m`;
                ASSUME `(sub1:num->num) ((rho:num->num) n2) = m2`] THEN
    UNDISCH_TAC `N1 + N2 <= n:num` THEN UNDISCH_TAC `M0 + N1 + n = n2:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= dx /\ K * dx <= dy` STRIP_ASSUME_TAC THENL
   [USE_THEN "sig" (MP_TAC o SPEC `m:num`) THEN USE_THEN "sig" (MP_TAC o SPEC `m2:num`) THEN
    REWRITE_TAC[ASSUME `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`;
                ASSUME `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m2)) = dy`] THEN
    UNDISCH_TAC `M0 <= n2:num` THEN UNDISCH_TAC `n2 <= m2:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `K * dx <= &M0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w s. mfd_tnorm (g:A->real^N^N) p w = &1
                      ==> mfd_geo (top,atlas) g p w s IN topspace top`
  (LABEL_TAC "geoin") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `w:real^N`] CMPB_GEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p ((un:num->real^N) m) = &1 /\
                mfd_tnorm g p (un m2) = &1` STRIP_ASSUME_TAC THENL
   [USE_THEN "un" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  (* closeness at time 1 *)
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N)
                  (mfd_geo (top,atlas) g p ((un:num->real^N) m) (&1))
                  (mfd_geo (top,atlas) g p (un m2) (&1)) <= eta` ASSUME_TAC THENL
   [USE_THEN "N1" (MP_TAC o SPEC `(rho:num->num) n`) THEN
    USE_THEN "N1" (MP_TAC o SPEC `(rho:num->num) n2`) THEN
    REWRITE_TAC[ASSUME `(sub1:num->num) ((rho:num->num) n) = m`;
                ASSUME `(sub1:num->num) ((rho:num->num) n2) = m2`] THEN
    ANTS_TAC THENL
     [USE_THEN "rho" (MP_TAC o SPEC `n2:num`) THEN UNDISCH_TAC `N1 <= n2:num` THEN ARITH_TAC;
      DISCH_TAC] THEN
    ANTS_TAC THENL
     [USE_THEN "rho" (MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `N1 <= n:num` THEN ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m2) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] P2BX0_DIST_QUAD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "geoin" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] MFD_DIST_REFL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "geoin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m2) (&1)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u0 (&1)`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scale r = A / sqrt(lam) <= dx *)
  SUBGOAL_THEN `&0 < sqrt((lam:num->real) ((sigma:num->num) m))` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN USE_THEN "lpos" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `A / sqrt((lam:num->real) ((sigma:num->num) m)) < dx` ASSUME_TAC THENL
   [USE_THEN "N2" (MP_TAC o SPEC `(sigma:num->num) m`) THEN
    ANTS_TAC THENL
     [USE_THEN "sigge" (MP_TAC o SPEC `m:num`) THEN UNDISCH_TAC `N2 <= n:num` THEN
      UNDISCH_TAC `n <= m:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME
      `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `A pow 2 < lam ((sigma:num->num) m) * dx pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the far pair *)
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p ((un:num->real^N) m) dx =
                (x:num->A) ((sigma:num->num) m)` ASSUME_TAC THENL
   [USE_THEN "un" (MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[ASSUME
      `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `(un:num->real^N) m`; `(un:num->real^N) m2`; `dx:real`; `dy:real`;
                 `eta:real`; `K:real`; `A / sqrt((lam:num->real) ((sigma:num->num) m))`]
                P2BX0_FAR_PAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "un" (MP_TAC o SPEC `m:num`) THEN
      REWRITE_TAC[ASSUME
        `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m)) = dx`] THEN
      SIMP_TAC[];
      USE_THEN "un" (MP_TAC o SPEC `m2:num`) THEN
      REWRITE_TAC[ASSUME
        `mfd_dist (top,atlas) (g:A->real^N^N) p ((x:num->A) ((sigma:num->num) m2)) = dy`] THEN
      SIMP_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt((lam:num->real) ((sigma:num->num) m)) *
                (A / sqrt(lam(sigma m))) = A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX0_PAIR_ARITH THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eta:real`; `ep:real`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
  EXISTS_TAC `(x:num->A) ((sigma:num->num) m)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(x:num->A) ((sigma:num->num) m)`; `a:A`] MFD_JOINABLE_SYM) THEN
  ASM_SIMP_TAC[]);;

(* X0.11a Setup lemmas for the X0 assembly: the slices of rfs_flow_view,    *)
(* regularity and Hausdorffness of the views, and divergence of distances   *)
(* from the divergence of R d^2 (closed balls are compact, R is continuous). *)

let P2BX0_VIEW_FACTS = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) J (g:real->B->real^3^3) t.
     rfs_vtop (rfs_flow_view (top,atlas) J g) t =
     (if t IN J then top else discrete_topology {}) /\
     rfs_vatlas (rfs_flow_view (top,atlas) J g) t = atlas /\
     rfs_vmetric (rfs_flow_view (top,atlas) J g) t = g t`,
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2BX0_VIEW_REGULAR = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) J (g:real->B->real^3^3).
     smooth_manifold_atlas top atlas /\ (!s. s IN J ==> riemannian_metric atlas (g s))
     ==> !s. ~(topspace(rfs_vtop (rfs_flow_view (top,atlas) J g) s) = {})
             ==> smooth_manifold_atlas (rfs_vtop (rfs_flow_view (top,atlas) J g) s)
                                       (rfs_vatlas (rfs_flow_view (top,atlas) J g) s) /\
                 riemannian_metric (rfs_vatlas (rfs_flow_view (top,atlas) J g) s)
                                   (rfs_vmetric (rfs_flow_view (top,atlas) J g) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN
  REWRITE_TAC[P2BX0_VIEW_FACTS] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY]);;

let P2BX0_VIEW_HAUSDORFF = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) J (g:real->B->real^3^3).
     hausdorff_space top
     ==> !t. hausdorff_space (rfs_vtop (rfs_flow_view (top,atlas) J g) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BX0_VIEW_FACTS] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[HAUSDORFF_SPACE_DISCRETE_TOPOLOGY]);;

let P2BX0_DIST_DIVERGE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p (q:num->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ p IN topspace top /\
     (!k. q k IN topspace top) /\
     (!M. ?N. !k. N <= k
                  ==> M < mfd_scalar atlas g (q k) * mfd_dist (top,atlas) g p (q k) pow 2)
     ==> !M. ?N. !k. N <= k ==> M < mfd_dist (top,atlas) g p (q k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "qin") (LABEL_TAC "div"))))))) THEN
  X_GEN_TAC `M:real` THEN
  ABBREV_TAC `M' = max M (&0)` THEN
  ABBREV_TAC `Kb = mfd_cball (top,atlas) (g:A->real^N^N) p M'` THEN
  SUBGOAL_THEN `compact_in top (Kb:A->bool) /\ (p:A) IN Kb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kb" THEN CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_complete];
      REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MFD_DIST_REFL; MFD_JOINABLE_REFL] THEN EXPAND_TAC "M'" THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `\y:A. --(mfd_scalar atlas (g:A->real^N^N) y)`;
                 `Kb:A->bool`] RFA_CMAP_COMPACT_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_NEG2] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max"))) THEN
  ABBREV_TAC `C = max (mfd_scalar atlas (g:A->real^N^N) y0) (&0)` THEN
  USE_THEN "div" (MP_TAC o SPEC `C * M' pow 2`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_THEN(LABEL_TAC "N") THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `M <= M' /\ ~(d <= M') ==> M < d`) THEN CONJ_TAC THENL
   [EXPAND_TAC "M'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  USE_THEN "N" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p ((q:num->A) k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "qin" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^N^N) ((q:num->A) k) <= C` ASSUME_TAC THENL
   [USE_THEN "max" (MP_TAC o SPEC `(q:num->A) k`) THEN ANTS_TAC THENL
     [EXPAND_TAC "Kb" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "C" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) p ((q:num->A) k)` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^N^N) ((q:num->A) k)` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL [EXPAND_TAC "C" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 <= M' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `R * d pow 2 <= C * d pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `C * d pow 2 <= C * M' pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* X0.6 Limit properties in the X0 setting (views of g on s < b at the      *)
(* times s0 + s / Q k, Q k = R(s0,q k)) from the LIM statements:             *)
(* sec >= 0 and R(xl,0) = 1 (LIM_CURV).                                      *)

let p2bx0_xlim = new_definition
 `p2bx0_xlim kappa (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
             b s0 (q:num->B) (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
             (g':real->B->real^3^3) (xl:B) (W:num->B->bool) (phi:num->B->B) <=>
    p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\
    (!k. q k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q k)) /\
    p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s < b} g) q (\k. s0)
                        (\k. mfd_scalar atlas (g s0) (q k)) {s | s <= &0}
                        (top',atlas') g' xl W phi /\
    (!s. s <= &0 ==> riemannian_metric atlas' (g' s))`;;

let P2BX0_XVIEW = prove
 (`!(top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) b s0 Q s.
     s0 < b /\ &0 < Q /\ s <= &0
     ==> rfs_vtop (rfs_flow_view (top,atlas) {s | s < b} g) (s0 + s / Q) = top /\
         rfs_vatlas (rfs_flow_view (top,atlas) {s | s < b} g) (s0 + s / Q) = atlas /\
         rfs_vmetric (rfs_flow_view (top,atlas) {s | s < b} g) (s0 + s / Q) = g (s0 + s / Q) /\
         s0 + s / Q < b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s0 + s / Q < b` ASSUME_TAC THENL
   [SUBGOAL_THEN `s / Q <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2BX0_VIEW_FACTS; IN_ELIM_THM]);;

let P2BX0_XLIM_BASIC = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi
     ==> hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
         (!s. s < b ==> riemannian_metric atlas (g s)) /\
         (!s x u v. s < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g s) x u v) /\
         hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ xl IN topspace top' /\
         (!k. (phi:num->B->B) k xl = q k) /\
         (!n:num s. ~(topspace(rfs_vtop (rfs_flow_view (top,atlas) {s | s < b} g) s) = {})
                ==> smooth_manifold_atlas
                      (rfs_vtop (rfs_flow_view (top,atlas) {s | s < b} g) s)
                      (rfs_vatlas (rfs_flow_view (top,atlas) {s | s < b} g) s) /\
                    riemannian_metric
                      (rfs_vatlas (rfs_flow_view (top,atlas) {s | s < b} g) s)
                      (rfs_vmetric (rfs_flow_view (top,atlas) {s | s < b} g) s)) /\
         (!k:num tau. hausdorff_space
                    (rfs_vtop (rfs_flow_view (top,atlas) {s | s < b} g) tau))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx0_xlim] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
  REWRITE_TAC[p2b_ancflow0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                (!s. s < b ==> riemannian_metric atlas ((g:real->B->real^3^3) s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `b - &1` o check (fun th ->
        can (term_match [] `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)`)
            (concl th))) THEN
      REWRITE_TAC[REAL_ARITH `b - &1 < b`] THEN MESON_TAC[ricci_flow_on];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th ->
        can (term_match [] `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)`)
            (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hausdorff_space (top':B topology) /\ smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
                (xl:B) IN topspace top' /\ (!k. (phi:num->B->B) k xl = q k)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p2c_flow_limit_with]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{s:real | s < b}`;
                   `g:real->B->real^3^3`] P2BX0_VIEW_REGULAR) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{s:real | s < b}`;
                   `g:real->B->real^3^3`] P2BX0_VIEW_HAUSDORFF) THEN
    ASM_SIMP_TAC[]]);;

(* X0.6b sec >= 0 and R(xl,0) = 1 on the X0 limit (LIM_CURV).                *)

let P2BX0_XLIM_SEC = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi
     ==> !s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                   ==> &0 <= mfd_sectional atlas' (g' s) y u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  UNDISCH_TAC `LIM_CURV_STATEMENT (w:B->bool) w` THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`; `y:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `0` THEN MAP_EVERY X_GEN_TAC [`k:num`; `z:B`; `u':real^3`; `v':real^3`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `b:real`; `s0:real`;
                   `mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`; `s:real`]
                  P2BX0_XVIEW) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:B) IN topspace (rfs_vtop (rfs_flow_view (top,atlas) {s | s < b}
                     (g:real->B->real^3^3)) (s0 + s / mfd_scalar atlas (g s0) ((q:num->B) k)))` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BX0_XLIM_R1 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi
     ==> mfd_scalar atlas' (g'(&0)) xl = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th))) THEN
  UNDISCH_TAC `LIM_CURV_STATEMENT (w:B->bool) w` THEN REWRITE_TAC[LIM_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `xl:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k) *
                     inv (mfd_scalar atlas (g s0) (q k))) = (\k. &1)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC REAL_MUL_RINV THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_CONST_EQ; TRIVIAL_LIMIT_SEQUENTIALLY] THEN MESON_TAC[]);;

(* X0.6c A function nondecreasing up to s has a nonnegative derivative at   *)
(* s (REAL_DERIVATIVE_POS_RIGHT_MAXIMUM on [s - 1,s]); used for dR/ds >= 0  *)
(* on the X0 limit.                                                          *)

let P2BX0_MONO_DERIV_NONNEG = prove
 (`!f s d. (!s1 s2. s1 <= s2 /\ s2 <= s ==> f s1 <= f s2) /\
           (f has_real_derivative d) (atreal s)
           ==> &0 <= d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_POS_RIGHT_MAXIMUM THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `s - &1`; `s:real`; `&1`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN; REAL_LT_01; REAL_ARITH `s - &1 < s`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* For y in the X0 limit, eventually phi k y lies in M and its rescaled     *)
(* distance to q k approaches d(xl,y) (LIM_DIST on {xl,y}).                 *)

let P2BX0_XLIM_NEAR = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi
    s y e.
     LIM_DIST_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ s <= &0 /\ mfd_complete (top',atlas') (g' s) /\
     y IN topspace top' /\ &0 < e
     ==> ?k0. !k. k0 <= k
                  ==> (phi:num->B->B) k y IN topspace top /\
                      mfd_joinable (top,atlas) (q k) (phi k y) /\
                      abs(sqrt(mfd_scalar atlas (g s0) (q k)) *
                          mfd_dist (top,atlas) (g(s0 + s / mfd_scalar atlas (g s0) (q k)))
                                   (q k) (phi k y) -
                          mfd_dist (top',atlas') (g' s) xl y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th)) STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `LIM_DIST_STATEMENT (w:B->bool) w` THEN REWRITE_TAC[LIM_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `s:real`;
    `{xl:B,y}`; `e:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_THEN(LABEL_TAC "d") THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "d" (MP_TAC o SPECL [`k:num`; `xl:B`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`;
                 `mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`; `s:real`]
                P2BX0_XVIEW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[]);;

(* X0.6d R(0,y) <= 4 on the X0 limit: the picked balls bound R by 4 R(q k)   *)
(* on balls of radius A / sqrt(R(q k)), LIM_DIST puts phi k y in them,     *)
(* LIM_CURV passes the bound to the limit.                                  *)

let P2BX0_XLIM_R4 = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ mfd_complete (top',atlas') (g'(&0)) /\
     (!A. ?N. !k y. N <= k /\
                    y IN mfd_ball (top,atlas) (g s0) (q k)
                                  (A * inv(sqrt(mfd_scalar atlas (g s0) (q k))))
                    ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q k))
     ==> !y. y IN topspace top' ==> mfd_scalar atlas' (g'(&0)) y <= &4`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L5") (CONJUNCTS_THEN2 (LABEL_TAC "L1")
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "balls")))))) THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  ABBREV_TAC `A = mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl y + &1` THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `&0`; `y:B`; `&1`] P2BX0_XLIM_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "near")) THEN
  USE_THEN "balls" (MP_TAC o SPEC `A:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  USE_THEN "L5" (MP_TAC o REWRITE_RULE[LIM_CURV_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `y:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((phi:num->B->B) k y) *
                  inv(mfd_scalar atlas (g s0) ((q:num->B) k))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `k0 + N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "near" (MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k) /\
                &0 < sqrt(mfd_scalar atlas (g s0) (q k))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  USE_THEN "N" (MP_TAC o SPECL [`k:num`; `(phi:num->B->B) k y`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + N <= k:num` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    UNDISCH_TAC `abs(sqrt(mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)) *
                     mfd_dist (top,atlas) (g s0) (q k) ((phi:num->B->B) k y) -
                     mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl y) < &1` THEN
    EXPAND_TAC "A" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

(* X0.6e Completeness for all s <= 0 and monotonicity of R in time on the   *)
(* X0 limit.                                                                 *)

let P2BX0_XLIM_COMPLETE = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
     mfd_complete (top',atlas') (g'(&0))
     ==> !s. s <= &0 ==> mfd_complete (top',atlas') (g' s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L6")
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th))
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0_XLIM_SEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s = &0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "L6" (MP_TAC o REWRITE_RULE[LIM_FLOW_COMPLETE_BACK_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `g':real->B->real^3^3`; `s - &1`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2BX0_XLIM_MONO = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s))
     ==> !s1 s2 y. s1 <= s2 /\ s2 <= &0 /\ y IN topspace top'
                   ==> mfd_scalar atlas' (g' s1) y <= mfd_scalar atlas' (g' s2) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L5") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "comp"))))) THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y:B`] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
  REWRITE_TAC[p2b_ancflow0] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`;
                 `s1:real`; `y:B`; `&1`] P2BX0_XLIM_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; USE_THEN "comp" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "near")) THEN
  SUBGOAL_THEN `s1 <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (sv,lab) ->
    USE_THEN "L5" (MP_TAC o REWRITE_RULE[LIM_CURV_STATEMENT]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`; `q:num->B`;
      `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
      `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; sv; `y:B`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(LABEL_TAC lab o CONJUNCT1)])
    [`s1:real`,"lim1"; `s2:real`,"lim2"] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\k. mfd_scalar (rfs_vatlas ((\k:num. rfs_flow_view (top,atlas) {s | s < b}
                                              (g:real->B->real^3^3)) k)
                      ((\k:num. (s0:real)) k + s1 / (\k. mfd_scalar atlas (g s0) ((q:num->B) k)) k))
                    (rfs_vmetric ((\k:num. rfs_flow_view (top,atlas) {s | s < b} g) k)
                      ((\k:num. s0) k + s1 / (\k. mfd_scalar atlas (g s0) (q k)) k))
                    ((phi:num->B->B) k y) / (\k. mfd_scalar atlas (g s0) (q k)) k`;
    `\k. mfd_scalar (rfs_vatlas ((\k:num. rfs_flow_view (top,atlas) {s | s < b}
                                              (g:real->B->real^3^3)) k)
                      ((\k:num. (s0:real)) k + s2 / (\k. mfd_scalar atlas (g s0) ((q:num->B) k)) k))
                    (rfs_vmetric ((\k:num. rfs_flow_view (top,atlas) {s | s < b} g) k)
                      ((\k:num. s0) k + s2 / (\k. mfd_scalar atlas (g s0) (q k)) k))
                    ((phi:num->B->B) k y) / (\k. mfd_scalar atlas (g s0) (q k)) k`] THEN
  CONJ_TAC THENL [USE_THEN "lim1" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "lim2" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "near" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)` THEN
  SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
   [EXPAND_TAC "Qk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`; `Qk:real`; `s1:real`]
                P2BX0_XVIEW) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`; `Qk:real`; `s2:real`]
                P2BX0_XVIEW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC P2BX0_SCALAR_MONO THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `s0 + s1 / Qk - &1`; `b:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)`)
          (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> s0 + x <= s0 + y`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    MAP_EVERY X_GEN_TAC [`s:real`; `dR:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(phi:num->B->B) k y`; `dR:real`] o
      check (fun th -> can (term_match []
        `!s x dR. s < b /\ x IN topspace top /\
                  ((\t. mfd_scalar atlas ((g:real->B->real^3^3) t) x) has_real_derivative dR)
                  (atreal s) ==> &0 <= dR`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC]]);;

(* X0.6f |Rm| <= 2, dR/ds >= 0 and kappa-noncollapsing on the X0 limit.    *)

let P2BX0_XLIM_RM = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
     (!y. y IN topspace top' ==> mfd_scalar atlas' (g'(&0)) y <= &4)
     ==> !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r4")))))) THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0_XLIM_SEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sec") THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`]
                P2BX0_XLIM_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "mono") THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s. s <= &0 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) s`; `y:B`] P2BX0_RM_NORM_LE_HALF_SCALAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  USE_THEN "mono" (MP_TAC o SPECL [`s:real`; `&0`; `y:B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  USE_THEN "r4" (MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BX0_XLIM_DRDS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_CURV_STATEMENT w w /\ LIM_DIST_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     connected_space top' /\ (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s))
     ==> !s y dR. s <= &0 /\ y IN topspace top' /\
                  ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                  ==> &0 <= dR`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "mono" o MATCH_MP P2BX0_XLIM_MONO) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:B`; `dR:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. mfd_scalar atlas' ((g':real->B->real^3^3) t) (y:B)`; `s:real`; `dR:real`]
                P2BX0_MONO_DERIV_NONNEG) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`] THEN STRIP_TAC THEN
  USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BX0_XLIM_KNC = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q:num->B) top' atlas' g' xl W phi.
     LIM_KNC_STATEMENT w w /\
     p2bx0_xlim kappa (top,atlas) g b s0 q (top',atlas') g' xl W phi /\
     (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s))
     ==> !r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s <= &0} g') kappa r0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L3") (CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th)) (LABEL_TAC "comp"))) THEN
  X_GEN_TAC `r0:real` THEN
  UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
  REWRITE_TAC[p2b_ancflow0] THEN STRIP_TAC THEN
  USE_THEN "L3" (MP_TAC o REWRITE_RULE[LIM_KNC_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`; `q:num->B`;
    `\k:num. (s0:real)`; `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q:num->B) k)`;
    `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `kappa:real`;
    `r0:real`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

(* X0.11b The X0 limit exists: ANCIENT_COMPACT on the shifted flows g(s0+t) *)
(* at the points q1 k with Q k = R(s0,q1 k) (hypotheses by                  *)
(* P2BX0_ANCIENT_HYPS), restriction of every per-Tl limit to the joinable   *)
(* class of xl (P2CO_P3_FLOW_RESTRICT, connected), one p2c_flow_limit_with  *)
(* on s <= 0 (P2BX0_FLOW_LIMIT_DIAG), and conversion to the X0 views        *)
(* rfs_flow_view of g on the times s < b, at times s0 + s/Q k               *)
(* (P2BX0_FLOW_LIMIT_WITH_CONG).                                            *)

let P2BX0_ANC_BASIC = prove
 (`!kappa top atlas (g:real->B->real^3^3) b.
     p2b_ancflow0 kappa (top,atlas) g b
     ==> hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
         (!s. s < b ==> riemannian_metric atlas (g s)) /\
         (!s. s < b ==> mfd_complete (top,atlas) (g s)) /\
         (!s x u v. s < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g s) x u v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b - &1` o check (fun th ->
      can (term_match [] `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)`)
          (concl th))) THEN
    REWRITE_TAC[REAL_ARITH `b - &1 < b`] THEN MESON_TAC[ricci_flow_on];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s - &1` o check (fun th ->
      can (term_match [] `!a. a < b ==> ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)`)
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let P2BX0_LIMIT_EXISTS = prove
 (`!(w:B->bool) kappa top atlas (g:real->B->real^3^3) b s0 (q1:num->B).
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\
     (!k. q1 k IN topspace top /\ &0 < mfd_scalar atlas (g s0) (q1 k)) /\
     (!A. ?N. !k y. N <= k /\
                    y IN mfd_ball (top,atlas) (g s0) (q1 k)
                                  (A * inv(sqrt(mfd_scalar atlas (g s0) (q1 k))))
                    ==> mfd_scalar atlas (g s0) y <= &4 * mfd_scalar atlas (g s0) (q1 k))
     ==> ?sub (top':B topology) atlas' g' xl W phi.
            p3_subseq sub /\
            p2bx0_xlim kappa (top,atlas) g b s0 (q1 o sub) (top',atlas') g' xl W phi /\
            connected_space top' /\
            (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
            mfd_complete (top',atlas') (g'(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AC") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "q1") (LABEL_TAC "balls"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`; `q1:num->B`] P2BX0_ANCIENT_HYPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "hyps")] THEN
  USE_THEN "AC" (MP_TAC o REWRITE_RULE[P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\k:num. (top:B topology)`; `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
    `\k:num t. (g:real->B->real^3^3) (s0 + t)`; `q1:num->B`;
    `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)`]) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [USE_THEN "hyps" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top1:B topology`
    (X_CHOOSE_THEN `atlas1:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g1:real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lim1")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem1") (LABEL_TAC "comp1"))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top1:B topology) (atlas1:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "lim1" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; p3_flow_limit] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the shifted views are regular *)
  SUBGOAL_THEN
   `!s. ~(topspace(rfs_vtop (rfs_flow_view (top,atlas) {t | t <= &0}
                                  (\t. (g:real->B->real^3^3) (s0 + t))) s) = {})
              ==> smooth_manifold_atlas
                    (rfs_vtop (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s)
                    (rfs_vatlas (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s) /\
                  riemannian_metric
                    (rfs_vatlas (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s)
                    (rfs_vmetric (rfs_flow_view (top,atlas) {t | t <= &0} (\t. g (s0 + t))) s)`
  (LABEL_TAC "reg") THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `{t:real | t <= &0}`;
                   `\t. (g:real->B->real^3^3) (s0 + t)`] P2BX0_VIEW_REGULAR) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* restriction of every per-Tl limit to the joinable class of xl *)
  SUBGOAL_THEN
   `(!Tl. &0 < Tl
          ==> p3_flow_limit
                (\k:num. rfs_flow_view (top,atlas) {t | t <= &0}
                                       (\t. (g:real->B->real^3^3) (s0 + t)))
                ((q1:num->B) o (sub1:num->num)) (\k. &0)
                ((\k. mfd_scalar atlas (g s0) (q1 k)) o sub1)
                (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                 restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
                (\s. restrict_metric atlas1 {y | mfd_joinable (top1,atlas1) xl y}
                                     ((g1:real->B->real^3^3) s)) xl Tl) /\
    connected_space
      (subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y})`
  (CONJUNCTS_THEN2 (LABEL_TAC "rlim") ASSUME_TAC) THENL
   [CONJ_TAC THENL [X_GEN_TAC `Tl:real` THEN DISCH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0} (\t. (g:real->B->real^3^3) (s0 + t))`;
      `(q1:num->B) o (sub1:num->num)`; `\k:num. &0`;
      `(\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)`;
      `top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`; `g1:real->B->real^3^3`; `xl:B`]
     P2CO_P3_FLOW_RESTRICT) THENL
     [DISCH_THEN(MP_TAC o SPEC `Tl:real`); DISCH_THEN(MP_TAC o SPEC `&1`)] THEN
    REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [CONJ_TAC THENL
        [FIRST [USE_THEN "reg" ACCEPT_TAC; GEN_TAC THEN USE_THEN "reg" ACCEPT_TAC];
         USE_THEN "lim1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_01]];
       SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < &0
        ==> rfs_flow_upto
              (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
               restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y}) a (&0)
              (\s. restrict_metric atlas1
                     {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                     ((g1:real->B->real^3^3) s))`
  (LABEL_TAC "upto") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "rlim" (MP_TAC o SPEC `&1 - a`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p3_flow_limit] THEN
    DISCH_THEN(MP_TAC o el 5 o CONJUNCTS) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s <= &0
        ==> riemannian_metric
              (restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
              (restrict_metric atlas1
                 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                 ((g1:real->B->real^3^3) s))`
  (LABEL_TAC "riem") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
      `s - &1`; `&0`;
      `\s. restrict_metric atlas1
             {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
             ((g1:real->B->real^3^3) s)`;
      `s:real`] P2AP_UPTO_RIEM) THEN
    REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_complete (subtopology top1 {y | mfd_joinable (top1,atlas1) xl y},
                  restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1) xl y})
                 (restrict_metric atlas1
                    {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
                    ((g1:real->B->real^3^3) (&0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CO_CLASS_COMPLETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* one limit on s <= 0 *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0} (\t. (g:real->B->real^3^3) (s0 + t))`;
    `(q1:num->B) o (sub1:num->num)`; `\k:num. &0`;
    `(\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)`;
    `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`] P2BX0_FLOW_LIMIT_DIAG) THEN
  ANTS_TAC THENL [USE_THEN "rlim" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `W:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "with"))))) THEN
  (* to the X0 views *)
  MP_TAC(ISPECL
   [`\k:num. rfs_flow_view (top,atlas) {t | t <= &0} (\t. (g:real->B->real^3^3) (s0 + t))`;
    `\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
    `((q1:num->B) o (sub1:num->num)) o (sub2:num->num)`;
    `(\k:num. &0) o (sub2:num->num)`; `\k:num. (s0:real)`;
    `((\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)) o
     (sub2:num->num)`;
    `{s:real | s <= &0}`;
    `subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`] P2BX0_FLOW_LIMIT_WITH_CONG) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "with" ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN DISCH_TAC THEN
    ABBREV_TAC `Qk = mfd_scalar atlas ((g:real->B->real^3^3) s0)
                                ((q1:num->B) ((sub1:num->num) ((sub2:num->num) k)))` THEN
    SUBGOAL_THEN `&0 < Qk` ASSUME_TAC THENL
     [EXPAND_TAC "Qk" THEN USE_THEN "q1" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `b:real`; `s0:real`; `Qk:real`; `s:real`]
                  P2BX0_XVIEW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[P2BX0_VIEW_FACTS; IN_ELIM_THM; REAL_ADD_LID] THEN
    SUBGOAL_THEN `s / Qk <= &0` (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q1:num->B) k)) o (sub1:num->num)) o
    (sub2:num->num) =
    (\k. mfd_scalar atlas (g s0) (q1 (sub1 (sub2 k))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(sub1:num->num) o (sub2:num->num)` THEN
  MAP_EVERY EXISTS_TAC
   [`subtopology top1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas atlas1 {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}`;
    `\s. restrict_metric atlas1
           {y | mfd_joinable (top1,atlas1:((B->bool)#(B->real^3))->bool) xl y}
           ((g1:real->B->real^3^3) s)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2bx0_xlim; o_ASSOC] THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "upto" ACCEPT_TAC;
    ASM_REWRITE_TAC[]]);;

(* X0.11c Assembly: MT Prop 9.11 split at infinity (P2B_SPLIT_AT_INFINITY) *)
(* from the LIM statements and ANCIENT_COMPACT.  Picked points q0 at time   *)
(* s0 (P2BX0_PICKED_POINTS), almost-line pairs along them                   *)
(* (P2BX0_ALMOST_PAIRS), the X0 limit (P2BX0_LIMIT_EXISTS), its properties  *)
(* (X0.6), a line at time 0 (P2BX0_LIMIT_PAIRS, P2BX0_LINE_FROM_PAIRS), the *)
(* splitting field (CMP_R3_SPLIT) and its time invariance                   *)
(* (P2BX0_TIME_INVARIANCE).                                                 *)

let p2bx0_xargs =
  [`w:B->bool`; `kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
   `g:real->B->real^3^3`; `b:real`; `s0:real`;
   `((q0:num->B) o (suba:num->num)) o (subb:num->num)`;
   `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
   `xl:B`; `W:num->B->bool`; `phi:num->B->B`];;

let P2BX0_SPLIT_BODY = prove
 (`!w:B->bool.
     LIM_DIST_STATEMENT w w /\ LIM_BALL_STATEMENT w w /\ LIM_KNC_STATEMENT w w /\
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
     ==> P2B_SPLIT_AT_INFINITY_STATEMENT w`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "L2")
    (CONJUNCTS_THEN2 (LABEL_TAC "L3") (CONJUNCTS_THEN2 (LABEL_TAC "L5")
    (CONJUNCTS_THEN2 (LABEL_TAC "L6") (LABEL_TAC "AC")))))) THEN
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `p:B`; `pp:num->B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ppin") (LABEL_TAC "ppdiv"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  (* facts at time s0 *)
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0) /\
                mfd_complete (top,atlas) (g s0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> &0 <= mfd_sectional atlas ((g:real->B->real^3^3) s0) y u v`
  (LABEL_TAC "sec0") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN topspace top ==> &0 <= mfd_scalar atlas ((g:real->B->real^3^3) s0) y`
  (LABEL_TAC "Rnn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s0`; `y:B`;
                   `mfd_rm_norm atlas ((g:real->B->real^3^3) s0) y`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN USE_THEN "sec0" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal)
                  (mfd_scalar atlas ((g:real->B->real^3^3) s0))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x. x IN topspace top /\ &0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) x`
  ASSUME_TAC THENL
   [USE_THEN "ppdiv" (MP_TAC o SPEC `&0`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN EXISTS_TAC `(pp:num->B) N` THEN
    USE_THEN "ppin" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= r /\ ~(r = &0) ==> &0 < r`) THEN CONJ_TAC THENL
     [USE_THEN "Rnn" MATCH_MP_TAC THEN USE_THEN "ppin" (fun th -> REWRITE_TAC[th]);
      DISCH_TAC THEN
      UNDISCH_TAC `&0 < mfd_scalar atlas ((g:real->B->real^3^3) s0) ((pp:num->B) N) *
                        mfd_dist (top,atlas) (g s0) p (pp N) pow 2` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL]];
    ALL_TAC] THEN
  (* picked points *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `pp:num->B`] P2BX0_PICKED_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:num->B` (CONJUNCTS_THEN2 (LABEL_TAC "q0")
    (CONJUNCTS_THEN2 (LABEL_TAC "q0div") (LABEL_TAC "q0balls")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `q0:num->B`] P2BX0_DIST_DIVERGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    DISCH_THEN(LABEL_TAC "q0far")] THEN
  (* almost-line pairs along q0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `p:B`; `q0:num->B`;
                 `\n. mfd_scalar atlas ((g:real->B->real^3^3) s0) ((q0:num->B) n)`]
                P2BX0_ALMOST_PAIRS) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `suba:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pairs"))) THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) k` (LABEL_TAC "subage") THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_GE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the X0 limit along q0 o suba *)
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `b:real`;
                 `s0:real`; `(q0:num->B) o (suba:num->num)`] P2BX0_LIMIT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subage" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `subb:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g':real->B->real^3^3`
    (X_CHOOSE_THEN `xl:B` (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xlim")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "comp0")))))))))))) THEN
  USE_THEN "xlim" (fun th -> STRIP_ASSUME_TAC(MATCH_MP P2BX0_XLIM_BASIC th) THEN
                             STRIP_ASSUME_TAC(REWRITE_RULE[p2bx0_xlim] th)) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3) (&0))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!s. s <= &0 ==> riemannian_metric atlas' ((g':real->B->real^3^3) s)`) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k <= (suba:num->num) ((subb:num->num) k)` (LABEL_TAC "subge") THENL
   [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `k:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    USE_THEN "subage" (MP_TAC o SPEC `(subb:num->num) k`) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. ?N. !k y. N <= k /\
                  y IN mfd_ball (top,atlas) ((g:real->B->real^3^3) s0)
                         ((((q0:num->B) o (suba:num->num)) o (subb:num->num)) k)
                         (A * inv(sqrt(mfd_scalar atlas (g s0) (((q0 o suba) o subb) k))))
                  ==> mfd_scalar atlas (g s0) y <=
                      &4 * mfd_scalar atlas (g s0) (((q0 o suba) o subb) k)`
  (LABEL_TAC "qballs") THENL
   [REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
    USE_THEN "q0balls" (MP_TAC o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "subge" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* X0.6: the limit properties *)
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_COMPLETE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "compall")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_SEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "secl")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_R1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "r1")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_R4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "r4")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_RM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rm")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_DRDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "drds")] THEN
  MP_TAC(ISPECL p2bx0_xargs P2BX0_XLIM_KNC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "knc")] THEN
  (* X0.8: exact pairs at time 0, then a line *)
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?a b. a IN topspace top' /\ b IN topspace top' /\
                  mfd_dist (top',atlas') ((g':real->B->real^3^3) (&0)) xl a = A /\
                  mfd_dist (top',atlas') (g' (&0)) xl b = A /\
                  mfd_dist (top',atlas') (g' (&0)) a b = &2 * A`
  (LABEL_TAC "lpairs") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`w:B->bool`; `w:B->bool`;
      `\k:num. rfs_flow_view (top,atlas) {s | s < b} (g:real->B->real^3^3)`;
      `((q0:num->B) o (suba:num->num)) o (subb:num->num)`; `\k:num. (s0:real)`;
      `\k. mfd_scalar atlas ((g:real->B->real^3^3) s0)
                      ((((q0:num->B) o (suba:num->num)) o (subb:num->num)) k)`;
      `{s:real | s <= &0}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
      `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `&0`; `A:real`]
     P2BX0_LIMIT_PAIRS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2BX0_VIEW_FACTS; IN_ELIM_THM; o_THM] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pairs" (MP_TAC o SPECL [`A:real`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `(subb:num->num) k`) THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `subb:num->num` P2BX0_SUBSEQ_GE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3) (&0)`; `xl:B`] P2BX0_LINE_FROM_PAIRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real->B` (LABEL_TAC "line")) THEN
  (* X0.9: the splitting field at time 0 *)
  MP_TAC(SPEC `w:B->bool` CMP_R3_SPLIT) THEN REWRITE_TAC[CMP_R3_SPLIT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                             `(g':real->B->real^3^3) (&0)`; `lam:real->B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "secl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `X:B->real^3` STRIP_ASSUME_TAC)) THEN
  (* X0.10: time invariance *)
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `X:B->real^3`; `xl:B`; `&2`] P2BX0_TIME_INVARIANCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the conclusion *)
  MAP_EVERY EXISTS_TAC
   [`(suba:num->num) o (subb:num->num)`; `((q0:num->B) o (suba:num->num)) o (subb:num->num)`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->B`; `X:B->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BX0_SUBSEQ_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN GEN_TAC THEN USE_THEN "q0" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `M:real` THEN
    USE_THEN "q0div" (MP_TAC o SPEC `M:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "subge" (MP_TAC o SPEC `k:num`) THEN UNDISCH_TAC `N <= k:num` THEN ARITH_TAC;
    EXISTS_TAC `&2` THEN USE_THEN "rm" ACCEPT_TAC]);;

(* The route form: ANCIENT_COMPACT is the antecedent of the route           *)
(* statement.  The five LIM inputs are proved in pc_lim_dist (LIM_DIST,     *)
(* LIM_BALL), pc_lim_back (LIM_FLOW_COMPLETE_BACK), pc_lim_vol (LIM_KNC)    *)
(* and pc_lim_curv (LIM_CURV).                                              *)

let P2B_SPLIT_AT_INFINITY_ROUTE_LIM = prove
 (`!w:B->bool.
     LIM_DIST_STATEMENT w w /\ LIM_BALL_STATEMENT w w /\ LIM_KNC_STATEMENT w w /\
     LIM_CURV_STATEMENT w w /\ LIM_FLOW_COMPLETE_BACK_STATEMENT w
     ==> P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT w`,
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT] THEN MESON_TAC[P2BX0_SPLIT_BODY]);;

