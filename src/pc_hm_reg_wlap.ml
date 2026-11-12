(* ========================================================================= *)
(* The weak Laplace system of a continuous weakly harmonic map and its       *)
(* C^(1,al) regularity (part of the harmonic map regularity layer            *)
(* pc_hm_regularity).  Testing the Euler-Lagrange equation (HMRC_EL_W120)    *)
(* with phi G(u)^(-1) e_j gives Lap u_j = f_j weakly with f_j quadratic in   *)
(* the weak gradient; f_j is locally bounded (HMRC_WD_LOCBOUND), and         *)
(* WAN_LOGPOT_C1A_QUANT gives C^1 with Hoelder partials.                     *)
(* ========================================================================= *)

needs "src/pc_hm_reg_c1a.ml";;
needs "src/pc_wan_pot2c.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The coefficient fields and the pointwise algebra.  hmrw_gj G j p is the   *)
(* j-th column of G(p)^(-1); hmrw_fq S G j p q is the density of the         *)
(* right-hand side (twice f_j for one partial q).                            *)
(* ------------------------------------------------------------------------- *)

let hmrw_gj = new_definition
 `hmrw_gj (G:real^K->real^K^K) j (p:real^K) = matrix_inv(G p) ** basis j`;;

let hmrw_fq = new_definition
 `hmrw_fq (S:real^K->bool) (G:real^K->real^K^K) j (p:real^K) (q:real^K) =
    hmrm_eld S G p q (hmrw_gj G j p) (vec 0) +
    &2 * (frechet_derivative (hmrw_gj G j) (at p) q dot (G p ** q))`;;

let HMRW_GJ_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d j.
     cm_target S G d /\ 1 <= j /\ j <= dimindex(:K)
     ==> smooth_map_on (:real^K) (hmrw_gj G j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  SUBGOAL_THEN `smooth_map_on (:real^K)
                  ((vectorize:real^K^K->real^(K,K)finite_prod) o
                   (\z. matrix_inv((G:real^K->real^K^K) z)))` MP_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [UNDISCH_TAC `metric_field (:real^K) (G:real^K->real^K^K)` THEN SIMP_TAC[metric_field];
      X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `z:real^K`] LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[IN_UNIV]];
    ALL_TAC] THEN
  SIMP_TAC[LRG_SMOOTH_VECTORIZE; OPEN_UNIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^K)`; `hmrw_gj (G:real^K->real^K^K) j`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[hmrw_gj; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let HMRW_GJ_DOT = prove
 (`!S (G:real^K->real^K^K) d j p q.
     cm_target S G d /\ 1 <= j /\ j <= dimindex(:K)
     ==> hmrw_gj G j p dot (G p ** q) = q$j`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `p:real^K`] LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `p:real^K`;
                 `hmrw_gj (G:real^K->real^K^K) j p`; `q:real^K`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[hmrw_gj; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID; DOT_BASIS]);;

let HMRW_ELD_CMUL = prove
 (`!S (G:real^K->real^K^K) d p q h c.
     cm_target S G d /\ p IN cm_tube S d
     ==> hmrm_eld S G p q (c % h) (vec 0) = c * hmrm_eld S G p q h (vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point (S:real^K->bool)) (at y))) differentiable (at (p:real^K)) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) differentiable (at p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[hmrm_eld; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID; MATRIX_VECTOR_MUL_RMUL] THEN
  ASM_SIMP_TAC[LRG_MDERIV_LINEAR; MATRIX_VECTOR_LMUL; DOT_LMUL; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

let HMRW_ELD_TEST = prove
 (`!S (G:real^K->real^K^K) d j p q a c.
     cm_target S G d /\ p IN S /\ 1 <= j /\ j <= dimindex(:K) /\
     jacobian (closest_point S) (at p) ** q = q
     ==> hmrm_eld S G p q (c % hmrw_gj G j p)
                  (a % hmrw_gj G j p + c % frechet_derivative (hmrw_gj G j) (at p) q) =
         c * hmrw_fq S G j p q + &2 * a * q$j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                 `c % hmrw_gj (G:real^K->real^K^K) j p`;
                 `a % hmrw_gj (G:real^K->real^K^K) j p +
                  c % frechet_derivative (hmrw_gj G j) (at p) q`] HMRC_ELD_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                 `a % hmrw_gj (G:real^K->real^K^K) j p +
                  c % frechet_derivative (hmrw_gj G j) (at p) q`] HMRC_ELD_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                 `hmrw_gj (G:real^K->real^K^K) j p`; `c:real`] HMRW_ELD_CMUL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[hmrw_fq; DOT_LADD; DOT_LMUL] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `j:num`; `p:real^K`;
                 `q:real^K`] HMRW_GJ_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* Uniform bounds for the derivative of a smooth map on a compact set. *)

let HMRW_LINEAR_BASIS_BOUND = prove
 (`!(f:real^M->real^N) x.
     linear f ==> norm(f x) <= sum(1..dimindex(:M)) (\j. norm(f(basis j))) * norm x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[COMPONENT_LE_NORM; NORM_POS_LE]);;

let HMRW_FD_BOUND = prove
 (`!(g:real^M->real^N) O K.
     open O /\ smooth_map_on O g /\ compact K /\ K SUBSET O
     ==> ?B. &0 <= B /\ !z v. z IN K ==> norm(frechet_derivative g (at z) v) <= B * norm v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. (\y. frechet_derivative (g:real^M->real^N) (at y) (basis j)) continuous_on O`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`0`; `O:real^M->bool`; `g:real^M->real^N`]
                  CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
    REWRITE_TAC[continuously_differentiable] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bounded (IMAGE (\z. lift(sum(1..dimindex(:M))
                     (\j. norm(frechet_derivative (g:real^M->real^N) (at z) (basis j))))) K)`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `v:real^M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^M->real^N) (at z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^M->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M))
                (\j. norm(frechet_derivative (g:real^M->real^N) (at z) (basis j))) *
              norm(v:real^M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HMRW_LINEAR_BASIS_BOUND THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
  REAL_ARITH_TAC);;

(* The density hmrw_fq is quadratic in q, uniformly for p in S. *)

let HMRW_FQ_BOUND = prove
 (`!S (G:real^K->real^K^K) d j.
     cm_target S G d /\ 1 <= j /\ j <= dimindex(:K)
     ==> ?C. &0 <= C /\ !p q. p IN S ==> abs(hmrw_fq S G j p q) <= C * norm q pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` (X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRC_ELD_BOUND) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam1:real` (X_CHOOSE_THEN `CJ:real`
    (X_CHOOSE_THEN `CG:real` (X_CHOOSE_THEN `C2:real` (X_CHOOSE_THEN `C3:real`
    (X_CHOOSE_THEN `C4:real` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) (hmrw_gj (G:real^K->real^K^K) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRW_GJ_SMOOTH THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hmrw_gj (G:real^K->real^K^K) j`; `(:real^K)`; `S:real^K->bool`]
    HMRW_FD_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?Bg. &0 <= Bg /\ !p. p IN S ==> norm(hmrw_gj (G:real^K->real^K^K) j p) <= Bg`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hmrw_gj (G:real^K->real^K^K) j`; `S:real^K->bool`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^K)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `Ca * Bg + &2 * Bd * Lam1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^K`; `q:real^K`] THEN DISCH_TAC THEN
  REWRITE_TAC[hmrw_fq] THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= x * n /\ abs b <= y * n
                            ==> abs(a + &2 * b) <= (x + &2 * y) * n`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^K`; `q:real^K`; `hmrw_gj (G:real^K->real^K^K) j p`;
                                  `vec 0:real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Cb:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(frechet_derivative (hmrw_gj (G:real^K->real^K^K) j) (at p) q) *
              norm((G:real^K->real^K^K) p ** q)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Bd * norm(q:real^K)) * (Lam1 * norm q)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Bounds for test functions and the truncated coefficient field (bounded    *)
(* derivative, for WAN_CHAIN_W12).                                           *)
(* ========================================================================= *)

let HMRW_TEST_BOUNDED = prove
 (`!(s:real^N->bool) phi. wan_test s phi ==> ?B. &0 <= B /\ !x. abs(phi x) <= B`,
  REWRITE_TAC[wan_test] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((phi:real^N->real) x)`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN k` THEN
  ASM_SIMP_TAC[REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC);;

let HMRW_TEST_DPART_BOUNDED = prove
 (`!(s:real^N->bool) phi.
     wan_test s phi
     ==> ?B. &0 <= B /\ !x i. 1 <= i /\ i <= dimindex(:N) ==> abs(wan_dpart i phi x) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. ?Bi. &0 <= Bi /\ !x. abs(wan_dpart i (phi:real^N->real) x) <= Bi`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMRW_TEST_BOUNDED THEN EXISTS_TAC `s:real^N->bool` THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC WAN_TEST_DPART_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Bi:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (Bi:num->real)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Bi:num->real) i` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Bi:num->real`; `sum(1..dimindex(:N)) (Bi:num->real)`; `1..dimindex(:N)`]
    SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[IN_NUMSEG]]);;

let HMRW_TRUNC_G = prove
 (`!S (G:real^K->real^K^K) d j R.
     cm_target S G d /\ 1 <= j /\ j <= dimindex(:K) /\ &0 < R
     ==> ?V:real^K->real^K.
           smooth_map_on (:real^K) V /\
           (?Bd. !y. onorm(frechet_derivative V (at y)) <= Bd) /\
           (?Mv. !y. norm(V y) <= Mv) /\
           (!y. norm y < R
                ==> V y = hmrw_gj G j y /\
                    frechet_derivative V (at y) = frechet_derivative (hmrw_gj G j) (at y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `R:real` HMRC_TRUNC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Tr:real^K->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) (hmrw_gj (G:real^K->real^K^K) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRW_GJ_SMOOTH THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hmrw_gj (G:real^K->real^K^K) j`; `(:real^K)`;
                 `cball(vec 0:real^K,&2 * R)`] HMRW_FD_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?Mg. !y. y IN cball(vec 0:real^K,&2 * R)
                         ==> norm(hmrw_gj (G:real^K->real^K^K) j y) <= Mg`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hmrw_gj (G:real^K->real^K^K) j`; `cball(vec 0:real^K,&2 * R)`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^K)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (Tr:real^K->real^K) y IN cball(vec 0,&2 * R)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. frechet_derivative (hmrw_gj (G:real^K->real^K^K) j o (Tr:real^K->real^K)) (at y) =
        frechet_derivative (hmrw_gj G j) (at (Tr y)) o frechet_derivative Tr (at y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  EXISTS_TAC `hmrw_gj (G:real^K->real^K^K) j o (Tr:real^K->real^K)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
    EXISTS_TAC `Bd * L` THEN X_GEN_TAC `y:real^K` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `frechet_derivative (hmrw_gj (G:real^K->real^K^K) j)
                    (at ((Tr:real^K->real^K) y)) o
                  frechet_derivative (Tr:real^K->real^K) (at y)` ONORM) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `v:real^K` THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Bd * norm(frechet_derivative (Tr:real^K->real^K) (at y) v)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `Mg:real` THEN ASM_SIMP_TAC[o_THM];
    X_GEN_TAC `y:real^K` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN
    REWRITE_TAC[o_DEF; ETA_AX]]);;

(* ========================================================================= *)
(* The test maps phi % G(u)^(-1) e_j on a disc: bounded continuous W_0^(1,2) *)
(* maps with the expected weak partials.                                     *)
(* ========================================================================= *)

let HMRW_TEST_W = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r j phi.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
     1 <= j /\ j <= dimindex(:K) /\ wan_test (ball(a,r)) phi
     ==> ?V:real^K->real^K.
           (!x. x IN ball(a,r) ==> V(u x) = hmrw_gj G j (u x)) /\
           wan_w120 (ball(a,r)) (\x. phi x % V(u x)) /\
           (\x. phi x % V(u x)) continuous_on ball(a,r) /\
           (?M. !x. x IN ball(a,r) ==> norm(phi x % V(u x)) <= M) /\
           !i. 1 <= i /\ i <= 2
               ==> negligible
                     {x | x IN ball(a,r) /\
                          ~(wan_wd (ball(a,r)) i (\x. phi x % V(u x)) x =
                            wan_dpart i phi x % hmrw_gj G j (u x) +
                            phi x % frechet_derivative (hmrw_gj G j) (at (u x))
                                      (wan_wd (ball(a,r)) i u x))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `ball(a:real^2,r) SUBSET s /\ wan_w12 (ball(a,r)) (u:real^2->real^K) /\
                (u:real^2->real^K) continuous_on ball(a,r)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(a:real^2,r) SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Ru. &0 <= Ru /\ !x. x IN cball(a,r) ==> norm((u:real^2->real^K) x) <= Ru`
  (X_CHOOSE_THEN `Ru:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ub"))) THENL
   [MP_TAC(ISPECL [`u:real^2->real^K`; `cball(a:real^2,r)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `j:num`; `Ru + &1`]
    HMRW_TRUNC_G) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^K->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Bd:real`) (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Mv:real`)
      (LABEL_TAC "loc"))))) THEN
  EXISTS_TAC `V:real^K->real^K` THEN
  SUBGOAL_THEN
   `!x. x IN ball(a:real^2,r)
        ==> (V:real^K->real^K)((u:real^2->real^K) x) = hmrw_gj G j (u x) /\
            frechet_derivative V (at (u x)) = frechet_derivative (hmrw_gj G j) (at (u x))`
  (LABEL_TAC "locu") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN USE_THEN "loc" MATCH_MP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `n <= Ru ==> n < Ru + &1`) THEN USE_THEN "ub" MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  (* the chain rule for V o u *)
  MP_TAC(REWRITE_RULE[WAN_CHAIN_W12_STATEMENT] (ISPECL [`(:2)`; `(:K)`; `(:K)`] WAN_CHAIN_W12)) THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `u:real^2->real^K`; `V:real^K->real^K`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `smooth_map_on (:real^K) (V:real^K->real^K)` THEN SIMP_TAC[smooth_map_on];
      EXISTS_TAC `Bd:real` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "chw"))] THEN
  (* the product with phi *)
  FIRST_ASSUM(X_CHOOSE_THEN `Bp:real` STRIP_ASSUME_TAC o MATCH_MP HMRW_TEST_BOUNDED) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Bq:real` STRIP_ASSUME_TAC o MATCH_MP HMRW_TEST_DPART_BOUNDED) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(REWRITE_RULE[WAN_MUL_W12_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_MUL_W12)) THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `\x. (V:real^K->real^K)((u:real^2->real^K) x)`;
                             `phi:real^2->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `Bp:real` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `Bq:real` THEN ASM_SIMP_TAC[DIMINDEX_2]];
    REWRITE_TAC[DIMINDEX_2] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mw"))] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "locu" (fun th -> MP_TAC(MP (SPEC `x:real^2` th)
                                         (ASSUME `(x:real^2) IN ball(a,r)`))) THEN
    SIMP_TAC[];
    MATCH_MP_TAC WAN_W12_COMPACT_SUPPORT_W120 THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      SUBGOAL_THEN `(\x. (V:real^K->real^K)((u:real^2->real^K) x)) = V o u` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]];
    EXISTS_TAC `Bp * Mv` THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `{x | x IN ball(a,r) /\
         ~(wan_wd (ball(a,r)) i (\x. (phi:real^2->real) x % (V:real^K->real^K)((u:real^2->real^K) x)) x =
           wan_dpart i phi x % V(u x) + phi x % wan_wd (ball(a,r)) i (\x. V(u x)) x)} UNION
    {x | x IN ball(a,r) /\
         ~(wan_wd (ball(a,r)) i (\x. (V:real^K->real^K)((u:real^2->real^K) x)) x =
           frechet_derivative V (at (u x)) (wan_wd (ball(a,r)) i u x))}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
    ASM_SIMP_TAC[OPEN_BALL; DIMINDEX_2];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
  ASM_CASES_TAC `(x:real^2) IN ball(a,r)` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "locu" (fun th -> MP_TAC(MP (SPEC `x:real^2` th)
                                       (ASSUME `(x:real^2) IN ball(a,r)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THEN MESON_TAC[]);;

(* One partial derivative: the Euler-Lagrange density of the test map splits *)
(* a.e. into phi times the density hmrw_fq plus twice dphi times (D_i u)_j.  *)

let HMRW_EL_TERM = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r j phi (V:real^K->real^K) M i.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
     1 <= j /\ j <= dimindex(:K) /\ wan_test (ball(a,r)) phi /\
     (!x. x IN ball(a,r) ==> V(u x) = hmrw_gj G j (u x)) /\
     wan_w120 (ball(a,r)) (\x. phi x % V(u x)) /\
     (\x. phi x % V(u x)) continuous_on ball(a,r) /\
     (!x. x IN ball(a,r) ==> norm(phi x % V(u x)) <= M) /\
     negligible {x | x IN ball(a,r) /\
                     ~(wan_wd (ball(a,r)) i (\x. phi x % V(u x)) x =
                       wan_dpart i phi x % hmrw_gj G j (u x) +
                       phi x % frechet_derivative (hmrw_gj G j) (at (u x))
                                 (wan_wd (ball(a,r)) i u x))} /\
     1 <= i /\ i <= 2
     ==> (\x. lift(wan_dpart i phi x * (wan_wd (ball(a,r)) i u x)$j)) integrable_on
         ball(a,r) /\
         (\x. lift(phi x * hmrw_fq S G j (u x) (wan_wd (ball(a,r)) i u x))) integrable_on
         ball(a,r) /\
         drop(integral (ball(a,r))
           (\x. lift(hmrm_eld S G (u x) (wan_wd (ball(a,r)) i u x) (phi x % V(u x))
                       (wan_wd (ball(a,r)) i (\x. phi x % V(u x)) x)))) =
         drop(integral (ball(a,r))
           (\x. lift(phi x * hmrw_fq S G j (u x) (wan_wd (ball(a,r)) i u x)))) +
         &2 * drop(integral (ball(a,r))
                (\x. lift(wan_dpart i phi x * (wan_wd (ball(a,r)) i u x)$j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `ball(a:real^2,r) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (u:real^2->real^K) /\
                (u:real^2->real^K) continuous_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> (u:real^2->real^K) x IN S) /\
                wan_w12 (ball(a,r)) (\x. (phi:real^2->real) x % (V:real^K->real^K)(u x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      ASM_MESON_TAC[wan_w120]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_wd (ball(a,r)) i (u:real^2->real^K) IN lspace (ball(a,r)) (&2) /\
    wan_wd (ball(a,r)) i (\x. (phi:real^2->real) x % (V:real^K->real^K)((u:real^2->real^K) x))
      IN lspace (ball(a,r)) (&2)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]; ALL_TAC] THEN
  ABBREV_TAC `q = wan_wd (ball(a,r)) i (u:real^2->real^K)` THEN
  ABBREV_TAC `kk = wan_wd (ball(a,r)) i
                     (\x. (phi:real^2->real) x % (V:real^K->real^K)((u:real^2->real^K) x))` THEN
  (* integrability of the Euler-Lagrange density *)
  SUBGOAL_THEN
   `(\x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                ((phi:real^2->real) x % (V:real^K->real^K)(u x)) ((kk:real^2->real^K) x)))
    integrable_on ball(a,r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                   `u:real^2->real^K`;
                   `\x. (phi:real^2->real) x % (V:real^K->real^K)((u:real^2->real^K) x)`;
                   `q:real^2->real^K`; `kk:real^2->real^K`; `M:real`] HMRC_ELD_INTEGRABLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* integrability of dphi times the j-th component *)
  SUBGOAL_THEN
   `(\x. lift(wan_dpart i (phi:real^2->real) x * ((q:real^2->real^K) x)$j)) integrable_on
    ball(a,r)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(wan_dpart i (phi:real^2->real) x * ((q:real^2->real^K) x)$j)) =
      (\x. lift((wan_dpart i phi x % basis j) dot q x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; DOT_LMUL] THEN ASM_SIMP_TAC[DOT_BASIS]; ALL_TAC] THEN
    MATCH_MP_TAC WAN_LSPACE2_DOT_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HMR_LSPACE_CBALL THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; o_DEF] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `phi:real^2->real`; `i:num`] WAN_TEST_DPART_OPEN) THEN
    ASM_REWRITE_TAC[wan_test] THEN MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  (* the pointwise identity off a null set *)
  SUBGOAL_THEN
   `?N. negligible N /\
        !x. x IN ball(a,r) DIFF N
            ==> hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                  ((phi:real^2->real) x % (V:real^K->real^K)(u x)) ((kk:real^2->real^K) x) =
                phi x * hmrw_fq S G j (u x) (q x) + &2 * (wan_dpart i phi x * (q x)$j)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `{x | x IN ball(a,r) /\
           ~((kk:real^2->real^K) x =
             wan_dpart i (phi:real^2->real) x % hmrw_gj G j ((u:real^2->real^K) x) +
             phi x % frechet_derivative (hmrw_gj G j) (at (u x)) ((q:real^2->real^K) x))} UNION
      {x | x IN ball(a,r) /\
           ~(jacobian (closest_point S) (at ((u:real^2->real^K) x)) ** (q:real^2->real^K) x =
             q x)}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        EXPAND_TAC "q" THEN MATCH_MP_TAC HMRM_WD_TANGENT THEN
        MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN
        ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL]];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(kk:real^2->real^K) x =
      wan_dpart i (phi:real^2->real) x % hmrw_gj G j ((u:real^2->real^K) x) +
      phi x % frechet_derivative (hmrw_gj G j) (at (u x)) ((q:real^2->real^K) x) /\
      jacobian (closest_point S) (at ((u:real^2->real^K) x)) ** (q:real^2->real^K) x = q x /\
      (V:real^K->real^K)(u x) = hmrw_gj G j (u x)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMRW_ELD_TEST THEN EXISTS_TAC `d:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((phi:real^2->real) x * hmrw_fq S G j ((u:real^2->real^K) x)
                ((q:real^2->real^K) x))) integrable_on ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
    EXISTS_TAC
     `\x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                 ((phi:real^2->real) x % (V:real^K->real^K)(u x)) ((kk:real^2->real^K) x)) -
          &2 % lift(wan_dpart i phi x * (q x)$j)` THEN
    EXISTS_TAC `N:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_SUB] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_SIMP_TAC[INTEGRABLE_CMUL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral (ball(a,r))
      (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) ((q:real^2->real^K) x)
                  ((phi:real^2->real) x % (V:real^K->real^K)(u x)) ((kk:real^2->real^K) x))) =
    integral (ball(a,r))
      (\x. lift(phi x * hmrw_fq S G j (u x) (q x)) + &2 % lift(wan_dpart i phi x * (q x)$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `N:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD];
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL]]);;

(* The weak Laplace system on a disc. *)

let HMRW_WEAK_SYSTEM = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r j phi.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
     1 <= j /\ j <= dimindex(:K) /\ wan_test (ball(a,r)) phi
     ==> (!i. 1 <= i /\ i <= 2
              ==> (\x. lift(phi x * hmrw_fq S G j (u x) (wan_wd (ball(a,r)) i u x)))
                  integrable_on ball(a,r)) /\
         sum(1..2) (\i. drop(integral (ball(a,r))
            (\x. lift(wan_dpart i phi x * (wan_wd (ball(a,r)) i u x)$j)))) =
         --(inv(&2) * sum(1..2) (\i. drop(integral (ball(a,r))
            (\x. lift(phi x * hmrw_fq S G j (u x) (wan_wd (ball(a,r)) i u x))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `a:real^2`; `r:real`; `j:num`; `phi:real^2->real`]
    HMRW_TEST_W) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^K->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `M:real`) (LABEL_TAC "ae")))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `ball(a:real^2,r)`;
                 `\x. (phi:real^2->real) x % (V:real^K->real^K)((u:real^2->real^K) x)`; `M:real`]
    HMRC_EL_W120) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN ASM_SIMP_TAC[CLOSURE_BALL]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift((phi:real^2->real) x *
                      hmrw_fq S G j ((u:real^2->real^K) x) (wan_wd (ball(a,r)) i u x)))
            integrable_on ball(a,r) /\
            drop(integral (ball(a,r))
              (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd (ball(a,r)) i u x)
                          ((phi:real^2->real) x % (V:real^K->real^K)(u x))
                          (wan_wd (ball(a,r)) i (\x. phi x % V(u x)) x)))) =
            drop(integral (ball(a,r))
              (\x. lift(phi x * hmrw_fq S G j (u x) (wan_wd (ball(a,r)) i u x)))) +
            &2 * drop(integral (ball(a,r))
                   (\x. lift(wan_dpart i phi x * (wan_wd (ball(a,r)) i u x)$j)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `u:real^2->real^K`; `a:real^2`; `r:real`; `j:num`; `phi:real^2->real`;
                   `V:real^K->real^K`; `M:real`; `i:num`] HMRW_EL_TERM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ae" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
   `sum(1..2) (\i. drop(integral (ball(a,r))
      (\x. lift(hmrm_eld S G ((u:real^2->real^K) x) (wan_wd (ball(a,r)) i u x)
                  ((phi:real^2->real) x % (V:real^K->real^K)(u x))
                  (wan_wd (ball(a,r)) i (\x. phi x % V(u x)) x))))) = &0` THEN
  REWRITE_TAC[SUM_2] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Components of weak derivatives, the measurability of the right-hand side, *)
(* and the weak Laplace equation of each component in the form of            *)
(* WAN_LOGPOT_C1A_QUANT.                                                     *)
(* ========================================================================= *)

let HMRW_WD_COMPONENT = prove
 (`!(B:real^2->bool) (u:real^2->real^K) i j.
     open B /\ bounded B /\ wan_w12 B u /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= dimindex(:K)
     ==> wan_w12 B (\x. lift(u x$j)) /\
         negligible {x | x IN B /\ ~(wan_wd B i (\x. lift(u x$j)) x = lift(wan_wd B i u x$j))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[WAN_CHAIN_W12_STATEMENT] (ISPECL [`(:2)`; `(:K)`; `(:1)`] WAN_CHAIN_W12)) THEN
  DISCH_THEN(MP_TAC o SPECL [`B:real^2->bool`; `u:real^2->real^K`; `\y:real^K. lift(y$j)`]) THEN
  SUBGOAL_THEN `!y:real^K. frechet_derivative (\y:real^K. lift(y$j)) (at y) = (\y. lift(y$j))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; LINEAR_LIFT_COMPONENT];
      EXISTS_TAC `&1` THEN REPEAT GEN_TAC THEN
      MP_TAC(ISPEC `\y:real^K. lift(y$j)` ONORM) THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC[NORM_LIFT; REAL_MUL_LID; COMPONENT_LE_NORM]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_SIMP_TAC[DIMINDEX_2]);;

let HMRW_CD_COMPONENTWISE = prove
 (`!n s (f:real^M->real^N).
     open s /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> continuously_differentiable n s (\x. lift(f x$j)))
     ==> continuously_differentiable n s f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = (\x:real^M. vsum(1..dimindex(:N))
                        (\j. drop(lift((f:real^M->real^N) x$j)) % basis j))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; BASIS_EXPANSION]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`; `\x. lift((f:real^M->real^N) x$j)`;
                 `\x:real^M. basis j:real^N`] CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST]);;

let HMRW_FQ_MEAS = prove
 (`!S (G:real^K->real^K^K) d (B:real^2->bool) (u:real^2->real^K) (q:real^2->real^K) j.
     cm_target S G d /\ open B /\ 1 <= j /\ j <= dimindex(:K) /\
     u continuous_on B /\ (!x. x IN B ==> u x IN S) /\ q IN lspace B (&2)
     ==> (\x. lift(hmrw_fq S G j (u x) (q x))) measurable_on B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  SUBGOAL_THEN `(q:real^2->real^K) measurable_on B` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_LSPACE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) (hmrw_gj (G:real^K->real^K^K) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRW_GJ_SMOOTH THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Bg. !p. p IN S ==> norm(hmrw_gj (G:real^K->real^K^K) j p) <= Bg`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hmrw_gj (G:real^K->real^K^K) j`; `S:real^K->bool`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^K)` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. hmrw_gj (G:real^K->real^K^K) j ((u:real^2->real^K) x)) continuous_on B`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. hmrw_gj (G:real^K->real^K^K) j ((u:real^2->real^K) x)) =
                  hmrw_gj G j o u` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[hmrw_fq; LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `B:real^2->bool`;
                   `u:real^2->real^K`;
                   `\x. hmrw_gj (G:real^K->real^K^K) j ((u:real^2->real^K) x)`;
                   `q:real^2->real^K`; `\x:real^2. vec 0:real^K`; `Bg:real`]
      HMRC_ELD_INTEGRABLE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LSPACE_0; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_CMUL THEN MATCH_MP_TAC HMC_MEAS_DOT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMRC_FD_APPLY_MEAS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^2->bool`;
                 `\x. (vectorize:real^K^K->real^(K,K)finite_prod)
                        ((G:real^K->real^K^K)((u:real^2->real^K) x))`;
                 `q:real^2->real^K`] HMC_MEAS_MATMUL) THEN
  REWRITE_TAC[MATRIFY_VECTORIZE; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
  SUBGOAL_THEN `(\x. (vectorize:real^K^K->real^(K,K)finite_prod)
                       ((G:real^K->real^K^K)((u:real^2->real^K) x))) =
                (vectorize o G) o u` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]);;

(* The component u_j solves Lap u_j = f weakly, for any f equal a.e. to     *)
(* half the sum of the densities.                                           *)

let HMRW_LAP_FORM = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r j (f:real^2->real) N.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
     1 <= j /\ j <= dimindex(:K) /\ negligible N /\
     (!x. x IN ball(a,r) DIFF N
          ==> f x = inv(&2) * sum(1..2) (\i. hmrw_fq S G j (u x) (wan_wd (ball(a,r)) i u x)))
     ==> wan_w12 (ball(a,r)) (\x. lift(u x$j)) /\
         !phi. wan_test (ball(a,r)) phi
               ==> vsum(1..2) (\i. integral (ball(a,r))
                      (\x. wan_dpart i phi x % wan_wd (ball(a,r)) i (\y. lift(u y$j)) x)) =
                   --(integral (ball(a,r)) (\x. lift(f x * phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (u:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_w12 (ball(a,r)) (\x. lift((u:real^2->real^K) x$j)) /\
            negligible {x | x IN ball(a,r) /\
                            ~(wan_wd (ball(a,r)) i (\x. lift(u x$j)) x =
                              lift(wan_wd (ball(a,r)) i u x$j))}`
  (LABEL_TAC "cp") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC HMRW_WD_COMPONENT THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "cp" (MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^2->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `a:real^2`; `r:real`; `j:num`; `phi:real^2->real`]
    HMRW_WEAK_SYSTEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum(1..2) (\i. integral (ball(a,r))
      (\x. wan_dpart i phi x % wan_wd (ball(a,r)) i (\y. lift((u:real^2->real^K) y$j)) x)) =
    lift(sum(1..2) (\i. drop(integral (ball(a,r))
      (\x. lift(wan_dpart i phi x * (wan_wd (ball(a,r)) i u x)$j)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_DROP] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN ball(a,r) /\
                     ~(wan_wd (ball(a,r)) i (\x. lift((u:real^2->real^K) x$j)) x =
                       lift(wan_wd (ball(a,r)) i u x$j))}` THEN
    CONJ_TAC THENL
     [USE_THEN "cp" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `wan_wd (ball(a,r)) i (\x. lift((u:real^2->real^K) x$j)) x =
                  lift(wan_wd (ball(a,r)) i u x$j)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[LIFT_CMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (ball(a,r)) (\x. lift((f:real^2->real) x * phi x)) =
    lift(inv(&2) * sum(1..2) (\i. drop(integral (ball(a,r))
      (\x. lift(phi x * hmrw_fq S G j ((u:real^2->real^K) x) (wan_wd (ball(a,r)) i u x))))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral (ball(a,r))
        (\x. inv(&2) %
             (lift(phi x * hmrw_fq S G j ((u:real^2->real^K) x) (wan_wd (ball(a,r)) 1 u x)) +
              lift(phi x * hmrw_fq S G j (u x) (wan_wd (ball(a,r)) 2 u x))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `N:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[SUM_2] THEN
      REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRABLE_ADD; INTEGRAL_ADD; SUM_2; ARITH] THEN
      REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_DROP]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_NEG]);;

(* ========================================================================= *)
(* Bounded weak gradient on a disc, the log-potential estimate for each      *)
(* component, and C^(1,1/2) regularity.                                      *)
(* ========================================================================= *)

let HMRW_LOCAL_SETUP = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ a IN s
     ==> ?r M0 N. &0 < r /\ cball(a,r) SUBSET s /\ negligible N /\
                  !i x. 1 <= i /\ i <= 2 /\ x IN ball(a,r) /\ ~(x IN N)
                        ==> norm(wan_wd (ball(a,r)) i u x) <= M0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  MP_TAC(SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMRC_WD_LOCBOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`s:real^2->bool`; `u:real^2->real^K`; `a:real^2`; `1`] th) THEN
    MP_TAC(SPECL [`s:real^2->bool`; `u:real^2->real^K`; `a:real^2`; `2`] th)) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `M2:real`
    (X_CHOOSE_THEN `N2:real^2->bool` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `M1:real`
    (X_CHOOSE_THEN `N1:real^2->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `r = min r1 r2 / &2` THEN
  SUBGOAL_THEN `&0 < r /\ r < r1 /\ r < r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,r) SUBSET s /\ cball(a:real^2,r) SUBSET s /\
                ball(a:real^2,r) SUBSET ball(a,r1) /\ ball(a:real^2,r) SUBSET ball(a,r2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^2,r1)` THEN
      ASM_SIMP_TAC[SUBSET_BALL; REAL_LT_IMP_LE];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^2,r1)` THEN
      ASM_REWRITE_TAC[SUBSET_BALLS; DIST_REFL; REAL_ADD_LID];
      ASM_SIMP_TAC[SUBSET_BALL; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[SUBSET_BALL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`r:real`; `abs M1 + abs M2`;
    `N1 UNION N2 UNION
     {x | x IN ball(a,r) /\
          ~(wan_wd (ball(a,r)) 1 (u:real^2->real^K) x = wan_wd s 1 u x)} UNION
     {x | x IN ball(a,r) /\
          ~(wan_wd (ball(a,r)) 2 (u:real^2->real^K) x = wan_wd s 2 u x)}`] THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
   [CONJ_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `ball(a:real^2,r)`; `u:real^2->real^K`]
      WAN_WD_RESTRICT) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2; ARITH] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((x:real^2) IN N1) /\ ~((x:real^2) IN N2) /\
                wan_wd (ball(a,r)) 1 (u:real^2->real^K) x = wan_wd s 1 u x /\
                wan_wd (ball(a,r)) 2 (u:real^2->real^K) x = wan_wd s 2 u x`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `wan_wd (ball(a,r)) 1 (u:real^2->real^K) x = wan_wd s 1 u x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `n <= M1 ==> n <= abs M1 + abs M2`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `M1:real`)) (concl th) && is_forall (concl th))) THEN
    ASM SET_TAC[];
    SUBGOAL_THEN `wan_wd (ball(a,r)) 2 (u:real^2->real^K) x = wan_wd s 2 u x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `n <= M2 ==> n <= abs M1 + abs M2`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `M2:real`)) (concl th) && is_forall (concl th))) THEN
    ASM SET_TAC[]]);;

(* One component: the log-potential estimate on the half disc. *)

let HMRW_COMP_LOGPOT = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r M0 N j.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
     negligible N /\
     (!i x. 1 <= i /\ i <= 2 /\ x IN ball(a,r) /\ ~(x IN N)
            ==> norm(wan_wd (ball(a,r)) i u x) <= M0) /\
     1 <= j /\ j <= dimindex(:K)
     ==> ?w L. continuously_differentiable 1 (ball(a,r / &2)) (\x. lift(w x)) /\
               (!x. x IN ball(a,r / &2) ==> u x$j = w x) /\
               (!x y. x IN ball(a,r / &2) /\ y IN ball(a,r / &2)
                      ==> norm(wan_grad w x - wan_grad w y) <= L * norm(x - y) rpow (&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `ball(a:real^2,r) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> (u:real^2->real^K) x IN S) /\
                wan_w12 (ball(a,r)) (u:real^2->real^K)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?Ru. !x. x IN cball(a,r) ==> norm((u:real^2->real^K) x) <= Ru`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^2->real^K`; `cball(a:real^2,r)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `j:num`] HMRW_FQ_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cq:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `f = \x. if x IN N then &0
            else inv(&2) * sum(1..2) (\i. hmrw_fq S G j ((u:real^2->real^K) x)
                                            (wan_wd (ball(a,r)) i u x))` THEN
  SUBGOAL_THEN
   `!x. x IN ball(a,r) DIFF N
        ==> (f:real^2->real) x =
            inv(&2) * sum(1..2) (\i. hmrw_fq S G j ((u:real^2->real^K) x)
                                      (wan_wd (ball(a,r)) i u x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `a:real^2`; `r:real`; `j:num`; `f:real^2->real`;
                 `N:real^2->bool`] HMRW_LAP_FORM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the bound for f *)
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> abs((f:real^2->real) x) <= Cq * M0 pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_2; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                      ==> abs(hmrw_fq S G j ((u:real^2->real^K) x)
                                (wan_wd (ball(a,r)) i u x)) <= Cq * M0 pow 2`
    (fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Cq * norm(wan_wd (ball(a,r)) i (u:real^2->real^K) x) pow 2` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `M0:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* measurability of f *)
  SUBGOAL_THEN `(\x. lift((f:real^2->real) x)) measurable_on ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
    EXISTS_TAC `\x. inv(&2) %
                    (lift(hmrw_fq S G j ((u:real^2->real^K) x) (wan_wd (ball(a,r)) 1 u x)) +
                     lift(hmrw_fq S G j (u x) (wan_wd (ball(a,r)) 2 u x)))` THEN
    EXISTS_TAC `N:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[SUM_2] THEN
      REWRITE_TAC[LIFT_CMUL; LIFT_ADD];
      MATCH_MP_TAC MEASURABLE_ON_CMUL THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC HMRW_FQ_MEAS THEN EXISTS_TAC `d:real` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[OPEN_BALL; WAN_WD_WORKS; DIMINDEX_2; ARITH]];
    ALL_TAC] THEN
  (* the log-potential estimate *)
  MP_TAC(SPEC `&1 / &2` (REWRITE_RULE[WAN_LOGPOT_C1A_QUANT_STATEMENT] WAN_LOGPOT_C1A_QUANT)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL
    [`a:real^2`; `r:real`; `\x. (u:real^2->real^K) x$j`; `f:real^2->real`; `Cq * M0 pow 2`;
     `Ru:real`]))) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((u:real^2->real^K) x)` THEN
    REWRITE_TAC[COMPONENT_LE_NORM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real^2->real` THEN
  EXISTS_TAC `(C * (Cq * M0 pow 2) * r pow 2 + C * Ru) / r rpow (&3 / &2)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,r / &2)`; `\x. lift((u:real^2->real^K) x$j)`;
                   `\x. lift((w:real^2->real) x)`] WAN_CONT_AE_EQ_OPEN) THEN
    REWRITE_TAC[LIFT_EQ; OPEN_BALL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
    can (find_term (fun t -> t = `wan_grad (w:real^2->real)`)) (concl th) &&
    can (find_term (fun t -> t = `rpow`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < r rpow (&3 / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ABBREV_TAC `Q = norm(wan_grad (w:real^2->real) x - wan_grad w y)` THEN
  ABBREV_TAC `Z = norm(x - y:real^2) rpow (&1 / &2)` THEN
  ABBREV_TAC `rr = r rpow (&3 / &2)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `((C * (Cq * M0 pow 2) * r pow 2 + C * Ru) / rr) * Z =
                ((C * (Cq * M0 pow 2) * r pow 2 + C * Ru) * Z) / rr` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN POP_ASSUM MP_TAC THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* C^(1,1/2) regularity of continuous weakly harmonic maps (HMRW_C1A).       *)
(* ========================================================================= *)

let HMRW_PD_COMP_GRAD = prove
 (`!s (u:real^2->real^K) (w:real^2->real) x i j.
     open s /\ x IN s /\ u differentiable (at x) /\ (!y. y IN s ==> u y$j = w y) /\
     1 <= i /\ i <= 2
     ==> (partial_derivative i u x)$j = (wan_grad w x)$i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `j:num`; `u:real^2->real^K`; `x:real^2`]
    PARTIAL_DERIVATIVE_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(partial_derivative i (u:real^2->real^K) x)$j =
                drop(partial_derivative i (\x. lift(u x$j)) x)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (\x. lift((u:real^2->real^K) x$j)) x =
                partial_derivative i (\x. lift((w:real^2->real) x)) x` SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[wan_grad; LAMBDA_BETA; DIMINDEX_2] THEN
  REWRITE_TAC[wan_dpart; partial_derivative]);;

let HMRW_C1A = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ a IN s
     ==> ?r L. &0 < r /\ ball(a,r) SUBSET s /\
               continuously_differentiable 1 (ball(a,r)) u /\
               !i x y. 1 <= i /\ i <= 2 /\ x IN ball(a,r) /\ y IN ball(a,r)
                       ==> norm(partial_derivative i u x - partial_derivative i u y)
                           <= L * norm(x - y) rpow (&1 / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `a:real^2`] HMRW_LOCAL_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `M0:real`
    (X_CHOOSE_THEN `N:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!j. ?w L. 1 <= j /\ j <= dimindex(:K)
              ==> continuously_differentiable 1 (ball(a,r / &2)) (\x. lift(w x)) /\
                  (!x. x IN ball(a,r / &2) ==> (u:real^2->real^K) x$j = w x) /\
                  (!x y. x IN ball(a,r / &2) /\ y IN ball(a,r / &2)
                         ==> norm(wan_grad w x - wan_grad w y) <=
                             L * norm(x - y) rpow (&1 / &2))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `1 <= j /\ j <= dimindex(:K)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `u:real^2->real^K`; `a:real^2`; `r:real`; `M0:real`; `N:real^2->bool`;
                   `j:num`] HMRW_COMP_LOGPOT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->real^2->real` (X_CHOOSE_THEN `LL:num->real`
    (LABEL_TAC "wj"))) THEN
  SUBGOAL_THEN `ball(a:real^2,r / &2) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^2,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a:real^2,r)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a,r / &2)) (u:real^2->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRW_CD_COMPONENTWISE THEN REWRITE_TAC[OPEN_BALL] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC `\x. lift((W:num->real^2->real) j x)` THEN
    USE_THEN "wj" (fun th -> MP_TAC(MP (SPEC `j:num` th)
                    (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:K)`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r / &2`; `sum(1..dimindex(:K)) (LL:num->real)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN ball(a,r / &2) ==> (u:real^2->real^K) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`0`; `ball(a:real^2,r / &2)`; `u:real^2->real^K`]
      CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K))
                (\j. abs((partial_derivative i (u:real^2->real^K) x -
                          partial_derivative i u y)$j))` THEN
  REWRITE_TAC[NORM_LE_L1; GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
  USE_THEN "wj" (fun th -> MP_TAC(MP (SPEC `j:num` th)
                  (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:K)`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(partial_derivative i (u:real^2->real^K) x)$j =
                (wan_grad ((W:num->real^2->real) j) x)$i /\
                (partial_derivative i u y)$j = (wan_grad (W j) y)$i`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMRW_PD_COMP_GRAD THEN
    EXISTS_TAC `ball(a:real^2,r / &2)` THEN ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(wan_grad ((W:num->real^2->real) j) x - wan_grad (W j) y)` THEN
  REWRITE_TAC[COMPONENT_LE_NORM] THEN ASM_SIMP_TAC[]);;

(* For a C^1 map the right-hand side can be written with classical partials. *)

let HMRW_LAP_C1 = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a r j.
     cm_target S G d /\ open s /\ cm_wharmonic S G s u /\ &0 < r /\ cball(a,r) SUBSET s /\
     continuously_differentiable 1 (ball(a,r)) u /\ 1 <= j /\ j <= dimindex(:K)
     ==> wan_w12 (ball(a,r)) (\x. lift(u x$j)) /\
         !phi. wan_test (ball(a,r)) phi
               ==> vsum(1..2) (\i. integral (ball(a,r))
                      (\x. wan_dpart i phi x % wan_wd (ball(a,r)) i (\y. lift(u y$j)) x)) =
                   --(integral (ball(a,r))
                        (\x. lift((inv(&2) * sum(1..2) (\i. hmrw_fq S G j (u x)
                                                 (partial_derivative i u x))) * phi x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_wharmonic]) THEN
  SUBGOAL_THEN `wan_w12 (ball(a,r)) (u:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(a:real^2,r)` THEN ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> negligible {x | x IN ball(a,r) /\
                            ~(wan_wd (ball(a,r)) i (u:real^2->real^K) x =
                              partial_derivative i u x)}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real^K`; `i:num`] WAN_WPD_C1) THEN
    ASM_REWRITE_TAC[OPEN_BALL; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRW_LAP_FORM THEN
  MAP_EVERY EXISTS_TAC
   [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
    `{x | x IN ball(a,r) /\
          ~(wan_wd (ball(a,r)) 1 (u:real^2->real^K) x = partial_derivative 1 u x)} UNION
     {x | x IN ball(a,r) /\
          ~(wan_wd (ball(a,r)) 2 (u:real^2->real^K) x = partial_derivative 2 u x)}`] THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION_EQ; ARITH] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd (ball(a,r)) 1 (u:real^2->real^K) x = partial_derivative 1 u x /\
                wan_wd (ball(a,r)) 2 (u:real^2->real^K) x = partial_derivative 2 u x`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUM_2]);;

