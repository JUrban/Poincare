(* ========================================================================= *)
(* Unit pc_hm_reg_cov (a unit of the harmonic map regularity chain of        *)
(* pc_hm_regularity): smooth harmonic maps into an embedded target cm_target *)
(* S G d, in the ambient picture.  The tangent projection P = jacobian       *)
(* (closest_point S) and its algebra on S (symmetric, idempotent, P G        *)
(* (I - P) = 0); the strong Euler-Lagrange equation P(u)(Lap u + sum_i       *)
(* Gam(u)(d_i u, d_i u)) = 0 of a smooth cm_harmonic map (from HMC_EL_TEST   *)
(* of pc_hm_convexity by integration by parts and constant test directions); *)
(* the explicit system                                                       *)
(*   Lap u = sum_i hmr_bq S G u (d_i u) (d_i u);                            *)
(* the Bochner inequality for the Euclidean energy density; the covariant   *)
(* derivative along u.                                                       *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;
needs "src/pc_hm_convexity.ml";;
needs "src/pc_cm_lemma122.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The tangent projection of cm_target.                                     *)
(* hmr_tp S z = jacobian (closest_point S) (at z), hmr_dtp its derivative   *)
(* along a; on S: symmetric, idempotent, P G (I - P) = 0 = (I - P) G P, G   *)
(* maps tangent vectors to tangent vectors, and P G P w = 0 forces P w = 0. *)
(* ========================================================================= *)

let hmr_tp = new_definition
 `hmr_tp (S:real^K->bool) (z:real^K) = jacobian (closest_point S) (at z)`;;

let hmr_dtp = new_definition
 `hmr_dtp (S:real^K->bool) (z:real^K) (a:real^K) =
    mderiv (\y. jacobian (closest_point S) (at y)) z a`;;

let HMR_METRIC_FIELD = prove
 (`!S (G:real^K->real^K^K) d. cm_target S G d ==> metric_field (:real^K) G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_target] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[metric_field; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `y:real^K` THEN X_GEN_TAC `v:real^K` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `lam * norm(v:real^K) pow 2` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]);;

let HMR_SYM_DOT = prove
 (`!(P:real^N^N) x y. transp P = P ==> (P ** x) dot y = x dot (P ** y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
    [GSYM th]) THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]);;

let HMR_SYM_IDEM_DOT = prove
 (`!(P:real^N^N) x y.
     transp P = P /\ P ** P = P ==> (P ** x) dot (P ** y) = (P ** x) dot y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[HMR_SYM_DOT; MATRIX_VECTOR_MUL_ASSOC]);;

let HMR_PROJ_ALG = prove
 (`!(P:real^N^N) (M:real^N^N).
     transp P = P /\ P ** P = P /\ transp M = M /\
     (!u v. (P ** u) dot (M ** ((mat 1 - P) ** v)) = &0)
     ==> P ** M ** (mat 1 - P) = mat 0 /\ (mat 1 - P) ** M ** P = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:real^N^N) ** (M:real^N^N) ** (mat 1 - P) = mat 0` ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_MUL_LZERO] THEN X_GEN_TAC `v:real^N` THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM DOT_EQ_0] THEN
    ASM_SIMP_TAC[HMR_SYM_IDEM_DOT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `transp:real^N^N->real^N^N`) THEN
  ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_MATRIX_SUB; TRANSP_MAT; MATRIX_MUL_ASSOC]);;

let HMR_TP_ALG = prove
 (`!S (G:real^K->real^K^K) d z.
     cm_target S G d /\ z IN S
     ==> transp(hmr_tp S z) = hmr_tp S z /\
         hmr_tp S z ** hmr_tp S z = hmr_tp S z /\
         hmr_tp S z ** G z ** (mat 1 - hmr_tp S z) = mat 0 /\
         (mat 1 - hmr_tp S z) ** G z ** hmr_tp S z = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `transp(hmr_tp S z) = hmr_tp S z /\
                hmr_tp S z ** hmr_tp S z = hmr_tp (S:real^K->bool) z`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[hmr_tp] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMR_PROJ_ALG THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[hmr_tp] THEN ASM_SIMP_TAC[]);;

let HMR_TP_TANGENT = prove
 (`!S (G:real^K->real^K^K) d z t.
     cm_target S G d /\ z IN S /\ hmr_tp S z ** t = t
     ==> hmr_tp S z ** (G z ** t) = G z ** t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `z:real^K`] HMR_TP_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(mat 1 - hmr_tp S z) ** ((G:real^K->real^K^K) z ** (t:real^K)) = vec 0` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO];
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN MESON_TAC[]]);;

let HMR_TP_INJ = prove
 (`!S (G:real^K->real^K^K) d z w.
     cm_target S G d /\ z IN S /\ hmr_tp S z ** (G z ** (hmr_tp S z ** w)) = vec 0
     ==> hmr_tp S z ** w = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `z:real^K`] HMR_TP_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  SUBGOAL_THEN `(hmr_tp S z ** (w:real^K)) dot
                ((G:real^K->real^K^K) z ** (hmr_tp S z ** w)) = &0` MP_TAC THENL
   [ASM_SIMP_TAC[HMR_SYM_DOT; DOT_RZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `lam * norm(hmr_tp S z ** (w:real^K)) pow 2 <= &0` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < lam * norm(hmr_tp S z ** (w:real^K)) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Smoothness and partial derivatives of ambient compositions along a planar *)
(* map w: matrix fields M(w z) applied to vector fields, scalar products     *)
(* with a constant vector, Christoffel terms (generic forms of the           *)
(* dimension-3 lemmas CML_MATVEC_SMOOTH and CML_CHR_SMOOTH of                *)
(* pc_cm_lemma122).                                                          *)
(* ========================================================================= *)

let HMR_MFIELD_COMPOSE = prove
 (`!V W (M:real^N->real^N^N) (w:real^2->real^N).
     open V /\ open W /\ smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
     smooth_map_on W w /\ (!z. z IN W ==> w z IN V)
     ==> smooth_map_on W ((vectorize:real^N^N->real^(N,N)finite_prod) o (\z. M(w z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vectorize:real^N^N->real^(N,N)finite_prod) o
                (\z. (M:real^N->real^N^N)((w:real^2->real^N) z)) =
                ((vectorize:real^N^N->real^(N,N)finite_prod) o M) o w` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

let HMR_MATVEC_SMOOTH = prove
 (`!V W (M:real^N->real^N^N) (w:real^2->real^N) (Y:real^2->real^N).
     open V /\ open W /\ smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
     smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\ smooth_map_on W Y
     ==> smooth_map_on W (\z. M(w z) ** Y z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `\z. (M:real^N->real^N^N)((w:real^2->real^N) z)`;
                 `Y:real^2->real^N`] LRG_SMOOTH_MATVEC) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HMR_MFIELD_COMPOSE THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HMR_PD_MATVEC = prove
 (`!V W (M:real^N->real^N^N) (w:real^2->real^N) (Y:real^2->real^N) z i.
     open V /\ open W /\ smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
     smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\ smooth_map_on W Y /\ z IN W
     ==> partial_derivative i (\z. M(w z) ** Y z) z =
         mderiv M (w z) (partial_derivative i w z) ** Y z +
         M(w z) ** partial_derivative i Y z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o M) differentiable at
                ((w:real^2->real^N) z) /\ w differentiable at z /\
                (Y:real^2->real^N) differentiable at z`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `V:real^N->bool`; EXISTS_TAC `W:real^2->bool`; EXISTS_TAC `W:real^2->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (M:real^N->real^N^N)((w:real^2->real^N) z)`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o M)
                    (at ((w:real^2->real^N) z)) o frechet_derivative w (at z)`;
                 `Y:real^2->real^N`; `frechet_derivative (Y:real^2->real^N) (at z)`;
                 `z:real^2`] LRG_HAS_DERIVATIVE_MATVEC) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(vectorize:real^N^N->real^(N,N)finite_prod) o
                    (\z. (M:real^N->real^N^N)((w:real^2->real^N) z)) =
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o M) o w` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[partial_derivative] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[o_THM; mderiv]);;

let HMR_D_DOT_CONST = prove
 (`!W (Y:real^2->real^N) c z i.
     open W /\ smooth_map_on W Y /\ z IN W
     ==> cml_d i (\x. c dot Y x) z = c dot partial_derivative i Y z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d] THEN
  SUBGOAL_THEN `(\x. lift(c dot (Y:real^2->real^N) x)) = (\y. lift(c dot y)) o Y`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^2->real^N) differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\y:real^N. lift(c dot y))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Y:real^2->real^N`; `\y:real^N. lift(c dot y)`;
                 `frechet_derivative (Y:real^2->real^N) (at z)`; `\y:real^N. lift(c dot y)`;
                 `z:real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[partial_derivative] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[o_THM; LIFT_DROP]);;

(* Matrix fields differentiated along a planar map.                          *)

let HMR_MDERIV_SMOOTH = prove
 (`!V W (M:real^N->real^N^N) (w:real^2->real^N) (A:real^2->real^N).
     open V /\ open W /\ smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o M) /\
     smooth_map_on W w /\ (!z. z IN W ==> w z IN V) /\ smooth_map_on W A
     ==> smooth_map_on W ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (\z. mderiv M (w z) (A z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. vsum(1..dimindex(:N))
                    (\k. drop(lift((A:real^2->real^N) z$k)) %
                         partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               (M:real^N->real^N^N)) ((w:real^2->real^N) z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; mderiv; VECTORIZE_MATRIFY; LIFT_DROP; partial_derivative] THEN
    SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o M) differentiable
                  at ((w:real^2->real^N) z)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT] THEN
  SUBGOAL_THEN
   `(\z. partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o
                               (M:real^N->real^N^N)) ((w:real^2->real^N) z)) =
    partial_derivative k ((vectorize:real^N^N->real^(N,N)finite_prod) o M) o w`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

let HMR_PD_SCALAR_CMUL = prove
 (`!(psi:real^2->real) (c:real^N) y i.
     (\x. lift(psi x)) differentiable at y
     ==> partial_derivative i (\x. psi x % c) y = cml_d i psi y % c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d] THEN
  SUBGOAL_THEN `(\x. (psi:real^2->real) x % (c:real^N)) =
                (\t:real^1. drop t % c) o (\x. lift(psi x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `linear (\t:real^1. drop t % (c:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((psi:real^2->real) x)`; `\t:real^1. drop t % (c:real^N)`;
                 `frechet_derivative (\x. lift((psi:real^2->real) x)) (at y)`;
                 `\t:real^1. drop t % (c:real^N)`; `y:real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[partial_derivative] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[o_THM]);;

(* ========================================================================= *)
(* The Euler-Lagrange density of a smooth map v into S tested in a constant  *)
(* direction c with a scalar bump psi:                                       *)
(*   hmc_ld(psi c) = 2 d_i(psi c.G(v) d_i v) + psi hmr_elci S G v c i,      *)
(* and smoothness of hmr_elci.                                               *)
(* ========================================================================= *)

let hmr_elci = new_definition
 `hmr_elci (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K) (c:real^K) (i:num)
           (x:real^2) =
    --(&2) * (c dot (mderiv G (v x) (partial_derivative i v x) ** partial_derivative i v x +
                     G(v x) ** partial_derivative i (partial_derivative i v) x)) +
    &2 * ((hmr_dtp S (v x) c ** partial_derivative i v x) dot
          (G(v x) ** partial_derivative i v x)) +
    partial_derivative i v x dot
    (mderiv G (v x) (hmr_tp S (v x) ** c) ** partial_derivative i v x)`;;

let hmr_elc = new_definition
 `hmr_elc (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K) (c:real^K) (x:real^2) =
    sum(1..2) (\i. hmr_elci S G v c i x)`;;

(* Tangent vectors of v and the scalar product with P c.                     *)

let HMR_TANGENT_DOT = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (c:real^K) i x.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\ x IN s
     ==> (hmr_tp S (v x) ** c) dot (G(v x) ** partial_derivative i v x) =
         c dot (G(v x) ** partial_derivative i v x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(v:real^2->real^K) x`]
                HMR_TP_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[HMR_SYM_DOT] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC HMR_TP_TANGENT THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[hmr_tp] THEN
  MATCH_MP_TAC HMC_TANGENT_PARTIAL THEN
  MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `s:real^2->bool`] THEN
  ASM_REWRITE_TAC[]);;

let HMR_LD_DIRECTION_PT = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (psi:real^2->real) (c:real^K) i x.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
     smooth_map_on (:real^2) (\x. lift(psi x)) /\ x IN s
     ==> hmc_ld S G v (\y. psi y % c) (\y. partial_derivative i (\y. psi y % c) y) i x =
         &2 * cml_d i (\y. psi y * (c dot (G(v y) ** partial_derivative i v y))) x +
         psi x * hmr_elci S G v c i x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((psi:real^2->real) x)) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (\y. (G:real^K->real^K^K)((v:real^2->real^K) y) **
                                     partial_derivative i v y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `psi:real^2->real`;
                 `\y. (c:real^K) dot ((G:real^K->real^K^K)((v:real^2->real^K) y) **
                                     partial_derivative i v y)`;
                 `x:real^2`; `i:num`] CML_D_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`;
                 `\y. (G:real^K->real^K^K)((v:real^2->real^K) y) ** partial_derivative i v y`;
                 `c:real^K`; `x:real^2`; `i:num`] HMR_D_DOT_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(:real^K)`; `s:real^2->bool`; `G:real^K->real^K^K`; `v:real^2->real^K`;
                 `partial_derivative i (v:real^2->real^K)`; `x:real^2`; `i:num`]
                HMR_PD_MATVEC) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `v:real^2->real^K`; `c:real^K`; `i:num`; `x:real^2`] HMR_TANGENT_DOT) THEN
  ASM_REWRITE_TAC[hmr_tp] THEN DISCH_TAC THEN
  REWRITE_TAC[hmc_ld; hmr_elci; hmr_tp; hmr_dtp] THEN ASM_SIMP_TAC[HMR_PD_SCALAR_CMUL] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point S) (at y))) differentiable at ((v:real^2->real^K) x) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) differentiable at (v x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_MDERIV_LINEAR; MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_LMUL] THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Integrals over an open planar set of smooth functions vanishing off a     *)
(* compact subset: integrability, the divergence integral is zero,           *)
(* positivity.  (Gluing by zero, then CML_CSUPP_ABSINT, CML_DIV_ZERO and     *)
(* CML_INTEGRAL_POS of pc_cm_lemma122.)                                      *)
(* ========================================================================= *)

let HMR_GLUE_FACTS = prove
 (`!B k (f:real^2->real).
     open B /\ compact k /\ k SUBSET B /\ smooth_map_on B (\x. lift(f x)) /\
     (!x. x IN B DIFF k ==> f x = &0)
     ==> smooth_map_on (:real^2) (\x. lift(if x IN B then f x else &0)) /\
         (!x. ~(x IN k) ==> (if x IN B then f x else &0) = &0) /\
         (\x. lift(if x IN B then f x else &0)) absolutely_integrable_on (:real^2) /\
         integral B (\x. lift(f x)) = integral (:real^2) (\x. lift(if x IN B then f x else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `k:real^2->bool`; `f:real^2->real`] CML_GLUE_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_CSUPP_ABSINT THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LIFT_NUM];
    GEN_REWRITE_TAC LAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM]]);;

let HMR_SUPP_ABSINT = prove
 (`!B k (f:real^2->real).
     open B /\ compact k /\ k SUBSET B /\ smooth_map_on B (\x. lift(f x)) /\
     (!x. x IN B DIFF k ==> f x = &0)
     ==> (\x. lift(f x)) absolutely_integrable_on B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_GLUE_FACTS) THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN BETA_TAC THEN
  SUBGOAL_THEN `(\x. if x IN B then lift((f:real^2->real) x) else vec 0) =
                (\x. lift(if x IN B then f x else &0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
    ASM_REWRITE_TAC[]]);;

let HMR_SUPP_DIV_ZERO = prove
 (`!B k (f:real^2->real) i.
     open B /\ compact k /\ k SUBSET B /\ smooth_map_on B (\x. lift(f x)) /\
     (!x. x IN B DIFF k ==> f x = &0)
     ==> integral B (\x. lift(cml_d i f x)) = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_GLUE_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  ABBREV_TAC `H = \x. if x IN B then (f:real^2->real) x else &0` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  MP_TAC(ISPECL [`H:real^2->real`; `k:real^2->bool`; `i:num`] CML_DIV_ZERO) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "H" THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
  COND_CASES_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC CML_D_LOCAL THEN EXISTS_TAC `B:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "H" THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^2) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2) DIFF k`; `H:real^2->real`; `\x:real^2. &0`; `x:real^2`; `i:num`]
                CML_D_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
    EXPAND_TAC "H" THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[IN_DIFF] THEN
    ASM SET_TAC[];
    SIMP_TAC[CML_D_CONST; LIFT_NUM]]);;

let HMR_SUPP_POS = prove
 (`!B k (f:real^2->real) x0.
     open B /\ compact k /\ k SUBSET B /\ smooth_map_on B (\x. lift(f x)) /\
     (!x. x IN B DIFF k ==> f x = &0) /\ (!x. x IN B ==> &0 <= f x) /\
     x0 IN B /\ &0 < f x0
     ==> &0 < drop(integral B (\x. lift(f x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `k:real^2->bool`; `f:real^2->real`] HMR_GLUE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_INTEGRAL_POS THEN EXISTS_TAC `x0:real^2` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

(* ========================================================================= *)
(* The Euler-Lagrange equation of a smooth cm_harmonic map in constant       *)
(* directions: hmr_elc S G v c x = 0 (test fields psi c with psi a bump;     *)
(* HMC_EL_TEST, the divergence integral vanishes, positivity).               *)
(* ========================================================================= *)

let HMR_ELCI_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (c:real^K) i.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S)
     ==> smooth_map_on s (\x. lift(hmr_elci S G v c i x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!y. y IN s ==> (v:real^2->real^K) y IN cm_tube S d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. smooth_map_on s (partial_derivative a (v:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!Y. smooth_map_on s Y
                    ==> smooth_map_on s (\x. (G:real^K->real^K^K)((v:real^2->real^K) x) ** Y x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A Y. smooth_map_on s A /\ smooth_map_on s Y
                      ==> smooth_map_on s (\x. mderiv (G:real^K->real^K^K)
                                                 ((v:real^2->real^K) x) (A x) ** Y x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`;
                   `\x. mderiv (G:real^K->real^K^K) ((v:real^2->real^K) x) ((A:real^2->real^K) x)`;
                   `Y:real^2->real^K`] LRG_SMOOTH_MATVEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HMR_MDERIV_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[hmr_elci; hmr_tp; hmr_dtp] THEN
  MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX]] THEN
    MP_TAC(ISPECL [`s:real^2->bool`;
                   `\x. mderiv (\y. jacobian (closest_point S) (at y)) ((v:real^2->real^K) x) (c:real^K)`;
                   `partial_derivative i (v:real^2->real^K)`] LRG_SMOOTH_MATVEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HMR_MDERIV_SMOOTH THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`; `s:real^2->bool`;
                 `\y:real^K. jacobian (closest_point S) (at y)`; `v:real^2->real^K`;
                 `\x:real^2. (c:real^K)`] HMR_MATVEC_SMOOTH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let HMR_ELC_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (c:real^K).
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S)
     ==> smooth_map_on s (\x. lift(hmr_elc S G v c x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_elc; SUM_2] THEN
  MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC HMR_ELCI_SMOOTH THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[]);;

let HMR_ELC_NEG = prove
 (`!S (G:real^K->real^K^K) d (v:real^2->real^K) (c:real^K) x.
     cm_target S G d /\ v x IN S
     ==> hmr_elc S G v (--c) x = --(hmr_elc S G v c x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\y. jacobian (closest_point S) (at y))) differentiable at ((v:real^2->real^K) x) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K)) differentiable at (v x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[hmr_elc; hmr_elci; hmr_tp; hmr_dtp; SUM_2] THEN
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN
  ASM_SIMP_TAC[LRG_MDERIV_LINEAR; MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_LMUL] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* One term of the tested equation: the divergence part integrates to zero. *)

let HMR_EL_TERM = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (c:real^K) B k (psi:real^2->real) i.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
     open B /\ B SUBSET s /\ compact k /\ k SUBSET B /\
     smooth_map_on (:real^2) (\x. lift(psi x)) /\ (!x. ~(x IN k) ==> psi x = &0)
     ==> (\x. lift(psi x * hmr_elci S G v c i x)) absolutely_integrable_on B /\
         drop(integral B (\x. lift(&2 * cml_d i (\y. psi y * (c dot (G(v y) **
                                                       partial_derivative i v y))) x +
                                   psi x * hmr_elci S G v c i x))) =
         drop(integral B (\x. lift(psi x * hmr_elci S G v c i x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `h = \y. (c:real^K) dot ((G:real^K->real^K^K)((v:real^2->real^K) y) **
                                       partial_derivative i v y)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  SUBGOAL_THEN `!y. (c:real^K) dot ((G:real^K->real^K^K)((v:real^2->real^K) y) **
                                    partial_derivative i v y) = h y`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "h" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on B (\x. lift((psi:real^2->real) x * h x))` ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN EXISTS_TAC `(:real^K)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on B (\x. lift((psi:real^2->real) x *
                     hmr_elci (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K) (c:real^K) i x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMR_ELCI_SMOOTH THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(B DIFF k:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN B DIFF k ==> cml_d i (\y. (psi:real^2->real) y * h y) x = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`B DIFF k:real^2->bool`; `\y. (psi:real^2->real) y * h y`;
                   `\y:real^2. &0`; `x:real^2`; `i:num`] CML_D_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO];
      SIMP_TAC[CML_D_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(cml_d i (\y. (psi:real^2->real) y * h y) x)) absolutely_integrable_on B /\
                integral B (\x. lift(cml_d i (\y. psi y * h y) x)) = vec 0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HMR_SUPP_ABSINT THEN EXISTS_TAC `k:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CML_D_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HMR_SUPP_DIV_ZERO THEN EXISTS_TAC `k:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((psi:real^2->real) x *
                     hmr_elci (S:real^K->bool) (G:real^K->real^K^K) (v:real^2->real^K) (c:real^K) i x))
                absolutely_integrable_on B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMR_SUPP_ABSINT THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_ADD; GEN `x:real` (SPECL [`x:real`; `&2`] LIFT_CMUL)] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
               INTEGRABLE_CMUL] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let HMR_EL_DIRECTION = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (c:real^K) x0.
     cm_target S G d /\ open s /\ cm_harmonic S G s v /\ x0 IN s
     ==> hmr_elc S G v c x0 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `!c:real^K. ~(&0 < hmr_elc S G (v:real^2->real^K) c x0)` MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(fun th -> MP_TAC(SPEC `c:real^K` th) THEN MP_TAC(SPEC `--c:real^K` th)) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `v:real^2->real^K`;
                   `c:real^K`; `x0:real^2`] HMR_ELC_NEG) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC] THEN
  X_GEN_TAC `c:real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(x0:real^2,r) SUBSET s /\
                    !x. x IN ball(x0,r) ==> &0 < hmr_elc S G (v:real^2->real^K) c x`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. lift(hmr_elc S G (v:real^2->real^K) c x)) continuous at x0` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMR_ELC_SMOOTH THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `hmr_elc S G (v:real^2->real^K) c x0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?r2. &0 < r2 /\ ball(x0:real^2,r2) SUBSET s` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
    EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x0:real^2,r2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `psi = \x:real^2. smooth_bump (r / &4) (r / &2) (x - x0)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. lift((psi:real^2->real) x)) /\
                (!x. &0 <= psi x) /\ psi x0 = &1 /\
                (!x. ~(x IN cball(x0:real^2,r / &2)) ==> psi x = &0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. lift(smooth_bump (r / &4) (r / &2) (x - x0:real^2))) =
                    (\y. lift(smooth_bump (r / &4) (r / &2) y)) o (\x. x - x0)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
        MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SMOOTH_BUMP_BOUNDS];
      MATCH_MP_TAC SMOOTH_BUMP_1 THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_BUMP_0 THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x0:real^2,r / &2) SUBSET ball(x0,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `x0:real^2`; `r:real`;
                 `v:real^2->real^K`; `\y:real^2. (psi:real^2->real) y % (c:real^K)`]
                HMC_EL_TEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[wan_vtest] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^2)`; `\x. lift((psi:real^2->real) x)`; `\x:real^2. (c:real^K)`]
                      SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; LIFT_DROP];
        EXISTS_TAC `cball(x0:real^2,r / &2)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
        ASM_SIMP_TAC[VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
  SUBGOAL_THEN
   `!i. integral (ball(x0,r))
          (\x. lift(hmc_ld S G (v:real^2->real^K) (\y. (psi:real^2->real) y % (c:real^K))
                           (\y. partial_derivative i (\y. psi y % c) y) i x)) =
        integral (ball(x0,r))
          (\x. lift(&2 * cml_d i (\y. psi y * (c dot (G(v y) ** partial_derivative i v y))) x +
                    psi x * hmr_elci S G v c i x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC HMR_LD_DIRECTION_PT THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `v:real^2->real^K`; `c:real^K`; `ball(x0:real^2,r)`; `cball(x0:real^2,r / &2)`;
                 `psi:real^2->real`; `2`] HMR_EL_TERM) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `v:real^2->real^K`; `c:real^K`; `ball(x0:real^2,r)`; `cball(x0:real^2,r / &2)`;
                 `psi:real^2->real`; `1`] HMR_EL_TERM) THEN
  ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN
   `drop(integral (ball(x0,r)) (\x. lift((psi:real^2->real) x *
                                       hmr_elci S G (v:real^2->real^K) c 1 x))) +
    drop(integral (ball(x0,r)) (\x. lift(psi x * hmr_elci S G v c 2 x))) =
    drop(integral (ball(x0,r)) (\x. lift(psi x * hmr_elc S G v c x)))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_ADD; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; hmr_elc; SUM_2; GSYM LIFT_ADD; LIFT_EQ] THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
  MATCH_MP_TAC HMR_SUPP_POS THEN
  MAP_EVERY EXISTS_TAC [`cball(x0:real^2,r / &2)`; `x0:real^2`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL; CENTRE_IN_BALL; REAL_MUL_LID] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CML_SM_MUL THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMR_ELC_SMOOTH THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ========================================================================= *)
(* The strong Euler-Lagrange equation                                        *)
(*   P(v)(Lap v + sum_i Gam(v)(d_i v, d_i v)) = 0                           *)
(* of a smooth cm_harmonic map, and the explicit system                     *)
(*   Lap v = sum_i hmr_bq S G v (d_i v) (d_i v),                            *)
(*   hmr_bq S G p a b = (dP(p) a) b - P(p) Gam(p)(a,b).                      *)
(* ========================================================================= *)

let hmr_vlap = new_definition
 `hmr_vlap (v:real^2->real^K) (x:real^2) =
    vsum(1..2) (\i. partial_derivative i (partial_derivative i v) x)`;;

let hmr_bq = new_definition
 `hmr_bq (S:real^K->bool) (G:real^K->real^K^K) (p:real^K) (a:real^K) (b:real^K) =
    hmr_dtp S p a ** b - hmr_tp S p ** christoffel G p a b`;;

(* Normal times tangent: dP(a) b is normal for tangent a, b.               *)

let HMR_DTP_TANGENT_DOT = prove
 (`!S (G:real^K->real^K^K) d z a b.
     cm_target S G d /\ z IN S /\ hmr_tp S z ** a = a /\ hmr_tp S z ** b = b
     ==> (hmr_dtp S z a ** b) dot (G z ** b) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `z:real^K`] HMR_TP_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `z:real^K`; `b:real^K`]
                HMR_TP_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(hmr_dtp S z a ** b) dot ((G:real^K->real^K^K) z ** b) =
                (hmr_tp S z ** (hmr_dtp S z a ** b)) dot (G z ** (b:real^K))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[HMR_SYM_DOT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `z:real^K`; `a:real^K`;
                 `b:real^K`] HMC_JDJ) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[hmr_tp]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[hmr_tp; hmr_dtp] THEN SIMP_TAC[DOT_LZERO]);;

let HMR_EL_STRONG = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) x.
     cm_target S G d /\ open s /\ cm_harmonic S G s v /\ x IN s
     ==> hmr_tp S (v x) **
         (hmr_vlap v x +
          vsum(1..2) (\i. christoffel G (v x) (partial_derivative i v x)
                                              (partial_derivative i v x))) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(v:real^2->real^K) x`]
                HMR_TP_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  SUBGOAL_THEN `!i. hmr_tp S ((v:real^2->real^K) x) ** partial_derivative i v x =
                    partial_derivative i v x` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[hmr_tp] THEN MATCH_MP_TAC HMC_TANGENT_PARTIAL THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `s:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = hmr_vlap (v:real^2->real^K) x +
                  vsum(1..2) (\i. christoffel (G:real^K->real^K^K) (v x)
                                    (partial_derivative i v x) (partial_derivative i v x))` THEN
  SUBGOAL_THEN `!w. (hmr_tp S ((v:real^2->real^K) x) ** w) dot
                    ((G:real^K->real^K^K)(v x) ** X) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^K` THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `v:real^2->real^K`; `hmr_tp S ((v:real^2->real^K) x) ** (w:real^K)`;
                   `x:real^2`] HMR_EL_DIRECTION) THEN
    ASM_REWRITE_TAC[hmr_elc; hmr_elci; SUM_2] THEN
    SUBGOAL_THEN `hmr_tp S ((v:real^2->real^K) x) ** hmr_tp S (v x) ** (w:real^K) =
                  hmr_tp S (v x) ** w` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. (hmr_dtp S ((v:real^2->real^K) x) (hmr_tp S (v x) ** (w:real^K)) **
           partial_derivative i v x) dot
          ((G:real^K->real^K^K)(v x) ** partial_derivative i v x) = &0`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC HMR_DTP_TANGENT_DOT THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
      ALL_TAC] THEN
    EXPAND_TAC "X" THEN
    REWRITE_TAC[hmr_vlap; VSUM_2; MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD] THEN
    MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `(v:real^2->real^K) x`]
                  LRG_CHRISTOFFEL_DOT) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[DOT_LADD; MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hmr_tp S ((v:real^2->real^K) x) ** ((G:real^K->real^K^K)(v x) ** X) = vec 0`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM DOT_EQ_0] THEN
    ASM_SIMP_TAC[HMR_SYM_DOT; MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(G:real^K->real^K^K)((v:real^2->real^K) x) ** X`) THEN
    ASM_SIMP_TAC[HMR_SYM_DOT; MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC HMR_TP_INJ THEN
  MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(hmr_tp S ((v:real^2->real^K) x) ** (G:real^K->real^K^K)(v x) **
                 (mat 1 - hmr_tp S (v x))) ** X = vec 0` MP_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_LZERO; VECTOR_NEG_EQ_0]);;

let HMR_PDE = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) x.
     cm_target S G d /\ open s /\ cm_harmonic S G s v /\ x IN s
     ==> hmr_vlap v x =
         vsum(1..2) (\i. hmr_bq S G (v x) (partial_derivative i v x)
                                          (partial_derivative i v x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN
   `!i. mderiv (\y. jacobian (closest_point S) (at y)) ((v:real^2->real^K) x)
               (partial_derivative i v x) ** partial_derivative i v x +
        jacobian (closest_point S) (at (v x)) ** partial_derivative i (partial_derivative i v) x =
        partial_derivative i (partial_derivative i v) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(BETA_RULE(ISPECL [`cm_tube (S:real^K->bool) d`; `s:real^2->bool`;
                             `\y:real^K. jacobian (closest_point S) (at y)`; `v:real^2->real^K`;
                             `partial_derivative i (v:real^2->real^K)`; `x:real^2`; `i:num`]
                            HMR_PD_MATVEC)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HMC_TANGENT_PARTIAL THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `s:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `v:real^2->real^K`; `x:real^2`] HMR_EL_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  REWRITE_TAC[hmr_vlap; hmr_bq; hmr_tp; hmr_dtp; VSUM_2; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* A global smooth extension Pg of closest_point S (equal to it on a tube    *)
(* cm_tube S d1, d1 < d) with a globally bounded and Lipschitz derivative    *)
(* (cutoff GRGE_EUCLID_CUTOFF; used by pc_hm_dirichlet).  Derivative bounds  *)
(* for smooth maps with compact support.                                     *)
(* ========================================================================= *)

let HMR_CSUPP_DERIV_BOUND = prove
 (`!(f:real^M->real^N) L.
     smooth_map_on (:real^M) f /\ compact L /\ (!z. ~(z IN L) ==> f z = vec 0)
     ==> ?B. &0 <= B /\ !y h. norm(frechet_derivative f (at y) h) <= B * norm h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `L:real^M->bool`; `f:real^M->real^N`] HMC_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^M`; `h:real^M`] THEN
  ASM_CASES_TAC `(y:real^M) IN L` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `frechet_derivative (f:real^M->real^N) (at y) = (\h. vec 0)` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `frechet_derivative (\z:real^M. vec 0:real^N) (at y)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT]] THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `(:real^M) DIFF L` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV];
    REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

let HMR_CSUPP_LIPSCHITZ = prove
 (`!(f:real^M->real^N) L.
     smooth_map_on (:real^M) f /\ compact L /\ (!z. ~(z IN L) ==> f z = vec 0)
     ==> ?B. &0 <= B /\ !y z. norm(f y - f z) <= B * norm(y - z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP HMR_CSUPP_DERIV_BOUND) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `\x:real^M. frechet_derivative (f:real^M->real^N) (at x)`;
                 `(:real^M)`; `B:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[WITHIN_UNIV] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    X_GEN_TAC `x:real^M` THEN
    SUBGOAL_THEN `linear(frechet_derivative (f:real^M->real^N) (at x))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^M)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ASM_SIMP_TAC[ONORM_LE_EQ]]]);;

let HMR_PI_GLOBAL = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?d1 B (Pg:real^K->real^K).
           &0 < d1 /\ d1 < d /\ &0 <= B /\ smooth_map_on (:real^K) Pg /\
           (!z. z IN cm_tube S d1 ==> Pg z = closest_point S z) /\
           (!y v. norm(frechet_derivative Pg (at y) v) <= B * norm v) /\
           (!y z v. norm(frechet_derivative Pg (at y) v - frechet_derivative Pg (at z) v)
                    <= B * norm(y - z) * norm v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_SUBTUBE) THEN
  MP_TAC(ISPECL [`{p + q | p IN S /\ q IN cball(vec 0:real^K,d / &2)}`;
                 `cm_tube (S:real^K->bool) d`] GRGE_EUCLID_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (X_CHOOSE_THEN `L:real^K->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `Pg = \z:real^K. psi z % closest_point (S:real^K->bool) z` THEN
  SUBGOAL_THEN `!z. ~(z IN L) ==> (Pg:real^K->real^K) z = vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "Pg" THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) (Pg:real^K->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z0:real^K` THEN ASM_CASES_TAC `(z0:real^K) IN cm_tube S d` THENL
     [EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Pg" THEN
      MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`; `\z. lift((psi:real^K->real) z)`;
                     `closest_point (S:real^K->bool)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `(:real^K) DIFF L` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:real^K. vec 0:real^K` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV; SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Pg:real^K->real^K`; `L:real^K->bool`] HMR_CSUPP_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k. ?Bk. &0 <= Bk /\
             !y z. norm(partial_derivative k (Pg:real^K->real^K) y -
                        partial_derivative k Pg z) <= Bk * norm(y - z)`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMR_CSUPP_LIPSCHITZ THEN EXISTS_TAC `L:real^K->bool` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; ETA_AX]; ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN REWRITE_TAC[partial_derivative] THEN
    SUBGOAL_THEN `frechet_derivative (Pg:real^K->real^K) (at z) =
                  frechet_derivative (\z:real^K. vec 0:real^K) (at z)` SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `(:real^K) DIFF L` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV];
      REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `Bk:num->real` STRIP_ASSUME_TAC)] THEN
  MAP_EVERY EXISTS_TAC [`d / &2`; `max B1 (sum(1..dimindex(:K)) Bk)`; `Pg:real^K->real^K`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^K` THEN REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "Pg" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^K->real) z = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`p:real^K`; `z - p:real^K`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM dist] THEN UNDISCH_TAC `dist(z:real^K,p) < d / &2` THEN REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B1 * norm(v:real^K)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^K`; `z:real^K`; `v:real^K`] THEN
  SUBGOAL_THEN `!x:real^K. frechet_derivative (Pg:real^K->real^K) (at x) v =
                           vsum(1..dimindex(:K)) (\k. v$k % partial_derivative k Pg x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `x:real^K` THEN REWRITE_TAC[partial_derivative] THEN
    SUBGOAL_THEN `linear(frechet_derivative (Pg:real^K->real^K) (at x))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM VSUM_SUB_NUMSEG; GSYM VECTOR_SUB_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:K)) (\k. norm(v:real^K) * Bk k * norm(y - z:real^K))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; COMPONENT_LE_NORM];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN
  SUBGOAL_THEN
   `norm(v:real^K) * sum(1..dimindex(:K)) Bk * norm(y - z:real^K) =
    (norm v * norm(y - z)) * sum(1..dimindex(:K)) Bk /\
    max B1 (sum(1..dimindex(:K)) Bk) * norm(y - z) * norm v =
    (norm v * norm(y - z)) * max B1 (sum(1..dimindex(:K)) Bk)`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Calculus for the energy density hmr_e v = |d_1 v|^2 + |d_2 v|^2 of        *)
(* a planar map: product rule for dot products,                              *)
(* Lap e = 2 sum |d_j d_i v|^2 + 2 sum d_i v . d_i(Lap v).                   *)
(* ========================================================================= *)

let hmr_e = new_definition
 `hmr_e (v:real^2->real^K) (x:real^2) =
    partial_derivative 1 v x dot partial_derivative 1 v x +
    partial_derivative 2 v x dot partial_derivative 2 v x`;;

let HMR_D_DOT = prove
 (`!W (A:real^2->real^N) B z i.
     open W /\ smooth_map_on W A /\ smooth_map_on W B /\ z IN W
     ==> cml_d i (\x. A x dot B x) z =
         partial_derivative i A z dot B z + A z dot partial_derivative i B z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cml_d] THEN
  SUBGOAL_THEN `(A:real^2->real^N) differentiable at z /\ (B:real^2->real^N) differentiable at z`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N y:real^N. lift(x dot y)`; `A:real^2->real^N`; `B:real^2->real^N`;
                 `frechet_derivative (A:real^2->real^N) (at z)`;
                 `frechet_derivative (B:real^2->real^N) (at z)`; `z:real^2`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ANTS_TAC THENL
   [REWRITE_TAC[bilinear; linear; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN BETA_TAC THEN
  REWRITE_TAC[partial_derivative] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC);;

let HMR_SCHWARZ_ALL = prove
 (`!W (u:real^2->real^N) z i j.
     open W /\ smooth_map_on W u /\ z IN W /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> partial_derivative i (partial_derivative j u) z =
         partial_derivative j (partial_derivative i u) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(i = 1 \/ i = 2) /\ (j = 1 \/ j = 2)` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(MATCH_MP_TAC CML_SCHWARZ THEN EXISTS_TAC `W:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CML_SCHWARZ THEN EXISTS_TAC `W:real^2->bool` THEN
  ASM_REWRITE_TAC[]);;

let HMR_D_VLAP = prove
 (`!s (v:real^2->real^K) x i.
     open s /\ smooth_map_on s v /\ x IN s /\ 1 <= i /\ i <= 2
     ==> partial_derivative i (\y. hmr_vlap v y) x =
         partial_derivative 1 (partial_derivative 1 (partial_derivative i v)) x +
         partial_derivative 2 (partial_derivative 2 (partial_derivative i v)) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_vlap; VSUM_2] THEN
  SUBGOAL_THEN `!a b. smooth_map_on s (partial_derivative a (partial_derivative b (v:real^2->real^K)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. partial_derivative a (partial_derivative b (v:real^2->real^K)) differentiable at x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `partial_derivative 1 (partial_derivative 1 (v:real^2->real^K))`;
                 `partial_derivative 2 (partial_derivative 2 (v:real^2->real^K))`; `x:real^2`]
                PARTIAL_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 2
        ==> partial_derivative i (partial_derivative j (partial_derivative j (v:real^2->real^K))) x =
            partial_derivative j (partial_derivative j (partial_derivative i v)) x`
  (fun th -> SIMP_TAC[th; ARITH]) THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `partial_derivative j (partial_derivative i (partial_derivative j (v:real^2->real^K))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HMR_SCHWARZ_ALL THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC HMR_SCHWARZ_ALL THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

let HMR_D_SQ = prove
 (`!W (A:real^2->real^N) z i.
     open W /\ smooth_map_on W A /\ z IN W
     ==> cml_d i (\x. A x dot A x) z = &2 * (A z dot partial_derivative i A z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^2->bool`; `A:real^2->real^N`; `A:real^2->real^N`; `z:real^2`; `i:num`]
                HMR_D_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [DOT_SYM] THEN REAL_ARITH_TAC);;

let HMR_LAP_E = prove
 (`!s (v:real^2->real^K) x.
     open s /\ smooth_map_on s v /\ x IN s
     ==> cml_lap (hmr_e v) x =
         &2 * sum(1..2) (\i. sum(1..2) (\j. partial_derivative j (partial_derivative i v) x dot
                                            partial_derivative j (partial_derivative i v) x)) +
         &2 * sum(1..2) (\i. partial_derivative i v x dot
                             partial_derivative i (\y. hmr_vlap v y) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a. smooth_map_on s (partial_derivative a (v:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. smooth_map_on s (partial_derivative a (partial_derivative b (v:real^2->real^K)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j y. y IN s
          ==> cml_d j (hmr_e (v:real^2->real^K)) y =
              &2 * (partial_derivative 1 v y dot partial_derivative j (partial_derivative 1 v) y) +
              &2 * (partial_derivative 2 v y dot partial_derivative j (partial_derivative 2 v) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `hmr_e (v:real^2->real^K) =
                  (\y. partial_derivative 1 v y dot partial_derivative 1 v y +
                       partial_derivative 2 v y dot partial_derivative 2 v y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; hmr_e]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`;
                   `\y. partial_derivative 1 (v:real^2->real^K) y dot partial_derivative 1 v y`;
                   `\y. partial_derivative 2 (v:real^2->real^K) y dot partial_derivative 2 v y`;
                   `y:real^2`; `j:num`] CML_D_ADD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative 1 (v:real^2->real^K)`; `y:real^2`;
                   `j:num`] HMR_D_SQ) THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative 2 (v:real^2->real^K)`; `y:real^2`;
                   `j:num`] HMR_D_SQ) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 2
        ==> cml_d j (cml_d j (hmr_e (v:real^2->real^K))) x =
            &2 * (partial_derivative j (partial_derivative 1 v) x dot
                  partial_derivative j (partial_derivative 1 v) x +
                  partial_derivative 1 v x dot
                  partial_derivative j (partial_derivative j (partial_derivative 1 v)) x) +
            &2 * (partial_derivative j (partial_derivative 2 v) x dot
                  partial_derivative j (partial_derivative 2 v) x +
                  partial_derivative 2 v x dot
                  partial_derivative j (partial_derivative j (partial_derivative 2 v)) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `cml_d j (hmr_e (v:real^2->real^K))`;
                   `\y. &2 * (partial_derivative 1 (v:real^2->real^K) y dot
                              partial_derivative j (partial_derivative 1 v) y) +
                        &2 * (partial_derivative 2 v y dot
                              partial_derivative j (partial_derivative 2 v) y)`;
                   `x:real^2`; `j:num`] CML_D_LOCAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `!a. smooth_map_on s
                       (\y. lift(&2 * (partial_derivative a (v:real^2->real^K) y dot
                                       partial_derivative j (partial_derivative a v) y)))`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`;
                   `\y. &2 * (partial_derivative 1 (v:real^2->real^K) y dot
                              partial_derivative j (partial_derivative 1 v) y)`;
                   `\y. &2 * (partial_derivative 2 (v:real^2->real^K) y dot
                              partial_derivative j (partial_derivative 2 v) y)`;
                   `x:real^2`; `j:num`] CML_D_ADD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `!a. cml_d j (\y. &2 * (partial_derivative a (v:real^2->real^K) y dot
                             partial_derivative j (partial_derivative a v) y)) x =
          &2 * (partial_derivative j (partial_derivative a v) x dot
                partial_derivative j (partial_derivative a v) x +
                partial_derivative a v x dot
                partial_derivative j (partial_derivative j (partial_derivative a v)) x)`
    (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `&2`;
                   `\y. partial_derivative a (v:real^2->real^K) y dot
                        partial_derivative j (partial_derivative a v) y`;
                   `x:real^2`; `j:num`] CML_D_CMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative a (v:real^2->real^K)`;
                   `partial_derivative j (partial_derivative a (v:real^2->real^K))`; `x:real^2`;
                   `j:num`] HMR_D_DOT) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cml_lap] THEN ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[SUM_2] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`; `1`] HMR_D_VLAP) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`; `2`] HMR_D_VLAP) THEN
  ASM_REWRITE_TAC[ARITH] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[DOT_RADD] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Bochner inequality for the Euclidean energy density of a smooth       *)
(* cm_harmonic map:                                                          *)
(*   Lap e >= -C e^2,  e = |d_1 v|^2 + |d_2 v|^2,                            *)
(* with C depending only on (S,G,d): from the explicit system Lap v =       *)
(* sum_i hmr_bq(v)(d_i v, d_i v) and uniform bounds of the bilinear family   *)
(* hmr_bq and its derivative on the compact S.                               *)
(* ========================================================================= *)

let HMR_BQ_FAMILY = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> (!p. p IN cm_tube S d ==> bilinear (hmr_bq S G p)) /\
         (!a b. smooth_map_on (cm_tube S d) (\p. hmr_bq S G p a b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN CONJ_TAC THENL
   [X_GEN_TAC `p:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o
                   (\y. jacobian (closest_point S) (at y))) differentiable at p`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^K)`; `G:real^K->real^K^K`; `p:real^K`] LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN REWRITE_TAC[linear] THEN STRIP_TAC THEN
    REWRITE_TAC[bilinear; linear; hmr_bq; hmr_tp; hmr_dtp] THEN
    ASM_SIMP_TAC[LRG_MDERIV_LINEAR; MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
                 MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[hmr_bq; hmr_tp; hmr_dtp] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`;
                   `\p. mderiv (\y. jacobian (closest_point S) (at y)) p (a:real^K)`;
                   `\p:real^K. (b:real^K)`] LRG_SMOOTH_MATVEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LRG_SMOOTH_MDERIV; SMOOTH_MAP_ON_CONST];
    MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`; `\y:real^K. jacobian (closest_point S) (at y)`;
                   `\p. christoffel (G:real^K->real^K^K) p a b`] LRG_SMOOTH_MATVEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LRG_CHRISTOFFEL_SMOOTH]]);;

let HMR_BILFAM_BOUNDS = prove
 (`!W k (bb:real^N->real^N->real^N->real^N).
     open W /\ compact k /\ k SUBSET W /\ (!p. p IN W ==> bilinear (bb p)) /\
     (!a b. smooth_map_on W (\p. bb p a b))
     ==> ?B0 B1. &0 <= B0 /\ &0 <= B1 /\
                 (!p a b. p IN k ==> norm(bb p a b) <= B0 * norm a * norm b) /\
                 (!p a b w. p IN k
                            ==> norm(frechet_derivative (\q. bb q a b) (at p) w)
                                <= B1 * norm a * norm b * norm w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. ?C. &0 <= C /\
              !p. p IN k ==> norm((bb:real^N->real^N->real^N->real^N) p (basis i) (basis j)) <= C`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC HMC_CONT_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `C:num->num->real`)] THEN
  SUBGOAL_THEN
   `!i j. ?D. &0 <= D /\
              !p w. p IN k
                    ==> norm(frechet_derivative
                               (\q. (bb:real^N->real^N->real^N->real^N) q (basis i) (basis j))
                               (at p) w) <= D * norm w`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC HMC_DERIV_BOUND THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `D:num->num->real`)] THEN
  MAP_EVERY EXISTS_TAC
   [`sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. (C:num->num->real) i j))`;
    `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. (D:num->num->real) i j))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`p:real^N`; `a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `bilinear ((bb:real^N->real^N->real^N->real^N) p)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [MATCH_MP CMPC_BILINEAR_EXPAND th]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                  (\j. (norm(a:real^N) * norm(b:real^N)) * (C:num->num->real) i j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS; COMPONENT_LE_NORM];
      REWRITE_TAC[SUM_LMUL] THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^N`; `a:real^N`; `b:real^N`; `w:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:real^N) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\q. (bb:real^N->real^N->real^N->real^N) q a b) (at p) w =
    vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
      (\j. (a$i * b$j) % frechet_derivative (\q. bb q (basis i) (basis j)) (at p) w))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `frechet_derivative (\q. (bb:real^N->real^N->real^N->real^N) q a b) (at p) =
      frechet_derivative (\q. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                          (\j. (a$i * b$j) % bb q (basis i) (basis j)))) (at p)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPC_BILINEAR_EXPAND THEN
      ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (\q. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
                          (\j. ((a:real^N)$i * (b:real^N)$j) %
                               (bb:real^N->real^N->real^N->real^N) q (basis i) (basis j)))) (at p) =
      (\h. vsum(1..dimindex(:N)) (\i. vsum(1..dimindex(:N))
         (\j. (a$i * b$j) % frechet_derivative (\q. bb q (basis i) (basis j)) (at p) h)))`
    (fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
                (\j. (norm(a:real^N) * norm(b:real^N)) * (D:num->num->real) i j * norm(w:real^N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; COMPONENT_LE_NORM];
    REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN REAL_ARITH_TAC]);;
let HMR_BOCHNER_ALG = prove
 (`!a1 a2 m11 m12 m21 m22 B0 B1 X1 X2 L.
     &0 <= a1 /\ &0 <= a2 /\ &0 <= B0 /\ &0 <= B1 /\
     abs X1 <= a1 * (&2 * B0 * (m11 * a1 + m21 * a2) + B1 * (a1 pow 2 + a2 pow 2) * a1) /\
     abs X2 <= a2 * (&2 * B0 * (m12 * a1 + m22 * a2) + B1 * (a1 pow 2 + a2 pow 2) * a2) /\
     L = &2 * (m11 pow 2 + m12 pow 2 + m21 pow 2 + m22 pow 2) + &2 * (X1 + X2)
     ==> --((&2 * B0 pow 2 + &2 * B1) * (a1 pow 2 + a2 pow 2) pow 2) <= L`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Y1 = a1 * (&2 * B0 * (m11 * a1 + m21 * a2) + B1 * (a1 pow 2 + a2 pow 2) * a1)` THEN
  ABBREV_TAC `Y2 = a2 * (&2 * B0 * (m12 * a1 + m22 * a2) + B1 * (a1 pow 2 + a2 pow 2) * a2)` THEN
  SUBGOAL_THEN
   `&2 * (m11 pow 2 + m12 pow 2 + m21 pow 2 + m22 pow 2) - &2 * Y1 - &2 * Y2 +
    (&2 * B0 pow 2 + &2 * B1) * (a1 pow 2 + a2 pow 2) pow 2 =
    &2 * ((m11 - B0 * a1 * a1) pow 2 + (m21 - B0 * a1 * a2) pow 2 +
          (m12 - B0 * a1 * a2) pow 2 + (m22 - B0 * a2 * a2) pow 2)`
  MP_TAC THENL
   [EXPAND_TAC "Y1" THEN EXPAND_TAC "Y2" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `m11 - B0 * a1 * a1` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `m21 - B0 * a1 * a2` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `m12 - B0 * a1 * a2` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `m22 - B0 * a2 * a2` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

let HMR_BQ_DERIV = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (A:real^2->real^K) B x i.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
     smooth_map_on s A /\ smooth_map_on s B /\ x IN s
     ==> partial_derivative i (\y. hmr_bq S G (v y) (A y) (B y)) x =
         hmr_bq S G (v x) (partial_derivative i A x) (B x) +
         hmr_bq S G (v x) (A x) (partial_derivative i B x) +
         frechet_derivative (\q. hmr_bq S G q (A x) (B x)) (at (v x))
                            (partial_derivative i v x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  SUBGOAL_THEN `!y. y IN s ==> (v:real^2->real^K) y IN cm_tube S d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. (\z. hmr_bq S G ((v:real^2->real^K) z) a b) differentiable at x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z. hmr_bq S G ((v:real^2->real^K) z) a b) =
                  (\p. hmr_bq S (G:real^K->real^K^K) p a b) o v` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^2. hmr_bq (S:real^K->bool) (G:real^K->real^K^K) ((v:real^2->real^K) z)`;
                 `A:real^2->real^K`; `frechet_derivative (A:real^2->real^K) (at x)`;
                 `B:real^2->real^K`; `frechet_derivative (B:real^2->real^K) (at x)`;
                 `s:real^2->bool`; `x:real^2`] LRG_HAS_DERIVATIVE_BILFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[partial_derivative] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`v:real^2->real^K`;
                           `\q. hmr_bq S (G:real^K->real^K^K) q ((A:real^2->real^K) x)
                                       ((B:real^2->real^K) x)`;
                           `x:real^2`; `basis i:real^2`] LRG_FRECHET_DERIVATIVE_CHAIN)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `s:real^2->bool`; EXISTS_TAC `cm_tube (S:real^K->bool) d`] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

let HMR_BQ_DIFF = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (A:real^2->real^K) B x.
     cm_target S G d /\ open s /\ smooth_map_on s v /\ (!y. y IN s ==> v y IN S) /\
     smooth_map_on s A /\ smooth_map_on s B /\ x IN s
     ==> (\y. hmr_bq S G (v y) (A y) (B y)) differentiable at x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  SUBGOAL_THEN `!y. y IN s ==> (v:real^2->real^K) y IN cm_tube S d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[differentiable] THEN
  MP_TAC(ISPECL [`\z:real^2. hmr_bq (S:real^K->bool) (G:real^K->real^K^K) ((v:real^2->real^K) z)`;
                 `A:real^2->real^K`; `frechet_derivative (A:real^2->real^K) (at x)`;
                 `B:real^2->real^K`; `frechet_derivative (B:real^2->real^K) (at x)`;
                 `s:real^2->bool`; `x:real^2`] LRG_HAS_DERIVATIVE_BILFAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\z. hmr_bq S G ((v:real^2->real^K) z) (basis i) (basis j)) =
                    (\p. hmr_bq S (G:real^K->real^K^K) p (basis i) (basis j)) o v`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

let HMR_BOCHNER = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?C. &0 <= C /\
             !s (v:real^2->real^K) x.
                open s /\ cm_harmonic S G s v /\ x IN s
                ==> --(C * hmr_e v x pow 2) <= cml_lap (hmr_e v) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  MP_TAC(ISPECL [`cm_tube (S:real^K->bool) d`; `S:real^K->bool`;
                 `hmr_bq (S:real^K->bool) (G:real^K->real^K^K)`] HMR_BILFAM_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `&2 * B0 pow 2 + &2 * B1` THEN
  CONJ_TAC THENL [MP_TAC(SPEC `B0:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `!a. smooth_map_on s (partial_derivative a (v:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `x:real^2`] HMR_LAP_E) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (\y. hmr_vlap (v:real^2->real^K) y) x =
        (hmr_bq S G (v x) (partial_derivative i (partial_derivative 1 v) x)
                          (partial_derivative 1 v x) +
         hmr_bq S G (v x) (partial_derivative 1 v x)
                          (partial_derivative i (partial_derivative 1 v) x) +
         frechet_derivative (\q. hmr_bq S G q (partial_derivative 1 v x)
                                               (partial_derivative 1 v x))
                            (at (v x)) (partial_derivative i v x)) +
        (hmr_bq S G (v x) (partial_derivative i (partial_derivative 2 v) x)
                          (partial_derivative 2 v x) +
         hmr_bq S G (v x) (partial_derivative 2 v x)
                          (partial_derivative i (partial_derivative 2 v) x) +
         frechet_derivative (\q. hmr_bq S G q (partial_derivative 2 v x)
                                               (partial_derivative 2 v x))
                            (at (v x)) (partial_derivative i v x))`
  (LABEL_TAC "DF") THENL
   [GEN_TAC THEN
    TRANS_TAC EQ_TRANS
     `partial_derivative i
        (\y. hmr_bq S G ((v:real^2->real^K) y) (partial_derivative 1 v y)
                                               (partial_derivative 1 v y) +
             hmr_bq S G (v y) (partial_derivative 2 v y) (partial_derivative 2 v y)) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                     `v:real^2->real^K`; `y:real^2`] HMR_PDE) THEN
      ASM_REWRITE_TAC[VSUM_2];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`i:num`;
      `\y. hmr_bq S G ((v:real^2->real^K) y) (partial_derivative 1 v y) (partial_derivative 1 v y)`;
      `\y. hmr_bq S G ((v:real^2->real^K) y) (partial_derivative 2 v y) (partial_derivative 2 v y)`;
      `x:real^2`] PARTIAL_DERIVATIVE_ADD) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC HMR_BQ_DIFF THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THEN MATCH_MP_TAC HMR_BQ_DERIV THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `s:real^2->bool`] THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = partial_derivative 1 (v:real^2->real^K) x` THEN
  ABBREV_TAC `t2 = partial_derivative 2 (v:real^2->real^K) x` THEN
  SUBGOAL_THEN
   `!i. norm(partial_derivative i (\y. hmr_vlap (v:real^2->real^K) y) x) <=
        &2 * B0 * (norm(partial_derivative i (partial_derivative 1 v) x) * norm(t1:real^K) +
                   norm(partial_derivative i (partial_derivative 2 v) x) * norm(t2:real^K)) +
        B1 * (norm t1 pow 2 + norm t2 pow 2) * norm(partial_derivative i v x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "DF" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(GEN_ALL(NORM_ARITH
     `norm(a1:real^N) <= x1 /\ norm a2 <= x2 /\ norm a3 <= x3 /\
      norm b1 <= y1 /\ norm b2 <= y2 /\ norm b3 <= y3 /\
      x1 + x2 + x3 + y1 + y2 + y3 <= z
      ==> norm((a1 + a2 + a3) + (b1 + b2 + b3)) <= z`)) THEN
    MAP_EVERY EXISTS_TAC
     [`B0 * norm(partial_derivative i (partial_derivative 1 (v:real^2->real^K)) x) * norm(t1:real^K)`;
      `B0 * norm(t1:real^K) * norm(partial_derivative i (partial_derivative 1 (v:real^2->real^K)) x)`;
      `B1 * norm(t1:real^K) * norm(t1:real^K) * norm(partial_derivative i (v:real^2->real^K) x)`;
      `B0 * norm(partial_derivative i (partial_derivative 2 (v:real^2->real^K)) x) * norm(t2:real^K)`;
      `B0 * norm(t2:real^K) * norm(partial_derivative i (partial_derivative 2 (v:real^2->real^K)) x)`;
      `B1 * norm(t2:real^K) * norm(t2:real^K) * norm(partial_derivative i (v:real^2->real^K) x)`] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "DF" (K ALL_TAC) THEN
  REWRITE_TAC[hmr_e] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  MATCH_MP_TAC HMR_BOCHNER_ALG THEN
  MAP_EVERY EXISTS_TAC
   [`norm(partial_derivative 1 (partial_derivative 1 (v:real^2->real^K)) x)`;
    `norm(partial_derivative 2 (partial_derivative 1 (v:real^2->real^K)) x)`;
    `norm(partial_derivative 1 (partial_derivative 2 (v:real^2->real^K)) x)`;
    `norm(partial_derivative 2 (partial_derivative 2 (v:real^2->real^K)) x)`;
    `(t1:real^K) dot partial_derivative 1 (\y. hmr_vlap (v:real^2->real^K) y) x`;
    `(t2:real^K) dot partial_derivative 2 (\y. hmr_vlap (v:real^2->real^K) y) x`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(t1:real^K) *
                norm(partial_derivative 1 (\y. hmr_vlap (v:real^2->real^K) y) x)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(t2:real^K) *
                norm(partial_derivative 2 (\y. hmr_vlap (v:real^2->real^K) y) x)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_2] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

