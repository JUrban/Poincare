(* ========================================================================= *)
(* Unit pc_grg_divthm (Riemannian geometry layer): the divergence theorem on *)
(* a closed Riemannian manifold (MFD_DIVERGENCE_THEOREM, used by the PDE     *)
(* layer): chart invariance of ldiv, the formula ldiv G Z sqrt(det G)        *)
(* = trace D(sqrt(det G) Z), vanishing integrals of divergences of compactly *)
(* supported fields in real^N, smooth partitions of unity on compact         *)
(* manifolds.                                                                *)
(* ========================================================================= *)

needs "src/pc_grg_rfint.ml";;
needs "src/pc_mfd_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Chart invariance of the divergence ldiv.  Under a diffeomorphism h with   *)
(* Z0 o h = Dh Z1, the derivative of Z0 o h produces a second-derivative     *)
(* term dd2 h y u (Z1 y), and the Christoffel symbols of the pullback metric *)
(* produce the same term (LCHRISTOFFEL_PULLBACK of pc_lrg); they cancel in   *)
(* the trace, which is invariant under conjugation by Dh.                   *)
(* ------------------------------------------------------------------------- *)

let GRGT_DD2_LINEAR = prove
 (`!s (h:real^N->real^N) y u.
        open s /\ smooth_map_on s h /\ y IN s ==> linear (dd2 h y u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `dd2 (h:real^N->real^N) y u =
    frechet_derivative (\z. frechet_derivative h (at z) u) (at y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                   `u:real^N`; `v:real^N`] LRG_DD2_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[dd2];
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`; `y:real^N`; `u:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[]]);;

let GRGT_DH_APPLY_HAS_DERIVATIVE = prove
 (`!s (h:real^N->real^N) (w:real^N->real^N) y.
        open s /\ smooth_map_on s h /\ y IN s /\ w differentiable at y
        ==> ((\z. frechet_derivative h (at z) (w z)) has_derivative
             (\u. dd2 h y u (w y) +
                  frechet_derivative h (at y) (frechet_derivative w (at y) u)))
            (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN s ==> linear(frechet_derivative (h:real^N->real^N) (at z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\z. vsum(1..dimindex(:N))
          (\k. ((w:real^N->real^N) z)$k %
               frechet_derivative (h:real^N->real^N) (at z) (basis k))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(y:real^N,d) SUBSET s` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. dd2 (h:real^N->real^N) y u ((w:real^N->real^N) y) +
         frechet_derivative h (at y) (frechet_derivative w (at y) u)) =
    (\u. vsum(1..dimindex(:N))
           (\k. w y$k % dd2 h y u (basis k) +
                (frechet_derivative w (at y) u)$k %
                frechet_derivative h (at y) (basis k)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^N` THEN
    SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN
    BINOP_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`; `y:real^N`; `u:real^N`]
                    GRGT_DD2_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`dd2 (h:real^N->real^N) y u`;
                     `\i. ((w:real^N->real^N) y)$i % basis i:real^N`;
                     `1..dimindex(:N)`] LINEAR_VSUM) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_CMUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
      ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\z. ((w:real^N->real^N) z)$k`;
    `\u. (frechet_derivative (w:real^N->real^N) (at y) u)$k`;
    `\z. frechet_derivative (h:real^N->real^N) (at z) (basis k)`;
    `\u. dd2 (h:real^N->real^N) y u (basis k)`; `y:real^N`]
   HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN
       `(lift o (\z. ((w:real^N->real^N) z)$k)) = (\x:real^N. lift(x$k)) o w /\
        (lift o (\u. (frechet_derivative (w:real^N->real^N) (at y) u)$k)) =
        (\x:real^N. lift(x$k)) o frechet_derivative w (at y)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT];
      REWRITE_TAC[dd2; ETA_AX] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real^N`; `y:real^N`;
                     `basis k:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC(MESON[]
     `(f:real^N->real^N) = f'
      ==> (g has_derivative f) net ==> (g has_derivative f') net`) THEN
    REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_SYM]]);;

(* The trace is invariant under conjugation. *)

let GRGT_TRACE_CONJ = prove
 (`!(L:real^N->real^N) (J:real^N->real^N) (J':real^N->real^N).
        linear L /\ linear J /\ linear J' /\ (!v. J'(J v) = v)
        ==> sum(1..dimindex(:N)) (\i. (J'(L(J(basis i))))$i) = trace(matrix L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `matrix(J':real^N->real^N) ** matrix(J:real^N->real^N) = mat 1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN `(J':real^N->real^N) o (J:real^N->real^N) = (\x. x)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(matrix(J:real^N->real^N)) /\
                matrix_inv(matrix J) = matrix(J':real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MATRIX_INV_UNIQUE THEN ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. ((J':real^N->real^N)(L(J(basis i))))$i) =
    trace(matrix(J' o (L:real^N->real^N) o (J:real^N->real^N)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT; o_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE] THEN
  UNDISCH_TAC `matrix_inv(matrix(J:real^N->real^N)) = matrix(J':real^N->real^N)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[TRACE_SIMILAR]);;

(* The trace of the matrix of a linear map as a sum of diagonal entries. *)

let GRGT_TRACE_MATRIX = prove
 (`!L:real^N->real^N.
        trace(matrix L) = sum(1..dimindex(:N)) (\i. (L(basis i))$i)`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[MATRIX_COMPONENT]);;

let GRGT_LDIV_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' (G:real^N->real^N^N) (Z0:real^N->real^N) Z1 y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U' /\
        Z0 differentiable at (h y) /\ Z1 differentiable at y /\
        (!z. z IN U' ==> Z0(h z) = frechet_derivative h (at z) (Z1 z))
        ==> ldiv (mpullback h G) Z1 y = ldiv G Z0 (h y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ZZ")))))) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_INV_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (Z0:real^N->real^N) (at (h(y:real^N)))) /\
    linear(frechet_derivative (Z1:real^N->real^N) (at y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. frechet_derivative (Z0:real^N->real^N) (at (h(y:real^N)))
          (frechet_derivative h (at y) u) =
        dd2 h y u ((Z1:real^N->real^N) y) +
        frechet_derivative h (at y) (frechet_derivative Z1 (at y) u)`
  (LABEL_TAC "D1") THENL
   [SUBGOAL_THEN
     `((\z. (Z0:real^N->real^N)(h z)) has_derivative
       (frechet_derivative Z0 (at (h(y:real^N))) o frechet_derivative h (at y)))
      (at y)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\z. (Z0:real^N->real^N)((h:real^N->real^N) z)) = Z0 o h`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\z. (Z0:real^N->real^N)(h z)) has_derivative
       (\u. dd2 h y u ((Z1:real^N->real^N) y) +
            frechet_derivative (h:real^N->real^N) (at y)
              (frechet_derivative Z1 (at y) u))) (at y)`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
        check (fun th -> concl th = `open (U':real^N->bool)`)) THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      EXISTS_TAC `\z. frechet_derivative (h:real^N->real^N) (at z)
                                         ((Z1:real^N->real^N) z)` THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN USE_THEN "ZZ" MATCH_MP_TAC THEN
        UNDISCH_TAC `ball(y:real^N,d) SUBSET U'` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
        MATCH_MP_TAC GRGT_DH_APPLY_HAS_DERIVATIVE THEN
        EXISTS_TAC `U':real^N->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\z. (Z0:real^N->real^N)((h:real^N->real^N) z)`;
      `frechet_derivative (Z0:real^N->real^N) (at (h(y:real^N))) o
       frechet_derivative (h:real^N->real^N) (at y)`;
      `\u. dd2 (h:real^N->real^N) y u ((Z1:real^N->real^N) y) +
           frechet_derivative h (at y) (frechet_derivative Z1 (at y) u)`;
      `y:real^N`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. frechet_derivative (Z1:real^N->real^N) (at y) u +
        christoffel (mpullback (h:real^N->real^N) G) y u (Z1 y) =
        frechet_derivative (h':real^N->real^N) (at (h y))
          (frechet_derivative (Z0:real^N->real^N) (at (h y))
                              (frechet_derivative h (at y) u)) +
        frechet_derivative h' (at (h y))
          (christoffel G (h y) (frechet_derivative h (at y) u) (Z0(h y)))`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `u:real^N` THEN
    SUBGOAL_THEN
     `!a b. frechet_derivative (h:real^N->real^N) (at y) a =
            frechet_derivative h (at y) b ==> a = b`
    MATCH_MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                   `u:real^N`; `(Z1:real^N->real^N) y`] LCHRISTOFFEL_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(Z0:real^N->real^N)(h(y:real^N)) =
      frechet_derivative (h:real^N->real^N) (at y) (Z1 y)`
    ASSUME_TAC THENL
     [USE_THEN "ZZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (h:real^N->real^N) (at y))`
      (fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "D1" (MP_TAC o SPEC `u:real^N`) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ldiv; GRGT_TRACE_MATRIX] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `!i. (frechet_derivative (Z1:real^N->real^N) (at y) (basis i))$i +
        (christoffel (mpullback (h:real^N->real^N) G) y (basis i) (Z1 y))$i =
        (frechet_derivative (h':real^N->real^N) (at (h y))
           (frechet_derivative (Z0:real^N->real^N) (at (h y))
              (frechet_derivative h (at y) (basis i))))$i +
        (frechet_derivative h' (at (h y))
           (christoffel G (h y) (frechet_derivative h (at y) (basis i))
                        (Z0(h y))))$i`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM VECTOR_ADD_COMPONENT] THEN
    USE_THEN "PT" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN BINOP_TAC THENL
   [MP_TAC(ISPECL [`frechet_derivative (Z0:real^N->real^N) (at (h(y:real^N)))`;
                   `frechet_derivative (h:real^N->real^N) (at y)`;
                   `frechet_derivative (h':real^N->real^N) (at (h(y:real^N)))`]
                  GRGT_TRACE_CONJ) THEN
    ASM_REWRITE_TAC[GRGT_TRACE_MATRIX];
    MP_TAC(ISPECL [`\w. christoffel (G:real^N->real^N^N) (h(y:real^N)) w
                                    ((Z0:real^N->real^N) (h y))`;
                   `frechet_derivative (h:real^N->real^N) (at y)`;
                   `frechet_derivative (h':real^N->real^N) (at (h(y:real^N)))`]
                  GRGT_TRACE_CONJ) THEN
    ASM_REWRITE_TAC[GRGT_TRACE_MATRIX] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(h:real^N->real^N) y`]
                    LRG_CHRISTOFFEL_LINEAR) THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]]]);;

(* The chart representatives of a vector field transform with the Jacobian. *)

let GRGT_VREP_TRANS = prove
 (`!top atlas (Z:A->real^N) (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        x IN U INTER V
        ==> mfd_vrep atlas Z (V,psi) (psi x) =
            frechet_derivative (chart_trans (U,phi) (V,psi)) (at (phi x))
              (mfd_vrep atlas Z (U,phi) (phi x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN U /\ x IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[mfd_vrep] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `x:A`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
  DISCH_THEN(MP_TAC o C AP_THM `(Z:A->real^N) x`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[chart_jac; SND]);;

(* mfd_div may be computed in any chart. *)

let GRGT_MFD_DIV_CHART = prove
 (`!top atlas (g:A->real^N^N) (Z:A->real^N) (U:A->bool) (phi:A->real^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (!c. c IN atlas
             ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c)) /\
        (U,phi) IN atlas /\ x IN U
        ==> mfd_div atlas g Z x =
            ldiv (metric_local atlas (U,phi) g) (mfd_vrep atlas Z (U,phi)) (phi x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`
                PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN(LABEL_TAC "CA") THEN USE_THEN "CA" (fun th -> REWRITE_TAC[th; FST]) THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_div] THEN
  USE_THEN "CA" (fun th -> REWRITE_TAC[th; SND]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                CHART_TRANS_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN U INTER V` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi x) = psi x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (phi:A->real^N) (U INTER V)) /\ open (IMAGE (psi:A->real^N) (V INTER U))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (psi:A->real^N) (U INTER V))
                 (metric_local atlas (V,psi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> !y. y IN IMAGE (SND c) (FST c)
                ==> mfd_vrep atlas (Z:A->real^N) c differentiable at y`
  (LABEL_TAC "VD") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
    `mfd_vrep atlas (Z:A->real^N) (V:A->bool,psi:A->real^N)`;
    `mfd_vrep atlas (Z:A->real^N) (U:A->bool,phi:A->real^N)`;
    `(phi:A->real^N) x`] GRGT_LDIV_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      USE_THEN "VD" (MP_TAC o C MATCH_MP (ASSUME `(V:A->bool,psi:A->real^N) IN atlas`)) THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      USE_THEN "VD" (MP_TAC o C MATCH_MP (ASSUME `(U:A->bool,phi:A->real^N) IN atlas`)) THEN
      REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x':A` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi x') = psi x'`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC GRGT_VREP_TRANS THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LDIV_LOCAL THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x':A` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The divergence formula ldiv G Z sqrt(det G) = trace D(sqrt(det G) Z):     *)
(* the contracted Christoffel symbols are half the trace of G^-1 dG, and     *)
(* Jacobi's formula (LRG_DET_DERIV) gives the derivative of sqrt(det G).     *)
(* ------------------------------------------------------------------------- *)

let GRGT_SYM_TRACE_LEMMA = prove
 (`!(Gi:real^N^N) (A:num->num->real) (B:real^N^N).
        (!i j. Gi$i$j = Gi$j$i)
        ==> sum(1..dimindex(:N))
              (\i. sum(1..dimindex(:N))
                     (\j. Gi$i$j * inv(&2) * (A i j + B$j$i - A j i))) =
            inv(&2) * sum(1..dimindex(:N))
                        (\i. sum(1..dimindex(:N)) (\j. Gi$i$j * B$j$i))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `g * h * (a + b - c) = h * (g * b) + h * (g * a - g * c)`] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL] THEN
  REWRITE_TAC[REAL_ARITH `h * x + h * (y - z) = h * x <=> h * (y - z) = &0`] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0] THEN DISJ2_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV) [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let GRGT_CHRISTOFFEL_TRACE = prove
 (`!U (G:real^N->real^N^N) y v.
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N)) (\i. (christoffel G y (basis i) v)$i) =
            inv(&2) * trace(matrix_inv(G y) ** mderiv G y v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. matrix_inv((G:real^N->real^N^N) y)$i$j = matrix_inv(G y)$j$i`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[christoffel; trace] THEN
  SIMP_TAC[matrix_vector_mul; matrix_mul; LAMBDA_BETA] THEN
  MP_TAC(ISPECL
   [`matrix_inv((G:real^N->real^N^N) y)`;
    `\i j. sum(1..dimindex(:N))
              (\j'. mderiv (G:real^N->real^N^N) y (basis i)$j$j' * (v:real^N)$j')`;
    `mderiv (G:real^N->real^N^N) y v`] GRGT_SYM_TRACE_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\j'. mderiv (G:real^N->real^N^N) y v$j$j' *
                               (basis i:real^N)$j') =
    (mderiv G y v ** (basis i:real^N))$j`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA; DOT_BASIS]);;

(* Jacobi's formula for a metric field, and the derivative of the density. *)

let GRGT_DET_FIELD_HAS_DERIVATIVE = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> ((\z. lift(det(G z))) has_derivative
             (\v. lift(det(G y) * trace(matrix_inv(G y) ** mderiv G y v)))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N))
    differentiable at (y:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(det((G:real^N->real^N^N) z))) =
    (\x. lift(det(matrify x:real^N^N))) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)`;
    `\x. lift(det(matrify x:real^N^N))`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         (G:real^N->real^N^N)) (at (y:real^N))`;
    `frechet_derivative (\x. lift(det(matrify x:real^N^N)))
                        (at (((vectorize:real^N^N->real^(N,N)finite_prod) o
                              (G:real^N->real^N^N)) (y:real^N)))`;
    `y:real^N`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; LRG_DET_DIFFERENTIABLE] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^N->real^1) = f'
    ==> (g has_derivative f) net ==> (g has_derivative f') net`) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN
   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        (G:real^N->real^N^N)) (at y) v =
    vectorize(mderiv G y v)`
  SUBST1_TAC THENL [REWRITE_TAC[mderiv; VECTORIZE_MATRIFY]; ALL_TAC] THEN
  REWRITE_TAC[LRG_DET_DERIV; MATRIFY_VECTORIZE] THEN
  ASM_SIMP_TAC[COFACTOR_MATRIX_INV; REAL_LT_IMP_NZ] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MATRIX_CMUL_COMPONENT; TRANSP_COMPONENT; trace] THEN
  SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let GRGT_SQRT_DET_HAS_DERIVATIVE = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> ((\z. lift(sqrt(det(G z)))) has_derivative
             (\v. lift(sqrt(det(G y)) * inv(&2) *
                       trace(matrix_inv(G y) ** mderiv G y v)))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < det((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
    REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                GRGT_DET_FIELD_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `det((G:real^N->real^N^N) y)` HAS_REAL_DERIVATIVE_SQRT) THEN
  ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(sqrt(det((G:real^N->real^N^N) z)))) =
    (lift o sqrt o drop) o (\z. lift(det(G z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. lift(det((G:real^N->real^N^N) z))`; `lift o sqrt o drop`;
    `\v. lift(det((G:real^N->real^N^N) y) * trace(matrix_inv(G y) ** mderiv G y v))`;
    `\x:real^1. inv(&2 * sqrt(det((G:real^N->real^N^N) y))) % x`;
    `y:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^N->real^1) = f'
    ==> (g has_derivative f) net ==> (g has_derivative f') net`) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_CMUL] THEN X_GEN_TAC `v:real^N` THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `&0 < sqrt(det((G:real^N->real^N^N) y)) /\ sqrt(det(G y)) pow 2 = det(G y)`
  MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SPEC_TAC(`sqrt(det((G:real^N->real^N^N) y))`, `r:real`) THEN
  SPEC_TAC(`det((G:real^N->real^N^N) y)`, `d:real`) THEN
  CONV_TAC REAL_FIELD);;

let GRGT_LDIV_DENSITY = prove
 (`!U (G:real^N->real^N^N) (Z:real^N->real^N) y.
        metric_field U G /\ y IN U /\ Z differentiable at y
        ==> ldiv G Z y * sqrt(det(G y)) =
            trace(matrix(frechet_derivative (\z. sqrt(det(G z)) % Z z) (at y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                GRGT_SQRT_DET_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. sqrt(det((G:real^N->real^N^N) z)) % (Z:real^N->real^N) z)
                       (at y) =
    (\h. sqrt(det(G y)) % frechet_derivative Z (at y) h +
         (sqrt(det(G y)) * inv(&2) * trace(matrix_inv(G y) ** mderiv G y h)) % Z y)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL
     [`\z. sqrt(det((G:real^N->real^N^N) z))`;
      `\h. sqrt(det((G:real^N->real^N^N) y)) * inv(&2) *
           trace(matrix_inv(G y) ** mderiv G y h)`;
      `Z:real^N->real^N`; `frechet_derivative (Z:real^N->real^N) (at y)`;
      `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[GRGT_TRACE_MATRIX; ldiv; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(Z:real^N->real^N) y`] GRGT_CHRISTOFFEL_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. (sqrt(det((G:real^N->real^N^N) y)) * inv(&2) *
            trace(matrix_inv(G y) ** mderiv G y (basis i))) * (Z:real^N->real^N) y$i) =
    sqrt(det(G y)) * inv(&2) * trace(matrix_inv(G y) ** mderiv G y (Z y))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR) THEN
    ABBREV_TAC
     `D = \v. lift(sqrt(det((G:real^N->real^N^N) y)) * inv(&2) *
                   trace(matrix_inv(G y) ** mderiv G y v))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!v. sqrt(det((G:real^N->real^N^N) y)) * inv(&2) *
          trace(matrix_inv(G y) ** mderiv G y v) =
          drop((D:real^N->real^1) v)`
    (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DROP_VSUM;
                 DROP_CMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The integral of a divergence vanishes: for V smooth on real^N with        *)
(* compact support, the integral of the i-th partial derivative of V_i is 0, *)
(* since h |-> integral of V_i(y + h e_i) is constant (translation) and may  *)
(* be differentiated under the integral (GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_  *)
(* DOMINATED); hence the integral of trace(DW) over an open set O vanishes   *)
(* for W smooth on O with compact support in O.                              *)
(* ------------------------------------------------------------------------- *)

let GRGT_ZERO_OUTSIDE_DERIV = prove
 (`!(V:real^N->real^M) K y.
        closed K /\ (!z. ~(z IN K) ==> V z = vec 0) /\ ~(y IN K)
        ==> frechet_derivative V (at y) = (\h. vec 0)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\z:real^N. vec 0:real^M` THEN
  UNDISCH_TAC `closed(K:real^N->bool)` THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `ball(y:real^N,d) SUBSET (:real^N) DIFF K` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
  ASM_MESON_TAC[DIST_SYM]);;

let GRGT_CONT_COMPACT_SUPPORT_AI = prove
 (`!(f:real^N->real^M) K.
        f continuous_on (:real^N) /\ compact K /\ (!y. ~(y IN K) ==> f y = vec 0)
        ==> f absolutely_integrable_on (:real^N)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL o
              MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_TAC `b:real^N`)) THEN
  SUBGOAL_THEN `(f:real^N->real^M) absolutely_integrable_on interval[a,b]`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let GRGT_TRANSLATE_DERIV = prove
 (`!(V:real^N->real^N) v x k i.
        V differentiable at (v + x % basis k)
        ==> ((\x. (V(v + x % basis k))$i) has_real_derivative
             (frechet_derivative V (at (v + x % basis k)) (basis k))$i)
            (atreal x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\x. ((V:real^N->real^N)(v + x % basis k))$i) o drop) =
    (\z:real^N. lift(z$i)) o V o (\u:real^1. v + drop u % basis k)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u:real^1. (v:real^N) + drop u % basis k`;
    `(\z:real^N. lift(z$i)) o (V:real^N->real^N)`;
    `\u:real^1. drop u % (basis k:real^N)`;
    `(\z:real^N. lift(z$i)) o frechet_derivative (V:real^N->real^N)
                                (at (v + x % basis k))`;
    `lift x`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[LIFT_DROP; o_ASSOC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\u:real^1. v:real^N`; `\h:real^1. vec 0:real^N`;
                     `\u:real^1. drop u % (basis k:real^N)`;
                     `\u:real^1. drop u % (basis k:real^N)`; `at (lift x)`]
                    HAS_DERIVATIVE_ADD) THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^1) = f'
    ==> (g has_derivative f) net ==> (g has_derivative f') net`) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^1` THEN
  SUBGOAL_THEN `linear(frechet_derivative (V:real^N->real^N) (at (v + x % basis k)))`
  ASSUME_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_COMPONENT] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let GRGT_INTEGRAL_PARTIAL_ZERO = prove
 (`!(V:real^N->real^N) K i.
        smooth_map_on (:real^N) V /\ compact K /\ (!y. ~(y IN K) ==> V y = vec 0) /\
        1 <= i /\ i <= dimindex(:N)
        ==> (\y. lift((frechet_derivative V (at y) (basis i))$i))
              absolutely_integrable_on (:real^N) /\
            integral (:real^N) (\y. lift((frechet_derivative V (at y) (basis i))$i)) =
            vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. (V:real^N->real^N) differentiable at z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = \z. lift((frechet_derivative (V:real^N->real^N) (at z) (basis i))$i)` THEN
  SUBGOAL_THEN `(D:real^N->real^1) continuous_on (:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    SUBGOAL_THEN
     `(\z. lift((frechet_derivative (V:real^N->real^N) (at z) (basis i))$i)) =
      (\x:real^N. lift(x$i)) o (\z. frechet_derivative V (at z) (basis i))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN K) ==> (D:real^N->real^1) z = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    MP_TAC(ISPECL [`V:real^N->real^N`; `K:real^N->bool`; `z:real^N`]
                  GRGT_ZERO_OUTSIDE_DERIV) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; VEC_COMPONENT; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^N->real^1) absolutely_integrable_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GRGT_CONT_COMPACT_SUPPORT_AI THEN
    EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_BALL o
              MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`D:real^N->real^1`; `cball(vec 0:real^N,R + &2)`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV; COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x v. abs x < &1 /\ ~(v IN cball(vec 0:real^N,R + &1))
          ==> ~((v:real^N) + x % basis i IN K)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN STRIP_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `norm((v:real^N) + x % basis i) < R` MP_TAC THENL
     [UNDISCH_TAC `K SUBSET ball(vec 0:real^N,R)` THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(x % basis i:real^N) < &1` MP_TAC THENL
     [ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; REAL_MUL_RID]; ALL_TAC] THEN
    UNDISCH_TAC `R + &1 < norm(v:real^N)` THEN
    SPEC_TAC(`x % basis i:real^N`, `w:real^N`) THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x v. ((V:real^N->real^N)(v + x % basis i))$i`;
    `\x v. drop((D:real^N->real^1)(v + x % basis i))`;
    `\v:real^N. if v IN cball(vec 0,R + &1) then B else &0`;
    `real_interval(--(&1),&1)`; `(:real^N)`]
   GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC GRGT_CONT_COMPACT_SUPPORT_AI THEN
      EXISTS_TAC `IMAGE (\z:real^N. --(x % basis i) + z) K` THEN
      ASM_SIMP_TAC[COMPACT_TRANSLATION] THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `(\v. lift(((V:real^N->real^N)(v + x % basis i))$i)) =
          (\z:real^N. lift(z$i)) o V o (\v. v + x % basis i)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
            REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
            MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
            ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]];
          MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
        X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `~((v:real^N) + x % basis i IN K)` ASSUME_TAC THENL
         [UNDISCH_TAC `~((v:real^N) IN IMAGE (\z. --(x % basis i) + z) K)` THEN
          REWRITE_TAC[IN_IMAGE; CONTRAPOS_THM] THEN DISCH_TAC THEN
          EXISTS_TAC `(v:real^N) + x % basis i` THEN ASM_REWRITE_TAC[] THEN
          VECTOR_ARITH_TAC;
          ASM_SIMP_TAC[VEC_COMPONENT; LIFT_NUM]]];
      REWRITE_TAC[COND_RAND; LIFT_NUM] THEN
      REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST; MEASURABLE_CBALL];
      MAP_EVERY X_GEN_TAC [`x:real`; `v:real^N`] THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      EXPAND_TAC "D" THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC GRGT_TRANSLATE_DERIV THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real`; `v:real^N`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [REWRITE_TAC[ABS_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_CBALL_0] THEN
        UNDISCH_TAC `(v:real^N) IN cball(vec 0,R + &1)` THEN
        REWRITE_TAC[IN_CBALL_0] THEN
        SUBGOAL_THEN `norm(x % basis i:real^N) < &1` MP_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SPEC_TAC(`x % basis i:real^N`, `w:real^N`) THEN CONV_TAC NORM_ARITH;
        SUBGOAL_THEN `(D:real^N->real^1)((v:real^N) + x % basis i) = vec 0`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[DROP_VEC; REAL_ABS_NUM; REAL_LE_REFL]]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_DROP;
              ETA_AX] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; EXISTS_TAC `&1 / &2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `(\x. drop(integral (:real^N) (\v. lift(((V:real^N->real^N)(v + x % basis i))$i)))) =
    (\x. drop(integral (:real^N) (\v. lift((V v)$i))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\z. lift(((V:real^N->real^N) z)$i)`; `(:real^N)`;
                   `x % basis i:real^N`] INTEGRAL_TRANSLATION) THEN
    REWRITE_TAC[TRANSLATION_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[VECTOR_ADD_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_open(real_interval(--(&1),&1)) /\ &0 IN real_interval(--(&1),&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN] THEN
  DISCH_THEN(MP_TAC o C CONJ (ISPECL
   [`drop(integral (:real^N) (\v. lift(((V:real^N->real^N) v)$i)))`; `atreal(&0)`]
   HAS_REAL_DERIVATIVE_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]);;

let GRGT_INTEGRAL_DIVERGENCE_ZERO = prove
 (`!O (W:real^N->real^N) K.
        open O /\ compact K /\ K SUBSET O /\ smooth_map_on O W /\
        (!y. y IN O DIFF K ==> W y = vec 0)
        ==> (\y. lift(trace(matrix(frechet_derivative W (at y)))))
              absolutely_integrable_on O /\
            integral O (\y. lift(trace(matrix(frechet_derivative W (at y))))) =
            vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = \y. if y IN O then (W:real^N->real^N) y else vec 0` THEN
  SUBGOAL_THEN `!z. ~(z IN K) ==> (V:real^N->real^N) z = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "V" THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (V:real^N->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `y:real^N` THEN ASM_CASES_TAC `(y:real^N) IN O` THENL
     [EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `W:real^N->real^N` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN SIMP_TAC[];
      EXISTS_TAC `(:real^N) DIFF K` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:real^N. vec 0:real^N` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV;
                   SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O ==> frechet_derivative (V:real^N->real^N) (at y) =
                   frechet_derivative W (at y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `T0 = \y. lift(trace(matrix(frechet_derivative (V:real^N->real^N) (at y))))` THEN
  SUBGOAL_THEN
   `!i. i IN 1..dimindex(:N)
        ==> (\y. lift((frechet_derivative (V:real^N->real^N) (at y) (basis i))$i))
              absolutely_integrable_on (:real^N) /\
            integral (:real^N)
              (\y. lift((frechet_derivative V (at y) (basis i))$i)) = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC GRGT_INTEGRAL_PARTIAL_ZERO THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(T0:real^N->real^1) absolutely_integrable_on (:real^N) /\
                integral (:real^N) T0 = vec 0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(T0:real^N->real^1) =
      (\y. vsum(1..dimindex(:N))
             (\i. lift((frechet_derivative (V:real^N->real^N) (at y) (basis i))$i)))`
    SUBST1_TAC THENL
     [EXPAND_TAC "T0" THEN REWRITE_TAC[FUN_EQ_THM; GRGT_TRACE_MATRIX; LIFT_SUM; o_DEF];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN ASM_SIMP_TAC[FINITE_NUMSEG];
      ASM_SIMP_TAC[INTEGRAL_VSUM; FINITE_NUMSEG; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                   VSUM_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. ~(y IN K) ==> (T0:real^N->real^1) y = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "T0" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->real^N`; `K:real^N->bool`; `y:real^N`]
                  GRGT_ZERO_OUTSIDE_DERIV) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MATRIX_0; TRACE_0; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> lift(trace(matrix(frechet_derivative (W:real^N->real^N) (at y)))) =
            (T0:real^N->real^1) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "T0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN EXISTS_TAC `T0:real^N->real^1` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `integral O (T0:real^N->real^1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  UNDISCH_TAC `integral (:real^N) (T0:real^N->real^1) = vec 0` THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Smooth partitions of unity on a compact Hausdorff manifold, subordinate   *)
(* to finitely many chart balls: normalized chart bumps (MFDC_BUMP_SMOOTH,   *)
(* MFDC_BUMP_VALUES and MFDC_LOCAL_BALL of pc_mfd_cutoff).                   *)
(* ------------------------------------------------------------------------- *)

let GRGT_MEMBER_LE_SUM = prove
 (`!(f:A->real) s a.
        FINITE s /\ a IN s /\ (!x. x IN s ==> &0 <= f x) ==> f a <= sum s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `s:A->bool`; `a:A`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sum (s DELETE (a:A)) (f:A->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_DELETE]; ASM_REAL_ARITH_TAC]);;

let GRGT_PARTITION_OF_UNITY = prove
 (`!top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top
        ==> ?k (U:num->A->bool) (phi:num->A->real^N) (y0:num->real^N) (r:num->real)
              (rho:num->A->real).
              (!j. j IN 1..k
                   ==> (U j,phi j) IN atlas /\ &0 < r j /\
                       cball(y0 j,&2 * r j) SUBSET IMAGE (phi j) (U j) /\
                       mfd_smooth atlas (\x. lift(rho j x)) /\
                       (!x. ~(x IN U j /\ phi j x IN cball(y0 j,&2 * r j))
                            ==> rho j x = &0)) /\
              (!x. x IN topspace top ==> sum(1..k) (\j. rho j x) = &1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `{{p:A | p IN U /\ phi p IN ball(y,r)} |
     (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\ &0 < r /\
     cball(y:real^N,&2 * r) SUBSET IMAGE phi U}` o
   GEN_REWRITE_RULE I [COMPACT_SPACE_ALT]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN ASM_MESON_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `topspace top:A->bool`; `x:A`] MFDC_LOCAL_BALL) THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
        (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `{p:A | p IN V /\ (psi:A->real^N) p IN ball(psi x,s)}` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC
         [`V:A->bool`; `psi:A->real^N`; `(psi:A->real^N) x`; `s:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `k = CARD(F0:(A->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> ?U phi y r. (U,phi) IN atlas /\ &0 < r /\
                        cball(y:real^N,&2 * r) SUBSET IMAGE (phi:A->real^N) U /\
                        (w:num->A->bool) j = {p | p IN U /\ phi p IN ball(y,r)}`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A->bool) j IN F0` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `(F0:(A->bool)->bool) SUBSET
      {{p:A | p IN U /\ phi p IN ball(y,r)} |
       (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\ &0 < r /\
       cball(y:real^N,&2 * r) SUBSET IMAGE phi U}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:num->A->bool` (X_CHOOSE_THEN `phi:num->A->real^N`
   (X_CHOOSE_THEN `y0:num->real^N` (X_CHOOSE_THEN `r:num->real`
     (LABEL_TAC "W"))))) THEN
  ABBREV_TAC
   `b = \j (x:A). if x IN U j
                  then smooth_bump ((r:num->real) j) (&2 * r j)
                                   ((phi:num->A->real^N) j x - y0 j)
                  else &0` THEN
  SUBGOAL_THEN
   `!j (x:A). j IN 1..k
              ==> &0 <= (b:num->A->real) j x /\ b j x <= &1 /\
                  (x IN (U:num->A->bool) j /\ (phi:num->A->real^N) j x IN ball(y0 j,r j)
                   ==> b j x = &1) /\
                  (~(x IN U j /\ phi j x IN cball(y0 j,&2 * r j)) ==> b j x = &0)`
  (LABEL_TAC "BV") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(U:num->A->bool) j`; `(phi:num->A->real^N) j`;
                   `(y0:num->real^N) j`; `(r:num->real) j`; `x:A`]
                  MFDC_BUMP_VALUES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                       (\x. lift((b:num->A->real) j x))`
  (LABEL_TAC "BS") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC MFDC_BUMP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top ==> &1 <= sum(1..k) (\j. (b:num->A->real) j x)`
  (LABEL_TAC "BP") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?j. j IN 1..k /\ (x:A) IN (w:num->A->bool) j` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `topspace top SUBSET UNIONS (F0:(A->bool)->bool)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(b:num->A->real) j x` THEN CONJ_TAC THENL
     [USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o
                     SPECL [`j:num`; `x:A`]) THEN
      USE_THEN "W" (MP_TAC o last o CONJUNCTS o C MATCH_MP (ASSUME `j IN 1..k`)) THEN
      DISCH_THEN(fun th -> UNDISCH_TAC `(x:A) IN (w:num->A->bool) j` THEN
                           REWRITE_TAC[th; IN_ELIM_THM]) THEN
      MESON_TAC[REAL_LE_REFL];
      MP_TAC(ISPECL [`\i. (b:num->A->real) i x`; `1..k`; `j:num`]
                    GRGT_MEMBER_LE_SUM) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FINITE_NUMSEG]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `U:num->A->bool`; `phi:num->A->real^N`; `y0:num->real^N`;
    `r:num->real`;
    `\j (x:A). (b:num->A->real) j x / sum(1..k) (\i. b i x)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_smooth] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN
      DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\y. lift((b:num->A->real) j (chart_inv (c:(A->bool)#(A->real^N)) y))`;
        `\y. lift(sum(1..k) (\i. (b:num->A->real) i
                                    (chart_inv (c:(A->bool)#(A->real^N)) y)))`]
       SMOOTH_MAP_ON_LIFT_DIV) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "BS" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN
        REWRITE_TAC[mfd_smooth; o_DEF] THEN ASM_SIMP_TAC[];
        REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        USE_THEN "BS" (MP_TAC o C MATCH_MP (ASSUME `i IN 1..k`)) THEN
        REWRITE_TAC[mfd_smooth; o_DEF] THEN ASM_SIMP_TAC[];
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> ~(x = &0)`) THEN
        USE_THEN "BP" MATCH_MP_TAC THEN
        SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` MP_TAC THENL
         [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]]];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o
                     SPECL [`j:num`; `x:A`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[real_div; REAL_MUL_LZERO]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[real_div; SUM_RMUL] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> ~(x = &0)`) THEN
    USE_THEN "BP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Linearity and locality of the divergence: ldiv of a zero field and of a   *)
(* finite sum of fields, chart representatives of f Z and of sums, mfd_div   *)
(* of a field vanishing on an open set; finite sums of integrals.           *)
(* ------------------------------------------------------------------------- *)

let GRGT_LDIV_ZERO = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U ==> ldiv G (\z. vec 0) y = &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ldiv; FRECHET_DERIVATIVE_CONST_AT; MATRIX_0; TRACE_0; REAL_ADD_LID] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. christoffel (G:real^N->real^N^N) y a (vec 0) = vec 0`
    (fun th -> REWRITE_TAC[th; VEC_COMPONENT; SUM_0]) THEN
  X_GEN_TAC `a:real^N` THEN
  MP_TAC(ISPEC `christoffel (G:real^N->real^N^N) y a` LINEAR_0) THEN
  ASM_REWRITE_TAC[]);;

let GRGT_LDIV_VSUM = prove
 (`!U (G:real^N->real^N^N) (V:num->real^N->real^N) k y.
        metric_field U G /\ y IN U /\ (!j. j IN 1..k ==> V j differentiable at y)
        ==> ldiv G (\z. vsum(1..k) (\j. V j z)) y = sum(1..k) (\j. ldiv G (V j) y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ldiv] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. vsum(1..k) (\j. (V:num->real^N->real^N) j z)) (at y) =
    (\h. vsum(1..k) (\j. frechet_derivative (V j) (at y) h))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN
    REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[GRGT_TRACE_MATRIX; VSUM_COMPONENT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; VSUM_COMPONENT] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN BINOP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let GRGT_VREP_LINEAR = prove
 (`!top atlas (Z:A->real^N) (f:A->real) (W:num->A->real^N) k c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_vrep atlas (\x. f x % Z x) c y =
            f(chart_inv c y) % mfd_vrep atlas Z c y /\
            mfd_vrep atlas (\x. vsum(1..k) (\j. W j x)) c y =
            vsum(1..k) (\j. mfd_vrep atlas (W j) c y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear(chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                               (chart_inv (c:(A->bool)#(A->real^N)) y)) c
                     (chart_inv c y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 (chart_inv (c:(A->bool)#(A->real^N)) y))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 (chart_inv (c:(A->bool)#(A->real^N)) y))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `chart_inv (c:(A->bool)#(A->real^N)) y`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_vrep] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_VSUM; FINITE_NUMSEG; o_DEF]);;

let GRGT_MFD_DIV_ZERO_OPEN = prove
 (`!top atlas (g:A->real^N^N) (Z:A->real^N) W x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ x IN W /\ (!z. z IN W ==> Z z = vec 0)
        ==> mfd_div atlas g Z x = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_div] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W))
                 (metric_local atlas c (g:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `ldiv (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
         (\z. vec 0) (SND c x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LDIV_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      REWRITE_TAC[mfd_vrep] THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c z) = z` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `z:A`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `z:A`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
      DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN SIMP_TAC[]];
    MATCH_MP_TAC GRGT_LDIV_ZERO THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]]);;

let GRGT_HAS_INTEGRAL_SUM_ZERO = prove
 (`!top atlas (g:A->real^N^N) (f:num->A->real) S k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (?w. mfd_has_volume (top,atlas) g S w) /\
        (!j. j IN 1..k ==> mfd_has_integral (top,atlas) g (f j) S (&0))
        ==> mfd_has_integral (top,atlas) g (\x. sum(1..k) (\j. f j x)) S (&0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `w:real`) MP_TAC))) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `S:A->bool`; `w:real`; `&0`]
                  MFD_HAS_INTEGRAL_CONST) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `j IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* MFD_DIVERGENCE_THEOREM: on a closed Riemannian manifold the integral of   *)
(* the divergence of a smooth vector field vanishes (the closed case of the  *)
(* divergence theorem, Lee ISM 2nd ed., Chapter 16; no orientation is needed *)
(* with the Riemannian density).  The proof is direct.  A field supported in *)
(* a compact subset of one chart image is handled by the chart formula       *)
(* div(Z) sqrt(det g) = trace D(sqrt(det g) Z) (GRGT_LDIV_DENSITY) and       *)
(* GRGT_INTEGRAL_DIVERGENCE_ZERO; the general field is split by a smooth     *)
(* partition of unity (GRGT_PARTITION_OF_UNITY), using linearity and         *)
(* locality of mfd_div.                                                      *)
(* ------------------------------------------------------------------------- *)

let GRGT_SQRT_DET_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G ==> smooth_map_on U (\z. lift(sqrt(det(G z))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(det((G:real^N->real^N^N) z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[smooth_map_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`U:real^N->bool`; `\z. lift(det((G:real^N->real^N^N) z))`]
                          SMOOTH_MAP_ON_LIFT_SQRT)) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[]);;

let GRGT_VREP_ZERO = prove
 (`!top atlas (Z:A->real^N) c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        y IN IMAGE (SND c) (FST c) /\ Z(chart_inv c y) = vec 0
        ==> mfd_vrep atlas Z c y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                               (chart_inv (c:(A->bool)#(A->real^N)) y))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                               (chart_inv (c:(A->bool)#(A->real^N)) y))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
  REWRITE_TAC[mfd_vrep] THEN ASM_REWRITE_TAC[]);;

let GRGT_DIV_SUPPORTED_ZERO = prove
 (`!top atlas (g:A->real^N^N) (Z:A->real^N) (U:A->bool) (phi:A->real^N) K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas g /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c)) /\
        (U,phi) IN atlas /\ compact K /\ K SUBSET IMAGE phi U /\
        (!x. x IN topspace top /\ ~(x IN U /\ phi x IN K) ==> Z x = vec 0)
        ==> mfd_has_integral (top,atlas) g (mfd_div atlas g Z) (topspace top) (&0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "VS") STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(LABEL_TAC "ZK") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `Kt = {x:A | x IN U /\ (phi:A->real^N) x IN K}` THEN
  SUBGOAL_THEN `compact_in top (Kt:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kt" THEN MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (Kt:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Kt:A->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "Kt" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top DIFF Kt
        ==> mfd_div atlas (g:A->real^N^N) (Z:A->real^N) x = &0`
  (LABEL_TAC "DZ") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGT_MFD_DIV_ZERO_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `topspace top DIFF (Kt:A->bool)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "ZK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((z:A) IN Kt)` THEN EXPAND_TAC "Kt" THEN
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `topspace top = (U:A->bool) UNION (topspace top DIFF U)`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ALL_TAC;
    SET_TAC[]] THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_div atlas (g:A->real^N^N) (Z:A->real^N)`;
                   `(U:A->bool,phi:A->real^N)`; `U:A->bool`; `&0`]
                  MFD_HAS_INTEGRAL_CHART) THEN
    ASM_REWRITE_TAC[FST; SND; SUBSET_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (phi:A->real^N) U)
                   (metric_local atlas (U,phi) (g:A->real^N^N))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (IMAGE (phi:A->real^N) U)
                    (mfd_vrep atlas (Z:A->real^N) (U,phi))`
    ASSUME_TAC THENL
     [USE_THEN "VS" (MP_TAC o C MATCH_MP
        (ASSUME `(U:A->bool,phi:A->real^N) IN atlas`)) THEN
      REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN IMAGE (phi:A->real^N) U
          ==> mfd_chart_integrand atlas (g:A->real^N^N)
                (mfd_div atlas g (Z:A->real^N)) (U,phi) y =
              lift(trace(matrix(frechet_derivative
                (\z. sqrt(det(metric_local atlas (U,phi) g z)) %
                     mfd_vrep atlas Z (U,phi) z) (at y))))`
    (LABEL_TAC "CI") THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[mfd_chart_integrand; mfd_density] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
       `chart_inv (U,phi) y IN (U:A->bool) /\
        (phi:A->real^N)(chart_inv (U,phi) y) = y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `Z:A->real^N`; `U:A->bool`; `phi:A->real^N`;
                     `chart_inv (U:A->bool,phi:A->real^N) y`] GRGT_MFD_DIV_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGT_LDIV_DENSITY THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (IMAGE (phi:A->real^N) U)
        (\z. sqrt(det(metric_local atlas (U,phi) (g:A->real^N^N) z)) %
             mfd_vrep atlas (Z:A->real^N) (U,phi) z)`
    ASSUME_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
       [`IMAGE (phi:A->real^N) U`;
        `\z. lift(sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N)
                                        (g:A->real^N^N) z)))`;
        `mfd_vrep atlas (Z:A->real^N) (U:A->bool,phi:A->real^N)`]
       SMOOTH_MAP_ON_MUL_DROP_OPEN)) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGT_SQRT_DET_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (phi:A->real^N) U`;
      `\z. sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N) z)) %
           mfd_vrep atlas (Z:A->real^N) (U,phi) z`;
      `K:real^N->bool`] GRGT_INTEGRAL_DIVERGENCE_ZERO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `mfd_vrep atlas (Z:A->real^N) (U:A->bool,phi:A->real^N) y = vec 0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
      MATCH_MP_TAC GRGT_VREP_ZERO THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[FST; SND] THEN
      SUBGOAL_THEN
       `chart_inv (U,phi) y IN (U:A->bool) /\
        (phi:A->real^N)(chart_inv (U,phi) y) = y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "ZK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
      EXISTS_TAC
       `\y. lift(trace(matrix(frechet_derivative
              (\z. sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N)
                                         (g:A->real^N^N) z)) %
                   mfd_vrep atlas (Z:A->real^N) (U,phi) z) (at y))))` THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN
       `integral (IMAGE (phi:A->real^N) U)
          (mfd_chart_integrand atlas (g:A->real^N^N)
             (mfd_div atlas g (Z:A->real^N)) (U,phi)) = vec 0`
        (fun th -> REWRITE_TAC[th; DROP_VEC]) THEN
      TRANS_TAC EQ_TRANS
       `integral (IMAGE (phi:A->real^N) U)
          (\y. lift(trace(matrix(frechet_derivative
              (\z. sqrt(det(metric_local atlas (U:A->bool,phi:A->real^N)
                                         (g:A->real^N^N) z)) %
                   mfd_vrep atlas (Z:A->real^N) (U,phi) z) (at y)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN `compact_in top (topspace top DIFF (U:A->bool))` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `topspace top DIFF (U:A->bool)`]
                  MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `topspace top DIFF (U:A->bool)`; `v:real`; `&0`]
                  MFD_HAS_INTEGRAL_CONST) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "DZ" MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let MFD_DIVERGENCE_THEOREM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (Z:A->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas g /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c))
        ==> mfd_has_integral (top,atlas) g (mfd_div atlas g Z) (topspace top) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "VS") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                GRGT_PARTITION_OF_UNITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `U:num->A->bool`
   (X_CHOOSE_THEN `phi:num->A->real^N` (X_CHOOSE_THEN `y0:num->real^N`
    (X_CHOOSE_THEN `r:num->real` (X_CHOOSE_THEN `rho:num->A->real`
     (CONJUNCTS_THEN2 (LABEL_TAC "PU") (LABEL_TAC "SUM1")))))))) THEN
  SUBGOAL_THEN
   `!j c. j IN 1..k /\ c IN atlas
          ==> smooth_map_on (IMAGE (SND c) (FST c))
                (mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x) c)`
  (LABEL_TAC "WS") THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC
     `\y. drop(((\x. lift((rho:num->A->real) j x)) o
                chart_inv (c:(A->bool)#(A->real^N))) y) %
          mfd_vrep atlas (Z:A->real^N) c y` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM; LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Z:A->real^N`; `(rho:num->A->real) j`;
                     `(\i x. vec 0):num->A->real^N`; `0`;
                     `c:(A->bool)#(A->real^N)`; `y:real^N`] GRGT_VREP_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
      USE_THEN "PU" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN
      REWRITE_TAC[mfd_smooth] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> mfd_has_integral (top,atlas) (g:A->real^N^N)
              (mfd_div atlas g (\x. (rho:num->A->real) j x % (Z:A->real^N) x))
              (topspace top) (&0)`
  (LABEL_TAC "IJ") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "PU" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC GRGT_DIV_SUPPORTED_ZERO THEN
    MAP_EVERY EXISTS_TAC
     [`(U:num->A->bool) j`; `(phi:num->A->real^N) j`;
      `cball((y0:num->real^N) j,&2 * (r:num->real) j)`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
     [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      USE_THEN "WS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(rho:num->A->real) j x = &0`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w. mfd_has_volume (top,atlas) (g:A->real^N^N) (topspace top) w`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_COMPACT THEN ASM_REWRITE_TAC[GSYM compact_space];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\j. mfd_div atlas (g:A->real^N^N)
                 (\x. (rho:num->A->real) j x % (Z:A->real^N) x)`;
    `topspace top:A->bool`; `k:num`] GRGT_HAS_INTEGRAL_SUM_ZERO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "IJ" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN REWRITE_TAC[mfd_div] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0))
                 (metric_local atlas c0 (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c0:(A->bool)#(A->real^N)) x IN IMAGE (SND c0) (FST c0)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  TRANS_TAC EQ_TRANS
   `ldiv (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N))
         (\z. vsum(1..k)
                (\j. mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x) c0 z))
         (SND c0 x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LDIV_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!j. mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x) c0 y =
          rho j (chart_inv (c0:(A->bool)#(A->real^N)) y) % mfd_vrep atlas Z c0 y`
    (fun th -> REWRITE_TAC[th]) THENL
     [X_GEN_TAC `j:num` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Z:A->real^N`; `(rho:num->A->real) j`;
                     `(\i x. vec 0):num->A->real^N`; `0`;
                     `c0:(A->bool)#(A->real^N)`; `y:real^N`] GRGT_VREP_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VSUM_RMUL] THEN
    SUBGOAL_THEN
     `sum(1..k) (\j. (rho:num->A->real) j (chart_inv (c0:(A->bool)#(A->real^N)) y)) =
      &1`
    (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    USE_THEN "SUM1" MATCH_MP_TAC THEN
    SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) y IN FST c0` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `FST(c0:(A->bool)#(A->real^N)) SUBSET topspace top` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)`;
    `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
    `\j. mfd_vrep atlas (\x. (rho:num->A->real) j x % (Z:A->real^N) x)
                  (c0:(A->bool)#(A->real^N))`;
    `k:num`; `SND(c0:(A->bool)#(A->real^N)) x`] GRGT_LDIV_VSUM)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "WS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

