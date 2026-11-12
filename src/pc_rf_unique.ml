(* ========================================================================= *)
(* Unit pc_rf_unique (PDE layer): uniqueness of the Ricci flow on a closed   *)
(* manifold by Kotschwar's energy method (arXiv 1206.3225, Sec 1 and the     *)
(* compact case of Sec 2).  Two Ricci flows g1, g2 from the same initial     *)
(* metric; h = g1 - g2, A = Gamma1 - Gamma2 and S = Rm1 - Rm2, lowered and   *)
(* measured with g1; e = |h|^2 + |A|^2 + |S|^2 satisfies                     *)
(* e_t <= div Z + C e (local inequality RFU_KOT_LOCAL), hence by the         *)
(* divergence theorem and Gronwall the energy vanishes.                      *)
(*                                                                           *)
(* First the definitions.  The local tensors are built with two generic      *)
(* lowerings rfu_low3, rfu_low4 of vector valued forms by a metric;          *)
(* rfu_low4 G (lriemann G) is lrm4 G.                                        *)
(* ========================================================================= *)

needs "src/pc_rfa_r1.ml";;
needs "src/pc_grg_divthm.ml";;

prioritize_real();;
type_invention_error := true;;

(* Lowering of a vector valued bilinear form B (slots 1, 2) and of a vector  *)
(* valued trilinear form R (slots 1, 2, 4) by the metric G (slot 3).         *)

let rfu_low3 = new_definition
 `rfu_low3 (G:real^N->real^N^N) (B:real^N->real^N->real^N->real^N) =
    \z (u:num->real^N). u 3 dot (G z ** B z (u 1) (u 2))`;;

let rfu_low4 = new_definition
 `rfu_low4 (G:real^N->real^N^N) (R:real^N->real^N->real^N->real^N->real^N) =
    \z (u:num->real^N). u 3 dot (G z ** R z (u 1) (u 2) (u 4))`;;

(* Differences of the Christoffel symbols and of the (1,3) curvature tensors. *)

let rfu_dgam = new_definition
 `rfu_dgam (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (a:real^N) (b:real^N). christoffel G1 z a b - christoffel G2 z a b`;;

let rfu_drm = new_definition
 `rfu_drm (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (a:real^N) (b:real^N) (d:real^N). lriemann G1 z a b d - lriemann G2 z a b d`;;

(* The three tensors of the Kotschwar density (h, A and a slot permutation   *)
(* of S), and the difference X of the covariant derivatives of the curvature *)
(* 4-tensors, each for its own metric.                                       *)

let rfu_hh = new_definition
 `rfu_hh (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (u:num->real^N). lmetric2 G1 z u - lmetric2 G2 z u`;;

let rfu_aa = new_definition
 `rfu_aa (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    rfu_low3 G1 (rfu_dgam G1 G2)`;;

let rfu_q = new_definition
 `rfu_q (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    rfu_low4 G1 (rfu_drm G1 G2)`;;

let rfu_x = new_definition
 `rfu_x (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (u:num->real^N). lnabla 4 G1 (lrm4 G1) z u - lnabla 4 G2 (lrm4 G2) z u`;;

(* Divergence of a (0,k+1)-tensor in its last slot, and the vector field     *)
(* V^a = g^ab (2 <Q, X(.., e_b)>) of the integration by parts.              *)

let rfu_tdiv = new_definition
 `rfu_tdiv k (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) =
    \y (u:num->real^N).
      sum(1..dimindex(:N))
       (\a. sum(1..dimindex(:N))
         (\b. matrix_inv(G y)$a$b *
              lnabla (k + 1) G X y
                (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                     else u m)))`;;

let rfu_vf = new_definition
 `rfu_vf k (G:real^N->real^N^N) (Q:real^N->(num->real^N)->real)
         (X:real^N->(num->real^N)->real) =
    \z. matrix_inv(G z) **
        ((lambda b. &2 * ltinner k G Q
                           (\z' (u:num->real^N).
                              X z' (\m. if m = k + 1 then basis b else u m)) z)
         :real^N)`;;

(* The local vector field of Kotschwar's inequality. *)

let rfu_kz = new_definition
 `rfu_kz (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    rfu_vf 4 G1 (rfu_q G1 G2) (rfu_x G1 G2)`;;

(* ------------------------------------------------------------------------- *)
(* Basic facts: the density in terms of the three tensors, lrm4 as a         *)
(* lowering, tensor fields and smoothness of the lowerings.                  *)
(* ------------------------------------------------------------------------- *)

let RFU_SWAP34_VALUES = prove
 (`swap(3,4) 1 = 1 /\ swap(3,4) 2 = 2 /\ swap(3,4) 3 = 4 /\ swap(3,4) 4 = 3`,
  REWRITE_TAC[swap] THEN CONV_TAC NUM_REDUCE_CONV);;

let RFU_LRM4_LOW4 = prove
 (`!G:real^N->real^N^N. lrm4 G = rfu_low4 G (lriemann G)`,
  REWRITE_TAC[FUN_EQ_THM; lrm4; rfu_low4]);;

let RFU_KOT_DENSITY = prove
 (`!(G1:real^N->real^N^N) G2 y.
        pde_kot_density G1 G2 y =
        ltnorm2 2 G1 (rfu_hh G1 G2) y + ltnorm2 3 G1 (rfu_aa G1 G2) y +
        ltnorm2 4 G1 (ltperm (swap(3,4)) (rfu_q G1 G2)) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pde_kot_density; rfu_hh; rfu_aa; rfu_q; rfu_low3; rfu_low4;
              rfu_dgam; rfu_drm; ltperm; RFU_SWAP34_VALUES]);;

let RFU_LINEAR_DOT_MATVEC = prove
 (`!(a:real^N) (M:real^N^N) (f:real^N->real^N).
        linear f ==> linear (\v. lift(a dot (M ** f v)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                  DOT_RADD; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

let RFU_LINEAR_DOT_LEFT = prove
 (`!(b:real^N). linear (\v. lift(v dot b))`,
  REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL]);;

let RFU_LOW3_FIELD = prove
 (`!U (G:real^N->real^N^N) B.
        (!z. z IN U ==> bilinear (B z))
        ==> ltensor_field 3 U (rfu_low3 G B)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltensor_field; rfu_low3] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[bilinear] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "l1")) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2 /\ u 3 = u' 3`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH; RFU_LINEAR_DOT_LEFT] THEN
  MATCH_MP_TAC RFU_LINEAR_DOT_MATVEC THENL
   [USE_THEN "l1" (fun th -> REWRITE_TAC[th]);
    USE_THEN "l2" (fun th -> REWRITE_TAC[th])]);;

let RFU_LOW4_FIELD = prove
 (`!U (G:real^N->real^N^N) R.
        (!z. z IN U
             ==> (!b d. linear (\a. R z a b d)) /\ (!a d. linear (\b. R z a b d)) /\
                 (!a b. linear (\d. R z a b d)))
        ==> ltensor_field 4 U (rfu_low4 G R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltensor_field; rfu_low4] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1")
    (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "l3"))) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2 /\ u 3 = u' 3 /\ u 4 = u' 4`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3 \/ i = 4` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ARITH; RFU_LINEAR_DOT_LEFT] THEN
  MATCH_MP_TAC RFU_LINEAR_DOT_MATVEC THENL
   [USE_THEN "l1" (fun th -> REWRITE_TAC[th]);
    USE_THEN "l2" (fun th -> REWRITE_TAC[th]);
    USE_THEN "l3" (fun th -> REWRITE_TAC[th])]);;

let RFU_LOW3_SMOOTH = prove
 (`!U (G:real^N->real^N^N) B.
        metric_field U G /\ (!a b. smooth_map_on U (\z. B z a b))
        ==> !u. smooth_map_on U (\z. lift(rfu_low3 G B z u))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  REWRITE_TAC[rfu_low3] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]);;

let RFU_LOW4_SMOOTH = prove
 (`!U (G:real^N->real^N^N) R.
        metric_field U G /\ (!a b d. smooth_map_on U (\z. R z a b d))
        ==> !u. smooth_map_on U (\z. lift(rfu_low4 G R z u))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  REWRITE_TAC[rfu_low4] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]);;

(* ========================================================================= *)
(* The integration-by-parts identity.  For a (0,k)-tensor Q and              *)
(* a (0,k+1)-tensor X: div V = 2 <Q, div X> + 2 <nabla Q, X> for the vector  *)
(* field V^a = g^ab (2 <Q, X(.., e_b)>) (RFU_DIV_IDENTITY), from the         *)
(* divergence of a raised 1-form (RFU_LDIV_RAISE), the slot expansion of     *)
(* the inner product (RFU_LTINNER_SUC) and metric compatibility.             *)
(* ========================================================================= *)

(* The proof of RFA_LTNORM2_SUC (pc_rfa_rmnorm), for two tensors. *)

let RFU_LTINNER_SUC = prove
 (`!k (G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) tg y.
        ltinner (k + 1) G sf tg y =
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          ltinner k G (\z u. sf z (\m. if m = k + 1 then basis a else u m))
                      (\z u. tg z (\m. if m = k + 1 then basis b else u m)) y))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ltinner; LRG_SUM_INDEX_TUPLES_SUC; RFA_PRODUCT_NUMSEG_LAST] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SIMP_TAC[RFA_SUM4_REORDER; LRG_INDEX_TUPLES_FINITE; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `ip:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `jq:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `product(1..k) (\m. matrix_inv((G:real^N->real^N^N) y)
                         $(if m = k + 1 then a else (ip:num->num) m)
                         $(if m = k + 1 then b else (jq:num->num) m)) =
    product(1..k) (\m. matrix_inv(G y)$(ip m)$(jq m))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN SUBGOAL_THEN `~(m = k + 1)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COND_RAND] THEN CONV_TAC REAL_RING);;

let RFU_TRACE_LINEAR = prove
 (`!f:real^N->real^N.
        linear f ==> trace(matrix f) = sum(1..dimindex(:N)) (\i. f(basis i)$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_TRACE_BASIS] THEN ASM_SIMP_TAC[MATRIX_WORKS]);;

let RFU_FRECHET_COMPONENT = prove
 (`!(w:real^M->real^N) y h a.
        w differentiable at y /\ 1 <= a /\ a <= dimindex(:N)
        ==> drop(frechet_derivative (\z. lift(w z$a)) (at y) h) =
            (frechet_derivative w (at y) h)$a`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[LIFT_DROP]);;

let RFU_SUM3_SWAP23 = prove
 (`!n (f:num->num->num->real).
        sum(1..n) (\b. sum(1..n) (\c. sum(1..n) (\d. f b c d))) =
        sum(1..n) (\b. sum(1..n) (\d. sum(1..n) (\c. f b c d)))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  DISCH_TAC THEN BETA_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[]);;

(* The divergence of the vector field raised from a 1-form w: the trace of   *)
(* the covariant derivative of w.                                            *)

let RFU_LDIV_RAISE = prove
 (`!U (G:real^N->real^N^N) (w:real^N->real^N) y.
    metric_field U G /\ y IN U /\ w differentiable at y
    ==> ldiv G (\z. matrix_inv(G z) ** w z) y =
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          ((frechet_derivative w (at y) (basis b))$a -
           sum(1..dimindex(:N)) (\c. (christoffel G y (basis b) (basis a))$c * w y$c))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `((\z. matrix_inv((G:real^N->real^N^N) z) ** (w:real^N->real^N) z) has_derivative
     (\h. --(matrix_inv(G y) ** mderiv G y h ** matrix_inv(G y)) ** w y +
          matrix_inv(G y) ** frechet_derivative w (at y) h)) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `y:real^N`]
                  LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; DISCH_TAC] THEN
    MP_TAC(ISPECL
     [`\z. matrix_inv((G:real^N->real^N^N) z)`;
      `\h. (vectorize:real^N^N->real^(N,N)finite_prod)
             (--(matrix_inv((G:real^N->real^N^N) y) **
                 matrify(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                                            (at y) h) ** matrix_inv(G y)))`;
      `w:real^N->real^N`; `frechet_derivative (w:real^N->real^N) (at y)`; `y:real^N`]
     LRG_HAS_DERIVATIVE_MATVEC) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; MATRIFY_VECTORIZE; GSYM mderiv];
    ALL_TAC] THEN
  REWRITE_TAC[ldiv] THEN
  FIRST_ASSUM(fun th -> SUBST1_TAC(SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)) THEN
                        ASSUME_TAC(MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR th)) THEN
  ASM_SIMP_TAC[RFU_TRACE_LINEAR] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CL") THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. christoffel (G:real^N->real^N^N) y (basis i)
             (matrix_inv (G y) ** (w:real^N->real^N) y)$i) =
    sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
       matrix_inv(G y)$d$c * (christoffel G y (basis i) (basis d))$i * w y$c)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "CL" (MP_TAC o SPEC `basis b:real^N` o CONJUNCT1) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL
      [`matrix_inv((G:real^N->real^N^N) y) ** (w:real^N->real^N) y`; `b:num`]
      (MATCH_MP LINEAR_COMPONENTWISE_EXPANSION th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; GSYM SUM_RMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (--(matrix_inv((G:real^N->real^N^N) y) ** mderiv G y (basis i) **
                matrix_inv (G y)) ** (w:real^N->real^N) y +
             matrix_inv (G y) ** frechet_derivative w (at y) (basis i))$i =
            sum(1..dimindex(:N))
              (\a. matrix_inv(G y)$i$a * (frechet_derivative w (at y) (basis i))$a) -
            (sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
               matrix_inv(G y)$i$d * (christoffel G y (basis i) (basis d))$c * w y$c)) +
             sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
               matrix_inv(G y)$d$c * (christoffel G y (basis i) (basis d))$i * w y$c)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG] THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT;
                 MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\j. (matrix_inv((G:real^N->real^N^N) y) ** mderiv G y (basis i) **
              matrix_inv (G y))$i$j * (w:real^N->real^N) y$j) =
      sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
        matrix_inv(G y)$i$d * (christoffel G y (basis i) (basis d))$c * w y$c)) +
      sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
        matrix_inv(G y)$d$c * (christoffel G y (basis i) (basis d))$i * w y$c))`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                     `basis i:real^N`; `i:num`; `c:num`] LRG_GINV_MDERIV_GINV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL; GSYM REAL_MUL_ASSOC] THEN
      REWRITE_TAC[SUM_ADD_NUMSEG];
      REWRITE_TAC[REAL_ARITH `!a b c:real. --(a + b) + c = c - (a + b)`]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SUM_EQ_NUMSEG) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N))
       (\a. matrix_inv((G:real^N->real^N^N) y)$i$a *
             (frechet_derivative (w:real^N->real^N) (at y) (basis i))$a)) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b * (frechet_derivative w (at y) (basis b))$a))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[LRG_MATRIX_INV_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
       matrix_inv((G:real^N->real^N^N) y)$i$d * (christoffel G y (basis i) (basis d))$c *
       (w:real^N->real^N) y$c))) =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b *
       sum(1..dimindex(:N)) (\c. (christoffel G y (basis b) (basis a))$c * w y$c)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [RFU_SUM3_SWAP23] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `matrix_inv((G:real^N->real^N^N) y)$d$i = matrix_inv(G y)$i$d`
    SUBST1_TAC THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG] THEN REAL_ARITH_TAC);;

(* The covariant derivative of X with its last slot fixed to a basis vector. *)

let RFU_LNABLA_XB = prove
 (`!k U (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) y a b u.
        open U /\ ltensor_field (k + 1) U X /\ y IN U
        ==> lnabla k G (\z u. X z (\m. if m = k + 1 then basis a else u m)) y
                       (\m. if m = k + 1 then basis b else u m) =
            lnabla (k + 1) G X y
              (\m. if m = k + 1 then basis a else if m = k + 2 then basis b else u m) +
            sum(1..dimindex(:N))
              (\c. (christoffel G y (basis b) (basis a))$c *
                   X y (\m. if m = k + 1 then basis c else u m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `basis a:real^N`; `y:real^N`;
                 `\m. if m = k + 1 then basis b else (u:num->real^N) m`]
                RFA_LNABLA_FIX_SLOT) THEN
  ASM_REWRITE_TAC[RFA_COND_NEST; RFA_COND_NEST2] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LRG_SLOT_EXPAND THEN
  UNDISCH_TAC `ltensor_field (k + 1) U (X:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ARITH_TAC);;

(* The integration-by-parts identity behind the energy inequality. *)

let RFU_DIV_IDENTITY = prove
 (`!k U (G:real^N->real^N^N) (Q:real^N->(num->real^N)->real) X y.
        metric_field U G /\ y IN U /\
        ltensor_field k U Q /\ (!u. smooth_map_on U (\z. lift(Q z u))) /\
        ltensor_field (k + 1) U X /\ (!u. smooth_map_on U (\z. lift(X z u)))
        ==> ldiv G (rfu_vf k G Q X) y =
            &2 * ltinner k G Q (rfu_tdiv k G X) y +
            &2 * ltinner (k + 1) G (lnabla k G Q) X y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. ltensor_field k U
          (\z u. (X:real^N->(num->real^N)->real) z
                   (\m. if m = k + 1 then basis c else u m)) /\
        (!u. smooth_map_on U (\z. lift(X z (\m. if m = k + 1 then basis c else u m))))`
  (LABEL_TAC "XB") THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_FIX_SLOT_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. smooth_map_on U
          (\z. lift(&2 * ltinner k (G:real^N->real^N^N) Q
                   (\z' u. (X:real^N->(num->real^N)->real) z'
                             (\m. if m = k + 1 then basis c else u m)) z))`
  (LABEL_TAC "SM") THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LTINNER_SMOOTH THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "XB" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (lambda b. &2 * ltinner k (G:real^N->real^N^N) Q
                   (\z' u. (X:real^N->(num->real^N)->real) z'
                             (\m. if m = k + 1 then basis b else u m)) z):real^N)
    differentiable at y`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [DIFFERENTIABLE_COMPONENTWISE_AT] THEN X_GEN_TAC `c:num` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "SM" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[rfu_vf] THEN
  MP_TAC(ISPECL
   [`U:real^N->bool`; `G:real^N->real^N^N`;
    `\z. (lambda b. &2 * ltinner k (G:real^N->real^N^N) Q
                   (\z' u. (X:real^N->(num->real^N)->real) z'
                             (\m. if m = k + 1 then basis b else u m)) z):real^N`;
    `y:real^N`] RFU_LDIV_RAISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> (frechet_derivative
                (\z. (lambda c. &2 * ltinner k (G:real^N->real^N^N) Q
                        (\z' u. (X:real^N->(num->real^N)->real) z'
                                  (\m. if m = k + 1 then basis c else u m)) z):real^N)
                (at y) (basis b))$a -
              sum(1..dimindex(:N))
                (\c. (christoffel G y (basis b) (basis a))$c *
                     ((lambda c. &2 * ltinner k G Q
                        (\z' u. X z' (\m. if m = k + 1 then basis c else u m)) y):real^N)$c) =
              &2 * ltinner k G (\z u. lnabla k G Q z (\m. if m = k + 1 then basis b else u m))
                     (\z' u. X z' (\m. if m = k + 1 then basis a else u m)) y +
              &2 * ltinner k G Q
                     (\z' u. lnabla (k + 1) G X z'
                        (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                             else u m)) y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\z. (lambda c. &2 * ltinner k (G:real^N->real^N^N) Q
                        (\z' u. (X:real^N->(num->real^N)->real) z'
                                  (\m. if m = k + 1 then basis c else u m)) z):real^N`;
      `y:real^N`; `basis b:real^N`; `a:num`] RFU_FRECHET_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[LAMBDA_BETA; ETA_AX] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
      `\z. ltinner k (G:real^N->real^N^N) Q
             (\z' u. (X:real^N->(num->real^N)->real) z'
                       (\m. if m = k + 1 then basis a else u m)) z`;
      `&2`; `y:real^N`; `basis b:real^N`] RFA_FRECHET_LIFT_CMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LTINNER_SMOOTH THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "XB" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
      `Q:real^N->(num->real^N)->real`;
      `\z' u. (X:real^N->(num->real^N)->real) z'
               (\m. if m = k + 1 then basis a else u m)`;
      `y:real^N`; `basis b:real^N`] RFA_LTINNER_MC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "XB" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `ltinner k (G:real^N->real^N^N) Q
        (\z u. lnabla k G (\z u. (X:real^N->(num->real^N)->real) z
                            (\m. if m = k + 1 then basis a else u m)) z
                 (\m. if m = k + 1 then basis b else u m)) y =
      ltinner k G Q
        (\z' u. lnabla (k + 1) G X z'
                 (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                      else u m)) y +
      sum(1..dimindex(:N))
        (\c. (christoffel G y (basis b) (basis a))$c *
             ltinner k G Q (\z' u. X z' (\m. if m = k + 1 then basis c else u m)) y)`
    SUBST1_TAC THENL
     [TRANS_TAC EQ_TRANS
       `ltinner k (G:real^N->real^N^N) Q
          (\z' u. lnabla (k + 1) G (X:real^N->(num->real^N)->real) z'
                   (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                        else u m) +
                 sum(1..dimindex(:N))
                   (\c. (christoffel G y (basis b) (basis a))$c *
                        X z' (\m. if m = k + 1 then basis c else u m))) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN X_GEN_TAC `u:num->real^N` THEN
        BETA_TAC THEN MATCH_MP_TAC RFU_LNABLA_XB THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[RFA_LTINNER_RADD; RFA_LTINNER_RSUM; FINITE_NUMSEG;
                 RFA_LTINNER_RCMUL]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\c. (christoffel (G:real^N->real^N^N) y (basis b) (basis a))$c * &2 *
             ltinner k G Q
               (\z' u. (X:real^N->(num->real^N)->real) z'
                         (\m. if m = k + 1 then basis c else u m)) y) =
      &2 * sum(1..dimindex(:N))
        (\c. (christoffel G y (basis b) (basis a))$c *
             ltinner k G Q (\z' u. X z' (\m. if m = k + 1 then basis c else u m)) y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "S4") THEN
  TRANS_TAC EQ_TRANS
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv((G:real^N->real^N^N) y)$a$b *
      (&2 * ltinner k G (\z u. lnabla k G Q z (\m. if m = k + 1 then basis b else u m))
              (\z' u. (X:real^N->(num->real^N)->real) z'
                        (\m. if m = k + 1 then basis a else u m)) y +
       &2 * ltinner k G Q
              (\z' u. lnabla (k + 1) G X z'
                 (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                      else u m)) y)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN USE_THEN "S4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltinner k (G:real^N->real^N^N) Q (rfu_tdiv k G X) y =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv(G y)$a$b *
      ltinner k G Q
        (\z' u. lnabla (k + 1) G (X:real^N->(num->real^N)->real) z'
           (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                else u m)) y))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ltinner k (G:real^N->real^N^N) Q
        (\z' u. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           lnabla (k + 1) G (X:real^N->(num->real^N)->real) z'
             (\m. if m = k + 1 then basis a else if m = k + 2 then basis b
                  else u m)))) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN REWRITE_TAC[rfu_tdiv];
      SIMP_TAC[RFA_LTINNER_RSUM; FINITE_NUMSEG; RFA_LTINNER_RCMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltinner (k + 1) (G:real^N->real^N^N) (lnabla k G Q) X y =
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
      matrix_inv(G y)$a$b *
      ltinner k G (\z u. lnabla k G Q z (\m. if m = k + 1 then basis b else u m))
        (\z' u. (X:real^N->(num->real^N)->real) z'
                  (\m. if m = k + 1 then basis a else u m)) y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RFU_LTINNER_SUC] THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    BINOP_TAC THENL [ASM_MESON_TAC[LRG_MATRIX_INV_SYM]; REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_MUL_AC] THEN REWRITE_TAC[REAL_ADD_AC]);;

(* ========================================================================= *)
(* Time derivatives along two local Ricci flows.  rfu_bev is                 *)
(* the reaction term of RFA_LRM4_EVOLUTION (d/dt Rm = Lap Rm + B(Rm,Rm)).   *)
(* The time derivatives of h, A and Q are given by explicit single-slice    *)
(* formulas rfu_hhdot, rfu_aadot, rfu_qdot (RFU_HH_DT, RFU_AA_DT,            *)
(* RFU_Q_DT).                                                                *)
(* ========================================================================= *)

let rfu_bev = new_definition
 `rfu_bev:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
          (real^N->(num->real^N)->real)->real^N->(num->real^N)->real =
    @B. lbilin 4 4 4 B /\
        !U a b (G:real->real^N->real^N^N) t y u.
          lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
          ==> ((\s. lrm4 (G s) y u) has_real_derivative
               ltlap 4 (G t) (lrm4 (G t)) y u + B (G t) (lrm4 (G t)) (lrm4 (G t)) y u)
              (atreal t)`;;

let RFU_BEV = prove
 (`lbilin 4 4 4 (rfu_bev:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
                         (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) /\
   !U a b (G:real->real^N->real^N^N) t y u.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. lrm4 (G s) y u) has_real_derivative
          ltlap 4 (G t) (lrm4 (G t)) y u + rfu_bev (G t) (lrm4 (G t)) (lrm4 (G t)) y u)
         (atreal t)`,
  REWRITE_TAC[rfu_bev] THEN CONV_TAC SELECT_CONV THEN
  MATCH_ACCEPT_TAC RFA_LRM4_EVOLUTION);;

(* The combination of covariant derivatives of Ric in the evolution of the   *)
(* Christoffel symbols (LCHRISTOFFEL_EVOLUTION, with r the lowered slot).    *)

let rfu_lc = new_definition
 `rfu_lc (G:real^N->real^N^N) (y:real^N) (p:real^N) (q:real^N) (r:real^N) =
    lnabla 2 G (lric2 G) y (\m. if m = 1 then q else if m = 2 then r else p) +
    lnabla 2 G (lric2 G) y (\m. if m = 1 then p else if m = 2 then r else q) -
    lnabla 2 G (lric2 G) y (\m. if m = 1 then p else if m = 2 then q else r)`;;

(* The explicit time derivatives (single time slice, metrics G1, G2). *)

let rfu_hhdot = new_definition
 `rfu_hhdot (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (u:num->real^N). --(&2) * lricci G1 z (u 1) (u 2) + &2 * lricci G2 z (u 1) (u 2)`;;

let rfu_aadot = new_definition
 `rfu_aadot (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (u:num->real^N).
      --(&2) * lricci G1 z (u 3) (rfu_dgam G1 G2 z (u 1) (u 2)) -
      rfu_lc G1 z (u 1) (u 2) (u 3) +
      rfu_lc G2 z (u 1) (u 2) (matrix_inv(G2 z) ** G1 z ** u 3)`;;

let rfu_qdot = new_definition
 `rfu_qdot (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (u:num->real^N).
      (ltlap 4 G1 (lrm4 G1) z u + rfu_bev G1 (lrm4 G1) (lrm4 G1) z u) -
      (ltlap 4 G2 (lrm4 G2) z
         (\m. if m = 3 then matrix_inv(G2 z) ** G1 z ** u 3 else u m) +
       rfu_bev G2 (lrm4 G2) (lrm4 G2) z
         (\m. if m = 3 then matrix_inv(G2 z) ** G1 z ** u 3 else u m)) +
      &2 * lricci G1 z (u 3) (lriemann G2 z (u 1) (u 2) (u 4)) -
      &2 * lricci G2 z (matrix_inv(G2 z) ** G1 z ** u 3)
                   (lriemann G2 z (u 1) (u 2) (u 4))`;;

(* ------------------------------------------------------------------------- *)
(* Real derivatives from vector derivatives.                                 *)
(* ------------------------------------------------------------------------- *)

let RFU_VDERIV_LIFT_REAL = prove
 (`!(f:real->real) f' t.
        ((\s. lift(f(drop s))) has_vector_derivative lift f') (at (lift t))
        ==> (f has_real_derivative f') (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
  ASM_REWRITE_TAC[]);;

let RFU_DOT_DT = prove
 (`!(A:real->real^N^N) A1 (b:real->real^N) b1 a t.
        ((\s. vectorize(A(drop s))) has_vector_derivative vectorize A1) (at (lift t)) /\
        ((\s. b(drop s)) has_vector_derivative b1) (at (lift t))
        ==> ((\s. a dot (A s ** b s)) has_real_derivative
             (a dot (A1 ** b t) + a dot (A t ** b1))) (atreal t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_VDERIV_LIFT_REAL THEN
  MP_TAC(ISPECL [`\s. (A:real->real^N^N)(drop s)`; `A1:real^N^N`;
                 `\s. (b:real->real^N)(drop s)`; `b1:real^N`; `a:real^N`;
                 `lift t`] LRG_VDERIV_DOT_PRODUCT) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let RFU_FLOW_METRIC = prove
 (`!U a b (G:real->real^N->real^N^N) t.
        lricci_flow U a b G /\ a < t /\ t < b ==> metric_field U (G t) /\ open U`,
  REWRITE_TAC[lricci_flow] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The time derivative of the (1,3) curvature vector of one local flow, in   *)
(* terms of the evolution of lrm4.                                           *)
(* ------------------------------------------------------------------------- *)

let RFU_RIEMANN_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y (u:num->real^N).
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ?rd. ((\s. lriemann (G (drop s)) y (u 1) (u 2) (u 4)) has_vector_derivative rd)
                 (at (lift t)) /\
                 !c. 1 <= c /\ c <= dimindex(:N)
                     ==> (G t y ** rd)$c =
                         ltlap 4 (G t) (lrm4 (G t)) y
                           (\m. if m = 3 then basis c else u m) +
                         rfu_bev (G t) (lrm4 (G t)) (lrm4 (G t)) y
                           (\m. if m = 3 then basis c else u m) +
                         &2 * lricci (G t) y (basis c) (lriemann (G t) y (u 1) (u 2) (u 4))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`;
                `(u:num->real^N) 4`] LRG_FLOW_DRIEMANN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN SPEC_TAC(rand(rator(concl th)),`rd:real^N`)) THEN
  X_GEN_TAC `rd:real^N` THEN DISCH_TAC THEN EXISTS_TAC `rd:real^N` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (G:real->real^N->real^N^N) s y`;
                 `(lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                          (basis i) (basis j)):real^N^N`;
                 `\s. lriemann ((G:real->real^N->real^N^N) s) y ((u:num->real^N) 1)
                         (u 2) (u 4)`; `rd:real^N`;
                 `basis c:real^N`; `t:real`] RFU_DOT_DT) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                `t:real`; `y:real^N`] LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  MP_TAC(CONJUNCT2 (INST_TYPE [`:N`,`:N`] RFU_BEV)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`; `t:real`;
    `y:real^N`; `\m. if m = 3 then basis c else (u:num->real^N) m`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\s. lrm4 ((G:real->real^N->real^N^N) s) y
          (\m. if m = 3 then basis c else (u:num->real^N) m)) =
    (\s. basis c dot (G s y ** lriemann (G s) y (u 1) (u 2) (u 4)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lrm4] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\s. basis c dot ((G:real->real^N->real^N^N) s y **
                      lriemann (G s) y ((u:num->real^N) 1) (u 2) (u 4))`;
    `t:real`] REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`basis c dot ((lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                          (basis i) (basis j)):real^N^N **
                   lriemann (G t) y ((u:num->real^N) 1) (u 2) (u 4)) +
     basis c dot (G t y ** rd)`;
    `ltlap 4 ((G:real->real^N->real^N^N) t) (lrm4 (G t)) y
       (\m. if m = 3 then basis c else (u:num->real^N) m) +
     rfu_bev (G t) (lrm4 (G t)) (lrm4 (G t)) y
       (\m. if m = 3 then basis c else u m)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`] RFU_FLOW_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `basis c:real^N`;
                 `lriemann ((G:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) (u 4)`]
                LRG_HDOT) THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Algebraic helpers.                                                        *)
(* ------------------------------------------------------------------------- *)

let RFU_DOT_SYMMAT = prove
 (`!(G:real^N^N) x y. transp G = G ==> x dot (G ** y) = (G ** x) dot y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_REWRITE_TAC[]);;

let RFU_MINV_TRANSFER = prove
 (`!(G1:real^N^N) G2 x y.
        transp G1 = G1 /\ transp G2 = G2 /\ ~(det G2 = &0)
        ==> x dot (G1 ** y) = (matrix_inv G2 ** G1 ** x) dot (G2 ** y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(matrix_inv (G2:real^N^N) ** (G1:real^N^N) ** (x:real^N)) dot
                (G2 ** (y:real^N)) =
                (G2 ** matrix_inv G2 ** G1 ** x) dot y`
  SUBST1_TAC THENL [ASM_MESON_TAC[RFU_DOT_SYMMAT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_MUL_RINV; MATRIX_MUL_LID] THEN
  ASM_MESON_TAC[RFU_DOT_SYMMAT]);;

let RFU_T4_SLOT3 = prove
 (`!U (Tf:real^N->(num->real^N)->real) y u (c:real^N).
        ltensor_field 4 U Tf /\ y IN U
        ==> sum(1..dimindex(:N)) (\k. c$k * Tf y (\m. if m = 3 then basis k else u m)) =
            Tf y (\m. if m = 3 then c else u m)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_SLOT_EXPAND THEN
  UNDISCH_TAC `ltensor_field 4 U (Tf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ARITH_TAC);;

let RFU_TUPLE3_ID = prove
 (`!u:num->real^N. (\m. if m = 3 then u 3 else u m) = u`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let RFU_LRICCI_LIN1 = prove
 (`!U (G:real^N->real^N^N) y (c:real^N) w.
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N)) (\k. c$k * lricci G y (basis k) w) = lricci G y c w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N` o MATCH_MP LRG_LINEAR_DROP_EXPAND) THEN
  REWRITE_TAC[LIFT_DROP]);;

let RFU_LRICCI_SUB2 = prove
 (`!U (G:real^N->real^N^N) y p v w.
        metric_field U G /\ y IN U
        ==> lricci G y p (v - w) = lricci G y p v - lricci G y p w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:real^N` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o MATCH_MP LINEAR_SUB) THEN
  REWRITE_TAC[LIFT_SUB; GSYM LIFT_EQ; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* Time derivatives of h and of the quadratic forms of a flow.               *)
(* ------------------------------------------------------------------------- *)

let RFU_QFORM_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y p q.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. p dot (G s y ** q)) has_real_derivative
             --(&2) * lricci (G t) y p q) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (G:real->real^N->real^N^N) s y`;
                 `(lambda i j. --(&2) * lricci ((G:real->real^N->real^N^N) t) y
                                          (basis i) (basis j)):real^N^N`;
                 `\s:real. q:real^N`; `vec 0:real^N`; `p:real^N`; `t:real`] RFU_DOT_DT) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                `t:real`; `y:real^N`] LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_RID] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`] RFU_FLOW_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `p:real^N`; `q:real^N`] LRG_HDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let RFU_HH_DT = prove
 (`!U a b (G1:real->real^N->real^N^N) G2 t y u.
        lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U
        ==> ((\s. rfu_hh (G1 s) (G2 s) y u) has_real_derivative
             rfu_hhdot (G1 t) (G2 t) y u) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_hh; rfu_hhdot; lmetric2] THEN
  MATCH_MP_TAC(MESON[]
   `!f f' g. (f has_real_derivative g) (atreal t) /\ g = f'
             ==> (f has_real_derivative f') (atreal t)`) THEN
  EXISTS_TAC `--(&2) * lricci ((G1:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) -
              --(&2) * lricci ((G2:real->real^N->real^N^N) t) y (u 1) (u 2)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC RFU_QFORM_DT THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The time derivative of A.                                                 *)
(* ------------------------------------------------------------------------- *)

let RFU_METRIC_PROPS = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> open U /\ transp(G y) = G y /\ ~(det(G y) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[metric_field]; ASM_MESON_TAC[metric_field];
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]]);;

let RFU_LC_LIN3 = prove
 (`!U (G:real^N->real^N^N) y p q (c:real^N).
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N)) (\k. c$k * rfu_lc G y p q (basis k)) = rfu_lc G y p q c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 3 U (lnabla 2 (G:real^N->real^N^N) (lric2 G))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_N2_FIELD]; ALL_TAC] THEN
  REWRITE_TAC[rfu_lc; REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; SUM_ADD_NUMSEG;
              SUM_SUB_NUMSEG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `y:real^N`; `c:real^N`; `q:real^N`; `p:real^N`] LRG_TUPLE3_SLOT2) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `y:real^N`; `c:real^N`; `p:real^N`; `q:real^N`] LRG_TUPLE3_SLOT2) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `y:real^N`; `c:real^N`; `p:real^N`; `q:real^N`] LRG_TUPLE3_SLOT3) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

let RFU_AA_DT = prove
 (`!U a b (G1:real->real^N->real^N^N) G2 t y u.
        lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U
        ==> ((\s. rfu_aa (G1 s) (G2 s) y u) has_real_derivative
             rfu_aadot (G1 t) (G2 t) y u) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_aa; rfu_low3; rfu_dgam] THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                `t:real`] RFU_FLOW_METRIC) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G2:real->real^N->real^N^N`;
                `t:real`] RFU_FLOW_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`]
                RFU_METRIC_PROPS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G2:real->real^N->real^N^N) t`; `y:real^N`]
                RFU_METRIC_PROPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`]
               LCHRISTOFFEL_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W1"))) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G2:real->real^N->real^N^N`;
                `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`]
               LCHRISTOFFEL_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W2"))) THEN
  MP_TAC(ISPECL [`\s. (G1:real->real^N->real^N^N) s y`;
                 `(lambda i j. --(&2) * lricci ((G1:real->real^N->real^N^N) t) y
                                          (basis i) (basis j)):real^N^N`;
                 `\s. christoffel ((G1:real->real^N->real^N^N) s) y ((u:num->real^N) 1) (u 2) -
                      christoffel ((G2:real->real^N->real^N^N) s) y (u 1) (u 2)`;
                 `w1 - w2:real^N`; `(u:num->real^N) 3`; `t:real`] RFU_DOT_DT) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                `t:real`; `y:real^N`] LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!f f' g. g = f' ==> (f has_real_derivative g) (atreal t)
             ==> (f has_real_derivative f') (atreal t)`) THEN
  SUBGOAL_THEN
   `(u:num->real^N) 3 dot ((G1:real->real^N->real^N^N) t y ** w1) =
    --(rfu_lc (G1 t) y (u 1) (u 2) (u 3))`
  ASSUME_TAC THENL
   [REWRITE_TAC[dot] THEN
    SUBGOAL_THEN
     `!k. 1 <= k /\ k <= dimindex(:N)
          ==> (u:num->real^N) 3$k * ((G1:real->real^N->real^N^N) t y ** w1)$k =
              --((u 3)$k * rfu_lc (G1 t) y (u 1) (u 2) (basis k))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_lc] THEN ASM_SIMP_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N))
        (\k. --(((u:num->real^N) 3)$k *
                rfu_lc ((G1:real->real^N->real^N^N) t) y (u 1) (u 2) (basis k)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_NEG] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RFU_LC_LIN3 THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:num->real^N) 3 dot ((G1:real->real^N->real^N^N) t y ** w2) =
    --(rfu_lc ((G2:real->real^N->real^N^N) t) y (u 1) (u 2)
         (matrix_inv(G2 t y) ** G1 t y ** u 3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(G1:real->real^N->real^N^N) t y`; `(G2:real->real^N->real^N^N) t y`;
                   `(u:num->real^N) 3`; `w2:real^N`] RFU_MINV_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[dot] THEN
    SUBGOAL_THEN
     `!k. 1 <= k /\ k <= dimindex(:N)
          ==> (matrix_inv((G2:real->real^N->real^N^N) t y) **
               (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3)$k *
              (G2 t y ** w2)$k =
              --((matrix_inv(G2 t y) ** G1 t y ** u 3)$k *
                 rfu_lc (G2 t) y (u 1) (u 2) (basis k))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_lc] THEN ASM_SIMP_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N))
        (\k. --((matrix_inv((G2:real->real^N->real^N^N) t y) **
                 (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3)$k *
                rfu_lc (G2 t) y (u 1) (u 2) (basis k)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_NEG] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RFU_LC_LIN3 THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`;
                 `(u:num->real^N) 3`;
                 `christoffel ((G1:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) -
                  christoffel ((G2:real->real^N->real^N^N) t) y (u 1) (u 2)`] LRG_HDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[rfu_aadot; rfu_dgam; MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The time derivative of Q (the slot permutation of S).                     *)
(* ------------------------------------------------------------------------- *)

let RFU_EVOL_FIELDS = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 4 U (ltlap 4 G (lrm4 G)) /\
            ltensor_field 4 U (rfu_bev G (lrm4 G) (lrm4 G))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`] RFA_LTLAP_FIELD) THEN
    ASM_SIMP_TAC[];
    MP_TAC(MATCH_MP RFA_LBILIN_TENSOR (CONJUNCT1 (INST_TYPE [`:N`,`:N`] RFU_BEV))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RFU_Q_DT = prove
 (`!U a b (G1:real->real^N->real^N^N) G2 t y u.
        lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U
        ==> ((\s. rfu_q (G1 s) (G2 s) y u) has_real_derivative
             rfu_qdot (G1 t) (G2 t) y u) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_q; rfu_low4; rfu_drm] THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                `t:real`] RFU_FLOW_METRIC) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G2:real->real^N->real^N^N`;
                `t:real`] RFU_FLOW_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`]
                RFU_METRIC_PROPS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G2:real->real^N->real^N^N) t`; `y:real^N`]
                RFU_METRIC_PROPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`] RFU_EVOL_FIELDS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G2:real->real^N->real^N^N) t`] RFU_EVOL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                `t:real`; `y:real^N`; `u:num->real^N`] RFU_RIEMANN_DT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R1"))) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G2:real->real^N->real^N^N`;
                `t:real`; `y:real^N`; `u:num->real^N`] RFU_RIEMANN_DT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R2"))) THEN
  MP_TAC(ISPECL [`\s. (G1:real->real^N->real^N^N) s y`;
                 `(lambda i j. --(&2) * lricci ((G1:real->real^N->real^N^N) t) y
                                          (basis i) (basis j)):real^N^N`;
                 `\s. lriemann ((G1:real->real^N->real^N^N) s) y ((u:num->real^N) 1) (u 2) (u 4) -
                      lriemann ((G2:real->real^N->real^N^N) s) y (u 1) (u 2) (u 4)`;
                 `r1 - r2:real^N`; `(u:num->real^N) 3`; `t:real`] RFU_DOT_DT) THEN
  MP_TAC(SPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                `t:real`; `y:real^N`] LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!f f' g. g = f' ==> (f has_real_derivative g) (atreal t)
             ==> (f has_real_derivative f') (atreal t)`) THEN
  SUBGOAL_THEN
   `(u:num->real^N) 3 dot ((G1:real->real^N->real^N^N) t y ** r1) =
    ltlap 4 (G1 t) (lrm4 (G1 t)) y u + rfu_bev (G1 t) (lrm4 (G1 t)) (lrm4 (G1 t)) y u +
    &2 * lricci (G1 t) y (u 3) (lriemann (G1 t) y (u 1) (u 2) (u 4))`
  ASSUME_TAC THENL
   [REWRITE_TAC[dot] THEN
    TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N))
        (\k. ((u:num->real^N) 3)$k *
             ltlap 4 ((G1:real->real^N->real^N^N) t) (lrm4 (G1 t)) y
               (\m. if m = 3 then basis k else u m)) +
      sum(1..dimindex(:N))
        (\k. ((u:num->real^N) 3)$k *
             rfu_bev ((G1:real->real^N->real^N^N) t) (lrm4 (G1 t)) (lrm4 (G1 t)) y
               (\m. if m = 3 then basis k else u m)) +
      &2 * sum(1..dimindex(:N))
        (\k. ((u:num->real^N) 3)$k *
             lricci ((G1:real->real^N->real^N^N) t) y (basis k)
               (lriemann (G1 t) y (u 1) (u 2) (u 4)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ltlap 4 ((G1:real->real^N->real^N^N) t) (lrm4 (G1 t))`;
                   `y:real^N`; `u:num->real^N`; `(u:num->real^N) 3`] RFU_T4_SLOT3) THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `rfu_bev ((G1:real->real^N->real^N^N) t) (lrm4 (G1 t)) (lrm4 (G1 t))`;
                   `y:real^N`; `u:num->real^N`; `(u:num->real^N) 3`] RFU_T4_SLOT3) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`;
                   `(u:num->real^N) 3`;
                   `lriemann ((G1:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) (u 4)`]
                  RFU_LRICCI_LIN1) THEN
    ASM_REWRITE_TAC[RFU_TUPLE3_ID] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:num->real^N) 3 dot ((G1:real->real^N->real^N^N) t y ** r2) =
    ltlap 4 ((G2:real->real^N->real^N^N) t) (lrm4 (G2 t)) y
      (\m. if m = 3 then matrix_inv(G2 t y) ** G1 t y ** u 3 else u m) +
    rfu_bev (G2 t) (lrm4 (G2 t)) (lrm4 (G2 t)) y
      (\m. if m = 3 then matrix_inv(G2 t y) ** G1 t y ** u 3 else u m) +
    &2 * lricci (G2 t) y (matrix_inv(G2 t y) ** G1 t y ** u 3)
                         (lriemann (G2 t) y (u 1) (u 2) (u 4))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(G1:real->real^N->real^N^N) t y`; `(G2:real->real^N->real^N^N) t y`;
                   `(u:num->real^N) 3`; `r2:real^N`] RFU_MINV_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[dot] THEN
    TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N))
        (\k. (matrix_inv((G2:real->real^N->real^N^N) t y) **
              (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3)$k *
             ltlap 4 (G2 t) (lrm4 (G2 t)) y (\m. if m = 3 then basis k else u m)) +
      sum(1..dimindex(:N))
        (\k. (matrix_inv((G2:real->real^N->real^N^N) t y) **
              (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3)$k *
             rfu_bev (G2 t) (lrm4 (G2 t)) (lrm4 (G2 t)) y
               (\m. if m = 3 then basis k else u m)) +
      &2 * sum(1..dimindex(:N))
        (\k. (matrix_inv((G2:real->real^N->real^N^N) t y) **
              (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3)$k *
             lricci (G2 t) y (basis k) (lriemann (G2 t) y (u 1) (u 2) (u 4)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ltlap 4 ((G2:real->real^N->real^N^N) t) (lrm4 (G2 t))`;
                   `y:real^N`; `u:num->real^N`;
                   `matrix_inv((G2:real->real^N->real^N^N) t y) **
                    (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3`] RFU_T4_SLOT3) THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `rfu_bev ((G2:real->real^N->real^N^N) t) (lrm4 (G2 t)) (lrm4 (G2 t))`;
                   `y:real^N`; `u:num->real^N`;
                   `matrix_inv((G2:real->real^N->real^N^N) t y) **
                    (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3`] RFU_T4_SLOT3) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G2:real->real^N->real^N^N) t`; `y:real^N`;
                   `matrix_inv((G2:real->real^N->real^N^N) t y) **
                    (G1:real->real^N->real^N^N) t y ** (u:num->real^N) 3`;
                   `lriemann ((G2:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) (u 4)`]
                  RFU_LRICCI_LIN1) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`;
                 `(u:num->real^N) 3`;
                 `lriemann ((G1:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) (u 4) -
                  lriemann ((G2:real->real^N->real^N^N) t) y (u 1) (u 2) (u 4)`] LRG_HDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) t`; `y:real^N`;
                 `(u:num->real^N) 3`;
                 `lriemann ((G1:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) (u 4)`;
                 `lriemann ((G2:real->real^N->real^N^N) t) y ((u:num->real^N) 1) (u 2) (u 4)`]
                RFU_LRICCI_SUB2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[rfu_qdot; MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Tensor fields of the construction, and component bounds.                  *)
(* rfu_cb k tf y c: every component of tf at y on basis vectors is at most   *)
(* c in absolute value.  The density controls the components of h, A, Q      *)
(* (RFU_DENS_SMALL), and component bounds control g1-norms (RFU_LTNORM2_CB). *)
(* ========================================================================= *)

let rfu_cb = new_definition
 `rfu_cb k (tf:real^N->(num->real^N)->real) (y:real^N) (c:real) <=>
    !ip. ip IN index_tuples k (:N) ==> abs(tf y (\m. basis(ip m))) <= c`;;

(* The bounds on one pair of metrics at a point used by the local inequality. *)

let rfu_kbound = new_definition
 `rfu_kbound (K:real) (G1:real^N->real^N^N) (G2:real^N->real^N^N) (y:real^N) <=>
    &1 <= K /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> abs(G1 y$i$j) <= K /\ abs(G2 y$i$j) <= K /\
               abs(matrix_inv(G1 y)$i$j) <= K /\ abs(matrix_inv(G2 y)$i$j) <= K) /\
    rfu_cb 4 (lrm4 G1) y K /\ rfu_cb 4 (lrm4 G2) y K /\
    rfu_cb 5 (lnabla 4 G2 (lrm4 G2)) y K /\
    rfu_cb 6 (lnabla_iter 4 2 G2 (lrm4 G2)) y K`;;

(* ------------------------------------------------------------------------- *)
(* Tensor fields and smoothness.                                             *)
(* ------------------------------------------------------------------------- *)

let RFU_DGAM_BILINEAR = prove
 (`!U (G1:real^N->real^N^N) G2 z.
        metric_field U G1 /\ metric_field U G2 /\ z IN U
        ==> bilinear (rfu_dgam G1 G2 z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_dgam] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `z:real^N`]
                CHRISTOFFEL_BILINEAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`]
                CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[bilinear] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ASM_REWRITE_TAC[ETA_AX]);;

let RFU_DRM_TRILINEAR = prove
 (`!U (G1:real^N->real^N^N) G2 z.
        metric_field U G1 /\ metric_field U G2 /\ z IN U
        ==> (!b d. linear (\a. rfu_drm G1 G2 z a b d)) /\
            (!a d. linear (\b. rfu_drm G1 G2 z a b d)) /\
            (!a b. linear (\d. rfu_drm G1 G2 z a b d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfu_drm] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `z:real^N`]
                LRIEMANN_TRILINEAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `z:real^N`]
                LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ASM_REWRITE_TAC[]);;

let RFU_DENS_FIELDS = prove
 (`!U (G1:real^N->real^N^N) G2.
        metric_field U G1 /\ metric_field U G2
        ==> ltensor_field 2 U (rfu_hh G1 G2) /\
            (!u. smooth_map_on U (\z. lift(rfu_hh G1 G2 z u))) /\
            ltensor_field 3 U (rfu_aa G1 G2) /\
            (!u. smooth_map_on U (\z. lift(rfu_aa G1 G2 z u))) /\
            ltensor_field 4 U (rfu_q G1 G2) /\
            (!u. smooth_map_on U (\z. lift(rfu_q G1 G2 z u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `G1:real^N->real^N^N`]
                  LRG_LMETRIC2_DIFF_FIELD) THEN
    ASM_REWRITE_TAC[rfu_hh] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `G1:real^N->real^N^N`]
                  LRG_LMETRIC2_DIFF_FIELD) THEN
    ASM_REWRITE_TAC[rfu_hh] THEN SIMP_TAC[];
    REWRITE_TAC[rfu_aa] THEN MATCH_MP_TAC RFU_LOW3_FIELD THEN
    ASM_MESON_TAC[RFU_DGAM_BILINEAR];
    REWRITE_TAC[rfu_aa] THEN MATCH_MP_TAC RFU_LOW3_SMOOTH THEN
    ASM_REWRITE_TAC[rfu_dgam] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH];
    REWRITE_TAC[rfu_q] THEN MATCH_MP_TAC RFU_LOW4_FIELD THEN
    ASM_MESON_TAC[RFU_DRM_TRILINEAR];
    REWRITE_TAC[rfu_q] THEN MATCH_MP_TAC RFU_LOW4_SMOOTH THEN
    ASM_REWRITE_TAC[rfu_drm] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[LRG_LRIEMANN_SMOOTH]]);;

let RFU_X_FIELD = prove
 (`!U (G1:real^N->real^N^N) G2.
        metric_field U G1 /\ metric_field U G2
        ==> ltensor_field 5 U (rfu_x G1 G2) /\
            (!u. smooth_map_on U (\z. lift(rfu_x G1 G2 z u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                 `lrm4 (G1:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                 `lrm4 (G2:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_x] THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Component bounds and norms.                                               *)
(* ------------------------------------------------------------------------- *)

let RFU_ABS3_BOUND = prove
 (`!x y z a b d. abs x <= a /\ abs y <= b /\ abs z <= d ==> abs(x * y * z) <= a * b * d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]);;

let RFU_PRODUCT_ABS_BOUND = prove
 (`!(f:num->real) k K.
        (!m. 1 <= m /\ m <= k ==> abs(f m) <= K) ==> abs(product(1..k) f) <= K pow k`,
  REPEAT STRIP_TAC THEN SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM PRODUCT_CONST_NUMSEG_1] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_ABS_POS]);;

let RFU_LTNORM2_CB = prove
 (`!k (G:real^N->real^N^N) tf y K c.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(matrix_inv(G y)$i$j) <= K) /\
        rfu_cb k tf y c
        ==> ltnorm2 k G tf y <= &(CARD(index_tuples k (:N))) pow 2 * K pow k * c pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfu_cb] THEN STRIP_TAC THEN
  REWRITE_TAC[ltnorm2] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(index_tuples k (:N))) *
              (&(CARD(index_tuples k (:N))) * (c * c * K pow k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
    X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
    X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFU_ABS3_BOUND THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RFU_PRODUCT_ABS_BOUND THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let RFU_CB_LTNORM2 = prove
 (`!k U (G:real^N->real^N^N) tf y K.
        metric_field U G /\ ltensor_field k U tf /\ y IN U /\ &0 <= K /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> G y$i$i <= K)
        ==> rfu_cb k tf y (sqrt(ltnorm2 k G tf y * K pow k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_cb] THEN X_GEN_TAC `ip:num->num` THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ltnorm2 k (G:real^N->real^N^N) tf y *
              product(1..k) (\m. basis((ip:num->num) m) dot (G y ** basis(ip m)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM PRODUCT_CONST_NUMSEG_1] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LRG_METRIC_NONNEG]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ip:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX]);;

let RFU_CB_MONO = prove
 (`!k (tf:real^N->(num->real^N)->real) y c c'.
        rfu_cb k tf y c /\ c <= c' ==> rfu_cb k tf y c'`,
  REWRITE_TAC[rfu_cb] THEN MESON_TAC[REAL_LE_TRANS]);;

let RFU_SWAP34_PERMUTES = prove
 (`swap(3,4) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let RFU_DENS_TERMS = prove
 (`!U (G1:real^N->real^N^N) G2 y.
        metric_field U G1 /\ metric_field U G2 /\ y IN U
        ==> pde_kot_density G1 G2 y =
            ltnorm2 2 G1 (rfu_hh G1 G2) y + ltnorm2 3 G1 (rfu_aa G1 G2) y +
            ltnorm2 4 G1 (rfu_q G1 G2) y /\
            &0 <= ltnorm2 2 G1 (rfu_hh G1 G2) y /\
            &0 <= ltnorm2 3 G1 (rfu_aa G1 G2) y /\
            &0 <= ltnorm2 4 G1 (rfu_q G1 G2) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[RFU_KOT_DENSITY] THEN
  MP_TAC(ISPECL [`4`; `swap(3,4)`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                 `rfu_q (G1:real^N->real^N^N) G2`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
  ASM_REWRITE_TAC[RFU_SWAP34_PERMUTES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RFU_DENS_SMALL = prove
 (`!U (G1:real^N->real^N^N) G2 y K.
        metric_field U G1 /\ metric_field U G2 /\ y IN U /\ rfu_kbound K G1 G2 y
        ==> rfu_cb 2 (rfu_hh G1 G2) y (K pow 2 * sqrt(pde_kot_density G1 G2 y)) /\
            rfu_cb 3 (rfu_aa G1 G2) y (K pow 2 * sqrt(pde_kot_density G1 G2 y)) /\
            rfu_cb 4 (rfu_q G1 G2) y (K pow 2 * sqrt(pde_kot_density G1 G2 y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfu_kbound] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N) ==> (G1:real^N->real^N^N) y$i$i <= K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `i:num`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `matrix_inv:real^N^N->real^N^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K /\ &0 <= K pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k x. k <= 4 /\ &0 <= x /\ x <= pde_kot_density (G1:real^N->real^N^N) G2 y
          ==> sqrt(x * K pow k) <= K pow 2 * sqrt(pde_kot_density G1 G2 y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y * (K pow 2) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_POW_LE] THEN REWRITE_TAC[REAL_POW_POW] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC RFU_CB_MONO THENL
   [EXISTS_TAC `sqrt(ltnorm2 2 (G1:real^N->real^N^N) (rfu_hh G1 G2) y * K pow 2)`;
    EXISTS_TAC `sqrt(ltnorm2 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) y * K pow 3)`;
    EXISTS_TAC `sqrt(ltnorm2 4 (G1:real^N->real^N^N) (rfu_q G1 G2) y * K pow 4)`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC RFU_CB_LTNORM2 THEN EXISTS_TAC `U:real^N->bool` THEN
     ASM_REWRITE_TAC[];
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]));;

(* ========================================================================= *)
(* Bilinear contraction operations (lbilin of pc_rfa_talg) are               *)
(* locally Lipschitz in the inverse metric and in both tensor arguments, in  *)
(* components on basis vectors (RFU_LBILIN_LIP).  Used for the difference of *)
(* the reaction terms of the two curvature evolutions.                       *)
(* ========================================================================= *)

(* Tuples whose first k slots are basis vectors. *)

let rfu_btup = new_definition
 `rfu_btup k (u:num->real^N) <=>
    !m. 1 <= m /\ m <= k ==> ?i. 1 <= i /\ i <= dimindex(:N) /\ u m = basis i`;;

let RFU_BTUP_SHIFT = prove
 (`!p q (u:num->real^N).
        rfu_btup (p + q) u ==> rfu_btup p u /\ rfu_btup q (\m. u(m + p))`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

let RFU_BTUP_PERM = prove
 (`!k s (u:num->real^N).
        s permutes 1..k /\ rfu_btup k u ==> rfu_btup k (\m. u(s m))`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(s:num->num) m IN 1..k` MP_TAC THENL
   [MP_TAC(ISPECL [`s:num->num`; `1..k`; `m:num`] PERMUTES_IN_IMAGE) THEN
    ASM_REWRITE_TAC[IN_NUMSEG];
    REWRITE_TAC[IN_NUMSEG]]);;

let RFU_BTUP_CONTR = prove
 (`!k (u:num->real^N) a b.
        rfu_btup k u /\ 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> rfu_btup (k + 2)
              (\m. if m = 1 then basis a else if m = 2 then basis b else u(m - 2))`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let RFU_PROD_LIP = prove
 (`!x1 x2 y1 y2 K d.
        abs x1 <= K /\ abs x2 <= K /\ abs(x1 - x2) <= d /\
        abs y1 <= K /\ abs y2 <= K /\ abs(y1 - y2) <= d
        ==> abs(x1 * y1) <= K * K /\ abs(x1 * y1 - x2 * y2) <= (&2 * K) * d`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `x1 * y1 - x2 * y2 = (x1 - x2) * y1 + x2 * (y1 - y2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((x1 - x2) * y1) + abs(x2 * (y1 - y2))` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= d * K /\ b <= K * d ==> a + b <= (&2 * K) * d`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let RFU_SUM_ABS_BOUND_NUMSEG = prove
 (`!(f:num->real) n b.
        (!i. 1 <= i /\ i <= n ==> abs(f i) <= b) ==> abs(sum(1..n) f) <= &n * b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1..n`; `f:num->real`; `b:real`] SUM_ABS_BOUND) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1]);;

let RFU_CONTR_LIP_TERM = prove
 (`!g1 g2 x1 x2 K L d.
        abs g1 <= K /\ abs g2 <= K /\ abs(g1 - g2) <= d /\
        abs x1 <= L /\ abs(x1 - x2) <= L * d /\ &0 <= d
        ==> abs(g1 * x1) <= K * L /\
            abs(g1 * x1 - g2 * x2) <= (&1 + abs K) * L * d`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `g1 * x1 - g2 * x2 = (g1 - g2) * x1 + g2 * (x1 - x2)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((g1 - g2) * x1) + abs(g2 * (x1 - x2))` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= d * L /\ b <= abs K * (L * d) ==> a + b <= (&1 + abs K) * L * d`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_REAL_ARITH_TAC);;

(* The contraction step of the induction. *)

let RFU_LBILIN_LIP_CONTR = prove
 (`!(B1:num->num->real) B2 (g1:num->num->real) g2 K L d.
        &0 <= d /\
        (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
               ==> abs(g1 a b) <= K /\ abs(g2 a b) <= K /\ abs(g1 a b - g2 a b) <= d) /\
        (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
               ==> abs(B1 a b) <= L /\ abs(B1 a b - B2 a b) <= L * d)
        ==> abs(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. g1 a b * B1 a b)))
              <= &(dimindex(:N)) * &(dimindex(:N)) * L * (&1 + abs K) /\
            abs(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. g1 a b * B1 a b)) -
                sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. g2 a b * B2 a b)))
              <= (&(dimindex(:N)) * &(dimindex(:N)) * L * (&1 + abs K)) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `1`]) THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> abs(g1 a b * B1 a b) <= K * L /\
              abs(g1 a b * B1 a b - g2 a b * B2 a b) <= (&1 + abs K) * L * d`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RFU_CONTR_LIP_TERM THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) * &(dimindex(:N)) * K * L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= L * ((&1 + abs K) - K) ==> K * L <= L * (&1 + abs K)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) * &(dimindex(:N)) * (&1 + abs K) * L * d` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]]);;

let RFU_LBILIN_LIP = prove
 (`!k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin k p q B
        ==> !K. ?L. &0 <= L /\
              !G1 G2 tf1 tf2 tg1 tg2 y d.
                &0 <= d /\
                (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
                       ==> abs(matrix_inv(G1 y)$a$b) <= K /\
                           abs(matrix_inv(G2 y)$a$b) <= K /\
                           abs(matrix_inv(G1 y)$a$b - matrix_inv(G2 y)$a$b) <= d) /\
                (!u. rfu_btup p u
                     ==> abs(tf1 y u) <= K /\ abs(tf2 y u) <= K /\
                         abs(tf1 y u - tf2 y u) <= d) /\
                (!u. rfu_btup q u
                     ==> abs(tg1 y u) <= K /\ abs(tg2 y u) <= K /\
                         abs(tg1 y u - tg2 y u) <= d)
                ==> !u. rfu_btup k u
                        ==> abs(B G1 tf1 tg1 y u) <= L /\
                            abs(B G1 tf1 tg1 y u - B G2 tf2 tg2 y u) <= L * d`,
  MATCH_MP_TAC lbilin_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN BETA_TAC THENL
   [(* product *)
    EXISTS_TAC `&2 * (abs K + &1) pow 2` THEN
    REWRITE_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POS] THEN
    CONJ_TAC THENL [SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POS]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_BTUP_SHIFT) THEN
    REWRITE_TAC[ltprod] THEN
    MP_TAC(ISPECL [`(tf1:real^N->(num->real^N)->real) y u`;
                   `(tf2:real^N->(num->real^N)->real) y u`;
                   `(tg1:real^N->(num->real^N)->real) y (\m. (u:num->real^N)(m + p))`;
                   `(tg2:real^N->(num->real^N)->real) y (\m. (u:num->real^N)(m + p))`;
                   `abs K`; `d:real`] RFU_PROD_LIP) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[REAL_ARITH `x <= K ==> x <= abs K`]; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs K * abs K` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ x <= a ==> x <= &2 * a`) THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * abs K) * d` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &2 * x <= &2 * y`) THEN
      MATCH_MP_TAC(REAL_ARITH `x <= x pow 2 + &1 /\ &0 <= x ==> x <= (x + &1) pow 2`) THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MP_TAC(SPEC `abs K - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    (* permutation *)
    STRIP_TAC THEN X_GEN_TAC `K:real` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC o SPEC `K:real`) THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[ltperm] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
      `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
      `tg1:real^N->(num->real^N)->real`; `tg2:real^N->(num->real^N)->real`;
      `y:real^N`; `d:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC RFU_BTUP_PERM THEN ASM_REWRITE_TAC[];
    (* contraction *)
    DISCH_TAC THEN X_GEN_TAC `K:real` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC o SPEC `K:real`) THEN
    EXISTS_TAC `&(dimindex(:N)) * &(dimindex(:N)) * L * (&1 + abs K)` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
      `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
      `tg1:real^N->(num->real^N)->real`; `tg2:real^N->(num->real^N)->real`;
      `y:real^N`; `d:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "IH") THEN
    REWRITE_TAC[ltcontr] THEN
    MATCH_MP_TAC RFU_LBILIN_LIP_CONTR THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN USE_THEN "IH" MATCH_MP_TAC THEN
    MATCH_MP_TAC RFU_BTUP_CONTR THEN ASM_REWRITE_TAC[];
    (* sum *)
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B1") (LABEL_TAC "B2")) THEN
    X_GEN_TAC `K:real` THEN
    USE_THEN "B1" (X_CHOOSE_THEN `L1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L1"))
                   o SPEC `K:real`) THEN
    USE_THEN "B2" (X_CHOOSE_THEN `L2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L2"))
                   o SPEC `K:real`) THEN
    EXISTS_TAC `L1 + L2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
    USE_THEN "L1" (MP_TAC o SPECL
     [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
      `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
      `tg1:real^N->(num->real^N)->real`; `tg2:real^N->(num->real^N)->real`;
      `y:real^N`; `d:real`]) THEN
    USE_THEN "L2" (MP_TAC o SPECL
     [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
      `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
      `tg1:real^N->(num->real^N)->real`; `tg2:real^N->(num->real^N)->real`;
      `y:real^N`; `d:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    (* scalar multiple *)
    DISCH_THEN(LABEL_TAC "B") THEN X_GEN_TAC `K:real` THEN
    USE_THEN "B" (X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))
                  o SPEC `K:real`) THEN
    EXISTS_TAC `abs c * L` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPECL
     [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
      `tf1:real^N->(num->real^N)->real`; `tf2:real^N->(num->real^N)->real`;
      `tg1:real^N->(num->real^N)->real`; `tg2:real^N->(num->real^N)->real`;
      `y:real^N`; `d:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;

(* ========================================================================= *)
(* Component estimates at one point for two metrics G1, G2 whose data are    *)
(* bounded by K (rfu_kbound) and whose difference tensors h, A, Q have       *)
(* components at most c (rfu_hyp): the differences of the metric entries,    *)
(* inverse entries, Christoffel symbols, curvature vectors, lrm4 and Ricci   *)
(* entries are O(c); the curvature data are O(1).                            *)
(* ========================================================================= *)

let rfu_hyp = new_definition
 `rfu_hyp K c (U:real^N->bool) (G1:real^N->real^N^N) (G2:real^N->real^N^N) y <=>
    metric_field U G1 /\ metric_field U G2 /\ y IN U /\ rfu_kbound K G1 G2 y /\
    &0 <= c /\
    rfu_cb 2 (rfu_hh G1 G2) y c /\ rfu_cb 3 (rfu_aa G1 G2) y c /\
    rfu_cb 4 (rfu_q G1 G2) y c`;;

(* Component bounds hold on all tuples whose first k slots are basis vectors. *)

let RFU_CB_BTUP = prove
 (`!k U (tf:real^N->(num->real^N)->real) y c u.
        ltensor_field k U tf /\ y IN U /\ rfu_cb k tf y c /\ rfu_btup k u
        ==> abs(tf y u) <= c`,
  REWRITE_TAC[rfu_cb; rfu_btup] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `ix:num->num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\m. if 1 <= m /\ m <= k then (ix:num->num) m else 0`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[index_tuples; IN_ELIM_THM] THEN CONJ_TAC THEN GEN_TAC THEN
    DISCH_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> abs y <= c ==> abs x <= c`) THEN
  UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let RFU_BTUP_SLOT = prove
 (`!k (u:num->real^N) m q.
        rfu_btup k u /\ 1 <= q /\ q <= dimindex(:N)
        ==> rfu_btup k (\j. if j = m then basis q else u j)`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let RFU_SLOT_VEC_BOUND = prove
 (`!k U (tf:real^N->(num->real^N)->real) y c u m (v:real^N) b.
        ltensor_field k U tf /\ y IN U /\ rfu_cb k tf y c /\ rfu_btup k u /\
        1 <= m /\ m <= k /\ (!q. 1 <= q /\ q <= dimindex(:N) ==> abs(v$q) <= b)
        ==> abs(tf y (\j. if j = m then v else u j)) <= &(dimindex(:N)) * b * c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(tf:real^N->(num->real^N)->real) y (\j. if j = m then v else u j) =
    sum(1..dimindex(:N)) (\q. v$q * tf y (\j. if j = m then basis q else u j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_SLOT_EXPAND THEN
    UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC RFU_CB_BTUP THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFU_BTUP_SLOT THEN ASM_REWRITE_TAC[]);;

(* Small explicit tuples. *)

let RFU_BTUP_LIST2 = prove
 (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
         ==> rfu_btup 2 (\m. if m = 1 then basis i else basis j:real^N)`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let RFU_BTUP_LIST3 = prove
 (`!i j l. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
           1 <= l /\ l <= dimindex(:N)
           ==> rfu_btup 3 (\m. if m = 1 then basis i else if m = 2 then basis j
                               else basis l:real^N)`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let RFU_BTUP_LIST4 = prove
 (`!i j l n. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
             1 <= l /\ l <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N)
             ==> rfu_btup 4 (\m. if m = 1 then basis i else if m = 2 then basis j
                                 else if m = 3 then basis l else basis n:real^N)`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Matrix-vector helpers.                                                    *)
(* ------------------------------------------------------------------------- *)

let RFU_MATVEC_BOUND = prove
 (`!(A:real^N^N) (v:real^N) K b k.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(A$i$j) <= K) /\
        (!l. 1 <= l /\ l <= dimindex(:N) ==> abs(v$l) <= b) /\
        1 <= k /\ k <= dimindex(:N)
        ==> abs((A ** v)$k) <= &(dimindex(:N)) * K * b`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS]);;

let RFU_GINV_RECOVER = prove
 (`!(A:real^N^N) (v:real^N). ~(det A = &0) ==> matrix_inv A ** (A ** v) = v`,
  SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_LINV; MATRIX_VECTOR_MUL_LID]);;

let RFU_MATMUL_COMPONENT = prove
 (`!(A:real^N^N) (B:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (A ** B)$i$j = sum(1..dimindex(:N)) (\k. A$i$k * B$k$j)`,
  SIMP_TAC[matrix_mul; LAMBDA_BETA]);;

let RFU_INV_DIFF = prove
 (`!(A:real^N^N) B.
        ~(det A = &0) /\ ~(det B = &0)
        ==> matrix_inv A - matrix_inv B = matrix_inv A ** (B - A) ** matrix_inv B`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_MUL_LINV; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_SIMP_TAC[MATRIX_MUL_RINV; MATRIX_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* The O(c) and O(1) estimates.                                              *)
(* ------------------------------------------------------------------------- *)

let RFU_HYP_BASICS = prove
 (`!K c U (G1:real^N->real^N^N) G2 y.
        rfu_hyp K c U G1 G2 y
        ==> metric_field U G1 /\ metric_field U G2 /\ y IN U /\ &1 <= K /\ &0 <= c /\
            open U /\ transp(G1 y) = G1 y /\ ~(det(G1 y) = &0) /\
            transp(G2 y) = G2 y /\ ~(det(G2 y) = &0) /\
            (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                   ==> abs(G1 y$i$j) <= K /\ abs(G2 y$i$j) <= K /\
                       abs(matrix_inv(G1 y)$i$j) <= K /\ abs(matrix_inv(G2 y)$i$j) <= K) /\
            ltensor_field 2 U (rfu_hh G1 G2) /\ ltensor_field 3 U (rfu_aa G1 G2) /\
            ltensor_field 4 U (rfu_q G1 G2) /\
            ltensor_field 4 U (lrm4 G1) /\ ltensor_field 4 U (lrm4 G2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfu_hyp; rfu_kbound] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`] RFU_METRIC_PROPS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`] RFU_METRIC_PROPS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[]);;

let RFU_SM_G = prove
 (`!K c U (G1:real^N->real^N^N) G2 y.
        rfu_hyp K c U G1 G2 y
        ==> !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                  ==> abs(G1 y$i$j - G2 y$i$j) <= c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `rfu_hh (G1:real^N->real^N^N) G2`; `y:real^N`;
                 `c:real`; `\m. if m = 1 then basis i else basis j:real^N`] RFU_CB_BTUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFU_BTUP_LIST2] THEN ASM_MESON_TAC[rfu_hyp]; ALL_TAC] THEN
  REWRITE_TAC[rfu_hh; lmetric2] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX]);;

let RFU_SM_GV = prove
 (`!K c U (G1:real^N->real^N^N) G2 y l.
        rfu_hyp K c U G1 G2 y /\ 1 <= l /\ l <= dimindex(:N)
        ==> !k. 1 <= k /\ k <= dimindex(:N)
                ==> abs((G1 y ** basis l - G2 y ** basis l)$k) <= c`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP RFU_SM_G) THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA] THEN
  ASM_SIMP_TAC[]);;

let RFU_SM_GINV = prove
 (`!K c U (G1:real^N->real^N^N) G2 y.
        rfu_hyp K c U G1 G2 y
        ==> !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                  ==> abs(matrix_inv(G1 y)$i$j - matrix_inv(G2 y)$i$j) <=
                      &(dimindex(:N)) * K * (&(dimindex(:N)) * c * K)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFU_SM_G) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM MATRIX_SUB_COMPONENT; RFU_INV_DIFF] THEN
  ASM_SIMP_TAC[RFU_MATMUL_COMPONENT] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS] THEN
  ASM_SIMP_TAC[RFU_MATMUL_COMPONENT] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS; MATRIX_SUB_COMPONENT] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_SIMP_TAC[]);;

let RFU_RECOVER_BOUND = prove
 (`!(A:real^N^N) (v:real^N) K b.
        ~(det A = &0) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(matrix_inv A$i$j) <= K) /\
        (!l. 1 <= l /\ l <= dimindex(:N) ==> abs((A ** v)$l) <= b)
        ==> !k. 1 <= k /\ k <= dimindex(:N) ==> abs(v$k) <= &(dimindex(:N)) * K * b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N^N`; `v:real^N`] RFU_GINV_RECOVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RFU_MATVEC_BOUND THEN ASM_SIMP_TAC[]);;

let RFU_SM_D = prove
 (`!K c U (G1:real^N->real^N^N) G2 y i j.
        rfu_hyp K c U G1 G2 y /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> !k. 1 <= k /\ k <= dimindex(:N)
                ==> abs((rfu_dgam G1 G2 y (basis i) (basis j))$k) <=
                    &(dimindex(:N)) * K * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  MATCH_MP_TAC RFU_RECOVER_BOUND THEN EXISTS_TAC `(G1:real^N->real^N^N) y` THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `rfu_aa (G1:real^N->real^N^N) G2`; `y:real^N`;
                 `c:real`; `\m. if m = 1 then basis i else if m = 2 then basis j
                                else basis l:real^N`] RFU_CB_BTUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFU_BTUP_LIST3] THEN ASM_MESON_TAC[rfu_hyp]; ALL_TAC] THEN
  REWRITE_TAC[rfu_aa; rfu_low3] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let RFU_SM_R = prove
 (`!K c U (G1:real^N->real^N^N) G2 y a b d.
        rfu_hyp K c U G1 G2 y /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
        1 <= d /\ d <= dimindex(:N)
        ==> !k. 1 <= k /\ k <= dimindex(:N)
                ==> abs((rfu_drm G1 G2 y (basis a) (basis b) (basis d))$k) <=
                    &(dimindex(:N)) * K * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  MATCH_MP_TAC RFU_RECOVER_BOUND THEN EXISTS_TAC `(G1:real^N->real^N^N) y` THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `rfu_q (G1:real^N->real^N^N) G2`; `y:real^N`;
                 `c:real`; `\m. if m = 1 then basis a else if m = 2 then basis b
                                else if m = 3 then basis l else basis d:real^N`]
                RFU_CB_BTUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFU_BTUP_LIST4] THEN ASM_MESON_TAC[rfu_hyp]; ALL_TAC] THEN
  REWRITE_TAC[rfu_q; rfu_low4] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

let RFU_BD_R1 = prove
 (`!U (G:real^N->real^N^N) y K a b d.
        metric_field U G /\ y IN U /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(matrix_inv(G y)$i$j) <= K) /\
        rfu_cb 4 (lrm4 G) y K /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
        1 <= d /\ d <= dimindex(:N)
        ==> !k. 1 <= k /\ k <= dimindex(:N)
                ==> abs((lriemann G y (basis a) (basis b) (basis d))$k) <=
                    &(dimindex(:N)) * K * K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFU_METRIC_PROPS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC RFU_RECOVER_BOUND THEN EXISTS_TAC `(G:real^N->real^N^N) y` THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!x y K:real. x = y /\ abs y <= K ==> abs x <= K`) THEN
  EXISTS_TAC `lrm4 (G:real^N->real^N^N) y
                (\m. if m = 1 then basis a else if m = 2 then basis b
                     else if m = 3 then basis l else basis d)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lrm4] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    ASM_SIMP_TAC[DOT_BASIS];
    MATCH_MP_TAC RFU_CB_BTUP THEN
    MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
    ASM_SIMP_TAC[RFU_BTUP_LIST4]]);;

let RFU_BD_R = prove
 (`!K c U (G1:real^N->real^N^N) G2 y a b d.
        rfu_hyp K c U G1 G2 y /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
        1 <= d /\ d <= dimindex(:N)
        ==> !k. 1 <= k /\ k <= dimindex(:N)
                ==> abs((lriemann G1 y (basis a) (basis b) (basis d))$k) <=
                    &(dimindex(:N)) * K * K /\
                    abs((lriemann G2 y (basis a) (basis b) (basis d))$k) <=
                    &(dimindex(:N)) * K * K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`; `K:real`;
                   `a:num`; `b:num`; `d:num`] RFU_BD_R1);
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`; `K:real`;
                   `a:num`; `b:num`; `d:num`] RFU_BD_R1)] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

let RFU_BTUP_IDX = prove
 (`!k (u:num->real^N) m.
        rfu_btup k u /\ 1 <= m /\ m <= k
        ==> ?i. 1 <= i /\ i <= dimindex(:N) /\ u m = basis i`,
  REWRITE_TAC[rfu_btup] THEN MESON_TAC[]);;

let RFU_SM_MV = prove
 (`!K c U (G1:real^N->real^N^N) G2 y l.
        rfu_hyp K c U G1 G2 y /\ 1 <= l /\ l <= dimindex(:N)
        ==> !k. 1 <= k /\ k <= dimindex(:N)
                ==> abs((matrix_inv(G2 y) ** G1 y ** basis l - basis l)$k) <=
                    &(dimindex(:N)) * K * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN
   `matrix_inv((G2:real^N->real^N^N) y) ** (G1:real^N->real^N^N) y ** basis l - basis l =
    matrix_inv(G2 y) ** (G1 y ** basis l - G2 y ** basis l)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN ASM_SIMP_TAC[RFU_GINV_RECOVER];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_MATVEC_BOUND THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC_ALL RFU_SM_GV) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let RFU_SM_P = prove
 (`!K c U (G1:real^N->real^N^N) G2 y u.
        rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
        ==> abs(lrm4 G1 y u - lrm4 G2 y u) <=
            (&1 + &(dimindex(:N)) * &(dimindex(:N)) * K * K) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN
   `lrm4 (G1:real^N->real^N^N) y u - lrm4 G2 y u =
    rfu_q G1 G2 y u +
    (u:num->real^N) 3 dot ((G1 y - G2 y) ** lriemann G2 y (u 1) (u 2) (u 4))`
  SUBST1_TAC THENL
   [REWRITE_TAC[lrm4; rfu_q; rfu_low4; rfu_drm] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= c /\ abs y <= (n * n * K * K) * c ==> abs(x + y) <= (&1 + n * n * K * K) * c`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
    ASM_MESON_TAC[rfu_hyp];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `u:num->real^N`; `1`] RFU_BTUP_IDX) THEN
  MP_TAC(ISPECL [`4`; `u:num->real^N`; `2`] RFU_BTUP_IDX) THEN
  MP_TAC(ISPECL [`4`; `u:num->real^N`; `3`] RFU_BTUP_IDX) THEN
  MP_TAC(ISPECL [`4`; `u:num->real^N`; `4`] RFU_BTUP_IDX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * c * (&(dimindex(:N)) * K * K)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFU_MATVEC_BOUND THEN ASM_SIMP_TAC[MATRIX_SUB_COMPONENT] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC_ALL RFU_SM_G) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                    `G2:real^N->real^N^N`; `y:real^N`; `a:num`; `b:num`; `d:num`]
                   RFU_BD_R) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

let RFU_BD_RIC1 = prove
 (`!U (G:real^N->real^N^N) y K a b.
        metric_field U G /\ y IN U /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(matrix_inv(G y)$i$j) <= K) /\
        rfu_cb 4 (lrm4 G) y K /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> abs(lricci G y (basis a) (basis b)) <=
            &(dimindex(:N)) * &(dimindex(:N)) * K * K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `basis a:real^N`; `basis b:real^N`] LRG_LRM4_CONTRACT13) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
  ASM_SIMP_TAC[RFU_BTUP_LIST4]);;

(* Positivity of products and sums of nonnegative factors. *)

let RFU_POS_TAC =
  REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_ADD) THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_POS; REAL_ABS_POS];;

let RFU_SM_RIC = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y a b.
          rfu_hyp K c U G1 G2 y /\
          1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> abs(lricci G1 y (basis a) (basis b) - lricci G2 y (basis a) (basis b))
              <= L * c`,
  GEN_TAC THEN
  EXISTS_TAC `(&(dimindex(:N)) * &(dimindex(:N)) * abs K * (&1 + abs K)) *
              (&(dimindex(:N)) * abs K * (&(dimindex(:N)) * abs K) +
               (&1 + &(dimindex(:N)) * &(dimindex(:N)) * abs K * abs K))` THEN
  CONJ_TAC THENL [RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ABBREV_TAC `dC = n * K * (n * K) + (&1 + n * n * K * K)` THEN
  SUBGOAL_THEN `&1 <= dC` ASSUME_TAC THENL
   [EXPAND_TAC "dC" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &1 <= x + (&1 + y)`) THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`;
                 `basis a:real^N`; `basis b:real^N`] LRG_LRM4_CONTRACT13) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`;
                 `basis a:real^N`; `basis b:real^N`] LRG_LRM4_CONTRACT13) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL
   [`\i j. lrm4 (G1:real^N->real^N^N) y
             (\m. if m = 1 then basis i else if m = 2 then basis a
                  else if m = 3 then basis j else basis b)`;
    `\i j. lrm4 (G2:real^N->real^N^N) y
             (\m. if m = 1 then basis i else if m = 2 then basis a
                  else if m = 3 then basis j else basis b)`;
    `\i j. matrix_inv((G1:real^N->real^N^N) y)$i$j`;
    `\i j. matrix_inv((G2:real^N->real^N^N) y)$i$j`;
    `K:real`; `K:real`; `dC * c:real`] RFU_LBILIN_LIP_CONTR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN CONJ_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `n * K * (n * c * K)` THEN CONJ_TAC THENL
       [MP_TAC(SPEC_ALL RFU_SM_GINV) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "dC" THEN
      MATCH_MP_TAC(REAL_ARITH
       `!x y z c:real. x = y * c /\ &0 <= z * c ==> x <= (y + z) * c`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
      ASM_SIMP_TAC[RFU_BTUP_LIST4] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + n * n * K * K) * c` THEN CONJ_TAC THENL
     [EXPAND_TAC "n" THEN MATCH_MP_TAC RFU_SM_P THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[RFU_BTUP_LIST4];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dC * c:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "dC" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> y <= x + y`) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ARITH `&1 <= x ==> &0 <= x`]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* The covariant derivative of a lowered (1,3) field (the proof of           *)
(* LRG_LNABLA_LRM4 for any differentiable field R), the principal part of    *)
(* the evolution of A, and the three lower-order estimates of the energy     *)
(* computation: A_t - (principal part), Q_t - div X and nabla Q - X are O(c) *)
(* in components (RFU_LOT_AA, RFU_LOT_Q, RFU_LOT_Y).                         *)
(* ========================================================================= *)

let RFU_LNABLA_LOW4 = prove
 (`!U (G:real^N->real^N^N) (R:real^N->real^N->real^N->real^N->real^N) y u.
        metric_field U G /\ y IN U /\
        (\z. R z ((u:num->real^N) 1) (u 2) (u 4)) differentiable at y
        ==> lnabla 4 G (rfu_low4 G R) y u =
            u 3 dot (G y **
              (frechet_derivative (\z. R z (u 1) (u 2) (u 4)) (at y) (u 5) +
               christoffel G y (u 5) (R y (u 1) (u 2) (u 4)) -
               R y (christoffel G y (u 5) (u 1)) (u 2) (u 4) -
               R y (u 1) (christoffel G y (u 5) (u 2)) (u 4) -
               R y (u 1) (u 2) (christoffel G y (u 5) (u 4))))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lnabla; rfu_low4; SUM_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`G:real^N->real^N^N`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         (G:real^N->real^N^N)) (at y)`;
    `(\z. (u:num->real^N) 3):real^N->real^N`; `(\h. vec 0):real^N->real^N`;
    `\z. (R:real^N->real^N->real^N->real^N->real^N) z ((u:num->real^N) 1) (u 2) (u 4)`;
    `frechet_derivative
       (\z. (R:real^N->real^N->real^N->real^N->real^N) z ((u:num->real^N) 1) (u 2) (u 4))
       (at y)`;
    `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP; DOT_LZERO; REAL_ADD_LID; GSYM mderiv] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 3`; `(u:num->real^N) 5`;
                 `(R:real^N->real^N->real^N->real^N->real^N) y ((u:num->real^N) 1) (u 2) (u 4)`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y ((u:num->real^N) 5) (u 3)`;
                 `(R:real^N->real^N->real^N->real^N->real^N) y ((u:num->real^N) 1) (u 2) (u 4)`]
         LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RADD; DOT_RSUB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  REAL_ARITH_TAC);;

let RFU_FRECHET_SUB = prove
 (`!(f:real^M->real^N) g y.
        f differentiable at y /\ g differentiable at y
        ==> frechet_derivative (\z. f z - g z) (at y) =
            (\h. frechet_derivative f (at y) h - frechet_derivative g (at y) h)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]);;

let RFU_LRIEMANN_DIFFERENTIABLE = prove
 (`!U (G:real^N->real^N^N) y a b d.
        metric_field U G /\ y IN U ==> (\z. lriemann G z a b d) differentiable at y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[LRG_LRIEMANN_SMOOTH] THEN
  ASM_MESON_TAC[metric_field]);;

let RFU_Y_IDENTITY = prove
 (`!U (G1:real^N->real^N^N) G2 y u.
        metric_field U G1 /\ metric_field U G2 /\ y IN U
        ==> lnabla 4 G1 (rfu_q G1 G2) y u - rfu_x G1 G2 y u =
            --(u 3 dot ((G1 y - G2 y) **
                 (frechet_derivative (\z. lriemann G2 z (u 1) (u 2) (u 4)) (at y) (u 5) +
                  christoffel G2 y (u 5) (lriemann G2 y (u 1) (u 2) (u 4)) -
                  lriemann G2 y (christoffel G2 y (u 5) (u 1)) (u 2) (u 4) -
                  lriemann G2 y (u 1) (christoffel G2 y (u 5) (u 2)) (u 4) -
                  lriemann G2 y (u 1) (u 2) (christoffel G2 y (u 5) (u 4))))) -
            u 3 dot (G1 y **
                 (rfu_dgam G1 G2 y (u 5) (lriemann G2 y (u 1) (u 2) (u 4)) -
                  lriemann G2 y (rfu_dgam G1 G2 y (u 5) (u 1)) (u 2) (u 4) -
                  lriemann G2 y (u 1) (rfu_dgam G1 G2 y (u 5) (u 2)) (u 4) -
                  lriemann G2 y (u 1) (u 2) (rfu_dgam G1 G2 y (u 5) (u 4))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_q; rfu_x] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                 `rfu_drm (G1:real^N->real^N^N) G2`; `y:real^N`; `u:num->real^N`]
                RFU_LNABLA_LOW4) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rfu_drm] THEN MATCH_MP_TAC DIFFERENTIABLE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC RFU_LRIEMANN_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]
                LRG_LNABLA_LRM4) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]
                LRG_LNABLA_LRM4) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[rfu_drm; rfu_dgam] THEN
  MP_TAC(ISPECL [`\z. lriemann (G1:real^N->real^N^N) z ((u:num->real^N) 1) (u 2) (u 4)`;
                 `\z. lriemann (G2:real^N->real^N^N) z ((u:num->real^N) 1) (u 2) (u 4)`;
                 `y:real^N`] RFU_FRECHET_SUB) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFU_LRIEMANN_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB (SPEC `(u:num->real^N) 5` th)]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`]
                LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "T1")
    (CONJUNCTS_THEN2 (LABEL_TAC "T2") (LABEL_TAC "T3"))) THEN
  USE_THEN "T1" (fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB
    (SPECL [`(u:num->real^N) 2`; `(u:num->real^N) 4`] th))]) THEN
  USE_THEN "T2" (fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB
    (SPECL [`(u:num->real^N) 1`; `(u:num->real^N) 4`] th))]) THEN
  USE_THEN "T3" (fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB
    (SPECL [`(u:num->real^N) 1`; `(u:num->real^N) 2`] th))]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
              MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              DOT_RSUB; DOT_RADD] THEN
  REAL_ARITH_TAC);;

let RFU_LIN_VEC_BOUND = prove
 (`!(f:real^N->real^N) (v:real^N) B b.
        linear f /\
        (!m k. 1 <= m /\ m <= dimindex(:N) /\ 1 <= k /\ k <= dimindex(:N)
               ==> abs((f (basis m))$k) <= B) /\
        (!m. 1 <= m /\ m <= dimindex(:N) ==> abs(v$m) <= b)
        ==> !k. 1 <= k /\ k <= dimindex(:N) ==> abs((f v)$k) <= &(dimindex(:N)) * b * B`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`v:real^N`; `k:num`]
    (MATCH_MP LINEAR_COMPONENTWISE_EXPANSION th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS]);;

let RFU_BTUP5_IDX = prove
 (`!(u:num->real^N).
        rfu_btup 5 u
        ==> ?i1 i2 i3 i4 i5.
              1 <= i1 /\ i1 <= dimindex(:N) /\ 1 <= i2 /\ i2 <= dimindex(:N) /\
              1 <= i3 /\ i3 <= dimindex(:N) /\ 1 <= i4 /\ i4 <= dimindex(:N) /\
              1 <= i5 /\ i5 <= dimindex(:N) /\
              u 1 = basis i1 /\ u 2 = basis i2 /\ u 3 = basis i3 /\ u 4 = basis i4 /\
              u 5 = basis i5`,
  REWRITE_TAC[rfu_btup] THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun m -> FIRST_ASSUM(MP_TAC o SPEC m)) [`5`; `4`; `3`; `2`; `1`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let RFU_BTUP_LIST5 = prove
 (`!i j l n p. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
               1 <= l /\ l <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N) /\
               1 <= p /\ p <= dimindex(:N)
               ==> rfu_btup 5 (\m. if m = 1 then basis i else if m = 2 then basis j
                                   else if m = 3 then basis l else if m = 4 then basis n
                                   else basis p:real^N)`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let RFU_LOT_Y = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> !u. rfu_btup 5 u
                  ==> abs(lnabla 4 G1 (rfu_q G1 G2) y u - rfu_x G1 G2 y u) <= L * c`,
  GEN_TAC THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * abs K * abs K) +
              &(dimindex(:N)) * abs K *
              (&4 * (&(dimindex(:N)) * (&(dimindex(:N)) * abs K * abs K) *
                     (&(dimindex(:N)) * abs K)))` THEN
  CONJ_TAC THENL [RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `i1:num` (X_CHOOSE_THEN `i2:num` (X_CHOOSE_THEN `i3:num`
    (X_CHOOSE_THEN `i4:num` (X_CHOOSE_THEN `i5:num` STRIP_ASSUME_TAC)))) o
    MATCH_MP RFU_BTUP5_IDX) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`; `u:num->real^N`] RFU_Y_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC
   `W2 = frechet_derivative
          (\z. lriemann (G2:real^N->real^N^N) z (basis i1) (basis i2) (basis i4))
          (at y) (basis i5) +
         christoffel G2 y (basis i5) (lriemann G2 y (basis i1) (basis i2) (basis i4)) -
         lriemann G2 y (christoffel G2 y (basis i5) (basis i1)) (basis i2) (basis i4) -
         lriemann G2 y (basis i1) (christoffel G2 y (basis i5) (basis i2)) (basis i4) -
         lriemann G2 y (basis i1) (basis i2) (christoffel G2 y (basis i5) (basis i4))` THEN
  ABBREV_TAC
   `WD = rfu_dgam (G1:real^N->real^N^N) G2 y (basis i5)
           (lriemann G2 y (basis i1) (basis i2) (basis i4)) -
         lriemann G2 y (rfu_dgam G1 G2 y (basis i5) (basis i1)) (basis i2) (basis i4) -
         lriemann G2 y (basis i1) (rfu_dgam G1 G2 y (basis i5) (basis i2)) (basis i4) -
         lriemann G2 y (basis i1) (basis i2) (rfu_dgam G1 G2 y (basis i5) (basis i4))` THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= dimindex(:N) ==> abs((W2:real^N)$k) <= n * K * K`
  ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC RFU_RECOVER_BOUND THEN
    EXISTS_TAC `(G2:real^N->real^N^N) y` THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`;
      `\m. if m = 1 then basis i1 else if m = 2 then basis i2
           else if m = 3 then basis l else if m = 4 then basis i4
           else basis i5:real^N`] LRG_LNABLA_LRM4) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[DOT_BASIS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`5`; `U:real^N->bool`] THEN
    ASM_SIMP_TAC[RFU_BTUP_LIST5] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                     `lrm4 (G2:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
      ASM_REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[LRM4_TENSOR_FIELD]; SIMP_TAC[]];
      ASM_MESON_TAC[rfu_hyp; rfu_kbound]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> abs((WD:real^N)$k) <= &4 * (n * (n * K * K) * (n * K * c))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN EXPAND_TAC "WD" THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs a <= b /\ abs x <= b /\ abs z <= b /\ abs w <= b
      ==> abs(a - x - z - w) <= &4 * b`) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                   `y:real^N`] RFU_DGAM_BILINEAR) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`]
                  LRIEMANN_TRILINEAR) THEN
    ASM_REWRITE_TAC[bilinear] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "T1")
      (CONJUNCTS_THEN2 (LABEL_TAC "T2") (LABEL_TAC "T3"))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D2") (LABEL_TAC "D1")) THEN
    EXPAND_TAC "n" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\v. rfu_dgam (G1:real^N->real^N^N) G2 y (basis i5) v`;
                     `lriemann (G2:real^N->real^N^N) y (basis i1) (basis i2) (basis i4)`;
                     `&(dimindex(:N)) * K * c`; `&(dimindex(:N)) * K * K`]
                    RFU_LIN_VEC_BOUND) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "D2" (MP_TAC o SPEC `basis i5:real^N`) THEN REWRITE_TAC[ETA_AX];
          MAP_EVERY X_GEN_TAC [`m:num`; `k2:num`] THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i5:num`; `m:num`] RFU_SM_D) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k2:num`) THEN ASM_REWRITE_TAC[];
          X_GEN_TAC `m:num` THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`; `i4:num`]
                       RFU_BD_R) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_SIMP_TAC[]];
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MP_TAC(ISPECL [`\v. lriemann (G2:real^N->real^N^N) y v (basis i2) (basis i4)`;
                     `rfu_dgam (G1:real^N->real^N^N) G2 y (basis i5) (basis i1)`;
                     `&(dimindex(:N)) * K * K`; `&(dimindex(:N)) * K * c`]
                    RFU_LIN_VEC_BOUND) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "T1" (MP_TAC o SPECL [`basis i2:real^N`; `basis i4:real^N`]) THEN
          REWRITE_TAC[];
          MAP_EVERY X_GEN_TAC [`m:num`; `k2:num`] THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `m:num`; `i2:num`; `i4:num`]
                       RFU_BD_R) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k2:num`) THEN ASM_SIMP_TAC[];
          X_GEN_TAC `m:num` THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i5:num`; `i1:num`] RFU_SM_D) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MP_TAC(ISPECL [`\v. lriemann (G2:real^N->real^N^N) y (basis i1) v (basis i4)`;
                     `rfu_dgam (G1:real^N->real^N^N) G2 y (basis i5) (basis i2)`;
                     `&(dimindex(:N)) * K * K`; `&(dimindex(:N)) * K * c`]
                    RFU_LIN_VEC_BOUND) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "T2" (MP_TAC o SPECL [`basis i1:real^N`; `basis i4:real^N`]) THEN
          REWRITE_TAC[];
          MAP_EVERY X_GEN_TAC [`m:num`; `k2:num`] THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `m:num`; `i4:num`]
                       RFU_BD_R) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k2:num`) THEN ASM_SIMP_TAC[];
          X_GEN_TAC `m:num` THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i5:num`; `i2:num`] RFU_SM_D) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MP_TAC(ISPECL [`\v. lriemann (G2:real^N->real^N^N) y (basis i1) (basis i2) v`;
                     `rfu_dgam (G1:real^N->real^N^N) G2 y (basis i5) (basis i4)`;
                     `&(dimindex(:N)) * K * K`; `&(dimindex(:N)) * K * c`]
                    RFU_LIN_VEC_BOUND) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "T3" (MP_TAC o SPECL [`basis i1:real^N`; `basis i2:real^N`]) THEN
          REWRITE_TAC[];
          MAP_EVERY X_GEN_TAC [`m:num`; `k2:num`] THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`; `m:num`]
                       RFU_BD_R) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k2:num`) THEN ASM_SIMP_TAC[];
          X_GEN_TAC `m:num` THEN STRIP_TAC THEN
          MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                        `G2:real^N->real^N^N`; `y:real^N`; `i5:num`; `i4:num`] RFU_SM_D) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DOT_BASIS] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `n * c * (n * K * K) + n * K * (&4 * (n * (n * K * K) * (n * K * c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!x z a b. abs x <= a /\ abs z <= b ==> abs(--x - z) <= a + b`) THEN
    EXPAND_TAC "n" THEN CONJ_TAC THEN MATCH_MP_TAC RFU_MATVEC_BOUND THEN
    ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[MATRIX_SUB_COMPONENT] THEN
      MP_TAC(SPEC_ALL RFU_SM_G) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_SIMP_TAC[]];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The principal part of A_t and the estimate of the rest (RFU_LOT_AA).      *)
(* ========================================================================= *)

(* The g1-contraction of X carried by the evolution of A, and its            *)
(* combination as in rfu_lc.                                                 *)

let rfu_cx = new_definition
 `rfu_cx (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    ltcontr G1 (ltperm (swap(2,3)) (rfu_x G1 G2))`;;

let rfu_pa = new_definition
 `rfu_pa (G1:real^N->real^N^N) (G2:real^N->real^N^N) =
    \z (u:num->real^N).
      --(rfu_cx G1 G2 z (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) +
         rfu_cx G1 G2 z (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2) -
         rfu_cx G1 G2 z (\m. if m = 1 then u 1 else if m = 2 then u 2 else u 3))`;;

let RFU_LTCONTR_PERM_SUB = prove
 (`!(G:real^N->real^N^N) s (A:real^N->(num->real^N)->real) B y u.
        ltcontr G (ltperm s (\z u. A z u - B z u)) y u =
        ltcontr G (ltperm s A) y u - ltcontr G (ltperm s B) y u`,
  REWRITE_TAC[ltcontr; ltperm; REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG]);;

let RFU_LRICCI_LIN2 = prove
 (`!U (G:real^N->real^N^N) y v (c:real^N).
        metric_field U G /\ y IN U
        ==> sum(1..dimindex(:N)) (\k. c$k * lricci G y v (basis k)) = lricci G y v c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPEC `c:real^N` o MATCH_MP LRG_LINEAR_DROP_EXPAND) THEN
  REWRITE_TAC[LIFT_DROP]);;

(* aadot - pa as a combination of differences, for any tuple. *)

let RFU_AA_IDENTITY = prove
 (`!U (G1:real^N->real^N^N) G2 y u.
        metric_field U G1 /\ metric_field U G2 /\ y IN U
        ==> rfu_aadot G1 G2 y u - rfu_pa G1 G2 y u =
            --(&2) * lricci G1 y (u 3) (rfu_dgam G1 G2 y (u 1) (u 2)) -
            ((ltcontr G1 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y
                (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) -
              ltcontr G2 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y
                (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1)) +
             (ltcontr G1 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y
                (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2) -
              ltcontr G2 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y
                (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2)) -
             (ltcontr G1 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y
                (\m. if m = 1 then u 1 else if m = 2 then u 2 else u 3) -
              ltcontr G2 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y
                (\m. if m = 1 then u 1 else if m = 2 then u 2 else u 3))) +
            (rfu_lc G2 y (u 1) (u 2) (matrix_inv(G2 y) ** G1 y ** u 3) -
             rfu_lc G2 y (u 1) (u 2) (u 3))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfu_aadot; rfu_pa; rfu_cx; rfu_lc; rfu_x] THEN
  REWRITE_TAC[RFU_LTCONTR_PERM_SUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`]
                RFA_NABLA_RIC_CONTR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`]
                RFA_NABLA_RIC_CONTR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC);;

let RFU_BTUP3_PERMS = prove
 (`!(u:num->real^N).
        rfu_btup 3 u
        ==> rfu_btup 3 (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) /\
            rfu_btup 3 (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2) /\
            rfu_btup 3 (\m. if m = 1 then u 1 else if m = 2 then u 2 else u 3)`,
  REWRITE_TAC[rfu_btup] THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let RFU_SWAP23_PERMUTES = prove
 (`swap(2,3) permutes 1..5`,
  MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let RFU_BTUP_CPERM = prove
 (`!(w:num->real^N) a b.
        rfu_btup 3 w /\ 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> rfu_btup 5
              (\m. (\m. if m = 1 then basis a else if m = 2 then basis b else w(m - 2))
                   (swap(2,3) m))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_BTUP_PERM THEN
  REWRITE_TAC[ETA_AX; RFU_SWAP23_PERMUTES] THEN
  MP_TAC(ISPECL [`3`; `w:num->real^N`; `a:num`; `b:num`] RFU_BTUP_CONTR) THEN
  ASM_REWRITE_TAC[ARITH]);;

let RFU_C2_BOUNDS = prove
 (`!K c U (G1:real^N->real^N^N) G2 y w.
        rfu_hyp K c U G1 G2 y /\ rfu_btup 3 w
        ==> abs(ltcontr G2 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y w)
              <= &(dimindex(:N)) * &(dimindex(:N)) * (K * K) /\
            abs(ltcontr G1 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y w -
                ltcontr G2 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y w)
              <= &(dimindex(:N)) * &(dimindex(:N)) *
                 ((&(dimindex(:N)) * K * (&(dimindex(:N)) * c * K)) * K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `ltensor_field 5 U (lnabla 4 (G2:real^N->real^N^N) (lrm4 G2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                   `lrm4 (G2:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[LRM4_TENSOR_FIELD]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> abs(lnabla 4 (G2:real^N->real^N^N) (lrm4 G2) y
                   (\m. if swap(2,3) m = 1 then basis a
                        else if swap(2,3) m = 2 then basis b
                        else (w:num->real^N)(swap(2,3) m - 2))) <= K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_CB_BTUP THEN
    MAP_EVERY EXISTS_TAC [`5`; `U:real^N->bool`] THEN
    MP_TAC(BETA_RULE(ISPECL [`w:num->real^N`; `a:num`; `b:num`] RFU_BTUP_CPERM)) THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound];
    ALL_TAC] THEN
  REWRITE_TAC[ltcontr; ltperm; GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_RDISTRIB] THEN
  CONJ_TAC THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `a:num` THEN
  STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS] THEN
  MP_TAC(SPEC_ALL RFU_SM_GINV) THEN ASM_SIMP_TAC[]);;

let RFU_LC2_BOUND = prove
 (`!K c U (G1:real^N->real^N^N) G2 y a b k.
        rfu_hyp K c U G1 G2 y /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N) /\
        1 <= k /\ k <= dimindex(:N)
        ==> abs(rfu_lc G2 y (basis a) (basis b) (basis k)) <=
            &3 * (&(dimindex(:N)) * &(dimindex(:N)) * (K * K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  REWRITE_TAC[rfu_lc] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`]
                RFA_NABLA_RIC_CONTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= B /\ abs z <= B /\ abs w <= B ==> abs(x + z - w) <= &3 * B`) THEN
  SUBGOAL_THEN
   `!w. rfu_btup 3 w
        ==> abs(ltcontr (G2:real^N->real^N^N) (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2)))
                  y w) <= &(dimindex(:N)) * &(dimindex(:N)) * (K * K)`
  (fun th -> REPEAT CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_SIMP_TAC[RFU_BTUP_LIST3]) THEN
  X_GEN_TAC `w:num->real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                 `G2:real^N->real^N^N`; `y:real^N`; `w:num->real^N`] RFU_C2_BOUNDS) THEN
  ASM_SIMP_TAC[]);;

let RFU_BTUP3_IDX = prove
 (`!(u:num->real^N).
        rfu_btup 3 u
        ==> ?i1 i2 i3.
              1 <= i1 /\ i1 <= dimindex(:N) /\ 1 <= i2 /\ i2 <= dimindex(:N) /\
              1 <= i3 /\ i3 <= dimindex(:N) /\
              u 1 = basis i1 /\ u 2 = basis i2 /\ u 3 = basis i3`,
  REWRITE_TAC[rfu_btup] THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun m -> FIRST_ASSUM(MP_TAC o SPEC m)) [`3`; `2`; `1`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let RFU_LOT_AA = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> !u. rfu_btup 3 u
                  ==> abs(rfu_aadot G1 G2 y u - rfu_pa G1 G2 y u) <= L * c`,
  GEN_TAC THEN
  EXISTS_TAC
   `&2 * (&(dimindex(:N)) * (&(dimindex(:N)) * abs K) *
          (&(dimindex(:N)) * &(dimindex(:N)) * abs K * abs K)) +
    &3 * (&(dimindex(:N)) * &(dimindex(:N)) *
          ((&(dimindex(:N)) * abs K * (&(dimindex(:N)) * abs K)) * abs K)) +
    &(dimindex(:N)) * (&(dimindex(:N)) * abs K) *
          (&3 * (&(dimindex(:N)) * &(dimindex(:N)) * (abs K * abs K)))` THEN
  CONJ_TAC THENL [RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_BTUP3_PERMS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`; `u:num->real^N`] RFU_AA_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPEC `u:num->real^N` RFU_BTUP3_IDX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:num` (X_CHOOSE_THEN `i2:num` (X_CHOOSE_THEN `i3:num`
    STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  SUBGOAL_THEN `&0 <= n` ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (n * (n * K * c) * (n * n * K * K)) +
              &3 * (n * n * ((n * K * (n * c * K)) * K)) +
              n * (n * K * c) * (&3 * (n * n * (K * K)))` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b d A B D. abs a <= A /\ abs b <= B /\ abs d <= D
                  ==> abs(--(&2) * a - b + d) <= (&2 * A + B + D)`) THEN
  REPEAT CONJ_TAC THENL
   [(* the Ricci term *)
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`; `basis i3:real^N`;
                   `rfu_dgam (G1:real^N->real^N^N) G2 y (basis i1) (basis i2)`]
                  RFU_LRICCI_LIN2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                    `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`] RFU_SM_D) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_BD_RIC1 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound]];
    (* the contraction differences *)
    MATCH_MP_TAC(REAL_ARITH
     `!x z w B. abs x <= B /\ abs z <= B /\ abs w <= B ==> abs(x + z - w) <= &3 * B`) THEN
    EXPAND_TAC "n" THEN
    SUBGOAL_THEN
     `!w. rfu_btup 3 w
          ==> abs(ltcontr (G1:real^N->real^N^N)
                    (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y w -
                  ltcontr G2 (ltperm (swap(2,3)) (lnabla 4 G2 (lrm4 G2))) y w)
              <= &(dimindex(:N)) * &(dimindex(:N)) *
                 ((&(dimindex(:N)) * K * (&(dimindex(:N)) * c * K)) * K)`
    (fun th -> REPEAT CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
    X_GEN_TAC `w:num->real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                   `G2:real^N->real^N^N`; `y:real^N`; `w:num->real^N`] RFU_C2_BOUNDS) THEN
    ASM_SIMP_TAC[];
    (* the linear term in (M - I) u3 *)
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`; `basis i1:real^N`;
                   `basis i2:real^N`;
                   `matrix_inv((G2:real^N->real^N^N) y) ** (G1:real^N->real^N^N) y **
                    basis i3`] RFU_LC_LIN3) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`; `basis i1:real^N`;
                   `basis i2:real^N`; `basis i3:real^N`] RFU_LC_LIN3) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_RDISTRIB; GSYM VECTOR_SUB_COMPONENT] THEN
    EXPAND_TAC "n" THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                    `G2:real^N->real^N^N`; `y:real^N`; `i3:num`] RFU_SM_MV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                    `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`; `k:num`]
                   RFU_LC2_BOUND) THEN
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Towards the estimate of Q_t - div X.  The difference of the               *)
(* covariant derivatives of one tensor for two metrics is a Christoffel     *)
(* difference term (RFU_LNABLA_DIFF); Q_t - div X splits into six O(c)      *)
(* pieces (RFU_E_IDENTITY); the first piece is bounded (RFU_E1_BOUND).      *)
(* ========================================================================= *)

let RFU_LNABLA_DIFF = prove
 (`!k U (G1:real^N->real^N^N) G2 (tf:real^N->(num->real^N)->real) y u.
        ltensor_field k U tf /\ y IN U
        ==> lnabla k G1 tf y u - lnabla k G2 tf y u =
            --sum(1..k) (\i. tf y (\j. if j = i then rfu_dgam G1 G2 y (u(k + 1)) (u i)
                                      else u j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; rfu_dgam] THEN
  MATCH_MP_TAC(REAL_ARITH `!d a b s. a - b = s ==> (d - a) - (d - b) = --s`) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                 `y:real^N`; `i:num`; `u:num->real^N`] RFA_SLOT_LINEAR) THEN
  ASM_SIMP_TAC[]);;

let RFU_SLOT_SUB = prove
 (`!k U (tf:real^N->(num->real^N)->real) y i (u:num->real^N) a b.
        ltensor_field k U tf /\ y IN U /\ 1 <= i /\ i <= k
        ==> tf y (\m. if m = i then a else u m) - tf y (\m. if m = i then b else u m) =
            tf y (\m. if m = i then a - b else u m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                 `y:real^N`; `i:num`; `u:num->real^N`] RFA_SLOT_LINEAR) THEN
  ASM_SIMP_TAC[]);;

(* The tuple of the two derivative slots of the Laplacian. *)

let RFU_LTLAP_TDIV = prove
 (`!(G:real^N->real^N^N) T4 y (u:num->real^N).
        ltlap 4 G T4 y u = rfu_tdiv 4 G (lnabla 4 G T4) y u`,
  REWRITE_TAC[ltlap; rfu_tdiv; RFA_LNABLA_ITER_2]);;

let RFU_TDIV_SUB = prove
 (`!U (G:real^N->real^N^N) X1 X2 y (u:num->real^N).
        open U /\ y IN U /\
        (!u. smooth_map_on U (\z. lift(X1 z u))) /\
        (!u. smooth_map_on U (\z. lift(X2 z u)))
        ==> rfu_tdiv 4 G (\z u. X1 z u - X2 z u) y u =
            rfu_tdiv 4 G X1 y u - rfu_tdiv 4 G X2 y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_tdiv; GSYM SUM_SUB_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFU_LRICCI_SUB1 = prove
 (`!U (G:real^N->real^N^N) y v w p.
        metric_field U G /\ y IN U
        ==> lricci G y (v - w) p = lricci G y v p - lricci G y w p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:real^N` o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o MATCH_MP LINEAR_SUB) THEN
  REWRITE_TAC[LIFT_SUB; GSYM LIFT_EQ; LIFT_DROP]);;

(* Q_t - div X as six differences. *)

let RFU_E_IDENTITY = prove
 (`!U (G1:real^N->real^N^N) G2 y u.
        metric_field U G1 /\ metric_field U G2 /\ y IN U
        ==> rfu_qdot G1 G2 y u - rfu_tdiv 4 G1 (rfu_x G1 G2) y u =
            (rfu_tdiv 4 G1 (lnabla 4 G2 (lrm4 G2)) y u -
             rfu_tdiv 4 G2 (lnabla 4 G2 (lrm4 G2)) y u) +
            ltlap 4 G2 (lrm4 G2) y
              (\m. if m = 3 then u 3 - matrix_inv(G2 y) ** G1 y ** u 3 else u m) +
            (rfu_bev G1 (lrm4 G1) (lrm4 G1) y u - rfu_bev G2 (lrm4 G2) (lrm4 G2) y u) +
            rfu_bev G2 (lrm4 G2) (lrm4 G2) y
              (\m. if m = 3 then u 3 - matrix_inv(G2 y) ** G1 y ** u 3 else u m) +
            &2 * (lricci G1 y (u 3) (lriemann G2 y (u 1) (u 2) (u 4)) -
                  lricci G2 y (u 3) (lriemann G2 y (u 1) (u 2) (u 4))) +
            &2 * lricci G2 y (u 3 - matrix_inv(G2 y) ** G1 y ** u 3)
                             (lriemann G2 y (u 1) (u 2) (u 4))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                 `lrm4 (G1:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                 `lrm4 (G2:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`] RFU_EVOL_FIELDS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] RFU_EVOL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfu_qdot; rfu_x] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                 `lnabla 4 (G1:real^N->real^N^N) (lrm4 G1)`;
                 `lnabla 4 (G2:real^N->real^N^N) (lrm4 G2)`; `y:real^N`; `u:num->real^N`]
                RFU_TDIV_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFU_LTLAP_TDIV] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `ltlap 4 (G2:real^N->real^N^N) (lrm4 G2)`;
                 `y:real^N`; `3`; `u:num->real^N`; `(u:num->real^N) 3`;
                 `matrix_inv((G2:real^N->real^N^N) y) ** (G1:real^N->real^N^N) y **
                  (u:num->real^N) 3`] RFU_SLOT_SUB) THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`;
                 `rfu_bev (G2:real^N->real^N^N) (lrm4 G2) (lrm4 G2)`;
                 `y:real^N`; `3`; `u:num->real^N`; `(u:num->real^N) 3`;
                 `matrix_inv((G2:real^N->real^N^N) y) ** (G1:real^N->real^N^N) y **
                  (u:num->real^N) 3`] RFU_SLOT_SUB) THEN
  ASM_REWRITE_TAC[ARITH; RFU_TUPLE3_ID] THEN
  REWRITE_TAC[RFU_LTLAP_TDIV] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`; `(u:num->real^N) 3`;
                 `matrix_inv((G2:real^N->real^N^N) y) ** (G1:real^N->real^N^N) y **
                  (u:num->real^N) 3`;
                 `lriemann (G2:real^N->real^N^N) y ((u:num->real^N) 1) (u 2) (u 4)`]
                RFU_LRICCI_SUB1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFU_BTUP_MONO = prove
 (`!k k' (u:num->real^N). k' <= k /\ rfu_btup k u ==> rfu_btup k' u`,
  REWRITE_TAC[rfu_btup] THEN MESON_TAC[LE_TRANS]);;

let RFU_BTUP_EXT2 = prove
 (`!k (u:num->real^N) a b.
        rfu_btup k u /\ 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> rfu_btup (k + 2)
              (\m. if m = k + 1 then basis a else if m = k + 2 then basis b else u m)`,
  REWRITE_TAC[rfu_btup] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[ARITH_RULE
   `~(m = k + 1) /\ ~(m = k + 2) /\ m <= k + 2 ==> m <= k`]);;

(* The difference of the two divergences of nabla Rm2. *)

let RFU_E1_BOUND = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y u.
          rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
          ==> abs(rfu_tdiv 4 G1 (lnabla 4 G2 (lrm4 G2)) y u -
                  rfu_tdiv 4 G2 (lnabla 4 G2 (lrm4 G2)) y u) <= L * c`,
  GEN_TAC THEN
  EXISTS_TAC `(&(dimindex(:N)) * &(dimindex(:N)) * abs K * (&1 + abs K)) *
              (&(dimindex(:N)) * abs K * (&(dimindex(:N)) * abs K) +
               &5 * &(dimindex(:N)) * &(dimindex(:N)) * abs K)` THEN
  CONJ_TAC THENL [RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ltensor_field 5 U (lnabla 4 (G2:real^N->real^N^N) (lrm4 G2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                   `lrm4 (G2:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[ARITH] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[LRM4_TENSOR_FIELD]; SIMP_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN REWRITE_TAC[rfu_tdiv] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * y * z * w * v * c:real = (x * y * z * w) * (v * c)`] THEN
  MP_TAC(ISPECL
   [`\a b. lnabla 5 (G2:real^N->real^N^N) (lnabla 4 G2 (lrm4 G2)) y
             (\m. if m = 5 then basis a else if m = 6 then basis b else (u:num->real^N) m)`;
    `\a b. lnabla 5 (G1:real^N->real^N^N) (lnabla 4 G2 (lrm4 G2)) y
             (\m. if m = 5 then basis a else if m = 6 then basis b else (u:num->real^N) m)`;
    `\a b. matrix_inv((G2:real^N->real^N^N) y)$a$b`;
    `\a b. matrix_inv((G1:real^N->real^N^N) y)$a$b`;
    `K:real`; `K:real`;
    `(&(dimindex(:N)) * K * (&(dimindex(:N)) * K) +
      &5 * &(dimindex(:N)) * &(dimindex(:N)) * K) * c`] RFU_LBILIN_LIP_CONTR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RFU_POS_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(dimindex(:N)) * K * (&(dimindex(:N)) * c * K)` THEN CONJ_TAC THENL
       [MP_TAC(SPEC_ALL RFU_SM_GINV) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!x y z c:real. x = y * c /\ &0 <= z * c ==> x <= (y + z) * c`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RFU_POS_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `rfu_btup 6 (\m. if m = 5 then basis a else if m = 6 then basis b
                      else (u:num->real^N) m)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`4`; `u:num->real^N`; `a:num`; `b:num`] RFU_BTUP_EXT2) THEN
      ASM_REWRITE_TAC[ARITH];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `G2:real^N->real^N^N`; `lrm4 (G2:real^N->real^N^N)`]
                    RFA_LNABLA_ITER_2) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`6`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                       `lrm4 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[LRM4_TENSOR_FIELD]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `2`) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
        SIMP_TAC[];
        ASM_MESON_TAC[rfu_hyp; rfu_kbound]];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    MP_TAC(ISPECL [`5`; `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                   `lnabla 4 (G2:real^N->real^N^N) (lrm4 G2)`; `y:real^N`;
                   `\m. if m = 5 then basis a else if m = 6 then basis b
                        else (u:num->real^N) m`] RFU_LNABLA_DIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[REAL_ABS_NEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&5 * (&(dimindex(:N)) * (&(dimindex(:N)) * K * c) * K)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      BETA_TAC THEN
      MP_TAC(ISPECL [`6`; `\m. if m = 5 then basis a else if m = 6 then basis b
                               else (u:num->real^N) m`; `i:num`] RFU_BTUP_IDX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
      MATCH_MP_TAC(ISPECL [`5`; `U:real^N->bool`; `lnabla 4 (G2:real^N->real^N^N) (lrm4 G2)`;
                           `y:real^N`] RFU_SLOT_VEC_BOUND) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[rfu_hyp; rfu_kbound];
        MATCH_MP_TAC RFU_BTUP_MONO THEN EXISTS_TAC `6` THEN ASM_REWRITE_TAC[ARITH];
        X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                      `G2:real^N->real^N^N`; `y:real^N`; `b:num`; `j:num`] RFU_SM_D) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q:num`) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
        REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= K * (&(dimindex(:N)) * K * (&(dimindex(:N)) * K)) * c`
    MP_TAC THENL
     [RFU_POS_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* The remaining pieces of Q_t - div X and the estimate RFU_LOT_Q.           *)
(* ========================================================================= *)

let RFU_CB_OF_BTUP = prove
 (`!k (tf:real^N->(num->real^N)->real) y c.
        (!u. rfu_btup k u ==> abs(tf y u) <= c) ==> rfu_cb k tf y c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_cb] THEN X_GEN_TAC `ip:num->num` THEN
  DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[rfu_btup] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
  EXISTS_TAC `(ip:num->num) m` THEN
  MP_TAC(ISPECL [`ip:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let RFU_LTLAP_BOUND = prove
 (`!K c U (G1:real^N->real^N^N) G2 y u.
        rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
        ==> abs(ltlap 4 G2 (lrm4 G2) y u) <=
            &(dimindex(:N)) * &(dimindex(:N)) * K * K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `ltensor_field 6 U (lnabla_iter 4 2 (G2:real^N->real^N^N) (lrm4 G2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G2:real^N->real^N^N`;
                   `lrm4 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LRM4_TENSOR_FIELD]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `2`) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RFU_LTLAP_TDIV; rfu_tdiv] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS] THEN
  MP_TAC(ISPECL [`4`; `G2:real^N->real^N^N`; `lrm4 (G2:real^N->real^N^N)`]
                RFA_LNABLA_ITER_2) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`6`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[rfu_hyp; rfu_kbound];
    MP_TAC(ISPECL [`4`; `u:num->real^N`; `a:num`; `b:num`] RFU_BTUP_EXT2) THEN
    ASM_REWRITE_TAC[ARITH]]);;

(* The component bound of the vector (I - M) u3 entering E2, E4 and E6. *)

let RFU_SM_MV_NEG = prove
 (`!K c U (G1:real^N->real^N^N) G2 y l q.
        rfu_hyp K c U G1 G2 y /\ 1 <= l /\ l <= dimindex(:N) /\
        1 <= q /\ q <= dimindex(:N)
        ==> abs((basis l - matrix_inv(G2 y) ** G1 y ** basis l)$q) <=
            &(dimindex(:N)) * K * c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                `G2:real^N->real^N^N`; `y:real^N`; `l:num`] RFU_SM_MV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `q:num`) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let RFU_E2_BOUND = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y u.
          rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
          ==> abs(ltlap 4 G2 (lrm4 G2) y
                    (\m. if m = 3 then u 3 - matrix_inv(G2 y) ** G1 y ** u 3 else u m))
              <= L * c`,
  GEN_TAC THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * abs K) *
              (&(dimindex(:N)) * &(dimindex(:N)) * abs K * abs K)` THEN
  CONJ_TAC THENL [RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `u:num->real^N`; `3`] RFU_BTUP_IDX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * K * c) *
              (&(dimindex(:N)) * &(dimindex(:N)) * K * K)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(ISPECL [`4`; `U:real^N->bool`; `ltlap 4 (G2:real^N->real^N^N) (lrm4 G2)`;
                       `y:real^N`] RFU_SLOT_VEC_BOUND) THEN
  ASM_REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] RFU_EVOL_FIELDS) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC RFU_CB_OF_BTUP THEN X_GEN_TAC `w:num->real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFU_LTLAP_BOUND THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN MATCH_MP_TAC RFU_SM_MV_NEG THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The reaction terms: a bound for the second metric and the difference. *)

let RFU_BEV_BOUNDS = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y u.
          rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
          ==> abs(rfu_bev G2 (lrm4 G2) (lrm4 G2) y u) <= L /\
              abs(rfu_bev G1 (lrm4 G1) (lrm4 G1) y u -
                  rfu_bev G2 (lrm4 G2) (lrm4 G2) y u) <= L * c`,
  GEN_TAC THEN
  MP_TAC(MATCH_MP RFU_LBILIN_LIP (CONJUNCT1 RFU_BEV)) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L")) o
             SPEC `K:real`) THEN
  EXISTS_TAC `L * (&1 + &(dimindex(:N)) * &(dimindex(:N)) * abs K * abs K +
                   &(dimindex(:N)) * abs K * (&(dimindex(:N)) * abs K))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N)) * &(dimindex(:N)) * K * K /\
                &0 <= &(dimindex(:N)) * K * (&(dimindex(:N)) * K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN RFU_POS_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. rfu_btup 4 w
        ==> abs(lrm4 (G1:real^N->real^N^N) y w) <= K /\
            abs(lrm4 (G2:real^N->real^N^N) y w) <= K /\
            abs(lrm4 G1 y w - lrm4 G2 y w) <=
            (&1 + &(dimindex(:N)) * &(dimindex(:N)) * K * K +
             &(dimindex(:N)) * K * (&(dimindex(:N)) * K)) * c`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:num->real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound];
      MATCH_MP_TAC RFU_CB_BTUP THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 + &(dimindex(:N)) * &(dimindex(:N)) * K * K) * c` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RFU_SM_P THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> abs(matrix_inv((G1:real^N->real^N^N) y)$a$b) <= K /\
              abs(matrix_inv((G2:real^N->real^N^N) y)$a$b) <= K /\
              abs(matrix_inv(G1 y)$a$b - matrix_inv(G2 y)$a$b) <=
              (&1 + &(dimindex(:N)) * &(dimindex(:N)) * K * K +
               &(dimindex(:N)) * K * (&(dimindex(:N)) * K)) * c`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) * K * (&(dimindex(:N)) * c * K)` THEN CONJ_TAC THENL
     [MP_TAC(SPEC_ALL RFU_SM_GINV) THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `&0 <= (&1 + &(dimindex(:N)) * &(dimindex(:N)) * K * K) * c`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L:real` THEN CONJ_TAC THENL
     [USE_THEN "L" (MP_TAC o SPECL
       [`G2:real^N->real^N^N`; `G2:real^N->real^N^N`;
        `lrm4 (G2:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`;
        `lrm4 (G2:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`; `y:real^N`; `&0`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LE_REFL; REAL_SUB_REFL; REAL_ABS_0] THEN ASM_SIMP_TAC[];
        DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC(REAL_ARITH `!L x:real. &0 <= L * x ==> L <= L * (&1 + x)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    USE_THEN "L" (MP_TAC o SPECL
       [`G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
        `lrm4 (G1:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`;
        `lrm4 (G1:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`; `y:real^N`;
        `(&1 + &(dimindex(:N)) * &(dimindex(:N)) * K * K +
          &(dimindex(:N)) * K * (&(dimindex(:N)) * K)) * c`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN ASM_SIMP_TAC[REAL_MUL_ASSOC]]]);;

let RFU_E4_BOUND = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y u.
          rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
          ==> abs(rfu_bev G2 (lrm4 G2) (lrm4 G2) y
                    (\m. if m = 3 then u 3 - matrix_inv(G2 y) ** G1 y ** u 3 else u m))
              <= L * c`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_BEV_BOUNDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * abs K) * L` THEN
  CONJ_TAC THENL [RFU_POS_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `u:num->real^N`; `3`] RFU_BTUP_IDX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * K * c) * L` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(ISPECL [`4`; `U:real^N->bool`;
                       `rfu_bev (G2:real^N->real^N^N) (lrm4 G2) (lrm4 G2)`;
                       `y:real^N`] RFU_SLOT_VEC_BOUND) THEN
  ASM_REWRITE_TAC[ARITH] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`] RFU_EVOL_FIELDS) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC RFU_CB_OF_BTUP THEN X_GEN_TAC `w:num->real^N` THEN DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`; `w:num->real^N`]) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN MATCH_MP_TAC RFU_SM_MV_NEG THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let RFU_E5_BOUND = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y u.
          rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
          ==> abs(lricci G1 y (u 3) (lriemann G2 y (u 1) (u 2) (u 4)) -
                  lricci G2 y (u 3) (lriemann G2 y (u 1) (u 2) (u 4))) <= L * c`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_SM_RIC) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * abs K * abs K) * L` THEN
  CONJ_TAC THENL [RFU_POS_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (m,v) ->
    MP_TAC(ISPECL [`4`; `u:num->real^N`; m] RFU_BTUP_IDX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN v STRIP_ASSUME_TAC))
   [`1`,`i1:num`; `2`,`i2:num`; `3`,`i3:num`; `4`,`i4:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`; `basis i3:real^N`;
                 `lriemann (G2:real^N->real^N^N) y (basis i1) (basis i2) (basis i4)`]
                RFU_LRICCI_LIN2) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`; `basis i3:real^N`;
                 `lriemann (G2:real^N->real^N^N) y (basis i1) (basis i2) (basis i4)`]
                RFU_LRICCI_LIN2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_LDISTRIB] THEN
  SUBGOAL_THEN
   `(&(dimindex(:N)) * (&(dimindex(:N)) * K * K) * L) * c =
    &(dimindex(:N)) * ((&(dimindex(:N)) * K * K) * (L * c))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                  `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`; `i4:num`] RFU_BD_R) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
    USE_THEN "L" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`; `i3:num`; `k:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

let RFU_E6_BOUND = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y u.
          rfu_hyp K c U G1 G2 y /\ rfu_btup 4 u
          ==> abs(lricci G2 y (u 3 - matrix_inv(G2 y) ** G1 y ** u 3)
                             (lriemann G2 y (u 1) (u 2) (u 4))) <= L * c`,
  GEN_TAC THEN
  EXISTS_TAC `&(dimindex(:N)) * (&(dimindex(:N)) * abs K * abs K) *
              (&(dimindex(:N)) * (&(dimindex(:N)) * abs K) *
               (&(dimindex(:N)) * &(dimindex(:N)) * abs K * abs K))` THEN
  CONJ_TAC THENL [RFU_POS_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (m,v) ->
    MP_TAC(ISPECL [`4`; `u:num->real^N`; m] RFU_BTUP_IDX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN v STRIP_ASSUME_TAC))
   [`1`,`i1:num`; `2`,`i2:num`; `3`,`i3:num`; `4`,`i4:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`;
                 `basis i3 - matrix_inv((G2:real^N->real^N^N) y) **
                  (G1:real^N->real^N^N) y ** basis i3`;
                 `lriemann (G2:real^N->real^N^N) y (basis i1) (basis i2) (basis i4)`]
                RFU_LRICCI_LIN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(&(dimindex(:N)) * (&(dimindex(:N)) * K * K) *
     (&(dimindex(:N)) * (&(dimindex(:N)) * K) *
      (&(dimindex(:N)) * &(dimindex(:N)) * K * K))) * c =
    &(dimindex(:N)) * ((&(dimindex(:N)) * K * K) *
     (&(dimindex(:N)) * ((&(dimindex(:N)) * K * c) *
      (&(dimindex(:N)) * &(dimindex(:N)) * K * K))))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`K:real`; `c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                  `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`; `i4:num`] RFU_BD_R) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`;
                 `basis i3 - matrix_inv((G2:real^N->real^N^N) y) **
                  (G1:real^N->real^N^N) y ** basis i3`;
                 `basis k:real^N`] RFU_LRICCI_LIN1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RFU_SUM_ABS_BOUND_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFU_SM_MV_NEG THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFU_BD_RIC1 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[rfu_hyp; rfu_kbound]]);;

let RFU_ABS6_BOUND = prove
 (`!e1 e2 e3 e4 e5 e6 b1 b2 b3 b4 b5 b6:real.
        abs e1 <= b1 /\ abs e2 <= b2 /\ abs e3 <= b3 /\ abs e4 <= b4 /\
        abs e5 <= b5 /\ abs e6 <= b6
        ==> abs(e1 + e2 + e3 + e4 + &2 * e5 + &2 * e6) <=
            b1 + b2 + b3 + b4 + &2 * b5 + &2 * b6`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs e1 + abs e2 + abs e3 + abs e4 + &2 * abs e5 + &2 * abs e6` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Q_t - div X is O(c) in components. *)

let RFU_LOT_Q = prove
 (`!K. ?L. &0 <= L /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> !u. rfu_btup 4 u
                  ==> abs(rfu_qdot G1 G2 y u - rfu_tdiv 4 G1 (rfu_x G1 G2) y u) <= L * c`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_E1_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E1"))) THEN
  MP_TAC(SPEC `K:real` RFU_E2_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E2"))) THEN
  MP_TAC(SPEC `K:real` RFU_BEV_BOUNDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `L3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E3"))) THEN
  MP_TAC(SPEC `K:real` RFU_E4_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `L4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E4"))) THEN
  MP_TAC(SPEC `K:real` RFU_E5_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `L5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E5"))) THEN
  MP_TAC(SPEC `K:real` RFU_E6_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `L6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E6"))) THEN
  EXISTS_TAC `L1 + L2 + L3 + L4 + &2 * L5 + &2 * L6` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`; `u:num->real^N`] RFU_E_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `L1 * c + L2 * c + L3 * c + L4 * c + &2 * (L5 * c) + &2 * (L6 * c)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC RFU_ABS6_BOUND THEN
  MAP_EVERY (fun l ->
    CONJ_TAC THENL
     [USE_THEN l (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC]) ["E1"; "E2"; "E3"; "E4"; "E5"] THEN
  USE_THEN "E6" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `G2:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* Norm-level tools for the local inequality.  Component bound of an inner   *)
(* product (RFU_LTINNER_CB), the curvature action terms of the norm          *)
(* derivatives (RFU_QA_INNER), and the principal part of A_t as              *)
(* a metric-natural bilinear operation (RFU_PA_NORM: |PA|^2 <= C |X|^2).     *)
(* ========================================================================= *)

let RFU_LTINNER_CB = prove
 (`!k (G:real^N->real^N^N) f g y K a b.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(matrix_inv(G y)$i$j) <= K) /\
        rfu_cb k f y a /\ rfu_cb k g y b
        ==> abs(ltinner k G f g y) <=
            &(CARD(index_tuples k (:N))) pow 2 * K pow k * a * b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfu_cb] THEN STRIP_TAC THEN
  REWRITE_TAC[ltinner] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(index_tuples k (:N))) *
              (&(CARD(index_tuples k (:N))) * (a * b * K pow k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
    X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
    X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC RFU_ABS3_BOUND THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RFU_PRODUCT_ABS_BOUND THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let RFU_LTINNER_SELF = prove
 (`!k (G:real^N->real^N^N) f y. ltinner k G f f y = ltnorm2 k G f y`,
  REWRITE_TAC[ltinner; ltnorm2]);;

let RFU_LTINNER_LADD = prove
 (`!k (G:real^N->real^N^N) (f:real^N->(num->real^N)->real) g h y.
        ltinner k G (\z u. f z u + g z u) h y =
        ltinner k G f h y + ltinner k G g h y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltinner] THEN
  REWRITE_TAC[GSYM(MATCH_MP SUM_ADD (SPEC `k:num` LRG_INDEX_TUPLES_FINITE))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  CONV_TAC REAL_RING);;

(* The constant 0-tensor 1. *)

let RFU_ONE_FIELD = prove
 (`!U (G:real^N->real^N^N) y.
        ltensor_field 0 U (\z (u:num->real^N). &1) /\
        (!u:num->real^N. smooth_map_on U (\z. lift((\z (u:num->real^N). &1) z u))) /\
        ltnorm2 0 G (\z (u:num->real^N). &1) y = &1`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field] THEN MESON_TAC[ARITH_RULE `!i. ~(1 <= i /\ i <= 0)`];
    REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    REWRITE_TAC[ltnorm2; LRG_SUM_INDEX_TUPLES_0; PRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    REAL_ARITH_TAC]);;

let RFU_QA_ARITH = prove
 (`!i a s b c n:real.
        i <= a * s * (b * s) /\ &0 <= a /\ b <= c /\ s * s = n /\ &0 <= n
        ==> i <= (a * c) * n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `a * s * (b * s):real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a * s * (b * s) = (a * n) * b /\ (a * c) * n = (a * n) * c:real`
  (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]);;

(* The curvature action term in the derivative of a squared norm. *)

let RFU_QA_INNER = prove
 (`!k. 1 <= k
       ==> !K. ?C. &0 <= C /\
             !U (G:real^N->real^N^N) Tf y.
               metric_field U G /\ y IN U /\ ltensor_field k U Tf /\
               (!u. smooth_map_on U (\z. lift(Tf z u))) /\
               (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                      ==> abs(matrix_inv(G y)$i$j) <= K) /\
               rfu_cb 4 (lrm4 G) y K
               ==> ltinner k G Tf
                     (\z u. sum(1..k) (\l. &2 * rfa_qact l G
                              (ltcontr G (ltperm (swap(2,3)) (lrm4 G))) Tf z u)) y
                   <= C * ltnorm2 k G Tf y`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MP_TAC(MATCH_MP (INST_TYPE [`:N`,`:N`] RFA_QRIC_LBILIN) (ASSUME `1 <= k`)) THEN
  DISCH_THEN(fun th -> LABEL_TAC "lb" th THEN MP_TAC(MATCH_MP RFA_LBILIN_ON_NORM th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cq"))) THEN
  EXISTS_TAC `sqrt C0 * sqrt(&(CARD(index_tuples 4 (:N))) pow 2 * K pow 4 * K pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `6 = 3 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field k U (\z u. sum(1..k) (\l. &2 * rfa_qact l (G:real^N->real^N^N)
                       (ltcontr G (ltperm (swap(2,3)) (lrm4 G))) Tf z u))`
  ASSUME_TAC THENL
   [USE_THEN "lb" (MP_TAC o MATCH_MP RFA_LBILIN_ON_FIELD) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                               `lrm4 (G:real^N->real^N^N)`;
                               `Tf:real^N->(num->real^N)->real`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 k (G:real^N->real^N^N) Tf y` ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFU_QA_ARITH THEN
  EXISTS_TAC `sqrt(ltnorm2 k (G:real^N->real^N^N) Tf y)` THEN
  EXISTS_TAC `sqrt(ltnorm2 4 (G:real^N->real^N^N) (lrm4 G) y)` THEN
  ASM_SIMP_TAC[SQRT_POS_LE; GSYM REAL_POW_2; SQRT_POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_INNER_BIL_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "cq" (MP_TAC o BETA_RULE o
                   SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                          `lrm4 (G:real^N->real^N^N)`;
                          `Tf:real^N->(num->real^N)->real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC RFU_LTNORM2_CB THEN
    ASM_REWRITE_TAC[]]);;

(* The principal part of A_t as a bilinear operation of X and the constant  *)
(* 0-tensor 1, so that |PA|^2 <= C |X|^2 with a universal C.                 *)

let rfu_pax = new_definition
 `rfu_pax (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) =
    \z (u:num->real^N).
      --(ltcontr G (ltperm (swap(2,3)) X) z
           (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) +
         ltcontr G (ltperm (swap(2,3)) X) z
           (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2) -
         ltcontr G (ltperm (swap(2,3)) X) z
           (\m. if m = 1 then u 1 else if m = 2 then u 2 else u 3))`;;

let RFU_PA_PAX = prove
 (`!(G1:real^N->real^N^N) G2. rfu_pa G1 G2 = rfu_pax G1 (rfu_x G1 G2)`,
  REWRITE_TAC[rfu_pa; rfu_pax; rfu_cx]);;

let RFU_SWAPS_3 = prove
 (`swap(1,2) permutes 1..3 /\ swap(2,3) permutes 1..3`,
  CONJ_TAC THEN MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let RFU_CXG_LBILIN = prove
 (`lbilin 3 5 0 (\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
                   (tg:real^N->(num->real^N)->real).
                    ltcontr G (ltperm (swap(2,3)) (ltprod 5 tf tg)))`,
  MP_TAC(ISPECL [`3`; `5`; `0`;
     `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
       (tg:real^N->(num->real^N)->real). ltperm (swap(2,3)) (ltprod 5 tf tg)`]
     (el 2 (CONJUNCTS lbilin_RULES))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`5`; `5`; `0`; `swap(2,3)`;
     `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
       (tg:real^N->(num->real^N)->real). ltprod 5 tf tg`]
     (el 1 (CONJUNCTS lbilin_RULES))) THEN
  BETA_TAC THEN REWRITE_TAC[RFU_SWAP23_PERMUTES] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES]
    (ISPECL [`5`; `0`] (el 0 (CONJUNCTS lbilin_RULES)))));;

let RFU_PAX_LBILIN = prove
 (`lbilin_on 3 5 0 (\(G:real^N->real^N^N) tf tg. rfu_pax G (ltprod 5 tf tg))`,
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  EXISTS_TAC
   `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
     (tg:real^N->(num->real^N)->real) (y:real^N) (u:num->real^N).
       --(&1) * ((ltperm (swap(1,2)) (ltperm (swap(2,3))
                   (ltcontr G (ltperm (swap(2,3)) (ltprod 5 tf tg)))) y u +
                  ltperm (swap(2,3)) (ltcontr G (ltperm (swap(2,3)) (ltprod 5 tf tg))) y u) +
                 --(&1) * ltcontr G (ltperm (swap(2,3)) (ltprod 5 tf tg)) y u)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_LBILIN THEN
    MATCH_MP_TAC(el 4 (CONJUNCTS lbilin_RULES)) THEN
    MATCH_MP_TAC(el 3 (CONJUNCTS lbilin_RULES)) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(el 3 (CONJUNCTS lbilin_RULES)) THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC(el 1 (CONJUNCTS lbilin_RULES)) THEN
             REWRITE_TAC[RFU_SWAPS_3]) THEN
      REWRITE_TAC[RFU_CXG_LBILIN];
      MATCH_MP_TAC(el 4 (CONJUNCTS lbilin_RULES)) THEN
      REWRITE_TAC[ETA_AX; RFU_CXG_LBILIN]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[rfu_pax] THEN BETA_TAC THEN
  MP_TAC(MATCH_MP RFA_LBILIN_TENSOR RFU_CXG_LBILIN) THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                             `tf:real^N->(num->real^N)->real`;
                             `tg:real^N->(num->real^N)->real`]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `CX = ltcontr (G:real^N->real^N^N)
                     (ltperm (swap(2,3)) (ltprod 5 (tf:real^N->(num->real^N)->real) tg))` THEN
  REWRITE_TAC[ltensor_field] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "slot" o CONJUNCT1) THEN
  REWRITE_TAC[ltperm] THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(CX:real^N->(num->real^N)->real) y
       (\m. if m = 1 then u 2 else if m = 2 then u 3 else u 1) =
    CX y (\m. u(swap(1,2) (swap(2,3) m))) /\
    CX y (\m. if m = 1 then u 1 else if m = 2 then u 3 else u 2) =
    CX y (\m. u(swap(2,3) m)) /\
    CX y (\m. if m = 1 then u 1 else if m = 2 then u 2 else u 3) = CX y u`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "slot" MATCH_MP_TAC THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN BETA_TAC THEN
    (SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[swap; ARITH_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFU_PA_NORM = prove
 (`?C. &0 <= C /\
       !U (G1:real^N->real^N^N) G2 y.
         metric_field U G1 /\ metric_field U G2 /\ y IN U
         ==> ltensor_field 3 U (rfu_pa G1 G2) /\
             ltnorm2 3 G1 (rfu_pa G1 G2) y <= C * ltnorm2 5 G1 (rfu_x G1 G2) y`,
  MP_TAC(MATCH_MP RFA_LBILIN_ON_NORM RFU_PAX_LBILIN) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nm"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`] RFU_ONE_FIELD) THEN
  BETA_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfu_pa (G1:real^N->real^N^N) G2 =
    rfu_pax G1 (ltprod 5 (rfu_x G1 G2) (\(z:real^N) (u:num->real^N). &1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RFU_PA_PAX] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ltprod; FUN_EQ_THM] THEN BETA_TAC THEN REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(MATCH_MP RFA_LBILIN_ON_FIELD RFU_PAX_LBILIN) THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                               `rfu_x (G1:real^N->real^N^N) G2`;
                               `\(z:real^N) (u:num->real^N). &1`]) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]; SIMP_TAC[]];
    USE_THEN "nm" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                   `rfu_x (G1:real^N->real^N^N) G2`;
                                   `\(z:real^N) (u:num->real^N). &1`; `y:real^N`]) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[REAL_MUL_RID]]]);;

(* ========================================================================= *)
(* The time derivative of the Kotschwar density (rfu_edot, RFU_EDOT_DERIV)   *)
(* and the O(c^2) estimates of its lower-order parts.                        *)
(* ========================================================================= *)

let rfu_qa = new_definition
 `rfu_qa k (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) =
    \z (u:num->real^N).
      sum(1..k) (\l. &2 * rfa_qact l G (ltcontr G (ltperm (swap(2,3)) (lrm4 G))) Tf z u)`;;

let rfu_edot = new_definition
 `rfu_edot (G1:real^N->real^N^N) (G2:real^N->real^N^N) (y:real^N) =
    (&2 * ltinner 2 G1 (rfu_hh G1 G2) (rfu_hhdot G1 G2) y +
     ltinner 2 G1 (rfu_hh G1 G2) (rfu_qa 2 G1 (rfu_hh G1 G2)) y) +
    (&2 * ltinner 3 G1 (rfu_aa G1 G2) (rfu_aadot G1 G2) y +
     ltinner 3 G1 (rfu_aa G1 G2) (rfu_qa 3 G1 (rfu_aa G1 G2)) y) +
    (&2 * ltinner 4 G1 (rfu_q G1 G2) (rfu_qdot G1 G2) y +
     ltinner 4 G1 (rfu_q G1 G2) (rfu_qa 4 G1 (rfu_q G1 G2)) y)`;;

let RFU_EDOT_DERIV = prove
 (`!U a b (G1:real->real^N->real^N^N) G2 t y.
        lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U
        ==> ((\s. pde_kot_density (G1 s) (G2 s) y) has_real_derivative
             rfu_edot (G1 t) (G2 t) y) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. ltnorm2 2 ((G1:real->real^N->real^N^N) s) (rfu_hh (G1 s) (G2 s)) y +
                  ltnorm2 3 (G1 s) (rfu_aa (G1 s) (G2 s)) y +
                  ltnorm2 4 (G1 s) (rfu_q (G1 s) (G2 s)) y` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `a < s /\ s < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G1:real->real^N->real^N^N`;
                   `s:real`] RFU_FLOW_METRIC) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G2:real->real^N->real^N^N`;
                   `s:real`] RFU_FLOW_METRIC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G1:real->real^N->real^N^N) s`;
                   `(G2:real->real^N->real^N^N) s`; `y:real^N`] RFU_DENS_TERMS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfu_edot; rfu_qa] THEN
  REPEAT(MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC) THEN
  MATCH_MP_TAC RFA_TNORM2_DERIV THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:num->real^N` THEN
  FIRST [MATCH_MP_TAC RFU_HH_DT; MATCH_MP_TAC RFU_AA_DT; MATCH_MP_TAC RFU_Q_DT] THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The density controls the components (c = K^2 sqrt e). *)

let RFU_HYP_DENS = prove
 (`!K U (G1:real^N->real^N^N) G2 y.
        metric_field U G1 /\ metric_field U G2 /\ y IN U /\ rfu_kbound K G1 G2 y
        ==> rfu_hyp K (K pow 2 * sqrt(pde_kot_density G1 G2 y)) U G1 G2 y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`; `K:real`] RFU_DENS_SMALL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[rfu_hyp] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC);;

let RFU_EHH_BOUND = prove
 (`!K. ?C. &0 <= C /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> abs(ltinner 2 G1 (rfu_hh G1 G2) (rfu_hhdot G1 G2) y) <= C * c pow 2`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_SM_RIC) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&(CARD(index_tuples 2 (:N))) pow 2 * K pow 2 * &2 * L` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(index_tuples 2 (:N))) pow 2 * K pow 2 * c * (&2 * L * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_LTINNER_CB THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[rfu_hyp];
      ALL_TAC] THEN
    MATCH_MP_TAC RFU_CB_OF_BTUP THEN X_GEN_TAC `u:num->real^N` THEN DISCH_TAC THEN
    MAP_EVERY (fun (m,v) ->
      MP_TAC(ISPECL [`2`; `u:num->real^N`; m] RFU_BTUP_IDX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN v STRIP_ASSUME_TAC))
     [`1`,`i1:num`; `2`,`i2:num`] THEN
    ASM_REWRITE_TAC[rfu_hhdot] THEN
    USE_THEN "L" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`; `i1:num`; `i2:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let RFU_EAA_BOUND = prove
 (`!K. ?C. &0 <= C /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> abs(ltinner 3 G1 (rfu_aa G1 G2)
                    (\z u. rfu_aadot G1 G2 z u - rfu_pa G1 G2 z u) y) <= C * c pow 2`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_LOT_AA) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&(CARD(index_tuples 3 (:N))) pow 2 * abs K pow 3 * L` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(index_tuples 3 (:N))) pow 2 * K pow 3 * c * (L * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_LTINNER_CB THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[rfu_hyp];
      ALL_TAC] THEN
    MATCH_MP_TAC RFU_CB_OF_BTUP THEN BETA_TAC THEN X_GEN_TAC `u:num->real^N` THEN
    DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let RFU_EQ_BOUND = prove
 (`!K. ?C. &0 <= C /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> abs(ltinner 4 G1 (rfu_q G1 G2)
                    (\z u. rfu_qdot G1 G2 z u - rfu_tdiv 4 G1 (rfu_x G1 G2) z u) y)
              <= C * c pow 2`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_LOT_Q) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&(CARD(index_tuples 4 (:N))) pow 2 * abs K pow 4 * L` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(index_tuples 4 (:N))) pow 2 * K pow 4 * c * (L * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_LTINNER_CB THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[rfu_hyp];
      ALL_TAC] THEN
    MATCH_MP_TAC RFU_CB_OF_BTUP THEN BETA_TAC THEN X_GEN_TAC `u:num->real^N` THEN
    DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

let RFU_Y_NORM = prove
 (`!K. ?C. &0 <= C /\
        !c U (G1:real^N->real^N^N) G2 y.
          rfu_hyp K c U G1 G2 y
          ==> ltnorm2 5 G1 (\z u. lnabla 4 G1 (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y
              <= C * c pow 2`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_LOT_Y) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L"))) THEN
  EXISTS_TAC `&(CARD(index_tuples 5 (:N))) pow 2 * abs K pow 5 * L pow 2` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_POW_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  SUBGOAL_THEN `abs K = K` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(index_tuples 5 (:N))) pow 2 * K pow 5 * (L * c) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_LTNORM2_CB THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RFU_CB_OF_BTUP THEN BETA_TAC THEN X_GEN_TAC `u:num->real^N` THEN
    DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPECL [`c:real`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                                  `G2:real^N->real^N^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `u:num->real^N`) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* The derivative of the density split into the divergence, the -2|X|^2     *)
(* term, the two cross terms and the lower-order rest.                       *)

let RFU_EDOT_SPLIT = prove
 (`!U (G1:real^N->real^N^N) G2 y.
        metric_field U G1 /\ metric_field U G2 /\ y IN U
        ==> rfu_edot G1 G2 y =
            ldiv G1 (rfu_kz G1 G2) y -
            &2 * ltnorm2 5 G1 (rfu_x G1 G2) y -
            &2 * ltinner 5 G1 (rfu_x G1 G2)
                   (\z u. lnabla 4 G1 (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y +
            &2 * ltinner 3 G1 (rfu_aa G1 G2) (rfu_pa G1 G2) y +
            ((&2 * ltinner 2 G1 (rfu_hh G1 G2) (rfu_hhdot G1 G2) y +
              ltinner 2 G1 (rfu_hh G1 G2) (rfu_qa 2 G1 (rfu_hh G1 G2)) y) +
             (&2 * ltinner 3 G1 (rfu_aa G1 G2)
                     (\z u. rfu_aadot G1 G2 z u - rfu_pa G1 G2 z u) y +
              ltinner 3 G1 (rfu_aa G1 G2) (rfu_qa 3 G1 (rfu_aa G1 G2)) y) +
             (&2 * ltinner 4 G1 (rfu_q G1 G2)
                     (\z u. rfu_qdot G1 G2 z u - rfu_tdiv 4 G1 (rfu_x G1 G2) z u) y +
              ltinner 4 G1 (rfu_q G1 G2) (rfu_qa 4 G1 (rfu_q G1 G2)) y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltinner 3 G1 (rfu_aa G1 G2) (rfu_aadot (G1:real^N->real^N^N) G2) y =
    ltinner 3 G1 (rfu_aa G1 G2) (rfu_pa G1 G2) y +
    ltinner 3 G1 (rfu_aa G1 G2) (\z u. rfu_aadot G1 G2 z u - rfu_pa G1 G2 z u) y`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RFA_LTINNER_RADD] THEN MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltinner 4 G1 (rfu_q G1 G2) (rfu_qdot (G1:real^N->real^N^N) G2) y =
    ltinner 4 G1 (rfu_q G1 G2) (rfu_tdiv 4 G1 (rfu_x G1 G2)) y +
    ltinner 4 G1 (rfu_q G1 G2)
      (\z u. rfu_qdot G1 G2 z u - rfu_tdiv 4 G1 (rfu_x G1 G2) z u) y`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RFA_LTINNER_RADD] THEN MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltinner 5 G1 (lnabla 4 G1 (rfu_q G1 G2)) (rfu_x (G1:real^N->real^N^N) G2) y =
    ltnorm2 5 G1 (rfu_x G1 G2) y +
    ltinner 5 G1 (rfu_x G1 G2)
      (\z u. lnabla 4 G1 (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`5`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                   `lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2)`;
                   `rfu_x (G1:real^N->real^N^N) G2`; `y:real^N`] RFA_LTINNER_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM RFU_LTINNER_SELF; GSYM RFA_LTINNER_RADD] THEN
    MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                 `rfu_q (G1:real^N->real^N^N) G2`; `rfu_x (G1:real^N->real^N^N) G2`;
                 `y:real^N`] RFU_DIV_IDENTITY) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM rfu_kz] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[rfu_edot] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFU_KOT_ARITH = prove
 (`!ed D xx x e s ixy iap R bb cp Cr:real.
        ed = D - &2 * xx - &2 * ixy + &2 * iap + R /\
        xx = x pow 2 /\ e = s pow 2 /\
        abs ixy <= x * (bb * s) /\ abs iap <= s * (cp * x) /\ R <= Cr * e
        ==> ed <= D + (Cr + (bb + cp) pow 2 / &2) * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MP_TAC(SPEC `&2 * x - (bb + cp) * s` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

(* The pointwise inequality e_t <= div Z + C e at one time. *)

let RFU_KOT_ALG = prove
 (`!K. ?C. &0 <= C /\
        !U (G1:real^N->real^N^N) G2 y.
          metric_field U G1 /\ metric_field U G2 /\ y IN U /\ rfu_kbound K G1 G2 y
          ==> rfu_edot G1 G2 y <= ldiv G1 (rfu_kz G1 G2) y + C * pde_kot_density G1 G2 y`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_EHH_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ch:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Ch"))) THEN
  MP_TAC(SPEC `K:real` RFU_EAA_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ca:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Ca"))) THEN
  MP_TAC(SPEC `K:real` RFU_EQ_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cq"))) THEN
  MP_TAC(SPEC `K:real` RFU_Y_NORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cy"))) THEN
  MP_TAC(SPEC `K:real` (MATCH_MP (INST_TYPE [`:N`,`:N`] RFU_QA_INNER)
                                 (ARITH_RULE `1 <= 2`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q2"))) THEN
  MP_TAC(SPEC `K:real` (MATCH_MP (INST_TYPE [`:N`,`:N`] RFU_QA_INNER)
                                 (ARITH_RULE `1 <= 3`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q3"))) THEN
  MP_TAC(SPEC `K:real` (MATCH_MP (INST_TYPE [`:N`,`:N`] RFU_QA_INNER)
                                 (ARITH_RULE `1 <= 4`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q4"))) THEN
  MP_TAC(INST_TYPE [`:N`,`:N`] RFU_PA_NORM) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cp"))) THEN
  EXISTS_TAC `(&2 * (Ch + Ca + Cq) * K pow 4 + Q2 + Q3 + Q4) +
              (sqrt(Cy * K pow 4) + sqrt Cp) pow 2 / &2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS] THEN
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `rfu_hyp K (K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)) U G1 G2 y`
  ASSUME_TAC THENL [MATCH_MP_TAC RFU_HYP_DENS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFU_HYP_BASICS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "Cp" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `G2:real^N->real^N^N`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `rfu_cb 4 (lrm4 (G1:real^N->real^N^N)) y K` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfu_kbound]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 5 U
      (\z u. lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2) z u - rfu_x G1 G2 z u)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G1:real^N->real^N^N`;
                   `rfu_q (G1:real^N->real^N^N) G2`] LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[ARITH] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)) pow 2 =
    K pow 4 * pde_kot_density G1 G2 y`
  (LABEL_TAC "cc") THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y` ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 3 (G1:real^N->real^N^N) (rfu_pa G1 G2) y` ASSUME_TAC THENL
   [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= pde_kot_density (G1:real^N->real^N^N) G2 y` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RFU_KOT_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y`;
    `sqrt(ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y)`;
    `sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
    `ltinner 5 G1 (rfu_x G1 G2)
       (\z u. lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y`;
    `ltinner 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) (rfu_pa G1 G2) y`;
    `(&2 * ltinner 2 G1 (rfu_hh G1 G2) (rfu_hhdot (G1:real^N->real^N^N) G2) y +
      ltinner 2 G1 (rfu_hh G1 G2) (rfu_qa 2 G1 (rfu_hh G1 G2)) y) +
     (&2 * ltinner 3 G1 (rfu_aa G1 G2)
             (\z u. rfu_aadot G1 G2 z u - rfu_pa G1 G2 z u) y +
      ltinner 3 G1 (rfu_aa G1 G2) (rfu_qa 3 G1 (rfu_aa G1 G2)) y) +
     (&2 * ltinner 4 G1 (rfu_q G1 G2)
             (\z u. rfu_qdot G1 G2 z u - rfu_tdiv 4 G1 (rfu_x G1 G2) z u) y +
      ltinner 4 G1 (rfu_q G1 G2) (rfu_qa 4 G1 (rfu_q G1 G2)) y)`] THEN
  REPEAT CONJ_TAC THENL
   [(* the splitting identity *)
    MATCH_MP_TAC RFU_EDOT_SPLIT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_POW_2];
    ASM_SIMP_TAC[SQRT_POW_2];
    (* the X-Y cross term *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sqrt(ltnorm2 5 (G1:real^N->real^N^N) (rfu_x G1 G2) y) *
      sqrt(ltnorm2 5 G1
        (\z u. lnabla 4 (G1:real^N->real^N^N) (rfu_q G1 G2) z u - rfu_x G1 G2 z u) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_ABS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    USE_THEN "Cy" (MP_TAC o SPECL
      [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
       `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "cc" SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC];
    (* the A-PA cross term *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sqrt(ltnorm2 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) y) *
      sqrt(ltnorm2 3 G1 (rfu_pa G1 G2) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTINNER_ABS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[]];
    (* the lower-order rest *)
    ALL_TAC] THEN
  USE_THEN "Ch" (MP_TAC o SPECL
    [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
     `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
  USE_THEN "Ca" (MP_TAC o SPECL
    [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
     `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
  USE_THEN "Cq" (MP_TAC o SPECL
    [`K pow 2 * sqrt(pde_kot_density (G1:real^N->real^N^N) G2 y)`;
     `U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`; `y:real^N`]) THEN
  USE_THEN "Q2" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `rfu_hh (G1:real^N->real^N^N) G2`; `y:real^N`]) THEN
  USE_THEN "Q3" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `rfu_aa (G1:real^N->real^N^N) G2`; `y:real^N`]) THEN
  USE_THEN "Q4" (MP_TAC o SPECL [`U:real^N->bool`; `G1:real^N->real^N^N`;
                                 `rfu_q (G1:real^N->real^N^N) G2`; `y:real^N`]) THEN
  REWRITE_TAC[GSYM rfu_qa] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "cc" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  SUBGOAL_THEN
   `Q2 * ltnorm2 2 (G1:real^N->real^N^N) (rfu_hh G1 G2) y <= Q2 * pde_kot_density G1 G2 y /\
    Q3 * ltnorm2 3 (G1:real^N->real^N^N) (rfu_aa G1 G2) y <= Q3 * pde_kot_density G1 G2 y /\
    Q4 * ltnorm2 4 (G1:real^N->real^N^N) (rfu_q G1 G2) y <= Q4 * pde_kot_density G1 G2 y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The local Kotschwar inequality for two local Ricci flows on one chart     *)
(* domain: e_t = rfu_edot <= div Z + C e, with C depending only on the bound *)
(* K of the two metrics, their inverses and the curvature tensors (with two *)
(* covariant derivatives of Rm2) at the point.                              *)

let RFU_KOT_LOCAL = prove
 (`!K. ?C. &0 <= C /\
        !U a b (G1:real->real^N->real^N^N) G2 t y.
          lricci_flow U a b G1 /\ lricci_flow U a b G2 /\ a < t /\ t < b /\ y IN U /\
          rfu_kbound K (G1 t) (G2 t) y
          ==> ((\s. pde_kot_density (G1 s) (G2 s) y) has_real_derivative
               rfu_edot (G1 t) (G2 t) y) (atreal t) /\
              rfu_edot (G1 t) (G2 t) y <=
              ldiv (G1 t) (rfu_kz (G1 t) (G2 t)) y +
              C * pde_kot_density (G1 t) (G2 t) y`,
  GEN_TAC THEN
  MP_TAC(SPEC `K:real` RFU_KOT_ALG) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFU_EDOT_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    USE_THEN "C" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[RFU_FLOW_METRIC]]);;

(* ========================================================================= *)
(* The Kotschwar density vanishes only where the two metrics agree           *)
(* (PDE_KOT_DENSITY_ZERO).                                                   *)
(* ========================================================================= *)

let RFU_LTNORM2_ZERO_CB = prove
 (`!k U (G:real^N->real^N^N) tf y.
        metric_field U G /\ ltensor_field k U tf /\ y IN U /\ ltnorm2 k G tf y = &0
        ==> rfu_cb k tf y (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `sum(1..dimindex(:N)) (\i. abs((G:real^N->real^N^N) y$i$i))`]
                RFU_CB_LTNORM2) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; SQRT_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= s ==> x <= s`) THEN
  MP_TAC(ISPECL [`\j. abs((G:real^N->real^N^N) y$j$j)`; `1..dimindex(:N)`; `i:num`]
                GRGT_MEMBER_LE_SUM) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ABS_POS]);;

let PDE_KOT_DENSITY_ZERO = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) top g1 g2 x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
        riemannian_metric atlas g2 /\ x IN topspace top
        ==> &0 <= pde_mkot_density atlas g1 g2 x /\
            (pde_mkot_density atlas g1 g2 x = &0 ==> g1 x = g2 x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (g1:A->real^N^N)) /\
    metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (g2:A->real^N^N)) /\
    SND (c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric; FUN_IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[pde_mkot_density] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g2:A->real^N^N)`;
                 `SND (c:(A->bool)#(A->real^N)) x`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 2 (metric_local atlas c (g1:A->real^N^N))
      (rfu_hh (metric_local atlas c g1) (metric_local atlas c (g2:A->real^N^N)))
      (SND (c:(A->bool)#(A->real^N)) x) = &0`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g2:A->real^N^N)`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N)`;
                 `rfu_hh (metric_local atlas c (g1:A->real^N^N))
                         (metric_local atlas c (g2:A->real^N^N))`;
                 `SND (c:(A->bool)#(A->real^N)) x`] RFU_LTNORM2_ZERO_CB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g1:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g2:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `rfu_hh (metric_local atlas c (g1:A->real^N^N))
                         (metric_local atlas c (g2:A->real^N^N))`;
                 `SND (c:(A->bool)#(A->real^N)) x`; `&0`;
                 `\m. if m = 1 then basis i else basis j:real^N`] RFU_CB_BTUP) THEN
  ASM_SIMP_TAC[RFU_BTUP_LIST2] THEN
  REWRITE_TAC[rfu_hh; lmetric2; ARITH] THEN
  ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chart invariance of local two-metric scalars.                             *)
(* ------------------------------------------------------------------------- *)

let RFU_CHART2_SCALAR = prove
 (`!(Qf:(real^N->real^N^N)->(real^N->real^N^N)->real^N->real)
    (top:A topology) atlas (g1:A->real^N^N) g2 U phi V psi x.
     (!U U' (h:real^N->real^N) h' G1 G2 y.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> Qf (mpullback h G1) (mpullback h G2) y = Qf G1 G2 (h y)) /\
     (!G1 G2 G1' G2' s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G1' z /\ G2 z = G2' z)
        ==> Qf G1 G2 y = Qf G1' G2' y) /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
     riemannian_metric atlas g2 /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
     x IN U INTER V
     ==> Qf (metric_local atlas (U,phi) g1) (metric_local atlas (U,phi) g2) (phi x) =
         Qf (metric_local atlas (V,psi) g1) (metric_local atlas (V,psi) g2) (psi x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pb")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:A->real^N^N. riemannian_metric atlas g
                    ==> metric_field (IMAGE (psi:A->real^N) (U INTER V))
                                     (metric_local atlas (V,psi) g)`
  (fun th -> STRIP_ASSUME_TAC(CONJ
     (MATCH_MP th (ASSUME `riemannian_metric atlas (g1:A->real^N^N)`))
     (MATCH_MP th (ASSUME `riemannian_metric atlas (g2:A->real^N^N)`)))) THENL
   [GEN_TAC THEN REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `(Qf:(real^N->real^N^N)->(real^N->real^N^N)->real^N->real)
      (mpullback (chart_trans (U,phi) (V,psi))
                 (metric_local atlas (V,psi) (g1:A->real^N^N)))
      (mpullback (chart_trans (U,phi) (V,psi))
                 (metric_local atlas (V,psi) (g2:A->real^N^N))) (phi(x:A))` THEN
  CONJ_TAC THENL
   [USE_THEN "loc" MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      CONJ_TAC THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  USE_THEN "pb" (MP_TAC o SPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g1:A->real^N^N)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g2:A->real^N^N)`;
    `(phi:A->real^N) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CHART_TRANS_AT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The three tensors of the density are natural under diffeomorphisms. *)

let RFU_HH_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y u.
        diffeomorphism_on U' U h h' /\ y IN U'
        ==> rfu_hh (mpullback h G1) (mpullback h G2) y u =
            ltpullback h (rfu_hh G1 G2) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfu_hh; lmetric2; ltpullback] THEN ASM_SIMP_TAC[LRG_MPULLBACK_DOT]);;

let RFU_AA_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y u.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> rfu_aa (mpullback h G1) (mpullback h G2) y u =
            ltpullback h (rfu_aa G1 G2) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfu_aa; rfu_low3; rfu_dgam; ltpullback] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[LINEAR_SUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G1:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`] LCHRISTOFFEL_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G2:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`] LCHRISTOFFEL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN VECTOR_ARITH_TAC);;

let RFU_Q_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y u.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> rfu_q (mpullback h G1) (mpullback h G2) y u =
            ltpullback h (rfu_q G1 G2) y u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfu_q; rfu_low4; rfu_drm; ltpullback] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[LINEAR_SUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G1:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`]
                LRIEMANN_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G2:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`]
                LRIEMANN_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let RFU_DENS_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> pde_kot_density (mpullback h G1) (mpullback h G2) y =
            pde_kot_density G1 G2 (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G1) /\
                metric_field U' (mpullback (h:real^N->real^N) G2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h':real^N->real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U':real^N->bool`; `mpullback (h:real^N->real^N) G1`;
                 `mpullback (h:real^N->real^N) G2`; `y:real^N`] RFU_DENS_TERMS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `(h:real^N->real^N) y`] RFU_DENS_TERMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 2 (mpullback (h:real^N->real^N) G1)
                          (ltpullback h (rfu_hh G1 G2)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC RFU_HH_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTNORM2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 3 (mpullback (h:real^N->real^N) G1)
                          (ltpullback h (rfu_aa G1 G2)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC RFU_AA_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTNORM2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 4 (mpullback (h:real^N->real^N) G1)
                          (ltpullback h (rfu_q G1 G2)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC RFU_Q_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LTNORM2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]]]);;

let RFU_DENS_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 G1' G2' s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G1' z /\ G2 z = G2' z)
        ==> pde_kot_density G1 G2 y = pde_kot_density G1' G2' y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G1' y /\ (G2:real^N->real^N^N) y = G2' y`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!a b. christoffel (G1:real^N->real^N^N) y a b = christoffel G1' y a b) /\
    (!a b. christoffel (G2:real^N->real^N^N) y a b = christoffel G2' y a b) /\
    (!a b d. lriemann (G1:real^N->real^N^N) y a b d = lriemann G1' y a b d) /\
    (!a b d. lriemann (G2:real^N->real^N^N) y a b d = lriemann G2' y a b d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL; MATCH_MP_TAC CHRISTOFFEL_LOCAL;
      MATCH_MP_TAC LRIEMANN_LOCAL; MATCH_MP_TAC LRIEMANN_LOCAL] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_kot_density] THEN
  BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
  ASM_REWRITE_TAC[lmetric2]);;

(* The density may be read in any chart. *)

let RFU_MKOT_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) g2 c x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
        riemannian_metric atlas g2 /\ c IN atlas /\ x IN FST c
        ==> pde_mkot_density atlas g1 g2 x =
            pde_kot_density (metric_local atlas c g1) (metric_local atlas c g2) (SND c x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[pde_mkot_density] THEN
  UNDISCH_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A) IN atlas` THEN
  UNDISCH_TAC `(x:A) IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)` THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `cc:(A->bool)#(A->real^N)`) THEN
  UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN atlas` THEN
  UNDISCH_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THEN
  SPEC_TAC(`c:(A->bool)#(A->real^N)`, `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `pde_kot_density:(real^N->real^N^N)->(real^N->real^N^N)->real^N->real`
                 RFU_CHART2_SCALAR) THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_DENS_PULLBACK THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_DENS_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The Kotschwar vector field Z = rfu_kz is natural under diffeomorphisms    *)
(* (RFU_KZ_PULLBACK): it transforms with the Jacobian.                       *)
(* ========================================================================= *)

let RFU_LTINNER_POLAR = prove
 (`!k U (G:real^N->real^N^N) f g y.
        metric_field U G /\ y IN U
        ==> ltinner k G f g y =
            (ltnorm2 k G (\z u. f z u + g z u) y - ltnorm2 k G f y - ltnorm2 k G g y) / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RFU_LTINNER_SELF] THEN
  REWRITE_TAC[RFU_LTINNER_LADD; RFA_LTINNER_RADD] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `g:real^N->(num->real^N)->real`; `f:real^N->(num->real^N)->real`;
                 `y:real^N`] RFA_LTINNER_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFU_LTINNER_EQ = prove
 (`!k (G:real^N->real^N^N) f f' g g' y.
        (!u. f y u = f' y u) /\ (!u. g y u = g' y u)
        ==> ltinner k G f g y = ltinner k G f' g' y`,
  SIMP_TAC[ltinner]);;

let RFU_LTINNER_PULLBACK = prove
 (`!k U U' (h:real^N->real^N) h' G f g y.
        metric_field U G /\ diffeomorphism_on U' U h h' /\
        ltensor_field k U f /\ ltensor_field k U g /\ y IN U'
        ==> ltinner k (mpullback h G) (ltpullback h f) (ltpullback h g) y =
            ltinner k G f g (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U' (mpullback (h:real^N->real^N) G)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `h':real^N->real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U':real^N->bool`; `mpullback (h:real^N->real^N) G`;
                 `ltpullback (h:real^N->real^N) f`; `ltpullback (h:real^N->real^N) g`;
                 `y:real^N`] RFU_LTINNER_POLAR) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `f:real^N->(num->real^N)->real`; `g:real^N->(num->real^N)->real`;
                 `(h:real^N->real^N) y`] RFU_LTINNER_POLAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `(\z u. ltpullback (h:real^N->real^N) f z u + ltpullback h g z u) =
    ltpullback h (\z u. f z u + g z u)`
  SUBST1_TAC THENL [REWRITE_TAC[ltpullback; FUN_EQ_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field k U (\z u. (f:real^N->(num->real^N)->real) z u + g z u)`
  ASSUME_TAC THENL [MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun t ->
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G:real^N->real^N^N`; t; `y:real^N`]
                  LTNORM2_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC)
   [`f:real^N->(num->real^N)->real`; `g:real^N->(num->real^N)->real`;
    `\z u. (f:real^N->(num->real^N)->real) z u + g z u`] THEN
  REFL_TAC);;

let RFU_NABLA_RM_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G y u.
        metric_field U G /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> lnabla 4 (mpullback h G) (lrm4 (mpullback h G)) y u =
            ltpullback h (lnabla 4 G (lrm4 G)) y u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (U':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 4 (mpullback (h:real^N->real^N) G) (ltpullback h (lrm4 G)) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LRM4_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC LNABLA_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let RFU_X_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y u.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> rfu_x (mpullback h G1) (mpullback h G2) y u =
            ltpullback h (rfu_x G1 G2) y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_x] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G1:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]
                RFU_NABLA_RM_PULLBACK) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G2:real^N->real^N^N`; `y:real^N`; `u:num->real^N`]
                RFU_NABLA_RM_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ltpullback]);;

let RFU_MATINV_PULLBACK_VEC = prove
 (`!(M:real^N^N) (G:real^N^N) (w:real^N).
        invertible M /\ invertible G
        ==> M ** (matrix_inv(transp M ** G ** M) ** (transp M ** w)) = matrix_inv G ** w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(M:real^N^N)) /\ invertible((G:real^N^N) ** M)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INVERTIBLE_TRANSP; INVERTIBLE_MATRIX_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID]);;

(* The covector 2 <Q, X(..,v)> transforms by the transpose Jacobian. *)

let RFU_KZ_COVECTOR = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y b.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\
        y IN U' /\ 1 <= b /\ b <= dimindex(:N)
        ==> ltinner 4 (mpullback h G1) (rfu_q (mpullback h G1) (mpullback h G2))
              (\z u. rfu_x (mpullback h G1) (mpullback h G2) z
                       (\m. if m = 5 then basis b else u m)) y =
            sum(1..dimindex(:N))
              (\c. matrix(frechet_derivative h (at y))$c$b *
                   ltinner 4 G1 (rfu_q G1 G2)
                     (\z u. rfu_x G1 G2 z (\m. if m = 5 then basis c else u m)) (h y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_DENS_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
                RFU_X_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `ltinner 4 (mpullback (h:real^N->real^N) G1) (ltpullback h (rfu_q G1 G2))
      (ltpullback h (\z u. rfu_x G1 G2 z
         (\m. if m = 5 then frechet_derivative h (at y) (basis b) else u m))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFU_LTINNER_EQ THEN CONJ_TAC THEN X_GEN_TAC `u:num->real^N` THENL
     [MATCH_MP_TAC RFU_Q_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[];
      BETA_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                     `h':real^N->real^N`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                     `y:real^N`; `\m. if m = 5 then basis b else (u:num->real^N) m`]
                    RFU_X_PULLBACK) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ltpullback] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `G1:real^N->real^N^N`; `rfu_q (G1:real^N->real^N^N) G2`;
                 `\z u. rfu_x (G1:real^N->real^N^N) G2 z
                     (\m. if m = 5 then frechet_derivative (h:real^N->real^N) (at y) (basis b)
                          else u m)`; `y:real^N`] RFU_LTINNER_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `rfu_x (G1:real^N->real^N^N) G2`;
                   `frechet_derivative (h:real^N->real^N) (at y) (basis b)`]
                  RFA_FIX_SLOT_FIELD) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `ltinner 4 (G1:real^N->real^N^N) (rfu_q G1 G2)
      (\z u. sum(1..dimindex(:N))
        (\c. (frechet_derivative (h:real^N->real^N) (at y) (basis b))$c *
             rfu_x G1 G2 z (\m. if m = 5 then basis c else u m))) (h y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN GEN_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_SLOT_EXPAND THEN
    UNDISCH_TAC `ltensor_field 5 U (rfu_x (G1:real^N->real^N^N) G2)` THEN
    REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) y`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[RFA_LTINNER_RSUM; FINITE_NUMSEG] THEN REWRITE_TAC[RFA_LTINNER_RCMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT]);;

let RFU_KZ_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G1 G2 y.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> frechet_derivative h (at y) (rfu_kz (mpullback h G1) (mpullback h G2) y) =
            rfu_kz G1 G2 (h y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_INV_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `U':real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(matrix(frechet_derivative (h:real^N->real^N) (at y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
    EXISTS_TAC `matrix(frechet_derivative (h':real^N->real^N)
                                          (at ((h:real^N->real^N) y)))` THEN
    ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
    SUBGOAL_THEN
     `frechet_derivative (h':real^N->real^N) (at ((h:real^N->real^N) y)) o
      frechet_derivative h (at y) = (\x. x)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[MATRIX_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G1:real^N->real^N^N) ((h:real^N->real^N) y))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  REWRITE_TAC[rfu_kz; rfu_vf] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN
   `(lambda b. &2 * ltinner 4 (mpullback (h:real^N->real^N) G1)
                      (rfu_q (mpullback h G1) (mpullback h G2))
                      (\z' u. rfu_x (mpullback h G1) (mpullback h G2) z'
                                (\m. if m = 5 then basis b else u m)) y):real^N =
    transp(matrix(frechet_derivative h (at y))) **
    (lambda b. &2 * ltinner 4 G1 (rfu_q G1 G2)
                      (\z u. rfu_x G1 G2 z (\m. if m = 5 then basis b else u m)) (h y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                   `y:real^N`; `b:num`] RFU_KZ_COVECTOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[dot; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; TRANSP_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `frechet_derivative (h:real^N->real^N) (at y)` MATRIX_WORKS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[mpullback] THEN MATCH_MP_TAC RFU_MATINV_PULLBACK_VEC THEN
  ASM_REWRITE_TAC[]);;

let RFU_LTINNER_EQ2 = prove
 (`!k (G:real^N->real^N^N) G' f f' g g' y.
        G y = G' y /\ (!u. f y u = f' y u) /\ (!u. g y u = g' y u)
        ==> ltinner k G f g y = ltinner k G' f' g' y`,
  SIMP_TAC[ltinner]);;

let RFU_KZ_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 G1' G2' s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G1' z /\ G2 z = G2' z)
        ==> rfu_kz G1 G2 y = rfu_kz G1' G2' y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z a b d. z IN s ==> lriemann (G1:real^N->real^N^N) z a b d = lriemann G1' z a b d /\
                         lriemann (G2:real^N->real^N^N) z a b d = lriemann G2' z a b d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRIEMANN_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z u. z IN s ==> lrm4 (G1:real^N->real^N^N) z u = lrm4 G1' z u /\
                     lrm4 (G2:real^N->real^N^N) z u = lrm4 G2' z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u. rfu_x (G1:real^N->real^N^N) G2 y u = rfu_x G1' G2' y u` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[rfu_x] THEN BINOP_TAC THEN MATCH_MP_TAC LRG_LNABLA_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. rfu_q (G1:real^N->real^N^N) G2 y u = rfu_q G1' G2' y u` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[rfu_q; rfu_low4; rfu_drm] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G1' y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfu_kz; rfu_vf] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFU_LTINNER_EQ2 THEN ASM_REWRITE_TAC[]);;

(* Chart invariance of local two-metric vector fields. *)

let RFU_CHART2_VECTOR = prove
 (`!(Qf:(real^N->real^N^N)->(real^N->real^N^N)->real^N->real^N)
    (top:A topology) atlas (g1:A->real^N^N) g2 U phi V psi x.
     (!U U' (h:real^N->real^N) h' G1 G2 y.
        metric_field U G1 /\ metric_field U G2 /\ diffeomorphism_on U' U h h' /\ y IN U'
        ==> frechet_derivative h (at y) (Qf (mpullback h G1) (mpullback h G2) y) =
            Qf G1 G2 (h y)) /\
     (!G1 G2 G1' G2' s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G1' z /\ G2 z = G2' z)
        ==> Qf G1 G2 y = Qf G1' G2' y) /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
     riemannian_metric atlas g2 /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
     x IN U INTER V
     ==> chart_jac (U,phi) (V,psi) x
           (Qf (metric_local atlas (U,phi) g1) (metric_local atlas (U,phi) g2) (phi x)) =
         Qf (metric_local atlas (V,psi) g1) (metric_local atlas (V,psi) g2) (psi x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pb")
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:A->real^N^N. riemannian_metric atlas g
                    ==> metric_field (IMAGE (psi:A->real^N) (U INTER V))
                                     (metric_local atlas (V,psi) g)`
  (fun th -> STRIP_ASSUME_TAC(CONJ
     (MATCH_MP th (ASSUME `riemannian_metric atlas (g1:A->real^N^N)`))
     (MATCH_MP th (ASSUME `riemannian_metric atlas (g2:A->real^N^N)`)))) THENL
   [GEN_TAC THEN REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Qf:(real^N->real^N^N)->(real^N->real^N^N)->real^N->real^N)
      (metric_local atlas (U,phi) (g1:A->real^N^N))
      (metric_local atlas (U,phi) (g2:A->real^N^N)) (phi(x:A)) =
    Qf (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g1))
       (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g2)) (phi x)`
  SUBST1_TAC THENL
   [USE_THEN "loc" MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      CONJ_TAC THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  REWRITE_TAC[chart_jac; SND] THEN
  USE_THEN "pb" (MP_TAC o SPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g1:A->real^N^N)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g2:A->real^N^N)`;
    `(phi:A->real^N) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CHART_TRANS_AT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The Kotschwar field on the manifold, in preferred coordinates, and its    *)
(* representative in any chart.                                              *)

let rfu_mkz = new_definition
 `rfu_mkz (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) (g2:A->real^N^N)
          (x:A) =
    rfu_kz (metric_local atlas (chart_at atlas x) g1)
           (metric_local atlas (chart_at atlas x) g2) (SND(chart_at atlas x) x)`;;

let RFU_MKZ_VREP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) g2 c y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g1 /\
        riemannian_metric atlas g2 /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_vrep atlas (rfu_mkz atlas g1 g2) c y =
            rfu_kz (metric_local atlas c g1) (metric_local atlas c g2) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
                SND c (chart_inv c y) = y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_vrep; rfu_mkz] THEN
  UNDISCH_TAC `SND (c:(A->bool)#(A->real^N)) (chart_inv c y) = y` THEN
  UNDISCH_TAC `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c` THEN
  SPEC_TAC(`chart_inv (c:(A->bool)#(A->real^N)) y`,`x:A`) THEN
  X_GEN_TAC `x:A` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A) IN atlas` THEN
  UNDISCH_TAC `(x:A) IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)` THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `cc:(A->bool)#(A->real^N)`) THEN
  UNDISCH_TAC `(c:(A->bool)#(A->real^N)) IN atlas` THEN
  UNDISCH_TAC `(x:A) IN FST(c:(A->bool)#(A->real^N))` THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th ->
    if can (find_term (fun t -> t = `c:(A->bool)#(A->real^N)`)) (concl th)
    then ALL_TAC else ASSUME_TAC th)) THEN
  SPEC_TAC(`c:(A->bool)#(A->real^N)`, `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `rfu_kz:(real^N->real^N^N)->(real^N->real^N^N)->real^N->real^N`
                 RFU_CHART2_VECTOR) THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_KZ_PULLBACK THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_KZ_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Joint smoothness in (t,y) of the density and of the Kotschwar field for   *)
(* smooth families of local metrics (lrg_lsmooth).                           *)
(* ========================================================================= *)

let RFU_LSMOOTH_LTINNER = prove
 (`!k U ta tb (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real) Sf.
     lrg_lsmooth U ta tb G /\
     (!u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
            (\z. lift(Tf (drop(fstcart z)) (sndcart z) u))) /\
     (!u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
            (\z. lift(Sf (drop(fstcart z)) (sndcart z) u)))
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(ltinner k (G (drop(fstcart z))) (Tf (drop(fstcart z)))
                       (Sf (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[ltinner] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_PRODUCT_REAL THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; LRG_LSMOOTH_GINV_ENTRY]);;

let RFU_LSMOOTH_LTNORM2 = prove
 (`!k U ta tb (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real).
     lrg_lsmooth U ta tb G /\
     (!u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
            (\z. lift(Tf (drop(fstcart z)) (sndcart z) u)))
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(ltnorm2 k (G (drop(fstcart z))) (Tf (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RFU_LTINNER_SELF] THEN
  MATCH_MP_TAC RFU_LSMOOTH_LTINNER THEN ASM_REWRITE_TAC[]);;

let RFU_LSMOOTH_DOTMAT = prove
 (`!U ta tb (G:real->real^N->real^N^N) (B:real^(1,N)finite_sum->real^N) a.
     lrg_lsmooth U ta tb G /\ smooth_map_on (interval(lift ta,lift tb) PCROSS U) B
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(a dot (G (drop(fstcart z)) (sndcart z) ** B z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `(\z. lift(a dot ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
                     (B:real^(1,N)finite_sum->real^N) z))) =
    (\x. lift(a dot x)) o (\z. G (drop(fstcart z)) (sndcart z) ** B z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_LIFT_DOT] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[o_DEF]);;

let RFU_LSMOOTH_TENSORS = prove
 (`!U ta tb (G1:real->real^N->real^N^N) G2.
     lrg_lsmooth U ta tb G1 /\ lrg_lsmooth U ta tb G2
     ==> !u. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
               (\z. lift(rfu_hh (G1 (drop(fstcart z))) (G2 (drop(fstcart z)))
                                (sndcart z) u)) /\
             smooth_map_on (interval(lift ta,lift tb) PCROSS U)
               (\z. lift(rfu_aa (G1 (drop(fstcart z))) (G2 (drop(fstcart z)))
                                (sndcart z) u)) /\
             smooth_map_on (interval(lift ta,lift tb) PCROSS U)
               (\z. lift(rfu_q (G1 (drop(fstcart z))) (G2 (drop(fstcart z)))
                               (sndcart z) u)) /\
             smooth_map_on (interval(lift ta,lift tb) PCROSS U)
               (\z. lift(rfu_x (G1 (drop(fstcart z))) (G2 (drop(fstcart z)))
                               (sndcart z) u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rfu_hh; lmetric2; LIFT_SUB] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC RFU_LSMOOTH_DOTMAT THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    REWRITE_TAC[rfu_aa; rfu_low3; rfu_dgam] THEN
    MATCH_MP_TAC RFU_LSMOOTH_DOTMAT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL];
    REWRITE_TAC[rfu_q; rfu_low4; rfu_drm] THEN
    MATCH_MP_TAC RFU_LSMOOTH_DOTMAT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[LRG_LSMOOTH_LRIEMANN];
    REWRITE_TAC[rfu_x; LIFT_SUB] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM RFA_LNABLA_ITER_1] THEN ASM_SIMP_TAC[RFA_LSMOOTH_LRM_DERIV]]);;

let RFU_DENS_LSMOOTH = prove
 (`!U ta tb (G1:real->real^N->real^N^N) G2.
     lrg_lsmooth U ta tb G1 /\ lrg_lsmooth U ta tb G2
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(pde_kot_density (G1 (drop(fstcart z))) (G2 (drop(fstcart z)))
                                      (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `G1:real->real^N->real^N^N`;
                 `G2:real->real^N->real^N^N`] RFU_LSMOOTH_TENSORS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T") THEN
  REWRITE_TAC[RFU_KOT_DENSITY; LIFT_ADD] THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THENL
   [MP_TAC(BETA_RULE(ISPECL [`2`; `U:real^N->bool`; `ta:real`; `tb:real`;
       `G1:real->real^N->real^N^N`;
       `\t. rfu_hh ((G1:real->real^N->real^N^N) t) (G2 t)`] RFU_LSMOOTH_LTNORM2));
    MP_TAC(BETA_RULE(ISPECL [`3`; `U:real^N->bool`; `ta:real`; `tb:real`;
       `G1:real->real^N->real^N^N`;
       `\t. rfu_aa ((G1:real->real^N->real^N^N) t) (G2 t)`] RFU_LSMOOTH_LTNORM2));
    MP_TAC(BETA_RULE(ISPECL [`4`; `U:real^N->bool`; `ta:real`; `tb:real`;
       `G1:real->real^N->real^N^N`;
       `\t. ltperm (swap(3,4)) (rfu_q ((G1:real->real^N->real^N^N) t) (G2 t))`]
       RFU_LSMOOTH_LTNORM2))] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ltperm] THEN GEN_TAC THEN USE_THEN "T" (fun th -> REWRITE_TAC[th]));;

let RFU_KZ_LSMOOTH = prove
 (`!U ta tb (G1:real->real^N->real^N^N) G2.
     lrg_lsmooth U ta tb G1 /\ lrg_lsmooth U ta tb G2
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. rfu_kz (G1 (drop(fstcart z))) (G2 (drop(fstcart z))) (sndcart z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `G1:real->real^N->real^N^N`;
                 `G2:real->real^N->real^N^N`] RFU_LSMOOTH_TENSORS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T") THEN
  REWRITE_TAC[rfu_kz; rfu_vf] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_SIMP_TAC[LRG_LSMOOTH_GINV] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE
    (ASSUME `open(interval(lift ta,lift tb) PCROSS (U:real^N->bool))`)] THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`4`; `U:real^N->bool`; `ta:real`; `tb:real`;
     `G1:real->real^N->real^N^N`;
     `\t. rfu_q ((G1:real->real^N->real^N^N) t) (G2 t)`;
     `\t z' (u:num->real^N). rfu_x ((G1:real->real^N->real^N^N) t) (G2 t) z'
                               (\m. if m = 5 then basis b else u m)`]
     RFU_LSMOOTH_LTINNER)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN USE_THEN "T" (fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* Smoothness up to the initial time of the density.  The three lemmas below *)
(* restate, under new names, PDM_CONTINUOUS_ON_LOCAL, PDM_APPROACH_SEQ of    *)
(* pc_pde_mloc and PDG_UPTO_LOCAL_ST of pc_pde_gauge, to keep the load       *)
(* closure of this unit small (those units pull in the ODE and torus         *)
(* layers).                                                                  *)
(* ========================================================================= *)

let RFU_CONTINUOUS_ON_LOCAL = prove
 (`!(f:real^M->real^N) s.
        (!x. x IN s ==> ?u. open u /\ x IN u /\ f continuous_on (s INTER u))
        ==> f continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `x:real^M`; `s:real^M->bool`;
                 `s INTER (u:real^M->bool)`] CONTINUOUS_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC `(f:real^M->real^N) continuous_on (s INTER u)` THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let RFU_APPROACH_SEQ = prove
 (`!a b. a < b
         ==> (!n. a < a + (b - a) * inv(&n + &2) /\ a + (b - a) * inv(&n + &2) < b) /\
             ((\n. lift(a + (b - a) * inv(&n + &2))) --> lift a) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 < inv(&n + &2) /\ inv(&n + &2) < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> a < a + x`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x < b - a ==> a + x < b`) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
    GEN_REWRITE_TAC LAND_CONV
      [GSYM(INST [`b - a:real`,`c:real`] (INST_TYPE [`:1`,`:N`] VECTOR_MUL_RZERO))] THEN
    MATCH_MP_TAC LIM_CMUL THEN REWRITE_TAC[SEQ_HARMONIC_OFFSET]]);;

let RFU_UPTO_LOCAL_ST = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ a < b /\
        (!t y. a <= t /\ t < b /\ y IN U
               ==> ?O (Fl:real^(1,N)finite_sum->real^K).
                     open O /\ pastecart (lift t) y IN O /\ smooth_map_on O Fl /\
                     !s z. a <= s /\ s < b /\ z IN U /\ pastecart (lift s) z IN O
                           ==> Fl(pastecart (lift s) z) = u s z)
        ==> pde_upto a b U u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] RFU_APPROACH_SEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dn") (LABEL_TAC "dlim")) THEN
  MATCH_MP_TAC PDE_SEELEY THEN ASM_REWRITE_TAC[pde_upto_classical] THEN
  REPEAT CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC RFU_CONTINUOUS_ON_LOCAL THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
    STRIP_TAC THEN USE_THEN "loc" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^(1,N)finite_sum->bool`
      (X_CHOOSE_THEN `Fl:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `Fl:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `z:real^N`
        STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[]];
    (* smoothness on the open slab *)
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^(1,N)finite_sum->bool`
      (X_CHOOSE_THEN `Fl:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(O:real^(1,N)finite_sum->bool) INTER
                (interval(lift a,lift b) PCROSS (U:real^N->bool))` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; IN_INTER; PASTECART_IN_PCROSS;
                 IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `Fl:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT;
                  IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the jets have continuous extensions *)
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum.
      if a < drop(fstcart w)
      then iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z)) w
      else lim sequentially
             (\n. iterated_partial l (\z. u (drop(fstcart z)) (sndcart z))
                    (pastecart (lift(a + (b - a) * inv(&n + &2))) (sndcart w)))` THEN
  REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MATCH_MP_TAC RFU_CONTINUOUS_ON_LOCAL THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  STRIP_TAC THEN USE_THEN "loc" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^(1,N)finite_sum->bool`
    (X_CHOOSE_THEN `Fl:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `iterated_partial l (Fl:real^(1,N)finite_sum->real^K)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN SET_TAC[]] THEN
  (* agreement of the jets with those of the local smooth map *)
  SUBGOAL_THEN
   `!s z. a < s /\ s < b /\ z IN U /\ pastecart (lift s) z IN O
          ==> iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z))
                (pastecart (lift s) z) =
              iterated_partial l (Fl:real^(1,N)finite_sum->real^K) (pastecart (lift s) z)`
  (LABEL_TAC "jagree") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `(O:real^(1,N)finite_sum->bool) INTER
                (interval(lift a,lift b) PCROSS (U:real^N->bool))` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; IN_INTER; PASTECART_IN_PCROSS;
                 IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `z:real^N`
    STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  COND_CASES_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "jagree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s:real = a` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC TENDSTO_LIM THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN
   `((\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N)) -->
     pastecart (lift a) z) sequentially`
  ASSUME_TAC THENL [MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?N. !n. N <= n
            ==> pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N) IN
                (O:real^(1,N)finite_sum->bool)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `pastecart (lift a) (z:real^N)` o
      REWRITE_RULE[OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open (O:real^(1,N)finite_sum->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC
     `((\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N)) -->
       pastecart (lift a) z) sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(pastecart (lift a) (z:real^N),r) SUBSET O` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. iterated_partial l (Fl:real^(1,N)finite_sum->real^K)
                    (pastecart (lift(a + (b - a) * inv(&n + &2))) z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "jagree" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "dn" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(iterated_partial l (Fl:real^(1,N)finite_sum->real^K)) continuous
      (at (pastecart (lift a) (z:real^N)))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`iterated_partial l (Fl:real^(1,N)finite_sum->real^K)`;
                   `O:real^(1,N)finite_sum->bool`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_AT_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N)`) THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* Restriction of smooth metric families to smaller boxes. *)

let RFU_LSMOOTH_SUB = prove
 (`!U V ta tb ta' tb' (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G /\ open V /\ V SUBSET U /\ ta <= ta' /\ ta' < tb' /\ tb' <= tb
     ==> lrg_lsmooth V ta' tb' G`,
  REWRITE_TAC[lrg_lsmooth] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM SET_TAC[]]]);;

(* Near any point of [a,b) x V, two metric families with smooth extensions  *)
(* past a agree with smooth families of metrics on a small box.             *)

let RFU_LOCAL_LSMOOTH2 = prove
 (`!V a b e1 e2 (Gc1:real->real^N->real^N^N) Gc2
    (FF1:real^(1,N)finite_sum->real^(N,N)finite_prod) FF2 t0 y0.
     open V /\ &0 < e1 /\ &0 < e2 /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc1 t) /\ metric_field V (Gc2 t)) /\
     smooth_map_on (interval(lift(a - e1),lift b) PCROSS V) FF1 /\
     smooth_map_on (interval(lift(a - e2),lift b) PCROSS V) FF2 /\
     (!t y. a <= t /\ t < b /\ y IN V
            ==> FF1(pastecart (lift t) y) = vectorize(Gc1 t y) /\
                FF2(pastecart (lift t) y) = vectorize(Gc2 t y)) /\
     a <= t0 /\ t0 < b /\ y0 IN V
     ==> ?d Gs1 Gs2.
           &0 < d /\
           lrg_lsmooth (ball(y0,d)) (t0 - d) (t0 + d) Gs1 /\
           lrg_lsmooth (ball(y0,d)) (t0 - d) (t0 + d) Gs2 /\
           (!t y. a <= t /\ t < b /\ y IN V /\
                  pastecart (lift t) y IN
                    interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(y0,d)
                  ==> Gs1 t y = Gc1 t y /\ Gs2 t y = Gc2 t y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (Gc:real->real^N->real^N^N).
      &0 < e /\ smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
      (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
      (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
      ==> ?d Gs. &0 < d /\ lrg_lsmooth (ball(y0,d)) (t0 - d) (t0 + d) Gs /\
                 (!t y. a <= t /\ t < b /\ y IN V ==> Gs t y = Gc t y)`
  (LABEL_TAC "one") THENL
   [REPEAT STRIP_TAC THEN
    ABBREV_TAC `O = interval(lift(a - e),lift b) PCROSS (V:real^N->bool)` THEN
    SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `V:real^N->bool`; `a:real`; `b:real`;
                   `Gc:real->real^N->real^N^N`;
                   `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] RFA_SYMM_EXT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`
      STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                   `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `pastecart (lift t0) (y0:real^N)`] RFA_LOCAL_LSMOOTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "O" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                              (pastecart (lift t0) y0)):real^N^N = Gc t0 y0`
      SUBST1_TAC THENL [ASM_SIMP_TAC[MATRIFY_VECTORIZE]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o
        check (fun th -> can (find_term ((=) `metric_field:(real^N->bool)->(real^N->real^N^N)->bool`)) (concl th) &&
                         is_forall(concl th))) THEN
      ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`d:real`; `\t y. matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                 (pastecart (lift t) y)):real^N^N`] THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  USE_THEN "one" (MP_TAC o SPECL [`e1:real`; `FF1:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                                  `Gc1:real->real^N->real^N^N`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `Gs1:real->real^N->real^N^N`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "one" (MP_TAC o SPECL [`e2:real`; `FF2:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                                  `Gc2:real->real^N->real^N^N`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (X_CHOOSE_THEN `Gs2:real->real^N->real^N^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`min d1 d2:real`; `Gs1:real->real^N->real^N^N`;
                        `Gs2:real->real^N->real^N^N`] THEN
  ASM_SIMP_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC RFU_LSMOOTH_SUB THENL
   [MAP_EVERY EXISTS_TAC [`ball(y0:real^N,d1)`; `t0 - d1:real`; `t0 + d1:real`];
    MAP_EVERY EXISTS_TAC [`ball(y0:real^N,d2)`; `t0 - d2:real`; `t0 + d2:real`]] THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  (CONJ_TAC THENL [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REAL_ARITH_TAC);;

(* The density along two Ricci flows smooth up to time a is smooth up to a. *)

let RFU_MKOT_SFUN = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g1:real->A->real^N^N) g2.
     ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2
     ==> pde_sfun_from atlas a b (\s. pde_mkot_density atlas (g1 s) (g2 s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_sfun_from] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun g ->
    UNDISCH_TAC (subst [g,`g:real->A->real^N^N`]
      `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                       (g:real->A->real^N^N)`) THEN
    REWRITE_TAC[ricci_flow_from] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC)
   [`g1:real->A->real^N^N`; `g2:real->A->real^N^N`] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN
    `FF2:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN
    `FF1:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> metric_field (IMAGE (SND c) (FST c))
              (metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) t)) /\
            metric_field (IMAGE (SND c) (FST c))
              (metric_local atlas c ((g2:real->A->real^N^N) t))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_upto a b (IMAGE (SND c) (FST c))
      (\t y. lift(pde_mkot_density atlas ((g1:real->A->real^N^N) t) (g2 t)
                                   (chart_inv (c:(A->bool)#(A->real^N)) y)))`
  MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[pde_upto] THEN SIMP_TAC[]] THEN
  MATCH_MP_TAC RFU_UPTO_LOCAL_ST THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                 `e1:real`; `e2:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) t)`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g2:real->A->real^N^N) t)`;
                 `FF1:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `FF2:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `t0:real`; `y0:real^N`] RFU_LOCAL_LSMOOTH2) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `Gs1:real->real^N->real^N^N`
    (X_CHOOSE_THEN `Gs2:real->real^N->real^N^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(y0:real^N,d)` THEN
  EXISTS_TAC `\z. lift(pde_kot_density ((Gs1:real->real^N->real^N^N) (drop(fstcart z)))
                                       ((Gs2:real->real^N->real^N^N) (drop(fstcart z)))
                                       (sndcart z))` THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL];
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFU_DENS_LSMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN FST c /\
                SND c (chart_inv c z) = z` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) s`; `(g2:real->A->real^N^N) s`;
                 `c:(A->bool)#(A->real^N)`; `chart_inv (c:(A->bool)#(A->real^N)) z`]
                RFU_MKOT_CHART) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFU_DENS_LOCAL THEN
  EXISTS_TAC `ball(y0:real^N,d) INTER IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER] THEN
  UNDISCH_TAC `pastecart (lift s) (z:real^N) IN
               interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(y0,d)` THEN
  REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `w:real^N`] o
    check (fun th -> can (find_term ((=) `Gs1:real->real^N->real^N^N`)) (concl th) &&
                     is_forall(concl th))) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The time derivative of a family smooth up to time a, taken                *)
(* within [a,oo), is again smooth up to a (RFU_SFUN_TDER).                    *)
(* ========================================================================= *)

let rfu_tder = new_definition
 `rfu_tder (a:real) (e:real->A->real) (t:real) (x:A) =
    @d. ((\s. e s x) has_real_derivative d) (atreal t within {s | a <= s})`;;

let RFU_NONTRIVIAL_HALFLINE = prove
 (`!a t. a <= t ==> ~trivial_limit (atreal t within {s | a <= s})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{s:real | a <= s}`; `t:real`] TRIVIAL_LIMIT_WITHIN_REALINTERVAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; is_realinterval] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `t + &1`) THEN ASM_REAL_ARITH_TAC]);;

let RFU_TDER_UNIQUE = prove
 (`!a (e:real->A->real) t x d.
     a <= t /\ ((\s. e s x) has_real_derivative d) (atreal t within {s | a <= s})
     ==> rfu_tder a e t x = d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfu_tder] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `d':real` THEN BETA_TAC THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN MATCH_MP_TAC NS_REAL_DERIVATIVE_UNIQUE_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\s. (e:real->A->real) s x`; `{s:real | a <= s}`; `t:real`] THEN
  ASM_SIMP_TAC[RFU_NONTRIVIAL_HALFLINE]);;

let RFU_SFUN_TDER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real).
     smooth_manifold_atlas top atlas /\ a < b /\ pde_sfun_from atlas a b e
     ==> pde_sfun_from atlas a b (rfu_tder a e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real)` THEN
  REWRITE_TAC[pde_sfun_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open(interval(lift(a - d),lift b) PCROSS
                     IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN
  EXISTS_TAC `\z. frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at z)
                                     (pastecart (lift(&1)) (vec 0))` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart (lift t) (y:real^N) IN
    interval(lift(a - d),lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FF:real^(1,N)finite_sum->real^1`;
                 `interval(lift(a - d),lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `t:real`; `y:real^N`] GRGT_TIME_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `rfu_tder a (e:real->A->real) t (chart_inv (c:(A->bool)#(A->real^N)) y) =
    drop(frechet_derivative (FF:real^(1,N)finite_sum->real^1) (at (pastecart (lift t) y))
                            (pastecart (lift(&1)) (vec 0)))`
  (fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
  MATCH_MP_TAC RFU_TDER_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`\s. drop((FF:real^(1,N)finite_sum->real^1) (pastecart (lift s) y))`;
                        `b - t:real`] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

(* ========================================================================= *)
(* Uniform bounds K for rfu_kbound along two Ricci flows on a compact        *)
(* manifold, on a compact time interval [a,b'] (RFU_KBOUND_COMPACT).         *)
(* ========================================================================= *)

(* The sum of squares of all the components controlled by rfu_kbound. *)

let rfu_qb = new_definition
 `rfu_qb (G:real^N->real^N^N) (y:real^N) =
    sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N)) (\j. (G y$i$j) pow 2 + (matrix_inv(G y)$i$j) pow 2)) +
    sum(index_tuples 4 (:N)) (\ip. lrm4 G y (\m. basis(ip m)) pow 2) +
    sum(index_tuples 5 (:N)) (\ip. lnabla 4 G (lrm4 G) y (\m. basis(ip m)) pow 2) +
    sum(index_tuples 6 (:N)) (\ip. lnabla_iter 4 2 G (lrm4 G) y (\m. basis(ip m)) pow 2)`;;

let RFU_QB_LSMOOTH = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(rfu_qb (G (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on (interval(lift ta,lift tb) PCROSS U)
            (\z. lift((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)$i$j))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(\z. lift((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)$i$j)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
      (\z. vectorize(G (drop(fstcart z)) (sndcart z)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY];
    ALL_TAC] THEN
  REWRITE_TAC[rfu_qb; LIFT_ADD; REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN
         ASM_REWRITE_TAC[FINITE_NUMSEG; LRG_INDEX_TUPLES_FINITE] THEN
         GEN_TAC THEN DISCH_TAC) THEN
  REWRITE_TAC[LIFT_ADD] THEN
  TRY(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC) THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN
  REWRITE_TAC[GSYM RFA_LNABLA_ITER_1] THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_GINV_ENTRY; RFA_LSMOOTH_LRM4; RFA_LSMOOTH_LRM_DERIV]);;

let RFU_QB_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
     ==> rfu_qb G1 y = rfu_qb G2 y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z u. z IN s ==> lrm4 (G1:real^N->real^N^N) z u = lrm4 G2 z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4] THEN ASM_SIMP_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRIEMANN_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `lrm4 (G1:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`;
                 `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!u. lnabla 4 (G1:real^N->real^N^N) (lrm4 G1) y u = lnabla 4 G2 (lrm4 G2) y u`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfu_qb] THEN ASM_SIMP_TAC[]);;

(* On a compact box of a chart and a compact time interval, the bound       *)
(* function of a Ricci flow smooth up to a is bounded.                       *)

let RFU_QB_CHART_BOUND = prove
 (`!(top:A topology) atlas a b b' (g:real->A->real^N^N) c (p:real^N) q.
     ricci_flow_from (top,atlas) a b g /\ c IN atlas /\ b' < b /\
     interval[p,q] SUBSET IMAGE (SND c) (FST c)
     ==> ?B. &0 < B /\
             !t y. a <= t /\ t <= b' /\ y IN interval[p,q]
                   ==> rfu_qb (metric_local atlas c (g t)) y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
  REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`rfu_qb:(real^N->real^N^N)->real^N->real`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                 `e:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`]
                RFA_EXT_LOCAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFU_QB_LSMOOTH] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_QB_LOCAL THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  MP_TAC(ISPECL [`\w. lift(rfu_qb (metric_local atlas (c:(A->bool)#(A->real^N))
                                    ((g:real->A->real^N^N) (drop(fstcart w)))) (sndcart w))`;
                 `{w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                       sndcart w IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)}`;
                 `a:real`; `b':real`; `p:real^N`; `q:real^N`] GRGT_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM PCROSS_INTERVAL; SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS;
                IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1;
                LIFT_DROP; FORALL_LIFT] THEN
    REPEAT STRIP_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           UNDISCH_TAC `interval[p:real^N,q] SUBSET
                        IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
           REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let RFU_QB_PARTS = prove
 (`!(G:real^N->real^N^N) y.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (G y$i$j) pow 2 <= rfu_qb G y /\
                (matrix_inv(G y)$i$j) pow 2 <= rfu_qb G y) /\
     (!ip. ip IN index_tuples 4 (:N)
           ==> lrm4 G y (\m. basis(ip m)) pow 2 <= rfu_qb G y) /\
     (!ip. ip IN index_tuples 5 (:N)
           ==> lnabla 4 G (lrm4 G) y (\m. basis(ip m)) pow 2 <= rfu_qb G y) /\
     (!ip. ip IN index_tuples 6 (:N)
           ==> lnabla_iter 4 2 G (lrm4 G) y (\m. basis(ip m)) pow 2 <= rfu_qb G y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfu_qb] THEN
  MAP_EVERY ABBREV_TAC
   [`S1 = sum(1..dimindex(:N))
            (\i. sum(1..dimindex(:N))
                   (\j. ((G:real^N->real^N^N) y$i$j) pow 2 +
                        (matrix_inv(G y)$i$j) pow 2))`;
    `S2 = sum(index_tuples 4 (:N)) (\ip. lrm4 (G:real^N->real^N^N) y (\m. basis(ip m)) pow 2)`;
    `S3 = sum(index_tuples 5 (:N))
            (\ip. lnabla 4 (G:real^N->real^N^N) (lrm4 G) y (\m. basis(ip m)) pow 2)`;
    `S4 = sum(index_tuples 6 (:N))
            (\ip. lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G) y (\m. basis(ip m)) pow 2)`] THEN
  SUBGOAL_THEN `&0 <= S1 /\ &0 <= S2 /\ &0 <= S3 /\ &0 <= S4` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"; "S3"; "S4"] THEN REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC SUM_POS_LE THEN
           REWRITE_TAC[FINITE_NUMSEG; LRG_INDEX_TUPLES_FINITE] THEN
           GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\j. ((G:real^N->real^N^N) y$i$j) pow 2 + (matrix_inv(G y)$i$j) pow 2) <= S1`
    ASSUME_TAC THENL
     [EXPAND_TAC "S1" THEN
      MP_TAC(ISPECL [`\i. sum(1..dimindex(:N))
                       (\j. ((G:real^N->real^N^N) y$i$j) pow 2 + (matrix_inv(G y)$i$j) pow 2)`;
                     `1..dimindex(:N)`; `i:num`] GRGT_MEMBER_LE_SUM) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((G:real^N->real^N^N) y$i$j) pow 2 + (matrix_inv(G y)$i$j) pow 2 <=
      sum(1..dimindex(:N))
        (\j. ((G:real^N->real^N^N) y$i$j) pow 2 + (matrix_inv(G y)$i$j) pow 2)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\j. ((G:real^N->real^N^N) y$i$j) pow 2 + (matrix_inv(G y)$i$j) pow 2`;
                     `1..dimindex(:N)`; `j:num`] GRGT_MEMBER_LE_SUM) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
      ALL_TAC] THEN
    MP_TAC(SPEC `(G:real^N->real^N^N) y$i$j` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `matrix_inv((G:real^N->real^N^N) y)$i$j` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x. x <= S2 /\ &0 <= S1 /\ &0 <= S3 /\ &0 <= S4
                                 ==> x <= S1 + S2 + S3 + S4`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S2";
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x. x <= S3 /\ &0 <= S1 /\ &0 <= S2 /\ &0 <= S4
                                 ==> x <= S1 + S2 + S3 + S4`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S3";
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x. x <= S4 /\ &0 <= S1 /\ &0 <= S2 /\ &0 <= S3
                                 ==> x <= S1 + S2 + S3 + S4`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S4"] THEN
  W(fun (_,w) -> let f = rand(rand w) in
     MP_TAC(ISPECL [f; rand(rator(rand w)); `ip:num->num`] GRGT_MEMBER_LE_SUM)) THEN
  ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_POW_2]);;

let RFU_SQ_LE_ABS = prove
 (`!x B K. x pow 2 <= B /\ sqrt B <= K ==> abs x <= K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt B` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM POW_2_SQRT_ABS] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]);;

let RFU_QB_BOUNDS1 = prove
 (`!K B (G:real^N->real^N^N) y.
     rfu_qb G y <= B /\ sqrt B <= K
     ==> (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                ==> abs(G y$i$j) <= K /\ abs(matrix_inv(G y)$i$j) <= K) /\
         rfu_cb 4 (lrm4 G) y K /\ rfu_cb 5 (lnabla 4 G (lrm4 G)) y K /\
         rfu_cb 6 (lnabla_iter 4 2 G (lrm4 G)) y K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`G:real^N->real^N^N`; `y:real^N`] RFU_QB_PARTS) THEN
  REWRITE_TAC[rfu_cb] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN TRY CONJ_TAC THEN
  MATCH_MP_TAC RFU_SQ_LE_ABS THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rfu_qb (G:real^N->real^N^N) y` THEN
  ASM_SIMP_TAC[]);;

let RFU_QB_KBOUND = prove
 (`!K B (G1:real^N->real^N^N) G2 y.
     &1 <= K /\ rfu_qb G1 y <= B /\ rfu_qb G2 y <= B /\ sqrt B <= K
     ==> rfu_kbound K G1 G2 y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`K:real`; `B:real`; `G1:real^N->real^N^N`; `y:real^N`] RFU_QB_BOUNDS1) THEN
  MP_TAC(SPECL [`K:real`; `B:real`; `G2:real^N->real^N^N`; `y:real^N`] RFU_QB_BOUNDS1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfu_kbound] THEN ASM_SIMP_TAC[]);;

(* Uniform bounds on a compact manifold and a compact time interval. *)

let RFU_KBOUND_COMPACT = prove
 (`!(top:A topology) atlas a b b' (g1:real->A->real^N^N) g2.
     compact_space top /\ ricci_flow_from (top,atlas) a b g1 /\
     ricci_flow_from (top,atlas) a b g2 /\ b' < b
     ==> ?K. &1 <= K /\
             !t x. a <= t /\ t <= b' /\ x IN topspace top
                   ==> ?c. c IN atlas /\ x IN FST c /\
                           rfu_kbound K (metric_local atlas c (g1 t))
                                        (metric_local atlas c (g2 t)) (SND c x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                GRGT_COMPACT_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `E:num->A->bool` (X_CHOOSE_THEN `p:num->real^N`
      (X_CHOOSE_THEN `q:num->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "box")))))))) THEN
  SUBGOAL_THEN
   `!n. ?B. n IN 1..k
            ==> &0 < B /\
                !t y. a <= t /\ t <= b' /\ y IN interval[(p:num->real^N) n,q n]
                      ==> rfu_qb (metric_local atlas ((c:num->(A->bool)#(A->real^N)) n)
                                   ((g1:real->A->real^N^N) t)) y <= B /\
                          rfu_qb (metric_local atlas (c n) ((g2:real->A->real^N^N) t)) y <= B`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n IN 1..k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `b':real`; `g1:real->A->real^N^N`;
                   `(c:num->(A->bool)#(A->real^N)) n`; `(p:num->real^N) n`;
                   `(q:num->real^N) n`] RFU_QB_CHART_BOUND) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `b':real`; `g2:real->A->real^N^N`;
                   `(c:num->(A->bool)#(A->real^N)) n`; `(p:num->real^N) n`;
                   `(q:num->real^N) n`] RFU_QB_CHART_BOUND) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B1 + B2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= B1 /\ &0 < B2 ==> x <= B1 + B2`);
      MATCH_MP_TAC(REAL_ARITH `x <= B2 /\ &0 < B1 ==> x <= B1 + B2`)] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `B:num->real` (LABEL_TAC "B"))] THEN
  EXISTS_TAC `&1 + sum(1..k) (\n. sqrt((B:num->real) n))` THEN
  SUBGOAL_THEN `!n. n IN 1..k ==> &0 <= sqrt((B:num->real) n)` (LABEL_TAC "sq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    USE_THEN "B" (MP_TAC o C MP (ASSUME `n IN 1..k`) o SPEC `n:num`) THEN
    SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_chart_partition (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                 (c:num->(A->bool)#(A->real^N)) (E:num->A->bool)` THEN
  REWRITE_TAC[mfd_chart_partition] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. (x:A) IN (E:num->A->bool) n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS {(E:num->A->bool) n | n IN (:num)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n IN 1..k` ASSUME_TAC THENL
   [ASM_CASES_TAC `n IN 1..k` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN (E:num->A->bool) n` THEN ASM_SIMP_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  USE_THEN "box" (MP_TAC o C MP (ASSUME `n IN 1..k`) o SPEC `n:num`) THEN STRIP_TAC THEN
  EXISTS_TAC `(c:num->(A->bool)#(A->real^N)) n` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SND((c:num->(A->bool)#(A->real^N)) n) (x:A) IN interval[(p:num->real^N) n,q n]`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "B" (MP_TAC o C MP (ASSUME `n IN 1..k`) o SPEC `n:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC RFU_QB_KBOUND THEN EXISTS_TAC `(B:num->real) n` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC(REAL_ARITH `x <= s ==> x <= &1 + s`) THEN
    MP_TAC(ISPECL [`\n. sqrt((B:num->real) n)`; `1..k`; `n:num`] GRGT_MEMBER_LE_SUM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN BETA_TAC THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Kotschwar's pointwise inequality on a compact manifold                    *)
(* (M5 = PDE_KOT_POINTWISE_STATEMENT of pc_pde_iface).                       *)
(* ========================================================================= *)

let RFU_LSMOOTH_CONST = prove
 (`!U (G:real^N->real^N^N). metric_field U G ==> lrg_lsmooth U (&0) (&1) (\t. G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrg_lsmooth] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((G:real^N->real^N^N) (sndcart z))) =
    (vectorize o G) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]);;

let RFU_SMOOTH_SLICE = prove
 (`!U (f:real^N->real^P).
     open U /\ smooth_map_on (interval(lift(&0),lift(&1)) PCROSS U) (\z. f(sndcart z))
     ==> smooth_map_on U f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^P) = (\z. f(sndcart z)) o (\y. pastecart (lift(&1 / &2)) y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift(&0),lift(&1)) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let RFU_KZ_SMOOTH = prove
 (`!U (G1:real^N->real^N^N) G2.
     metric_field U G1 /\ metric_field U G2 ==> smooth_map_on U (rfu_kz G1 G2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_SMOOTH_SLICE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`U:real^N->bool`; `&0`; `&1`; `\t:real. (G1:real^N->real^N^N)`;
                           `\t:real. (G2:real^N->real^N^N)`] RFU_KZ_LSMOOTH)) THEN
  ASM_SIMP_TAC[RFU_LSMOOTH_CONST]);;

(* At a point of a chart, the manifold density, its time derivative and the *)
(* divergence of the Kotschwar field are those of the chart representatives. *)

let RFU_KOT_AT_CHART = prove
 (`!(top:A topology) atlas a b (g1:real->A->real^N^N) g2 c t x.
     ricci_flow_from (top,atlas) a b g1 /\ ricci_flow_from (top,atlas) a b g2 /\
     c IN atlas /\ x IN FST c /\ a < t /\ t < b
     ==> ((\s. pde_mkot_density atlas (g1 s) (g2 s) x) has_real_derivative
          rfu_edot (metric_local atlas c (g1 t)) (metric_local atlas c (g2 t)) (SND c x))
         (atreal t) /\
         pde_mkot_density atlas (g1 t) (g2 t) x =
         pde_kot_density (metric_local atlas c (g1 t)) (metric_local atlas c (g2 t)) (SND c x) /\
         mfd_div atlas (g1 t) (rfu_mkz atlas (g1 t) (g2 t)) x =
         ldiv (metric_local atlas c (g1 t))
              (rfu_kz (metric_local atlas c (g1 t)) (metric_local atlas c (g2 t))) (SND c x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s) x =
            pde_kot_density (metric_local atlas (c:(A->bool)#(A->real^N)) (g1 s))
                            (metric_local atlas c (g2 s)) (SND c x)`
  (LABEL_TAC "dens") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_MKOT_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\s. pde_kot_density (metric_local atlas (c:(A->bool)#(A->real^N))
                                       ((g1:real->A->real^N^N) s))
                                    (metric_local atlas c (g2 s)) (SND c x)` THEN
    EXISTS_TAC `min (t - a) (b - t)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "dens" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                   `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s)`;
                   `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g2:real->A->real^N^N) s)`;
                   `t:real`; `SND (c:(A->bool)#(A->real^N)) x`] RFU_EDOT_DERIV) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g1:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g2:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "dens" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g1:real->A->real^N^N) t) /\
                riemannian_metric atlas ((g2:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g1:real->A->real^N^N) t`;
                 `rfu_mkz atlas ((g1:real->A->real^N^N) t) (g2 t)`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `x:A`] GRGT_MFD_DIV_CHART) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `rfu_kz (metric_local atlas (c':(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) t))
                       (metric_local atlas c' ((g2:real->A->real^N^N) t))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC RFU_MKZ_VREP THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFU_KZ_SMOOTH THEN ASM_MESON_TAC[riemannian_metric]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC LDIV_LOCAL THEN EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC RFU_MKZ_VREP THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* M5: Kotschwar's pointwise inequality. *)

let PDE_KOT_POINTWISE = prove
 (`!(u:A->bool) (n:N->bool). PDE_KOT_POINTWISE_STATEMENT u n`,
  REWRITE_TAC[PDE_KOT_POINTWISE_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g1:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g2:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `b':real`; `g1:real->A->real^N^N`;
                 `g2:real->A->real^N^N`] RFU_KBOUND_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kb"))) THEN
  MP_TAC(SPEC `K:real` (INST_TYPE [`:N`,`:N`] RFU_KOT_LOCAL)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN
   `ricci_flow_from (top,atlas) a b' (g1:real->A->real^N^N) /\
    ricci_flow_from (top,atlas) a b' (g2:real->A->real^N^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_sfun_from atlas a b'
      (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFU_MKOT_SFUN THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `C:real` THEN
  EXISTS_TAC `\t:real. rfu_mkz atlas ((g1:real->A->real^N^N) t) (g2 t)` THEN
  EXISTS_TAC `rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* e' smooth up to a *)
    MATCH_MP_TAC RFU_SFUN_TDER THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    (* Z smooth in charts *)
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\z. rfu_kz (metric_local atlas (c:(A->bool)#(A->real^N))
                              ((g1:real->A->real^N^N) (drop(fstcart z))))
                           (metric_local atlas c ((g2:real->A->real^N^N) (drop(fstcart z))))
                           (sndcart z)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                  FSTCART_PASTECART; SNDCART_PASTECART; FORALL_LIFT] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFU_MKZ_VREP THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g1:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `g2:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
    MP_TAC(BETA_RULE(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b':real`;
       `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s)`;
       `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g2:real->A->real^N^N) s)`]
       RFU_KZ_LSMOOTH)) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC RFU_LSMOOTH_SUB THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the derivative and the inequality *)
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  USE_THEN "kb" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `g2:real->A->real^N^N`;
                 `c:(A->bool)#(A->real^N)`; `t:real`; `x:A`] RFU_KOT_AT_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN
   `rfu_tder a (\s. pde_mkot_density atlas ((g1:real->A->real^N^N) s) (g2 s)) t x =
    rfu_edot (metric_local atlas (c:(A->bool)#(A->real^N)) (g1 t))
             (metric_local atlas c (g2 t)) (SND c x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFU_TDER_UNIQUE THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BETA_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g1:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                LRG_RICCI_FLOW_ON_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g2:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "loc" (MP_TAC o BETA_RULE o SPECL
   [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
    `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g1:real->A->real^N^N) s)`;
    `\s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g2:real->A->real^N^N) s)`;
    `t:real`; `SND (c:(A->bool)#(A->real^N)) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* R4 and R5 as statement constants (proved from the integration units       *)
(* pc_grg_divthm and pc_grg_rfint), and the integration facts used by the    *)
(* Gronwall argument: a nonnegative function continuous in charts with       *)
(* integral 0 vanishes; integrability of families smooth up to the initial   *)
(* time.                                                                     *)
(* ========================================================================= *)

(* R4, the divergence theorem, and R5, the time derivative of integrals      *)
(* along a Ricci flow.                                                       *)

let PDE_REQ_DIVERGENCE_STATEMENT = new_definition
 `PDE_REQ_DIVERGENCE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (Z:A->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        riemannian_metric atlas g /\
        (!c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (mfd_vrep atlas Z c))
        ==> mfd_has_integral (top,atlas) g (mfd_div atlas g Z) (topspace top) (&0)`;;

let PDE_REQ_INTEGRAL_DERIV_STATEMENT = new_definition
 `PDE_REQ_INTEGRAL_DERIV_STATEMENT (u:A->bool) (n:N->bool) <=>
    !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (g:real->A->real^N^N) (e:real->A->real) e'.
        hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b g /\
        pde_sfun_from atlas a b e /\ pde_sfun_from atlas a b e' /\
        (!s x. a < s /\ s < b /\ x IN topspace top
               ==> ((\r. e r x) has_real_derivative e' s x) (atreal s))
        ==> (\s. mfd_integral (top,atlas) (g s) (topspace top) (e s))
              real_continuous_on {s | a <= s /\ s < b} /\
            !t. a < t /\ t < b
                ==> ((\s. mfd_integral (top,atlas) (g s) (topspace top) (e s))
                     has_real_derivative
                     mfd_integral (top,atlas) (g t) (topspace top)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x)) (atreal t)`;;

let PDE_REQ_DIVERGENCE = prove
 (`!(u:A->bool) (n:N->bool). PDE_REQ_DIVERGENCE_STATEMENT u n`,
  REWRITE_TAC[PDE_REQ_DIVERGENCE_STATEMENT; MFD_DIVERGENCE_THEOREM]);;

let PDE_REQ_INTEGRAL_DERIV = prove
 (`!(u:A->bool) (n:N->bool). PDE_REQ_INTEGRAL_DERIV_STATEMENT u n`,
  REWRITE_TAC[PDE_REQ_INTEGRAL_DERIV_STATEMENT; MFD_INTEGRAL_RF_DERIV]);;

(* A nonnegative function, continuous in charts, with integral 0 vanishes. *)

let RFU_MFD_INTEGRAL_ZERO_IMP = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f x0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. x IN topspace top ==> &0 <= f x) /\
     mfd_has_integral (top,atlas) g f (topspace top) (&0) /\
     (!c. c IN atlas
          ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c)) /\
     x0 IN topspace top
     ==> f x0 = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "fpos") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "fcont") ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x0:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST (c:(A->bool)#(A->real^N)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_lebesgue_measurable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (FST (c:(A->bool)#(A->real^N))) /\
    mfd_lebesgue_measurable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (topspace top DIFF FST (c:(A->bool)#(A->real^N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integrable_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) (FST (c:(A->bool)#(A->real^N))) /\
    mfd_integrable_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) g f (topspace top DIFF FST (c:(A->bool)#(A->real^N)))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN
    EXISTS_TAC `topspace top:A->bool` THEN
    ASM_REWRITE_TAC[mfd_integrable_on; SUBSET_DIFF] THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN
  ABBREV_TAC `v = mfd_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (FST (c:(A->bool)#(A->real^N)))
                                (f:A->real)` THEN
  ABBREV_TAC `w = mfd_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                    (topspace top DIFF FST (c:(A->bool)#(A->real^N))) (f:A->real)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!S v. mfd_has_integral (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) S v /\
          S SUBSET topspace top
          ==> &0 <= v`
  (LABEL_TAC "nn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\x:A. &0 * f x`; `f:A->real`; `S:A->bool`;
                   `&0 * v'`; `v':real`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CMUL] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      USE_THEN "fpos" MATCH_MP_TAC THEN ASM SET_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v /\ &0 <= w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "nn" MATCH_MP_TAC THENL
     [EXISTS_TAC `FST (c:(A->bool)#(A->real^N))`;
      EXISTS_TAC `topspace top DIFF FST (c:(A->bool)#(A->real^N))`] THEN
    ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `v = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `FST (c:(A->bool)#(A->real^N))`;
                   `topspace top DIFF FST (c:(A->bool)#(A->real^N))`; `v:real`; `w:real`]
                  MFD_HAS_INTEGRAL_UNION) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `FST (c:(A->bool)#(A->real^N)) UNION (topspace top DIFF FST c) = topspace top`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `topspace top:A->bool`;
                   `v + w:real`; `&0`] MFD_HAS_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`;
                 `FST (c:(A->bool)#(A->real^N))`; `v:real`] MFD_HAS_INTEGRAL_CHART) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(mfd_chart_integrand atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)) has_integral vec 0)
      (IMAGE (SND c) (FST c))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`mfd_chart_integrand atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N))`;
                   `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`] HAS_INTEGRAL_INTEGRAL) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) HAS_INTEGRAL_NEGLIGIBLE_EQ o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `i:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `i = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_chart_integrand; GSYM drop; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [USE_THEN "fpos" MATCH_MP_TAC THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM SET_TAC[]];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  CONJ_TAC THENL [USE_THEN "fpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `{y | y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                     lift(f(chart_inv c y)) IN {z:real^1 | z$1 > &0}}`
               OPEN_NOT_NEGLIGIBLE) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN USE_THEN "fcont" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `SND (c:(A->bool)#(A->real^N)) x0` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; GSYM drop; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM drop; LIFT_DROP; mfd_chart_integrand] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC GRGV_DENSITY_POS THEN ASM_REWRITE_TAC[]]);;

(* Integrability at each time of a family smooth up to time a (and of its   *)
(* derivative combination), on a compact manifold along a Ricci flow.       *)

let RFU_SFUN_INTEGRABLE = prove
 (`!(top:A topology) atlas a b (g:real->A->real^N^N) (e:real->A->real) e'.
     hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b g /\
     pde_sfun_from atlas a b e /\
     (!s x. a < s /\ s < b /\ x IN topspace top
            ==> ((\r. e r x) has_real_derivative e' s x) (atreal s))
     ==> (!s. a <= s /\ s < b
              ==> mfd_integrable_on (top,atlas) (g s) (e s) (topspace top)) /\
         (!t. a < t /\ t < b
              ==> mfd_integrable_on (top,atlas) (g t)
                    (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (topspace top))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                GRGT_COMPACT_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` (X_CHOOSE_THEN `p:num->real^N`
    (X_CHOOSE_THEN `q:num->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "PART")
      (CONJUNCTS_THEN2 (LABEL_TAC "E0") (LABEL_TAC "PQ")))))))) THEN
  SUBGOAL_THEN
   `!n. n IN 1..k
        ==> lebesgue_measurable (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                       ((E:num->A->bool) n))`
  (LABEL_TAC "MEAS") THENL
   [USE_THEN "PART" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n IN 1..k
        ==> (!s. a <= s /\ s < b
                 ==> mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                       ((e:real->A->real) s) ((c:num->(A->bool)#(A->real^N)) n)
                     absolutely_integrable_on IMAGE (SND(c n)) ((E:num->A->bool) n)) /\
            (\s. drop(integral (IMAGE (SND(c n)) (E n))
                        (mfd_chart_integrand atlas (g s) (e s) (c n))))
              real_continuous_on {s | a <= s /\ s < b} /\
            (!t. a < t /\ t < b
                 ==> mfd_chart_integrand atlas (g t)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n)
                       absolutely_integrable_on IMAGE (SND(c n)) (E n) /\
                     ((\s. drop(integral (IMAGE (SND(c n)) (E n))
                                  (mfd_chart_integrand atlas (g s) (e s) (c n))))
                      has_real_derivative
                      drop(integral (IMAGE (SND(c n)) (E n))
                             (mfd_chart_integrand atlas (g t)
                               (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n))))
                     (atreal t))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGT_PIECE_INTEGRAL THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `(p:num->real^N) n`; `(q:num->real^N) n`] THEN
    USE_THEN "PQ" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "MEAS" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[mfd_integrable_on] THENL
   [EXISTS_TAC `sum(1..k) (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                                     ((E:num->A->bool) n))
                                  (mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                                                      ((e:real->A->real) s) (c n))))`;
    EXISTS_TAC `sum(1..k) (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                                     ((E:num->A->bool) n))
                                  (mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                                     (\x. e' s x - mfd_scalar atlas (g s) x *
                                                   (e:real->A->real) s x) (c n))))`] THEN
  MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
  USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
  ASM_SIMP_TAC[]);;

(* One-sided Gronwall (the upper half of RFA_GRONWALL_2SIDED of pc_rfa_shi,  *)
(* which assumes |q'| <= c q).                                               *)

let RFU_GRONWALL_UP = prove
 (`!(q:real->real) q' c a t.
     a < t /\ q real_continuous_on real_interval[a,t] /\
     (!s. a < s /\ s < t ==> (q has_real_derivative q' s) (atreal s)) /\
     (!s. a < s /\ s < t ==> q' s <= c * q s)
     ==> q t <= exp(c * (t - a)) * q a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s. --(exp(--c * (s - a)) * (q:real->real) s)`;
    `\s. --(exp(--c * (s - a)) * (q':real->real) s + (exp(--c * (s - a)) * --c) * q s)`;
    `a:real`; `t:real`] RFA_MVT_MONO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[RFA_EXP_AFFINE_CONTINUOUS];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
      ASM_SIMP_TAC[RFA_EXP_AFFINE_DERIV];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_RING `!e x c y:real.
                    --(e * x + (e * --c) * y) = e * (c * y - x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(c * (t - a)) * (exp(--(c * (t - a))) * (q:real->real) t)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* The density of two equal metrics vanishes. *)

let RFU_DENS_SAME = prove
 (`!(G:real^N->real^N^N) y. pde_kot_density G G y = &0`,
  REWRITE_TAC[pde_kot_density; REAL_SUB_REFL; VECTOR_SUB_REFL;
              MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN
  REWRITE_TAC[ltnorm2; REAL_MUL_LZERO; SUM_0; REAL_ADD_LID]);;

let RFU_MKOT_SAME = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g1:A->real^N^N) g2 x.
     smooth_manifold_atlas top atlas /\ x IN topspace top /\
     (!z. z IN topspace top ==> g1 z = g2 z)
     ==> pde_mkot_density atlas g1 g2 x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mkot_density] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV
   [SYM(ISPECL [`metric_local atlas (c:(A->bool)#(A->real^N)) (g1:A->real^N^N)`;
                `SND (c:(A->bool)#(A->real^N)) x`] RFU_DENS_SAME)] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFU_DENS_LOCAL THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST (c:(A->bool)#(A->real^N)))`)) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[]]);;

(* A lower bound for the scalar curvature along a Ricci flow smooth up to a *)
(* on a compact manifold (maximum principle RFA_SCALAR_LOWER at time a).    *)

let RFU_SCALAR_LB = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N).
     compact_space top /\ ricci_flow_from (top,atlas) a b g
     ==> ?H. &0 <= H /\
             !t x. a <= t /\ t < b /\ x IN topspace top
                   ==> --H <= mfd_scalar atlas (g t) x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`]
                RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                                 (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_from] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP CONTINUOUS_MAP_REAL_NEG) THEN
  MP_TAC(BETA_RULE(ISPECL [`top:A topology`;
                 `\t x. --(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                      ((g:real->A->real^N^N) t) x)`;
                 `a:real`; `b:real`] RFA_COMPACT_SLICE_BOUND)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `H:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `a:real`; `--H:real`]
                RFA_SCALAR_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `H:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = &(dimindex(:N)) - &2 * (t - a) * --H` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * --H / D` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(dimindex(:N)) * --H / D = (&(dimindex(:N)) * --H) / D` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= (t - a) * H * H` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "D" THEN REAL_ARITH_TAC);;

(* Time slices of space-time smooth maps. *)

let RFU_SMOOTH_SLICE_AT = prove
 (`!U ta tb t (FF:real^(1,N)finite_sum->real^P).
     open U /\ ta < t /\ t < tb /\
     smooth_map_on (interval(lift ta,lift tb) PCROSS U) FF
     ==> smooth_map_on U (\y. FF(pastecart (lift t) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (FF:real^(1,N)finite_sum->real^P) (pastecart (lift t) y)) =
                FF o (\y:real^N. pastecart (lift t) y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

(* Families smooth up to a are continuous in charts at every time in [a,b). *)

let RFU_SFUN_CHART_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real) c t.
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b e /\ c IN atlas /\
     a <= t /\ t < b
     ==> (\y. lift(e t (chart_inv c y))) continuous_on IMAGE (SND c) (FST c)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real)` THEN
  REWRITE_TAC[pde_sfun_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\y. (FF:real^(1,N)finite_sum->real^1) (pastecart (lift t) y)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGT_SLICE_CONTINUOUS THEN
  EXISTS_TAC `interval(lift(a - d),lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Uniqueness of Ricci flow on a closed manifold from M5, R4                 *)
(* and R5 (PDE_UNIQUENESS_FROM_KOT), and the uniqueness theorem itself.      *)
(* ========================================================================= *)

(* One time step of the energy estimate: integrating e' - R e <= div Z +    *)
(* C e - R e.                                                                *)

let RFU_ENERGY_STEP = prove
 (`!(top:A topology) atlas (g:A->real^N^N) d e e' R H C.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_integral (top,atlas) g d (topspace top) (&0) /\
     mfd_integrable_on (top,atlas) g e (topspace top) /\
     mfd_integrable_on (top,atlas) g (\x. e' x - R x * e x) (topspace top) /\
     &0 <= H /\
     (!x. x IN topspace top ==> &0 <= e x /\ --H <= R x /\ e' x <= d x + C * e x)
     ==> mfd_integral (top,atlas) g (topspace top) (\x. e' x - R x * e x) <=
         (abs C + H) * mfd_integral (top,atlas) g (topspace top) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MFD_INTEGRABLE_INTEGRAL]) THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\x:A. e' x - R x * e x`; `\x:A. d x + (abs C + H) * e x`; `topspace top:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `e':A->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= ((R:A->real) x + H) * (e:A->real) x /\ &0 <= (abs C - C) * e x`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let PDE_UNIQUENESS_FROM_KOT = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_KOT_POINTWISE_STATEMENT u n /\ PDE_REQ_DIVERGENCE_STATEMENT u n /\
        PDE_REQ_INTEGRAL_DERIV_STATEMENT u n
        ==> PDE_UNIQUENESS_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PDE_KOT_POINTWISE_STATEMENT; PDE_REQ_DIVERGENCE_STATEMENT;
              PDE_REQ_INTEGRAL_DERIV_STATEMENT; PDE_UNIQUENESS_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "M5")
    (CONJUNCTS_THEN2 (LABEL_TAC "R4") (LABEL_TAC "R5"))) THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `b':real`; `g:real->A->real^N^N`;
                       `g':real->A->real^N^N`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`] GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b':real`; `g':real->A->real^N^N`] GRGT_RF_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm'")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))) THEN
  ABBREV_TAC `T0 = min b b'` THEN ABBREV_TAC `b2 = (t + T0) / &2` THEN
  SUBGOAL_THEN `t < b2 /\ b2 < T0 /\ T0 <= b /\ T0 <= b' /\ a < T0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["b2"; "T0"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_from (top,atlas) a T0 (g:real->A->real^N^N) /\
    ricci_flow_from (top,atlas) a T0 (g':real->A->real^N^N) /\
    ricci_flow_from (top,atlas) a b2 (g:real->A->real^N^N)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PDE_RFF_RESTRICT THEN EXISTS_TAC `a:real` THENL
     [EXISTS_TAC `b:real`; EXISTS_TAC `b':real`; EXISTS_TAC `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "M5" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `T0:real`;
    `g:real->A->real^N^N`; `g':real->A->real^N^N`; `b2:real`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `Z:real->A->real^N`
    (X_CHOOSE_THEN `e':real->A->real`
     (CONJUNCTS_THEN2 (LABEL_TAC "es") (CONJUNCTS_THEN2 (LABEL_TAC "e's")
       (CONJUNCTS_THEN2 (LABEL_TAC "Zs") (LABEL_TAC "ineq"))))))) THEN
  USE_THEN "R5" (MP_TAC o BETA_RULE o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b2:real`;
    `g:real->A->real^N^N`;
    `\s. pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s)`; `e':real->A->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "ineq" (MP_TAC o SPECL [`s:real`; `x':A`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Ects") (LABEL_TAC "Eder")) THEN
  MP_TAC(BETA_RULE(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b2:real`;
    `g:real->A->real^N^N`;
    `\s. pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s)`; `e':real->A->real`]
   RFU_SFUN_INTEGRABLE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "ineq" (MP_TAC o SPECL [`s:real`; `x':A`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Ei") (LABEL_TAC "E'i")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b2:real`; `g:real->A->real^N^N`] RFU_SCALAR_LB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R"))) THEN
  SUBGOAL_THEN
   `!s y. a <= s /\ s < b2 /\ y IN topspace top
          ==> &0 <= pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s) y`
  (LABEL_TAC "epos") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                   `(g:real->A->real^N^N) s`; `(g':real->A->real^N^N) s`; `y:A`]
                  PDE_KOT_DENSITY_ZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "rm" MATCH_MP_TAC; USE_THEN "rm'" MATCH_MP_TAC] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b2
        ==> &0 <= mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                                 (pde_mkot_density atlas (g s) (g' s))`
  (LABEL_TAC "Epos") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "Ei" (MP_TAC o C MATCH_MP (CONJ (ASSUME `a <= s:real`) (ASSUME `s < b2:real`))) THEN
    REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) s`;
                   `\y:A. &0 * pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s) y`;
                   `pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s)`;
                   `topspace top:A->bool`;
                   `&0 * mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                                       (pde_mkot_density atlas (g s) (g' s))`;
                   `mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                                 (pde_mkot_density atlas (g s) (g' s))`]
                  MFD_HAS_INTEGRAL_LE) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) s`;
                     `pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s)`;
                     `topspace top:A->bool`;
                     `mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                                   (pde_mkot_density atlas (g s) (g' s))`; `&0`]
                    MFD_HAS_INTEGRAL_CMUL) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      REPEAT STRIP_TAC THEN USE_THEN "epos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the energy inequality E' <= (|C| + H) E on (a,b2) *)
  SUBGOAL_THEN
   `!s. a < s /\ s < b2
        ==> mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
              (\y. (e':real->A->real) s y -
                   mfd_scalar atlas (g s) y * pde_mkot_density atlas (g s) (g' s) y) <=
            (abs C + H) * mfd_integral (top,atlas) (g s) (topspace top)
                            (pde_mkot_density atlas (g s) (g' s))`
  (LABEL_TAC "bd") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFU_ENERGY_STEP THEN
    EXISTS_TAC `mfd_div atlas ((g:real->A->real^N^N) s) ((Z:real->A->real^N) s)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) s)` ASSUME_TAC THENL
     [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "R4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "Zs" (MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`) o
                     SPEC `c:(A->bool)#(A->real^N)`) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b2:real`;
                     `s:real`;
                     `\z. mfd_vrep atlas ((Z:real->A->real^N) (drop(fstcart z)))
                                   (c:(A->bool)#(A->real^N)) (sndcart z)`]
                    RFU_SMOOTH_SLICE_AT) THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; ETA_AX];
      USE_THEN "Ei" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "E'i" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [USE_THEN "epos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "ineq" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  (* E(a) = 0 *)
  SUBGOAL_THEN
   `mfd_integral (top,atlas) ((g:real->A->real^N^N) a) (topspace top)
                 (pde_mkot_density atlas (g a) (g' a)) = &0`
  (LABEL_TAC "E0") THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN CONJ_TAC THENL
     [USE_THEN "Epos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "Ei" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) a`;
                   `pde_mkot_density atlas ((g:real->A->real^N^N) a) (g' a)`;
                   `\y:A. &0 * pde_mkot_density atlas ((g:real->A->real^N^N) a) (g' a) y`;
                   `topspace top:A->bool`;
                   `mfd_integral (top,atlas) ((g:real->A->real^N^N) a) (topspace top)
                                 (pde_mkot_density atlas (g a) (g' a))`;
                   `&0 * mfd_integral (top,atlas) ((g:real->A->real^N^N) a) (topspace top)
                                       (pde_mkot_density atlas (g a) (g' a))`]
                  MFD_HAS_INTEGRAL_LE) THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(g:real->A->real^N^N) a`;
                     `pde_mkot_density atlas ((g:real->A->real^N^N) a) (g' a)`;
                     `topspace top:A->bool`;
                     `mfd_integral (top,atlas) ((g:real->A->real^N^N) a) (topspace top)
                                   (pde_mkot_density atlas (g a) (g' a))`; `&0`]
                    MFD_HAS_INTEGRAL_CMUL) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
      MATCH_MP_TAC RFU_MKOT_SAME THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* Gronwall *)
  MP_TAC(ISPECL
   [`\s. mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                      (pde_mkot_density atlas (g s) (g' s))`;
    `\s. mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                      (\y. (e':real->A->real) s y -
                           mfd_scalar atlas (g s) y * pde_mkot_density atlas (g s) (g' s) y)`;
    `abs C + H`; `a:real`; `t:real`] RFU_GRONWALL_UP) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{s:real | a <= s /\ s < b2}` THEN
      USE_THEN "Ects" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "Eder" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "bd" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "E0" SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN
  (* the density vanishes at time t *)
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((g:real->A->real^N^N) t)
      (pde_mkot_density atlas (g t) (g' t)) (topspace top) (&0)`
  ASSUME_TAC THENL
   [USE_THEN "Ei" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "Epos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`;
                 `pde_mkot_density atlas ((g:real->A->real^N^N) t) (g' t)`; `x:A`]
                RFU_MFD_INTEGRAL_ZERO_IMP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN USE_THEN "epos" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
         `a:real`; `b2:real`;
         `\s. pde_mkot_density atlas ((g:real->A->real^N^N) s) (g' s)`;
         `c:(A->bool)#(A->real^N)`; `t:real`] RFU_SFUN_CHART_CONTINUOUS)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `top:A topology`;
                 `(g:real->A->real^N^N) t`; `(g':real->A->real^N^N) t`; `x:A`]
                PDE_KOT_DENSITY_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "rm" MATCH_MP_TAC; USE_THEN "rm'" MATCH_MP_TAC] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

(* Uniqueness of Ricci flow with the same initial metric on a closed        *)
(* manifold (PDE_UNIQUENESS_STATEMENT of pc_pde_iface).                      *)

let PDE_UNIQUENESS = prove
 (`!(u:A->bool) (n:N->bool). PDE_UNIQUENESS_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_UNIQUENESS_FROM_KOT THEN
  REWRITE_TAC[PDE_KOT_POINTWISE; PDE_REQ_DIVERGENCE; PDE_REQ_INTEGRAL_DERIV]);;

