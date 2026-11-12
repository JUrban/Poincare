(* ========================================================================= *)
(* Unit pc_cmp_rad (comparison-geometry layer CMP): Euclidean radial         *)
(* analysis for the volume comparisons S1 (CMP_RELVOL) and S2                *)
(* (CMP_GUNTHER).  The radial map T(v) = (rho(|v|)/|v|) v with rho           *)
(* increasing has Jacobian rho'(|v|) (rho(|v|)/|v|)^(n-1) (a rank-one        *)
(* update of a multiple of the identity), so by the change of variables      *)
(* formula integrals over balls can be moved along such maps.  With rho      *)
(* defined through the model volume function this gives the integral of the  *)
(* model density (sn_k(|w|)/|w|)^(n-1) over a ball (= cmp_vmodel) and the    *)
(* Euclidean form of the Bishop-Gromov comparison for weights that are       *)
(* non-increasing along rays.                                                *)
(* ========================================================================= *)

needs "src/pc_cmp_pull.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The determinant of a rank-one update of a multiple of the                 *)
(* identity, h -> a h + b (u.h) u with |u| = 1, is (a + b) a^(n-1)           *)
(* (conjugate by an orthogonal P with P e1 = u to a diagonal matrix).        *)
(* ========================================================================= *)

let CMPV_DET_RANK_ONE = prove
 (`!a b (u:real^N).
        norm u = &1
        ==> det(matrix(\h:real^N. a % h + (b * (u dot h)) % u)) =
            (a + b) * a pow (dimindex(:N) - 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `P:real^N^N` STRIP_ASSUME_TAC o
    MATCH_MP ORTHOGONAL_MATRIX_EXISTS_BASIS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [orthogonal_matrix]) THEN
  ABBREV_TAC `D:real^N^N =
    lambda i j. if j = i then (if i = 1 then a + b else a) else &0` THEN
  SUBGOAL_THEN `!y:real^N. (D:real^N^N) ** y = a % y + (b * y$1) % basis 1`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "D" THEN
    SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[MESON[REAL_MUL_LZERO]
     `(if p then c else &0) * (x:real) = if p then c * x else &0`] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N))
        (\j. if j = i then (if i = 1 then a + b else a) * (y:real^N)$j else &0) =
      (if i = 1 then a + b else a) * y$i`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:N))
        (\j. if j = i then (if i = 1 then a + b else a) * (y:real^N)$i else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_CASES_TAC `j:num = i` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG]];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:real^N. (transp(P:real^N^N) ** h)$1 = u dot h` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`transp(P:real^N^N) ** (h:real^N)`; `1`] DOT_BASIS) THEN
    REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^N. a % h + (b * (u dot h)) % u) =
    (\h. ((P:real^N^N) ** (D:real^N^N) ** transp P) ** h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_MUL; DET_TRANSP] THEN
  SUBGOAL_THEN `det(P:real^N^N) * det(D:real^N^N) * det P = det D` SUBST1_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `diagonal_matrix(D:real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN SIMP_TAC[diagonal_matrix; LAMBDA_BETA] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DET_DIAGONAL] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product(1..dimindex(:N)) (\i. if i = 1 then a + b else a)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    EXPAND_TAC "D" THEN ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
  REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
  SUBGOAL_THEN
   `product(2..dimindex(:N)) (\i. if i = 1 then a + b else a) =
    product(2..dimindex(:N)) (\i. a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_CONST_NUMSEG] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC);;

(* ========================================================================= *)
(* The radial map T(v) = (rho(|v|)/|v|) v.  Its derivative at                *)
(* v <> 0 is the rank-one update h -> a h + b (u.h) u of a = rho/|v| with    *)
(* b = rho' - rho/|v| and u = v/|v|, with determinant rho' (rho/|v|)^(n-1).  *)
(* For rho a bijection of (0,a) onto (0,b), T is a bijection of the          *)
(* punctured balls, and the change of variables formula moves absolutely     *)
(* integrable functions on ball(0,b) to ball(0,a).                           *)
(* ========================================================================= *)

let CMPV_RADIAL_DERIV = prove
 (`!(rho:real->real) rho1 (v:real^N).
        ~(v = vec 0) /\ (rho has_real_derivative rho1) (atreal (norm v))
        ==> ((\w. (rho(norm w) / norm w) % w) has_derivative
             (\h. (rho(norm v) / norm v) % h +
                  ((rho1 - rho(norm v) / norm v) * ((inv(norm v) % v) dot h)) %
                  (inv(norm v) % v))) (at v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. rho s / s) has_real_derivative
     ((rho1 * norm(v:real^N) - rho(norm v) * &1) / norm v pow 2)) (atreal (norm v))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:real->real`; `rho1:real`; `\s:real. s`; `&1`; `norm(v:real^N)`]
      HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ID; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. rho(norm x) / norm x`;
                 `\h:real^N. (rho1 * norm(v:real^N) - rho(norm v) * &1) / norm v pow 2 *
                             (v dot h) / norm v`;
                 `\x:real^N. x`; `\h:real^N. h`; `v:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_DERIVATIVE_ID; o_DEF] THEN
    MP_TAC(ISPECL [`\s. rho s / s`;
                   `(rho1 * norm(v:real^N) - rho(norm v) * &1) / norm v pow 2`;
                   `\x:real^N. lift(norm x)`; `\h:real^N. lift((v dot h) / norm v)`;
                   `v:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    ASM_SIMP_TAC[LIFT_DROP; CMPP_NORM_DERIV] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  REWRITE_TAC[DOT_LMUL; VECTOR_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < norm(v:real^N)` THEN CONV_TAC REAL_FIELD);;

let CMPV_RADIAL_DET = prove
 (`!(v:real^N) a b.
        ~(v = vec 0)
        ==> det(matrix(\h. a % h + (b * ((inv(norm v) % v) dot h)) % (inv(norm v) % v))) =
            (a + b) * a pow (dimindex(:N) - 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPV_DET_RANK_ONE THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]);;

let CMPV_RADIAL_NORM = prove
 (`!(rho:real->real) (v:real^N).
        ~(v = vec 0) /\ &0 <= rho(norm v)
        ==> norm((rho(norm v) / norm v) % v) = rho(norm v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_DIV_RMUL; REAL_LT_IMP_NZ]);;

let CMPV_RADIAL_BIJ = prove
 (`!(rho:real->real) a b.
        (!t. &0 < t /\ t < a ==> &0 < rho t /\ rho t < b) /\
        (!s t. &0 < s /\ s < a /\ &0 < t /\ t < a /\ rho s = rho t ==> s = t) /\
        (!y. &0 < y /\ y < b ==> ?t. &0 < t /\ t < a /\ rho t = y)
        ==> (!v w:real^N. v IN ball(vec 0,a) DELETE vec 0 /\
                          w IN ball(vec 0,a) DELETE vec 0 /\
                          (rho(norm v) / norm v) % v = (rho(norm w) / norm w) % w
                          ==> v = w) /\
            IMAGE (\v:real^N. (rho(norm v) / norm v) % v) (ball(vec 0,a) DELETE vec 0) =
            ball(vec 0,b) DELETE vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_DELETE; IN_BALL_0] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`v:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(v:real^N) /\ &0 < norm(w:real^N)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `(rho:real->real)(norm(v:real^N)) = rho(norm(w:real^N))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`rho:real->real`; `v:real^N`] CMPV_RADIAL_NORM) THEN
      MP_TAC(ISPECL [`rho:real->real`; `w:real^N`] CMPV_RADIAL_NORM) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(v:real^N) = norm(w:real^N)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(rho(norm v) / norm v) % (v:real^N) = (rho(norm w) / norm w) % w` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
    SUBGOAL_THEN `~((rho:real->real)(norm(w:real^N)) / norm w = &0)` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_BALL_0] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rho:real->real`; `v:real^N`] CMPV_RADIAL_NORM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_SIMP_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `norm(y:real^N)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(t / norm(y:real^N)) % y` THEN
    SUBGOAL_THEN `norm((t / norm(y:real^N)) % y) = t` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `norm(y:real^N) / t * t / norm y = &1` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < norm(y:real^N)` THEN
        CONV_TAC REAL_FIELD;
        REWRITE_TAC[VECTOR_MUL_LID]];
      ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Change of variables along the radial map.  If rho is a                    *)
(* differentiable bijection of (0,a) onto (0,b) with rho' >= 0, then f is    *)
(* absolutely integrable on ball(0,b) with integral c iff                    *)
(* rho'(|v|) (rho(|v|)/|v|)^(n-1) f(T v) is so on ball(0,a).                 *)
(* ========================================================================= *)

let CMPV_DELETE0 = prove
 (`!(h:real^N->real^1) S.
        (h absolutely_integrable_on (S DELETE vec 0) <=> h absolutely_integrable_on S) /\
        integral (S DELETE vec 0) h = integral S h`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `negligible((S DELETE vec 0) DIFF S UNION S DIFF (S DELETE (vec 0:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^N}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SPIKE_SET_EQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN ASM_REWRITE_TAC[]]);;

let CMPV_RADIAL_CHANGE = prove
 (`!(rho:real->real) rho1 a b (f:real^N->real) c.
        (!t. &0 < t /\ t < a ==> &0 < rho t /\ rho t < b) /\
        (!s t. &0 < s /\ s < a /\ &0 < t /\ t < a /\ rho s = rho t ==> s = t) /\
        (!y. &0 < y /\ y < b ==> ?t. &0 < t /\ t < a /\ rho t = y) /\
        (!t. &0 < t /\ t < a
             ==> (rho has_real_derivative rho1 t) (atreal t) /\ &0 <= rho1 t)
        ==> ((\w. lift(f w)) absolutely_integrable_on ball(vec 0,b) /\
             integral (ball(vec 0,b)) (\w. lift(f w)) = lift c <=>
             (\v. lift(rho1(norm v) * (rho(norm v) / norm v) pow (dimindex(:N) - 1) *
                       f((rho(norm v) / norm v) % v)))
             absolutely_integrable_on ball(vec 0,a) /\
             integral (ball(vec 0,a))
               (\v. lift(rho1(norm v) * (rho(norm v) / norm v) pow (dimindex(:N) - 1) *
                         f((rho(norm v) / norm v) % v))) = lift c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "RINJ")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`rho:real->real`; `a:real`; `b:real`] CMPV_RADIAL_BIJ) THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "RINJ" (K ALL_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TINJ") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x:real^N. x IN ball(vec 0,a) DELETE vec 0
       ==> abs(det(matrix(\h. (rho(norm x) / norm x) % h +
                ((rho1(norm x) - rho(norm x) / norm x) * ((inv(norm x) % x) dot h)) %
                (inv(norm x) % x)))) % lift(f((rho(norm x) / norm x) % x)) =
           lift(rho1(norm x) * (rho(norm x) / norm x) pow (dimindex(:N) - 1) *
                f((rho(norm x) / norm x) % x))`
  ASSUME_TAC THENL
   [REMOVE_THEN "TINJ" (K ALL_TAC) THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DELETE; IN_BALL_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[CMPV_RADIAL_DET] THEN
    REWRITE_TAC[REAL_ARITH `a + (b - a) = b`; GSYM LIFT_CMUL; REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w:real^N. lift(f w)`;
    `\v:real^N. (rho(norm v) / norm v) % v`;
    `\v:real^N h:real^N. (rho(norm v) / norm v) % h +
         ((rho1(norm v) - rho(norm v) / norm v) * ((inv(norm v) % v) dot h)) %
         (inv(norm v) % v)`;
    `ball(vec 0:real^N,a) DELETE vec 0`; `lift c`] HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LEBESGUE_MEASURABLE_DELETE; LEBESGUE_MEASURABLE_BALL] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_DELETE; IN_BALL_0] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN MATCH_MP_TAC CMPV_RADIAL_DERIV THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ASM_SIMP_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "TINJ" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((\x:real^N. abs(det(matrix(\h. (rho(norm x) / norm x) % h +
                ((rho1(norm x) - rho(norm x) / norm x) * ((inv(norm x) % x) dot h)) %
                (inv(norm x) % x)))) % lift(f((rho(norm x) / norm x) % x)))
     absolutely_integrable_on (ball(vec 0,a) DELETE vec 0) <=>
     (\v. lift(rho1(norm v) * (rho(norm v) / norm v) pow (dimindex(:N) - 1) *
               f((rho(norm v) / norm v) % v)))
     absolutely_integrable_on (ball(vec 0,a) DELETE vec 0)) /\
    integral (ball(vec 0,a) DELETE vec 0)
     (\x:real^N. abs(det(matrix(\h. (rho(norm x) / norm x) % h +
                ((rho1(norm x) - rho(norm x) / norm x) * ((inv(norm x) % x) dot h)) %
                (inv(norm x) % x)))) % lift(f((rho(norm x) / norm x) % x))) =
    integral (ball(vec 0,a) DELETE vec 0)
     (\v. lift(rho1(norm v) * (rho(norm v) / norm v) pow (dimindex(:N) - 1) *
               f((rho(norm v) / norm v) % v)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABSOLUTELY_INTEGRABLE_EQ) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CMPV_DELETE0] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Radial profiles rho = V^-1 o U.  For V strictly increasing                *)
(* and continuous on [0,b] with V(0) = 0 and V' > 0 on (0,b), and U strictly *)
(* increasing and continuous on [0,a] with U(0) = 0, U(a) = V(b), the map    *)
(* rho is a bijection of (0,a) onto (0,b) with V(rho t) = U t and            *)
(* rho' = U'/V'(rho) (inverse function rule).                                *)
(* ========================================================================= *)

let CMPV_STRICT_INJ = prove
 (`!(V:real->real) b.
        (!s t. &0 <= s /\ s < t /\ t <= b ==> V s < V t)
        ==> !s t. &0 <= s /\ s <= b /\ &0 <= t /\ t <= b /\ V s = V t ==> s = t`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPECL [`s:real`; `t:real`] REAL_LT_TOTAL) THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `s:real`])] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;

let CMPV_STRICT_POS = prove
 (`!(V:real->real) b.
        (!s t. &0 <= s /\ s < t /\ t <= b ==> V s < V t) /\ V(&0) = &0
        ==> !s. &0 < s /\ s < b ==> &0 < V s /\ V s < V b`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mono") ASSUME_TAC) THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "mono" (MP_TAC o SPECL [`&0`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "mono" (MP_TAC o SPECL [`s:real`; `b:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMPV_INV_EXISTS = prove
 (`!(V:real->real) b.
        &0 < b /\ V real_continuous_on real_interval[&0,b] /\
        (!s t. &0 <= s /\ s < t /\ t <= b ==> V s < V t) /\ V(&0) = &0
        ==> ?Vi:real->real.
              (!y. &0 < y /\ y < V b ==> &0 < Vi y /\ Vi y < b /\ V(Vi y) = y) /\
              (!s. &0 < s /\ s < b ==> Vi(V s) = s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(LABEL_TAC "inj" o MATCH_MP CMPV_STRICT_INJ) THEN
  MP_TAC(ISPECL [`V:real->real`; `b:real`] CMPV_STRICT_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pos") THEN
  EXISTS_TAC `\y. @s. &0 <= s /\ s <= b /\ (V:real->real) s = y` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!y. &0 < y /\ y < (V:real->real) b
        ==> &0 <= (@s. &0 <= s /\ s <= b /\ V s = y) /\
            (@s. &0 <= s /\ s <= b /\ V s = y) <= b /\
            V(@s. &0 <= s /\ s <= b /\ V s = y) = y`
  (LABEL_TAC "sel") THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL [`V:real->real`; `&0`; `b:real`; `y:real`] REAL_IVT_INCREASING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    USE_THEN "sel" (MP_TAC o SPEC `y:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`);
      MATCH_MP_TAC(REAL_ARITH `x <= b /\ ~(x = b) ==> x < b`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(V:real->real)(@s. &0 <= s /\ s <= b /\ V s = y) = y` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "pos" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "sel" (MP_TAC o SPEC `(V:real->real) s`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let CMPV_INVERSE_COMPOSE = prove
 (`!(V:real->real) V1 (U:real->real) U1 a b.
        &0 < a /\ &0 < b /\
        V real_continuous_on real_interval[&0,b] /\
        (!s t. &0 <= s /\ s < t /\ t <= b ==> V s < V t) /\ V(&0) = &0 /\
        (!s. &0 < s /\ s < b ==> (V has_real_derivative V1 s) (atreal s) /\ &0 < V1 s) /\
        U real_continuous_on real_interval[&0,a] /\
        (!s t. &0 <= s /\ s < t /\ t <= a ==> U s < U t) /\ U(&0) = &0 /\ U a = V b /\
        (!t. &0 < t /\ t < a ==> (U has_real_derivative U1 t) (atreal t) /\ &0 <= U1 t)
        ==> ?rho:real->real.
              (!t. &0 < t /\ t < a ==> &0 < rho t /\ rho t < b /\ V(rho t) = U t) /\
              (!s t. &0 < s /\ s < a /\ &0 < t /\ t < a /\ rho s = rho t ==> s = t) /\
              (!y. &0 < y /\ y < b ==> ?t. &0 < t /\ t < a /\ rho t = y) /\
              (!t. &0 < t /\ t < a
                   ==> (rho has_real_derivative U1 t / V1(rho t)) (atreal t) /\
                       &0 <= U1 t / V1(rho t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Vmono")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Vder")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Umono")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Uder"))))))))))) THEN
  USE_THEN "Umono" (LABEL_TAC "Uinj" o MATCH_MP CMPV_STRICT_INJ) THEN
  MP_TAC(ISPECL [`U:real->real`; `a:real`] CMPV_STRICT_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "Upos") THEN
  MP_TAC(ISPECL [`V:real->real`; `b:real`] CMPV_STRICT_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "Vpos") THEN
  MP_TAC(ISPECL [`V:real->real`; `b:real`] CMPV_INV_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Vi:real->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "Vi") (LABEL_TAC "ViV"))) THEN
  EXISTS_TAC `(Vi:real->real) o (U:real->real)` THEN REWRITE_TAC[o_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "Upos" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Vi" (MP_TAC o SPEC `(U:real->real) t`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "Upos" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Upos" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Vi" (MP_TAC o SPEC `(U:real->real) s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Vi" (MP_TAC o SPEC `(U:real->real) t`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Uinj" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `(V:real->real)((Vi:real->real)((U:real->real) s)) = V(Vi(U t))`
    MP_TAC THENL [AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    USE_THEN "Vpos" (MP_TAC o SPEC `y:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real->real`; `&0`; `a:real`; `(V:real->real) y`]
      REAL_IVT_INCREASING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN
    SUBGOAL_THEN `&0 < t /\ t < a` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`);
        MATCH_MP_TAC(REAL_ARITH `x <= b /\ ~(x = b) ==> x < b`)] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `(U:real->real) t = (V:real->real) y` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ViV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  USE_THEN "Upos" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "Vi" (MP_TAC o SPEC `(U:real->real) t`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "Vder" (MP_TAC o SPEC `(Vi:real->real)((U:real->real) t)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "Uder" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
  SUBGOAL_THEN `(V:real->real) real_continuous_on real_interval(&0,b)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,b]` THEN
    ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((V1:real->real)((Vi:real->real)((U:real->real) t)) = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real->real`; `Vi:real->real`;
                 `(V1:real->real)((Vi:real->real)((U:real->real) t))`;
                 `real_interval(&0,b)`; `(Vi:real->real)((U:real->real) t)`]
    HAS_REAL_DERIVATIVE_INVERSE_STRONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ViV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real->real`; `Vi:real->real`; `(U1:real->real) t`;
                 `inv((V1:real->real)((Vi:real->real)((U:real->real) t)))`; `t:real`]
    REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The model volume function V_k(t) = cmp_vmodel (:N) k t is                 *)
(* continuous, strictly increasing on [0,B] and has derivative               *)
(* n |B^n| sn_k(t)^(n-1) > 0 on (0,B), where sn_k > 0 on (0,B).             *)
(* ========================================================================= *)

let CMPV_SN_CONTINUOUS_ON = prove
 (`!k s. cmp_sn k real_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  EXISTS_TAC `cmp_cs k x` THEN REWRITE_TAC[CMP_SN_HAS_DERIV]);;

let CMPV_VMODEL_FACTS = prove
 (`!k B. &0 < B /\ (!t. &0 < t /\ t < B ==> &0 < cmp_sn k t)
         ==> cmp_vmodel (:N) k real_continuous_on real_interval[&0,B] /\
             (!s t. &0 <= s /\ s < t /\ t <= B
                    ==> cmp_vmodel (:N) k s < cmp_vmodel (:N) k t) /\
             cmp_vmodel (:N) k (&0) = &0 /\
             (!s. &0 < s /\ s < B
                  ==> (cmp_vmodel (:N) k has_real_derivative
                       (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                       cmp_sn k s pow (dimindex(:N) - 1)) (atreal s) /\
                      &0 < (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                           cmp_sn k s pow (dimindex(:N) - 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N)) * measure(ball(vec 0:real^N,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01; REAL_OF_NUM_LT] THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C = &(dimindex(:N)) * measure(ball(vec 0:real^N,&1))` THEN
  SUBGOAL_THEN
   `cmp_vmodel (:N) k =
    (\t. C * real_integral (real_interval[&0,t])
                (\s. cmp_sn k s pow (dimindex(:N) - 1)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmp_vmodel] THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN real_interval[&0,B]
        ==> ((\t. C * real_integral (real_interval[&0,t])
                        (\s. cmp_sn k s pow (dimindex(:N) - 1))) has_real_derivative
             C * cmp_sn k x pow (dimindex(:N) - 1))
            (atreal x within real_interval[&0,B])`
  (LABEL_TAC "der") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
    MP_TAC(ISPECL [`\s. cmp_sn k s pow (dimindex(:N) - 1)`; `&0`; `B:real`]
      REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC[ETA_AX; CMPV_SN_CONTINUOUS_ON];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. &0 < x /\ x < B ==> &0 < C * cmp_sn k x pow (dimindex(:N) - 1)`
  (LABEL_TAC "pos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
    EXISTS_TAC `C * cmp_sn k x pow (dimindex(:N) - 1)` THEN
    USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
    EXISTS_TAC `\x. C * cmp_sn k x pow (dimindex(:N) - 1)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&0,B]` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [USE_THEN "der" MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      USE_THEN "pos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[REAL_INTEGRAL_REFL; REAL_MUL_RZERO];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`\t. C * real_integral (real_interval[&0,t])
                              (\s. cmp_sn k s pow (dimindex(:N) - 1))`;
                   `C * cmp_sn k s pow (dimindex(:N) - 1)`; `s:real`;
                   `real_interval(&0,B)`]
      HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&0,B]` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [USE_THEN "der" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The integral of the model density (sn_k(|w|)/|w|)^(n-1)                   *)
(* over ball(0,r) is cmp_vmodel (:N) k r (radial map from ball(0,1) with     *)
(* V_k(rho t) = V_k(r) t^n, whose Jacobian times the model density is        *)
(* constant).                                                                *)
(* ========================================================================= *)

let CMPV_JAC_ALG = prove
 (`!U1 C sr r t m.
        &0 < C /\ &0 < sr /\ &0 < r /\ &0 < t
        ==> U1 / (C * sr pow m) * (r / t) pow m * (sr / r) pow m = U1 / (C * t pow m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < sr pow m /\ &0 < r pow m /\ &0 < t pow m` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < sr pow m`; `&0 < r pow m`; `&0 < t pow m`; `&0 < C`] THEN
  CONV_TAC REAL_FIELD);;

let CMPV_SPIKE_CONST = prove
 (`!(G:real^N->real^1) s c d.
        measurable s /\ measure s * c = d /\
        (!x. x IN s DELETE vec 0 ==> G x = lift c)
        ==> G absolutely_integrable_on s /\ integral s G = lift d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    MAP_EVERY EXISTS_TAC [`(\x. lift c):real^N->real^1`; `{vec 0:real^N}`] THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_SING; ABSOLUTELY_INTEGRABLE_ON_CONST] THEN
    REWRITE_TAC[IN_DIFF; IN_SING] THEN ASM_SIMP_TAC[IN_DELETE];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral s ((\x. lift c):real^N->real^1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `{vec 0:real^N}` THEN
      REWRITE_TAC[NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN ASM_SIMP_TAC[IN_DELETE];
      ASM_SIMP_TAC[INTEGRAL_CONST_GEN; GSYM LIFT_CMUL]]]);;

let CMPV_MODEL_PROFILE = prove
 (`!k r. &0 < r /\ (!t. &0 < t /\ t < r ==> &0 < cmp_sn k t)
         ==> ?rho:real->real.
              (!t. &0 < t /\ t < &1
                   ==> &0 < rho t /\ rho t < r /\
                       cmp_vmodel (:N) k (rho t) =
                       cmp_vmodel (:N) k r * t pow dimindex(:N)) /\
              (!s t. &0 < s /\ s < &1 /\ &0 < t /\ t < &1 /\ rho s = rho t ==> s = t) /\
              (!y. &0 < y /\ y < r ==> ?t. &0 < t /\ t < &1 /\ rho t = y) /\
              (!t. &0 < t /\ t < &1
                   ==> (rho has_real_derivative
                        (cmp_vmodel (:N) k r * (&(dimindex(:N)) * t pow (dimindex(:N) - 1))) /
                        ((&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                         cmp_sn k (rho t) pow (dimindex(:N) - 1))) (atreal t) /\
                       &0 <= (cmp_vmodel (:N) k r *
                              (&(dimindex(:N)) * t pow (dimindex(:N) - 1))) /
                             ((&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                              cmp_sn k (rho t) pow (dimindex(:N) - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real`; `r:real`] CMPV_VMODEL_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cmp_vmodel (:N) k r` ASSUME_TAC THENL
   [UNDISCH_TAC
     `!s t. &0 <= s /\ s < t /\ t <= r
            ==> cmp_vmodel (:N) k s < cmp_vmodel (:N) k t` THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `r:real`]) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(dimindex(:N) = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`cmp_vmodel (:N) k`;
    `\s. (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
         cmp_sn k s pow (dimindex(:N) - 1)`;
    `\t. cmp_vmodel (:N) k r * t pow dimindex(:N)`;
    `\t. cmp_vmodel (:N) k r * (&(dimindex(:N)) * t pow (dimindex(:N) - 1))`;
    `&1`; `r:real`] CMPV_INVERSE_COMPOSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; REAL_POW_ONE; REAL_MUL_RID] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_POW_ZERO; REAL_MUL_RZERO];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[]]);;

let CMPV_MODEL_INTEGRAL = prove
 (`!k r. &0 < r /\ (!t. &0 < t /\ t < r ==> &0 < cmp_sn k t)
         ==> (\w:real^N. lift((cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1)))
             absolutely_integrable_on ball(vec 0,r) /\
             integral (ball(vec 0,r))
               (\w:real^N. lift((cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1))) =
             lift(cmp_vmodel (:N) k r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real`; `r:real`] CMPV_MODEL_PROFILE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "RINJ") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 < measure(ball(vec 0:real^N,&1))` ASSUME_TAC THENL
   [REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(dimindex(:N)) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`rho:real->real`;
    `\t. (cmp_vmodel (:N) k r * (&(dimindex(:N)) * t pow (dimindex(:N) - 1))) /
         ((&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
          cmp_sn k (rho t) pow (dimindex(:N) - 1))`;
    `&1`; `r:real`;
    `\w:real^N. (cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1)`;
    `cmp_vmodel (:N) k r`] CMPV_RADIAL_CHANGE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REMOVE_THEN "RINJ" (K ALL_TAC) THEN
  MATCH_MP_TAC CMPV_SPIKE_CONST THEN
  EXISTS_TAC `cmp_vmodel (:N) k r / measure(ball(vec 0:real^N,&1))` THEN
  REWRITE_TAC[MEASURABLE_BALL] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_DELETE; IN_BALL_0] THEN STRIP_TAC THEN
  REWRITE_TAC[LIFT_EQ] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (rho:real->real)(norm(v:real^N)) /\ rho(norm v) < r`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real->real`; `v:real^N`] CMPV_RADIAL_NORM) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < cmp_sn k ((rho:real->real)(norm(v:real^N)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N)) * measure(ball(vec 0:real^N,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMPV_JAC_ALG] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N) pow (dimindex(:N) - 1)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < measure(ball(vec 0:real^N,&1))`; `~(&(dimindex(:N)) = &0)`] THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The Euclidean Bishop-Gromov comparison.  For a weight                     *)
(* Phi >= 0 that is non-increasing along rays, the radial map of ball(0,r1)  *)
(* onto ball(0,r2) with V_k(rho t) = (V_k(r2)/V_k(r1)) V_k(t) multiplies the *)
(* model density by the constant V_k(r2)/V_k(r1) and moves points outwards,  *)
(* so int_{B(r2)} Phi mu_k / V_k(r2) <= int_{B(r1)} Phi mu_k / V_k(r1).     *)
(* ========================================================================= *)

let CMPV_COMPARE_PROFILE = prove
 (`!k r1 r2.
        &0 < r1 /\ r1 <= r2 /\ (!t. &0 < t /\ t < r2 ==> &0 < cmp_sn k t)
        ==> ?rho:real->real.
              (!t. &0 < t /\ t < r1
                   ==> &0 < rho t /\ rho t < r2 /\ t <= rho t /\
                       cmp_vmodel (:N) k (rho t) =
                       (cmp_vmodel (:N) k r2 / cmp_vmodel (:N) k r1) *
                       cmp_vmodel (:N) k t) /\
              (!s t. &0 < s /\ s < r1 /\ &0 < t /\ t < r1 /\ rho s = rho t ==> s = t) /\
              (!y. &0 < y /\ y < r2 ==> ?t. &0 < t /\ t < r1 /\ rho t = y) /\
              (!t. &0 < t /\ t < r1
                   ==> (rho has_real_derivative
                        ((cmp_vmodel (:N) k r2 / cmp_vmodel (:N) k r1) *
                         (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                         cmp_sn k t pow (dimindex(:N) - 1)) /
                        ((&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                         cmp_sn k (rho t) pow (dimindex(:N) - 1))) (atreal t) /\
                       &0 <= ((cmp_vmodel (:N) k r2 / cmp_vmodel (:N) k r1) *
                              (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                              cmp_sn k t pow (dimindex(:N) - 1)) /
                             ((&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
                              cmp_sn k (rho t) pow (dimindex(:N) - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real`; `r2:real`] CMPV_VMODEL_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "der")))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= r2 ==> &0 <= cmp_vmodel (:N) k t` (LABEL_TAC "nn") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    USE_THEN "mono" (MP_TAC o SPECL [`&0`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cmp_vmodel (:N) k r1` ASSUME_TAC THENL
   [USE_THEN "mono" (MP_TAC o SPECL [`&0`; `r1:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_vmodel (:N) k r1 <= cmp_vmodel (:N) k r2` ASSUME_TAC THENL
   [ASM_CASES_TAC `r1:real = r2` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "mono" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = cmp_vmodel (:N) k r2 / cmp_vmodel (:N) k r1` THEN
  SUBGOAL_THEN `&1 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `c * cmp_vmodel (:N) k r1 = cmp_vmodel (:N) k r2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`cmp_vmodel (:N) k`;
    `\s. (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
         cmp_sn k s pow (dimindex(:N) - 1)`;
    `\t. c * cmp_vmodel (:N) k t`;
    `\t. c * (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
             cmp_sn k t pow (dimindex(:N) - 1)`;
    `r1:real`; `r2:real`] CMPV_INVERSE_COMPOSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[&0,r2]` THEN
      ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; ETA_AX] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; USE_THEN "mono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        USE_THEN "der" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ETA_AX]];
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_IMP_LE THEN
          USE_THEN "der" (MP_TAC o SPEC `t:real`) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ETA_AX]]]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rho:real->real) t /\ rho t < r2 /\
                cmp_vmodel (:N) k (rho t) = c * cmp_vmodel (:N) k t`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cmp_vmodel (:N) k t <= c * cmp_vmodel (:N) k t` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "nn" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "mono" (MP_TAC o SPECL [`(rho:real->real) t`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMPV_COMPARE_ALG = prove
 (`!c C st srho t rho p q m.
        &0 < C /\ &0 < st /\ &0 < srho /\ &0 < t /\ &0 < rho /\ &0 <= c /\ q <= p
        ==> (c * C * st pow m) / (C * srho pow m) * (rho / t) pow m *
            q * (srho / rho) pow m <=
            c * p * (st / t) pow m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(c * C * st pow m) / (C * srho pow m) * (rho / t) pow m * q * (srho / rho) pow m =
    (c * (st / t) pow m) * q`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < st pow m /\ &0 < srho pow m /\ &0 < t pow m /\ &0 < rho pow m`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&0 < st pow m`; `&0 < srho pow m`; `&0 < t pow m`; `&0 < rho pow m`; `&0 < C`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * p * (st / t) pow m = (c * (st / t) pow m) * p` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let CMPV_INTEGRAL_LE_DELETE = prove
 (`!(G:real^N->real^1) s b.
        integral s G = lift b
        ==> !H. G absolutely_integrable_on s /\ H absolutely_integrable_on s /\
                (!x. x IN s DELETE vec 0 ==> drop(G x) <= drop(H x))
                ==> b <= drop(integral s H)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b = drop(integral s (G:real^N->real^1))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT2(SPEC_ALL CMPV_DELETE0))] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  ASM_REWRITE_TAC[CMPV_DELETE0]);;

let CMPV_RADIAL_COMPARE = prove
 (`!k r1 r2 (Phi:real^N->real).
        &0 < r1 /\ r1 <= r2 /\ (!t. &0 < t /\ t < r2 ==> &0 < cmp_sn k t) /\
        (!w. &0 <= Phi w) /\
        (!w s. w IN ball(vec 0,r2) /\ &0 < s /\ s <= &1 ==> Phi w <= Phi(s % w)) /\
        (\w. lift(Phi w * (cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1)))
        absolutely_integrable_on ball(vec 0,r2)
        ==> drop(integral (ball(vec 0,r2))
                 (\w. lift(Phi w * (cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1)))) *
            cmp_vmodel (:N) k r1 <=
            drop(integral (ball(vec 0,r1))
                 (\w. lift(Phi w * (cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1)))) *
            cmp_vmodel (:N) k r2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ray") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real`; `r2:real`] CMPV_VMODEL_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mono")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "der")))) THEN
  SUBGOAL_THEN `&0 < cmp_vmodel (:N) k r1` ASSUME_TAC THENL
   [USE_THEN "mono" (MP_TAC o SPECL [`&0`; `r1:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < measure(ball(vec 0:real^N,&1))` ASSUME_TAC THENL
   [REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N)) * measure(ball(vec 0:real^N,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real`; `r1:real`; `r2:real`] CMPV_COMPARE_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = cmp_vmodel (:N) k r2 / cmp_vmodel (:N) k r1` THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real->real` (CONJUNCTS_THEN2 (LABEL_TAC "rho")
    (CONJUNCTS_THEN2 (LABEL_TAC "rhoinj")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rhoder"))))) THEN
  SUBGOAL_THEN `&0 <= c /\ c * cmp_vmodel (:N) k r1 = cmp_vmodel (:N) k r2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [USE_THEN "mono" (MP_TAC o SPECL [`&0`; `r2:real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  ABBREV_TAC `f = \w:real^N. Phi w * (cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1)` THEN
  SUBGOAL_THEN `(\w:real^N. lift(f w)) absolutely_integrable_on ball(vec 0,r2)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\w:real^N. lift(f w)) absolutely_integrable_on ball(vec 0,r1)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,r2)` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w:real^N. lift(Phi w * (cmp_sn k (norm w) / norm w) pow (dimindex(:N) - 1))) =
    (\w. lift(f w))`
  SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `I2 = drop(integral (ball(vec 0:real^N,r2)) (\w. lift(f w)))` THEN
  ABBREV_TAC `I1 = drop(integral (ball(vec 0:real^N,r1)) (\w. lift(f w)))` THEN
  MP_TAC(ISPECL
   [`rho:real->real`;
    `\t. (c * (&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
               cmp_sn k t pow (dimindex(:N) - 1)) /
         ((&(dimindex(:N)) * measure(ball(vec 0:real^N,&1))) *
          cmp_sn k (rho t) pow (dimindex(:N) - 1))`;
    `r1:real`; `r2:real`; `f:real^N->real`; `I2:real`] CMPV_RADIAL_CHANGE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rho" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "rhoinj" (K ALL_TAC) THEN
  SUBGOAL_THEN `integral (ball(vec 0:real^N,r2)) (\w. lift(f w)) = lift I2` ASSUME_TAC THENL
   [EXPAND_TAC "I2" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `I2 <= c * I1` MP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(c * I1) * cmp_vmodel (:N) k r1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `(c * I1) * cmp_vmodel (:N) k r1 = I1 * (c * cmp_vmodel (:N) k r1)`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]]]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(vec 0:real^N,r1)) (\v. lift(c * f v)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    ASM_REWRITE_TAC[DROP_CMUL; REAL_LE_REFL]] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP CMPV_INTEGRAL_LE_DELETE) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_DELETE; IN_BALL_0] THEN STRIP_TAC THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  USE_THEN "rho" (MP_TAC o SPEC `norm(v:real^N)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`rho:real->real`; `v:real^N`] CMPV_RADIAL_NORM) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  EXPAND_TAC "f" THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPV_COMPARE_ALG THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ray" (MP_TAC o SPECL
   [`((rho:real->real)(norm(v:real^N)) / norm v) % v`;
    `norm(v:real^N) / (rho:real->real)(norm v)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `norm(v:real^N) / (rho:real->real)(norm v) * rho(norm v) / norm v = &1`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < norm(v:real^N)`; `&0 < (rho:real->real)(norm(v:real^N))`] THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[VECTOR_MUL_LID]]);;

