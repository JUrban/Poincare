(* ========================================================================= *)
(* pc_smt_cover: S6 (SMT_SPHERE_COVERING_STATEMENT), local diffeomorphisms   *)
(* of S^2 are diffeomorphisms.                                               *)
(*                                                                           *)
(* The radial extension F = radial_ext f of a map of the sphere              *)
(* with tangentially injective derivative has injective derivative on R^N    *)
(* minus 0 (F x . DF(x) h = x . h from |F z| = |z|; DF(x) = Df(x) on tangent *)
(* vectors along great circles; homogeneity off the sphere); smooth          *)
(* bijections of an open set with invertible derivative have smooth inverse. *)
(* ========================================================================= *)

needs "src/pc_smt_radial.ml";;
needs "src/pc_top_cover.ml";;
needs "src/poincare_statement_sanity.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_DET_NONZERO_INJECTIVE = prove
 (`!L:real^N->real^N.
        linear L ==> (~(det(matrix L) = &0) <=> !h. L h = vec 0 ==> h = vec 0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DET_MATRIX_EQ_0_LEFT] THEN
  EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; FUN_EQ_THM; o_THM; I_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:real^N->real^N`] THEN STRIP_TAC THEN
    X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[LINEAR_0];
    DISCH_TAC THEN MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN
    ASM_SIMP_TAC[LINEAR_INJECTIVE_0]]);;

let SMT_OPEN_INVERSE_SMOOTH = prove
 (`!(f:real^N->real^N) g s.
        open s /\ smooth_map_on s f /\
        (!x. x IN s ==> f x IN s /\ g(f x) = x) /\
        (!y. y IN s ==> g y IN s /\ f(g y) = y) /\
        (!x. x IN s ==> ~(det(matrix(frechet_derivative f (at x))) = &0))
        ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`; `(g:real^N->real^N) y0`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `k:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `diffeomorphism_on t u (f:real^N->real^N) k` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `k:real^N->real^N` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(k:real^N->real^N) v IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `t SUBSET (s:real^N->bool)` THEN
    UNDISCH_TAC `IMAGE (k:real^N->real^N) u = t` THEN
    UNDISCH_TAC `(v:real^N) IN u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) = f((k:real^N->real^N) v)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]);;

(* Homogeneity of the radial extension.                                      *)

let SMT_RADIAL_EXT_HOMOG = prove
 (`!(f:real^N->real^N) c y. &0 < c ==> radial_ext f (c % y) = c % radial_ext f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[radial_ext; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO; REAL_MUL_RZERO; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(c * norm(y:real^N)) % (c % y) = inv(norm y) % y` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[VECTOR_MUL_ASSOC]]);;

let SMT_RADIAL_EXT_SPHERE = prove
 (`!(f:real^N->real^N) x. x IN sphere(vec 0,&1) ==> radial_ext f x = f x`,
  REWRITE_TAC[IN_SPHERE_0; radial_ext] THEN SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID]);;

(* Vector derivatives.                                                       *)

let SMT_CHAIN_VECTOR = prove
 (`!(c:real^1->real^N) v (FF:real^N->real^P) FF' u.
        (c has_vector_derivative v) (at u) /\ (FF has_derivative FF') (at (c u))
        ==> ((FF o c) has_vector_derivative FF' v) (at u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^1. drop x % (FF':real^N->real^P) v) = FF' o (\x. drop x % v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `linear(FF':real^N->real^P)` MP_TAC THENL
     [UNDISCH_TAC `((FF:real^N->real^P) has_derivative FF') (at ((c:real^1->real^N) u))` THEN
      SIMP_TAC[has_derivative];
      SIMP_TAC[LINEAR_CMUL]];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]]);;

let SMT_CIRCLE_DERIV = prove
 (`!(a:real^N) b s.
        ((\u. cos(drop u) % a + sin(drop u) % b) has_vector_derivative
         (--sin(drop s) % a + cos(drop s) % b)) (at s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MP_TAC(REAL_DIFF_CONV
   `((\t. cos t * (a:real^N)$i + sin t * (b:real^N)$i) has_real_derivative f)
    (atreal (drop s))`) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF; REAL_MUL_LID]);;

let SMT_LINE_DERIV = prove
 (`!(a:real^N) s. ((\u. a + drop u % a) has_vector_derivative a) (at s)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the radial extension.                                   *)
(* ------------------------------------------------------------------------- *)

let SMT_RADIAL_DERIV_DOT = prove
 (`!(f:real^N->real^N) x D h.
        (!y. y IN sphere(vec 0,&1) ==> f y IN sphere(vec 0,&1)) /\
        (radial_ext f has_derivative D) (at x)
        ==> radial_ext f x dot D h = x dot h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z:real^N. lift(norm z pow 2)) o radial_ext f has_derivative
     (\h. &2 % lift(radial_ext (f:real^N->real^N) x dot h)) o (D:real^N->real^N))
    (at x)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^N. lift(norm z pow 2)) o radial_ext (f:real^N->real^N) =
    (\z. lift(norm z pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[SMT_RADIAL_EXT_NORM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^N. lift(norm z pow 2)`;
                 `(\h. &2 % lift(radial_ext (f:real^N->real^N) x dot h)) o
                  (D:real^N->real^N)`;
                 `\h:real^N. &2 % lift(x dot h)`; `x:real^N`]
    FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT] THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN
  REWRITE_TAC[o_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC);;

let SMT_RADIAL_DERIV_TANGENT = prove
 (`!(f:real^N->real^N) x h D Df.
        x IN sphere(vec 0,&1) /\ orthogonal x h /\
        (radial_ext f has_derivative D) (at x) /\ (f has_derivative Df) (at x)
        ==> D h = Df h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (D:real^N->real^N) /\ linear (Df:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(radial_ext (f:real^N->real^N) has_derivative D) (at x)`;
      UNDISCH_TAC `((f:real^N->real^N) has_derivative Df) (at x)`] THEN
    SIMP_TAC[has_derivative];
    ALL_TAC] THEN
  ASM_CASES_TAC `h:real^N = vec 0` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    UNDISCH_TAC `linear(D:real^N->real^N)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]);
    ALL_TAC] THEN
  ABBREV_TAC `k = inv(norm h) % (h:real^N)` THEN
  SUBGOAL_THEN `(h:real^N) = norm h % k` SUBST1_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  UNDISCH_TAC `linear(D:real^N->real^N)` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(x:real^N) dot k = &0 /\ (k:real^N) dot k = &1 /\ x dot x = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[DOT_RMUL; DOT_LMUL] THEN
    UNDISCH_TAC `orthogonal (x:real^N) h` THEN REWRITE_TAC[orthogonal] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    UNDISCH_TAC `(x:real^N) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM NORM_POW_2; REAL_MUL_ASSOC] THEN
    UNDISCH_TAC `~(h:real^N = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `c = \u:real^1. cos(drop u) % x + sin(drop u) % (k:real^N)` THEN
  SUBGOAL_THEN `((c:real^1->real^N) has_vector_derivative k) (at (vec 0))`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    MP_TAC(ISPECL [`x:real^N`; `k:real^N`; `vec 0:real^1`] SMT_CIRCLE_DERIV) THEN
    REWRITE_TAC[DROP_VEC; SIN_0; COS_0; REAL_NEG_0; VECTOR_MUL_LZERO;
                VECTOR_ADD_LID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^1->real^N) (vec 0) = x` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REWRITE_TAC[DROP_VEC; SIN_0; COS_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. (c:real^1->real^N) u IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `(k:real^N) dot x = &0` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `drop u` SIN_CIRCLE) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `radial_ext (f:real^N->real^N) o (c:real^1->real^N) = f o c`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[SMT_RADIAL_EXT_SPHERE];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`(f:real^N->real^N) o (c:real^1->real^N)`; `vec 0:real^1`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SMT_CHAIN_VECTOR THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMT_CHAIN_VECTOR THEN ASM_REWRITE_TAC[]]);;

let SMT_RADIAL_DERIV_INJ_SPHERE = prove
 (`!(f:real^N->real^N) x D Df.
        x IN sphere(vec 0,&1) /\
        (!y. y IN sphere(vec 0,&1) ==> f y IN sphere(vec 0,&1)) /\
        (radial_ext f has_derivative D) (at x) /\ (f has_derivative Df) (at x) /\
        (!h. orthogonal x h /\ Df h = vec 0 ==> h = vec 0)
        ==> !k. D k = vec 0 ==> k = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `orthogonal (x:real^N) k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `x:real^N`; `D:real^N->real^N`; `k:real^N`]
      SMT_RADIAL_DERIV_DOT) THEN
    ASM_REWRITE_TAC[DOT_RZERO; orthogonal] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `x:real^N`; `k:real^N`; `D:real^N->real^N`;
                 `Df:real^N->real^N`] SMT_RADIAL_DERIV_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let SMT_RADIAL_DERIV_INJ = prove
 (`!(f:real^N->real^N) y.
        smooth_near (sphere(vec 0,&1)) f /\
        (!y. y IN sphere(vec 0,&1) ==> f y IN sphere(vec 0,&1)) /\
        (!x h. x IN sphere(vec 0,&1) /\ orthogonal x h /\
               frechet_derivative f (at x) h = vec 0 ==> h = vec 0) /\
        ~(y = vec 0)
        ==> !k. frechet_derivative (radial_ext f) (at y) k = vec 0 ==> k = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") ASSUME_TAC))) THEN
  ABBREV_TAC `l = norm(y:real^N)` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `x = inv l % (y:real^N)` THEN
  SUBGOAL_THEN `(x:real^N) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN EXPAND_TAC "l" THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^N | ~(z = vec 0)} (radial_ext f)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_RADIAL_EXT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. ~(z = vec 0)
               ==> (radial_ext f has_derivative frechet_derivative (radial_ext f) (at z))
                   (at z)`
  (LABEL_TAC "der") THENL
   [MP_TAC(ISPECL [`{z:real^N | ~(z = vec 0)}`; `radial_ext (f:real^N->real^N)`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:real^N->real^N) has_derivative frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `smooth_near (sphere(vec 0,&1)) (f:real^N->real^N)` THEN
    REWRITE_TAC[smooth_near] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `f:real^N->real^N`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* injectivity at x *)
  MP_TAC(ISPECL [`f:real^N->real^N`; `x:real^N`;
                 `frechet_derivative (radial_ext (f:real^N->real^N)) (at x)`;
                 `frechet_derivative (f:real^N->real^N) (at x)`]
    SMT_RADIAL_DERIV_INJ_SPHERE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  (* homogeneity *)
  SUBGOAL_THEN
   `radial_ext (f:real^N->real^N) = (\z. l % radial_ext f (inv l % z))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
    SIMP_TAC[GSYM SMT_RADIAL_EXT_HOMOG; ASSUME `&0 < (l:real)`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; ASSUME `&0 < (l:real)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(radial_ext (f:real^N->real^N) has_derivative
     (\h. l % frechet_derivative (radial_ext f) (at x) (inv l % h))) (at y)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [th]) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    SUBGOAL_THEN
     `(\z:real^N. radial_ext (f:real^N->real^N) (inv l % z)) =
      radial_ext f o (\z. inv l % z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h:real^N. frechet_derivative (radial_ext (f:real^N->real^N)) (at x) (inv l % h)) =
      frechet_derivative (radial_ext f) (at x) o (\h. inv l % h)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
      REWRITE_TAC[] THEN SUBST1_TAC(ASSUME `inv l % (y:real^N) = x`) THEN
      USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  X_GEN_TAC `k:real^N` THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0] THEN SIMP_TAC[REAL_LT_IMP_NZ; ASSUME `&0 < (l:real)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv l % (k:real^N) = vec 0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ; ASSUME `&0 < (l:real)`]);;

(* ------------------------------------------------------------------------- *)
(* S6.  f is a local homeomorphism of the sphere (inverse                    *)
(* function theorem for the radial extension, whose local inverses preserve  *)
(* norms), hence a bijection (COMPACT_LOCAL_HOMEOMORPHISM_SIMPLY_CONNECTED_  *)
(* BIJECTIVE, S^2 simply connected); the radial extension of the inverse is  *)
(* the smooth inverse of radial_ext f on R^3 minus 0.                         *)
(* ------------------------------------------------------------------------- *)

let SMT_RADIAL_DET_NONZERO = prove
 (`!f:real^N->real^N.
        smooth_near (sphere(vec 0,&1)) f /\
        (!y. y IN sphere(vec 0,&1) ==> f y IN sphere(vec 0,&1)) /\
        (!x h. x IN sphere(vec 0,&1) /\ orthogonal x h /\
               frechet_derivative f (at x) h = vec 0 ==> h = vec 0)
        ==> !y. ~(y = vec 0)
                ==> ~(det(matrix(frechet_derivative (radial_ext f) (at y))) = &0)`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (radial_ext (f:real^N->real^N)) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^N | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_RADIAL_EXT; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `frechet_derivative (radial_ext (f:real^N->real^N)) (at y)`
    SMT_DET_NONZERO_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SMT_RADIAL_DERIV_INJ THEN ASM_REWRITE_TAC[]);;

let SMT_SPHERE_LOCAL_HOMEO = prove
 (`!f:real^N->real^N.
        smooth_near (sphere(vec 0,&1)) f /\
        (!y. y IN sphere(vec 0,&1) ==> f y IN sphere(vec 0,&1)) /\
        (!x h. x IN sphere(vec 0,&1) /\ orthogonal x h /\
               frechet_derivative f (at x) h = vec 0 ==> h = vec 0)
        ==> local_homeomorphism_map
              (subtopology euclidean (sphere(vec 0,&1)),
               subtopology euclidean (sphere(vec 0,&1))) f`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SMT_RADIAL_DET_NONZERO th) THEN
    ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  DISCH_TAC THEN
  REWRITE_TAC[local_homeomorphism_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`radial_ext (f:real^N->real^N)`; `{z:real^N | ~(z = vec 0)}`;
                 `x:real^N`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_RADIAL_EXT; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `G:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `diffeomorphism_on t u (radial_ext (f:real^N->real^N)) G` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^N. norm(radial_ext f z) = norm z` (LABEL_TAC "nrm") THENL
   [GEN_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) continuous_on sphere(vec 0,&1) /\
                (G:real^N->real^N) continuous_on u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `smooth_near (sphere(vec 0,&1)) (f:real^N->real^N)` THEN
      REWRITE_TAC[smooth_near] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^N,&1) INTER t`;
                        `sphere(vec 0:real^N,&1) INTER u`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY;
              SET_RULE `(s:A->bool) INTER s INTER t = s INTER t`] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
  EXISTS_TAC `G:real^N->real^N` THEN REWRITE_TAC[homeomorphism] THEN
  SUBGOAL_THEN `!z:real^N. z IN sphere(vec 0,&1) ==> (f:real^N->real^N) z = radial_ext f z`
  (LABEL_TAC "Fs") THENL [SIMP_TAC[SMT_RADIAL_EXT_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN sphere(vec 0,&1) /\ y IN u
               ==> (G:real^N->real^N) y IN sphere(vec 0,&1) /\ G y IN t /\
                   radial_ext f (G y) = y`
  (LABEL_TAC "Gs") THENL
   [X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(G:real^N->real^N) y IN t /\ radial_ext f (G y) = y`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SPHERE_0] THEN
    USE_THEN "nrm" (MP_TAC o SPEC `(G:real^N->real^N) y`) THEN
    UNDISCH_TAC `radial_ext (f:real^N->real^N) ((G:real^N->real^N) y) = y` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(y:real^N) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    USE_THEN "Fs" (fun th -> ASM_SIMP_TAC[th]);
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        USE_THEN "Fs" (fun th -> ASM_SIMP_TAC[th]) THEN
        UNDISCH_TAC `IMAGE (radial_ext (f:real^N->real^N)) t = u` THEN
        UNDISCH_TAC `(z:real^N) IN t` THEN SET_TAC[]];
      STRIP_TAC THEN EXISTS_TAC `(G:real^N->real^N) y` THEN
      USE_THEN "Gs" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "Fs" (fun th -> ASM_SIMP_TAC[th])];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^N,&1)` THEN ASM_REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    USE_THEN "Gs" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN USE_THEN "Fs" (fun th -> ASM_SIMP_TAC[th]);
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      USE_THEN "Gs" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `(f:real^N->real^N) z` THEN
      SUBGOAL_THEN `(f:real^N->real^N) z = radial_ext f z` ASSUME_TAC THENL
       [USE_THEN "Fs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC(ASSUME `!y:real^N. y IN sphere(vec 0,&1)
                                       ==> (f:real^N->real^N) y IN sphere(vec 0,&1)`) THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `radial_ext (f:real^N->real^N) z IN u` MP_TAC THENL
         [UNDISCH_TAC `IMAGE (radial_ext (f:real^N->real^N)) t = u` THEN
          UNDISCH_TAC `(z:real^N) IN t` THEN SET_TAC[];
          ASM_REWRITE_TAC[]]]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET]]);;

let SMT_SPHERE_COVERING = prove
 (`SMT_SPHERE_COVERING_STATEMENT`,
  REWRITE_TAC[SMT_SPHERE_COVERING_STATEMENT] THEN X_GEN_TAC `f:real^3->real^3` THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SMT_RADIAL_DET_NONZERO th) THEN
    MP_TAC(MATCH_MP SMT_SPHERE_LOCAL_HOMEO th) THEN
    ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT1(CONJUNCT2 th))) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^3->real^3) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `smooth_near (sphere(vec 0,&1)) (f:real^3->real^3)` THEN
    REWRITE_TAC[smooth_near] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`;
                 `subtopology euclidean (sphere(vec 0:real^3,&1))`;
                 `f:real^3->real^3`]
    COMPACT_LOCAL_HOMEOMORPHISM_SIMPLY_CONNECTED_BIJECTIVE) THEN
  ASM_REWRITE_TAC[COMPACT_SPACE_EUCLIDEAN_SUBTOPOLOGY; COMPACT_SPHERE;
                  PATH_CONNECTED_SPACE_EUCLIDEAN_SUBTOPOLOGY;
                  SIMPLY_CONNECTED_SPACE_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  CONTINUOUS_MAP_EUCLIDEAN2] THEN
  ANTS_TAC THENL
   [SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN;
             PATH_CONNECTED_SPHERE; SIMPLY_CONNECTED_SPHERE; DIMINDEX_3; ARITH] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPHERE_EQ_EMPTY; REAL_ARITH `~(&1 < &0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj1") ASSUME_TAC) THEN
  ABBREV_TAC `g0 = \y:real^3. @x. x IN sphere(vec 0,&1) /\ (f:real^3->real^3) x = y` THEN
  SUBGOAL_THEN
   `!y:real^3. y IN sphere(vec 0,&1)
               ==> (g0:real^3->real^3) y IN sphere(vec 0,&1) /\
                   (f:real^3->real^3)(g0 y) = y`
  (LABEL_TAC "g0") THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "g0" THEN CONV_TAC SELECT_CONV THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (sphere(vec 0,&1)) = sphere(vec 0,&1)` THEN
    UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN sphere(vec 0,&1)
               ==> (f:real^3->real^3) x IN sphere(vec 0,&1) /\
                   (g0:real^3->real^3)(f x) = x`
  (LABEL_TAC "fg0") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "inj1" MATCH_MP_TAC THEN
    USE_THEN "g0" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  EXISTS_TAC `radial_ext (g0:real^3->real^3)` THEN
  REWRITE_TAC[sphere_diffeo] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[smooth_near] THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    REWRITE_TAC[OPEN_NONZERO] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMT_OPEN_INVERSE_SMOOTH THEN
    EXISTS_TAC `radial_ext (f:real^3->real^3)` THEN
    REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_RADIAL_EXT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`f:real^3->real^3`; `x:real^3`] SMT_RADIAL_EXT_NORM) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN
        ASM_REWRITE_TAC[NORM_EQ_0];
        MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN USE_THEN "fg0" (fun th -> SIMP_TAC[th])];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`g0:real^3->real^3`; `y:real^3`] SMT_RADIAL_EXT_NORM) THEN
        ANTS_TAC THENL [USE_THEN "g0" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN
        ASM_REWRITE_TAC[NORM_EQ_0];
        MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN USE_THEN "g0" (fun th -> SIMP_TAC[th])];
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SMT_RADIAL_EXT_SPHERE] THEN
    USE_THEN "fg0" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "g0" (fun th -> ASM_SIMP_TAC[th])]);;

