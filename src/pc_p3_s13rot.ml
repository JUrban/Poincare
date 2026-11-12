(* ========================================================================= *)
(* Unit pc_p3_s13rot (Part 3 proofs; also used by Part 2C): the             *)
(* standard initial metric g0 of MT Ch 12 (p3_std_initial) for EVERY g0,    *)
(* from its invariance under rotations: the radial form of g0 with the      *)
(* radial and tangential coefficients a(r), b(r); the distance from the tip *)
(* d(x) = rho(|x|) with rho the integral of sqrt(a), its inverse and its    *)
(* smoothness away from 0; the warped form g0 = dd^2 + f(d)^2 g_S2 with the *)
(* warping function f; the sectional curvature in terms of f, f' and f''    *)
(* (K_tan = (1 - f'^2)/f^2 on tangential planes, K_rad = -f''/f on radial   *)
(* planes); the one-variable facts on f (0 < f <= sqrt 2, 0 <= f' <= 1,     *)
(* f'' <= 0, f = sqrt 2 beyond A0, f -> 0 and f' -> 1 at the tip); and MT   *)
(* Lemma 12.37 for every such g0.                                           *)
(* ========================================================================= *)

needs "src/pc_p2c_stdinit.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The exported definitions (also used by Part 2C).  a(r) and               *)
(* b(r) are the radial and tangential coefficients of g0 along the ray      *)
(* r e1; rho(r) is the distance from the tip along it (the integral of      *)
(* sqrt(a) over [0,r]) and rinv its inverse; f = p3s_warp g0 is the warping *)
(* function f(s) = R sqrt(b(R)) with R = rinv(s); p3s_sec_rad and           *)
(* p3s_sec_tan are -f''/f and (1 - f'^2)/f^2.                               *)
(* ========================================================================= *)

let p3s_rad_a = new_definition
 `p3s_rad_a (g0:real^3->real^3^3) (r:real) =
    basis 1 dot (g0 (r % basis 1) ** basis 1)`;;

let p3s_rad_b = new_definition
 `p3s_rad_b (g0:real^3->real^3^3) (r:real) =
    basis 2 dot (g0 (r % basis 1) ** basis 2)`;;

let p3s_rad_rho = new_definition
 `p3s_rad_rho (g0:real^3->real^3^3) (r:real) =
    real_integral (real_interval[&0,r]) (\u. sqrt(p3s_rad_a g0 u))`;;

let p3s_rad_rinv = new_definition
 `p3s_rad_rinv (g0:real^3->real^3^3) (s:real) =
    @r. &0 <= r /\ p3s_rad_rho g0 r = s`;;

let p3s_warp = new_definition
 `p3s_warp (g0:real^3->real^3^3) (s:real) =
    p3s_rad_rinv g0 s * sqrt(p3s_rad_b g0 (p3s_rad_rinv g0 s))`;;

let p3s_sec_rad = new_definition
 `p3s_sec_rad (g0:real^3->real^3^3) (s:real) =
    --(higher_real_derivative 2 (p3s_warp g0) s) / p3s_warp g0 s`;;

let p3s_sec_tan = new_definition
 `p3s_sec_tan (g0:real^3->real^3^3) (s:real) =
    (&1 - real_derivative (p3s_warp g0) s pow 2) / p3s_warp g0 s pow 2`;;

(* ========================================================================= *)
(* The radial form of g0.  g0 is a metric field on real^3, and              *)
(* its invariance under the rotations diag(1,-1,-1) and the quarter turn    *)
(* about e1 makes g0(r e1) diagonal with equal (2,2) and (3,3) entries; a   *)
(* rotation taking e1 to x/|x| then gives, for x <> 0,                       *)
(*   w . g0(x) v = a (w.x)(v.x)/|x|^2 + b (w.v - (w.x)(v.x)/|x|^2)           *)
(* with a = a(|x|), b = b(|x|); the quarter turn e1 to e2 gives a(0) = b(0)  *)
(* and g0(0) = a(0) I.                                                       *)
(* ========================================================================= *)

let P3S_STD_METRIC_FIELD = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> metric_field (:real^3) g0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_std_initial; riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `((:real^3),(\x:real^3. x))` o CONJUNCT1) THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; IMAGE_ID;
              P2C_OPEN_SET_METRIC_LOCAL_UNIV]);;

let P3S_STD_SYM = prove
 (`!g0 A0 x. p3_std_initial g0 A0
             ==> (g0 x:real^3^3)$2$1 = g0 x$1$2 /\ (g0 x:real^3^3)$3$1 = g0 x$1$3 /\
                 (g0 x:real^3^3)$3$2 = g0 x$2$3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  REWRITE_TAC[metric_field; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `x:real^3` o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\A:real^3^3. A$1$2, A$1$3, A$2$3`) THEN
  SIMP_TAC[transp; LAMBDA_BETA; DIMINDEX_3; ARITH; PAIR_EQ]);;

let P3S_STD_POS = prove
 (`!g0 A0 x v. p3_std_initial g0 A0 /\ ~(v = vec 0) ==> &0 < v dot (g0 x ** v)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  REWRITE_TAC[metric_field; IN_UNIV] THEN ASM_MESON_TAC[]);;

let P3S_ROT_FIX = prove
 (`!g0 A0 Q x. p3_std_initial g0 A0 /\ orthogonal_matrix Q /\ det Q = &1 /\
               Q ** x = x
               ==> transp Q ** g0 x ** Q = g0 x`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
  DISCH_THEN(MP_TAC o SPECL [`Q:real^3^3`; `x:real^3`] o CONJUNCT1 o CONJUNCT2 o
             CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

let P3S_ROTS = prove
 (`(?Q:real^3^3. orthogonal_matrix Q /\ det Q = &1 /\
                 (!r. Q ** (r % basis 1) = r % basis 1) /\
                 (!M:real^3^3. transp Q ** M ** Q = M ==> M$1$2 = &0 /\ M$1$3 = &0)) /\
   (?Q:real^3^3. orthogonal_matrix Q /\ det Q = &1 /\
                 (!r. Q ** (r % basis 1) = r % basis 1) /\
                 (!M:real^3^3. transp Q ** M ** Q = M
                               ==> M$3$3 = M$2$2 /\ M$2$3 = --(M$3$2))) /\
   (?Q:real^3^3. orthogonal_matrix Q /\ det Q = &1 /\ Q ** vec 0 = vec 0 /\
                 (!M:real^3^3. transp Q ** M ** Q = M ==> M$2$2 = M$1$1))`,
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `vector [vector [&1; &0; &0]; vector [&0; -- &1; &0];
                        vector [&0; &0; -- &1]]:real^3^3`;
    EXISTS_TAC `vector [vector [&1; &0; &0]; vector [&0; &0; -- &1];
                        vector [&0; &1; &0]]:real^3^3`;
    EXISTS_TAC `vector [vector [&0; -- &1; &0]; vector [&1; &0; &0];
                        vector [&0; &0; &1]]:real^3^3`] THEN
  REWRITE_TAC[orthogonal_matrix; DET_3; VECTOR_3; MATRIX_VECTOR_MUL_RZERO] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; transp; matrix_mul; matrix_vector_mul;
           mat; LAMBDA_BETA; SUM_3; VECTOR_3; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; ARITH] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_ROT_DIAG = prove
 (`!g0 A0 r. p3_std_initial g0 A0
             ==> (g0 (r % basis 1):real^3^3)$1$2 = &0 /\ g0 (r % basis 1)$1$3 = &0 /\
                 g0 (r % basis 1)$2$1 = &0 /\ g0 (r % basis 1)$3$1 = &0 /\
                 g0 (r % basis 1)$2$3 = &0 /\ g0 (r % basis 1)$3$2 = &0 /\
                 g0 (r % basis 1)$3$3 = g0 (r % basis 1)$2$2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r % basis 1:real^3`] P3S_STD_SYM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC P3S_ROTS THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `Q1:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M1")))))
    (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `Q2:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M2"))))) (K ALL_TAC))) THEN
  USE_THEN "M1" (MP_TAC o SPEC `(g0:real^3->real^3^3) (r % basis 1)`) THEN
  USE_THEN "M2" (MP_TAC o SPEC `(g0:real^3->real^3^3) (r % basis 1)`) THEN
  SUBGOAL_THEN `transp Q1 ** (g0:real^3->real^3^3) (r % basis 1) ** Q1 =
                g0 (r % basis 1) /\
                transp Q2 ** (g0:real^3->real^3^3) (r % basis 1) ** Q2 =
                g0 (r % basis 1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P3S_ROT_FIX THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let P3S_ROT_TIP0 = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> (g0 (vec 0):real^3^3)$2$2 = g0 (vec 0)$1$1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC P3S_ROTS THEN
  DISCH_THEN(X_CHOOSE_THEN `Q3:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M3")))) o
    CONJUNCT2 o CONJUNCT2) THEN
  USE_THEN "M3" MATCH_MP_TAC THEN MATCH_MP_TAC P3S_ROT_FIX THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_RAD_AB_ENTRY = prove
 (`!g0 r. p3s_rad_a g0 r = (g0 (r % basis 1):real^3^3)$1$1 /\
          p3s_rad_b g0 r = (g0 (r % basis 1):real^3^3)$2$2`,
  REWRITE_TAC[p3s_rad_a; p3s_rad_b] THEN
  SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3;
           BASIS_COMPONENT; DOT_3] THEN REAL_ARITH_TAC);;

let P3S_ROT_E1_BIL = prove
 (`!g0 A0 r (w:real^3) v.
     p3_std_initial g0 A0
     ==> w dot (g0 (r % basis 1) ** v) =
         p3s_rad_a g0 r * w$1 * v$1 + p3s_rad_b g0 r * (w dot v - w$1 * v$1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_ROT_DIAG) THEN
  ASM_REWRITE_TAC[P3S_RAD_AB_ENTRY] THEN STRIP_TAC THEN
  SIMP_TAC[DOT_3; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3S_ROT_BIL = prove
 (`!g0 A0 (x:real^3) w v.
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> w dot (g0 x ** v) =
         p3s_rad_a g0 (norm x) * (w dot x) * (v dot x) / norm x pow 2 +
         p3s_rad_b g0 (norm x) * (w dot v - (w dot x) * (v dot x) / norm x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis 1:real^3`; `inv(norm x) % x:real^3`] ROTATION_EXISTS_1) THEN
  ANTS_TAC THENL
   [SIMP_TAC[DIMINDEX_3; ARITH; NORM_BASIS; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q = matrix(f:real^3->real^3)` THEN
  SUBGOAL_THEN `linear(f:real^3->real^3) /\ orthogonal_matrix(Q:real^3^3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^3^3) ** basis 1 = inv(norm x) % x` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN ASM_SIMP_TAC[MATRIX_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^3^3) ** (norm(x:real^3) % basis 1) = x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp (Q:real^3^3) ** (g0:real^3->real^3^3) x ** Q = g0 (norm x % basis 1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
    DISCH_THEN(MP_TAC o SPECL [`Q:real^3^3`; `norm(x:real^3) % basis 1:real^3`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (Q:real^3^3) ** transp Q ** z = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_RMUL;
                 MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^3) dot ((g0:real^3->real^3^3) x ** v) =
    (transp (Q:real^3^3) ** w) dot (g0 (norm x % basis 1) ** (transp Q ** v))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `transp (Q:real^3^3) ** (g0:real^3->real^3^3) x ** Q = g0 (norm x % basis 1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`;
                 `transp (Q:real^3^3) ** (w:real^3)`;
                 `transp (Q:real^3^3) ** (v:real^3)`] P3S_ROT_E1_BIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!z:real^3. (transp (Q:real^3^3) ** z)$1 = inv(norm(x:real^3)) * (x dot z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `z:real^3` THEN
    SUBGOAL_THEN `(transp (Q:real^3^3) ** (z:real^3))$1 = basis 1 dot (transp Q ** z)`
    SUBST1_TAC THENL [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; DOT_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(transp (Q:real^3^3) ** (w:real^3)) dot (transp Q ** (v:real^3)) = w dot v`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN
  UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

let P3S_ROT_FORM = prove
 (`!g0 A0 (x:real^3) v.
  p3_std_initial g0 A0 /\ ~(x = vec 0)
  ==> v dot (g0 x ** v) =
      p3s_rad_a g0 (norm x) * (v dot x) pow 2 / norm x pow 2 +
      p3s_rad_b g0 (norm x) * (v dot v - (v dot x) pow 2 / norm x pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`; `v:real^3`]
         P3S_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

let P3S_ROT_TIP = prove
 (`!g0 A0 (w:real^3) v. p3_std_initial g0 A0
                        ==> w dot (g0 (vec 0) ** v) = p3s_rad_a g0 (&0) * (w dot v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`; `w:real^3`; `v:real^3`]
         P3S_ROT_E1_BIL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `p3s_rad_b g0 (&0) = p3s_rad_a g0 (&0)` SUBST1_TAC THENL
   [REWRITE_TAC[P3S_RAD_AB_ENTRY; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC P3S_ROT_TIP0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let P3S_ROT_AB = prove
 (`!g0 A0. p3_std_initial g0 A0
  ==> smooth_map_on (:real^1) (lift o p3s_rad_a g0 o drop) /\
      smooth_map_on (:real^1) (lift o p3s_rad_b g0 o drop) /\
      (!r. &0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r) /\
      p3s_rad_a g0 (&0) = p3s_rad_b g0 (&0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  SUBGOAL_THEN
   `!k. smooth_map_on (:real^1)
          (\t. lift(basis k dot ((g0:real^3->real^3^3) (drop t % basis 1) ** basis k)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\t. lift(basis k dot ((g0:real^3->real^3^3) (drop t % basis 1) ** basis k))) =
      (\x. lift(basis k dot (g0 x ** basis k))) o (\t:real^1. drop t % basis 1)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV] THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC LRG_DOT_METRIC_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_rad_a];
    FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_rad_b];
    GEN_TAC THEN REWRITE_TAC[p3s_rad_a; p3s_rad_b] THEN CONJ_TAC THEN
    MATCH_MP_TAC P3S_STD_POS THEN EXISTS_TAC `A0:real` THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
    REWRITE_TAC[P3S_RAD_AB_ENTRY; VECTOR_MUL_LZERO] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P3S_ROT_TIP0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The distance from the tip.  rho(r), the integral of                      *)
(* sqrt(a) over [0,r], is continuous and strictly increasing on [0,inf)     *)
(* with derivative sqrt(a(r)) for r > 0; the radial segment t x has length  *)
(* rho(|x|), and every C^1 curve from 0 to x has length >= rho(|x|) since   *)
(* its speed is at least sqrt(a(|c|)) (c.c')/|c| (the radial part of the    *)
(* form); hence d(x) = rho(|x|).  Completeness (closed balls are compact)   *)
(* makes rho unbounded, so rinv is a two-sided inverse on [0,inf).          *)
(* ========================================================================= *)

let P3S_STD_POS_LE = prove
 (`!g0 A0 x v. p3_std_initial g0 A0 ==> &0 <= v dot (g0 x ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P3S_STD_POS THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_SQRTA_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on (:real^1) (lift o (\u. sqrt(p3s_rad_a g0 u)) o drop)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o p3s_rad_a g0 o drop`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; o_THM; LIFT_DROP] THEN
  REWRITE_TAC[o_DEF]);;

let P3S_RHO_ALT = prove
 (`!g0. p3s_rad_rho g0 =
        (\r. real_integral (real_interval[&0,r]) (\u. sqrt(p3s_rad_a g0 u)))`,
  REWRITE_TAC[FUN_EQ_THM; p3s_rad_rho]);;

let P3S_RHO_DERIV_WITHIN = prove
 (`!g0 A0 R r. p3_std_initial g0 A0 /\ r IN real_interval[&0,R]
               ==> (p3s_rad_rho g0 has_real_derivative sqrt(p3s_rad_a g0 r))
                   (atreal r within real_interval[&0,R])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P3S_RHO_ALT] THEN
  MP_TAC(ISPECL [`\u. sqrt(p3s_rad_a g0 u)`; `&0`; `R:real`]
         REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC P2C_S1_CONTINUOUS THEN MATCH_MP_TAC P3S_SQRTA_SMOOTH THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[]]);;

let P3S_RHO_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> (p3s_rad_rho g0 has_real_derivative sqrt(p3s_rad_a g0 r)) (atreal r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P3S_RHO_ALT] THEN
  MP_TAC(ISPECL [`\u. sqrt(p3s_rad_a g0 u)`; `&0`; `r:real`] P2C_INTEGRAL_DERIV_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2C_S1_CONTINUOUS THEN MATCH_MP_TAC P3S_SQRTA_SMOOTH THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_RHO_0 = prove
 (`!g0. p3s_rad_rho g0 (&0) = &0`,
  REWRITE_TAC[p3s_rad_rho; REAL_INTEGRAL_REFL]);;

let P3S_RHO_CONT = prove
 (`!g0 A0 R. p3_std_initial g0 A0
             ==> p3s_rad_rho g0 real_continuous_on real_interval[&0,R]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[real_differentiable_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `sqrt(p3s_rad_a g0 x)` THEN
  MATCH_MP_TAC P3S_RHO_DERIV_WITHIN THEN EXISTS_TAC `A0:real` THEN
  ASM_REWRITE_TAC[]);;

let P3S_RHO_STRICT = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ &0 <= r1 /\ r1 < r2
                 ==> p3s_rad_rho g0 r1 < p3s_rad_rho g0 r2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `\r. sqrt(p3s_rad_a g0 r)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[&0,r2]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RHO_DERIV_WITHIN THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN ASM_REWRITE_TAC[]]);;

let P3S_RHO_POS_LE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 <= r ==> &0 <= p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THEN
  ASM_REWRITE_TAC[P3S_RHO_0; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `g0:real^3->real^3^3` P3S_RHO_0)] THEN
  MATCH_MP_TAC P3S_RHO_STRICT THEN EXISTS_TAC `A0:real` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC);;

let P3S_RHO_LT_EQ = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ &0 <= r1 /\ &0 <= r2
                 ==> (p3s_rad_rho g0 r1 < p3s_rad_rho g0 r2 <=> r1 < r2) /\
                     (p3s_rad_rho g0 r1 <= p3s_rad_rho g0 r2 <=> r1 <= r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ s < t ==> p3s_rad_rho g0 s < p3s_rad_rho g0 t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_RHO_STRICT THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_NOT_LT; REAL_LT_REFL; REAL_LE_LT]);;

let P3S_RAD_SPEED_GE = prove
 (`!g0 A0 (c:real->real^3) t.
     p3_std_initial g0 A0 /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
     t IN real_interval[&0,&1]
     ==> sqrt(p3s_rad_a g0 (norm(c t))) *
         ((c t dot vector_derivative (\r. c(drop r))
                     (at (lift t) within interval[lift(&0),lift(&1)])) / norm(c t)) <=
         mfd_speed (open_set_atlas (:real^3)) g0 c (&0) (&1) t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`; `c:real->real^3`; `&0`; `&1`;
                 `t:real`] GRGD_OPEN_SET_SPEED) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `v = vector_derivative (\r. (c:real->real^3)(drop r))
                    (at (lift t) within interval[lift(&0),lift(&1)])` THEN
  ABBREV_TAC `x = (c:real->real^3) t` THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC P3S_STD_POS_LE THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`]
         P3S_ROT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  ABBREV_TAC `aa = p3s_rad_a g0 (norm(x:real^3))` THEN
  ABBREV_TAC `bb = p3s_rad_b g0 (norm(x:real^3))` THEN
  SUBGOAL_THEN `&0 < aa /\ &0 < bb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `((v:real^3) dot x) pow 2 <= (v dot v) * norm(x:real^3) pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= bb * ((v:real^3) dot v - (v dot x) pow 2 / norm(x:real^3) pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `sqrt((sqrt aa * ((x dot v) / norm(x:real^3))) pow 2)` THEN
  CONJ_TAC THENL [REWRITE_TAC[POW_2_SQRT_ABS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 <= bb * ((v:real^3) dot v - (v dot x) pow 2 / norm(x:real^3) pow 2)` THEN
  REWRITE_TAC[DOT_SYM; REAL_POW_DIV] THEN REAL_ARITH_TAC);;

let P3S_RHO_NORM_CURVE_DERIV = prove
 (`!g0 A0 (c:real->real^3) t.
     p3_std_initial g0 A0 /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
     &0 < t /\ t < &1 /\ ~(c t = vec 0)
     ==> ((\t. p3s_rad_rho g0 (norm(c t))) has_real_derivative
          (sqrt(p3s_rad_a g0 (norm(c t))) *
           ((c t dot vector_derivative (\r. c(drop r))
                       (at (lift t) within interval[lift(&0),lift(&1)])) /
            norm(c t)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = vector_derivative (\r. (c:real->real^3)(drop r))
                    (at (lift t) within interval[lift(&0),lift(&1)])` THEN
  SUBGOAL_THEN `((\r. (c:real->real^3)(drop r)) has_vector_derivative v) (at (lift t))`
  ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC P2C_CURVE_VD_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (c:real->real^3) t dot c t) has_real_derivative (&2 * (c t dot v)))
    (atreal t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(ISPECL [`\x y:real^3. lift(x dot y)`; `\r. (c:real->real^3)(drop r)`;
                   `\r. (c:real->real^3)(drop r)`; `v:real^3`; `v:real^3`;
                   `lift t`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN REWRITE_TAC[DOT_SYM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c:real->real^3) t dot c t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. sqrt((c:real->real^3) t dot c t)) has_real_derivative
     (inv(&2 * sqrt(c t dot c t)) * (&2 * (c t dot v)))) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. (c:real->real^3) t dot c t`; `sqrt`;
                   `&2 * ((c:real->real^3) t dot v)`;
                   `inv(&2 * sqrt((c:real->real^3) t dot c t))`; `t:real`]
           REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((c:real->real^3) t dot c t)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sqrt((c:real->real^3) t dot c t)`; `p3s_rad_rho g0`;
                 `inv(&2 * sqrt((c:real->real^3) t dot c t)) * (&2 * (c t dot v))`;
                 `sqrt(p3s_rad_a g0 (sqrt((c:real->real^3) t dot c t)))`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_RHO_DERIV THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; GSYM vector_norm] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(norm((c:real->real^3) t) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

let P3S_RHO_NORM_CURVE_CONT = prove
 (`!g0 A0 (c:real->real^3) a b.
     p3_std_initial g0 A0 /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\
     &0 <= a /\ b <= &1
     ==> (\t. p3s_rad_rho g0 (norm(c t))) real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2C_CURVE_NORM_CONT) THEN
  SUBGOAL_THEN `~(real_interval[&0,&1] = {})` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. norm((c:real->real^3) t)`; `real_interval[&0,&1]`]
         REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\t. p3s_rad_rho g0 (norm((c:real->real^3) t))) =
    p3s_rad_rho g0 o (\t. norm(c t))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[&0,norm((c:real->real^3) t1)]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RHO_CONT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; NORM_POS_LE] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let P3S_RAD_LOWER = prove
 (`!g0 A0 (c:real->real^3).
     p3_std_initial g0 A0 /\
     mfd_c1_curve (euclidean,open_set_atlas (:real^3)) c (&0) (&1) /\ c(&0) = vec 0
     ==> p3s_rad_rho g0 (norm(c(&1))) <=
         mfd_length (open_set_atlas (:real^3)) g0 c (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) g0` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  ASM_CASES_TAC `(c:real->real^3)(&1) = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; P3S_RHO_0] THEN MATCH_MP_TAC MFD_LENGTH_POS_LE THEN
    EXISTS_TAC `euclidean:(real^3)topology` THEN ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:real->real^3` P2C_C1_LAST_ZERO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `v = \t. vector_derivative (\r. (c:real->real^3)(drop r))
              (at (lift t) within interval[lift(&0),lift(&1)])` THEN
  SUBGOAL_THEN
   `((\t. sqrt(p3s_rad_a g0 (norm((c:real->real^3) t))) * ((c t dot v t) / norm(c t)))
     has_real_integral
     (p3s_rad_rho g0 (norm(c(&1))) - p3s_rad_rho g0 (norm(c t0))))
    (real_interval[t0,&1])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. p3s_rad_rho g0 (norm((c:real->real^3) t))`;
                   `\t. sqrt(p3s_rad_a g0 (norm((c:real->real^3) t))) *
                        ((c t dot v t) / norm(c t))`;
                   `t0:real`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `t0 < &1` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_RHO_NORM_CURVE_CONT THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "v" THEN BETA_TAC THEN
      MATCH_MP_TAC P3S_RHO_NORM_CURVE_DERIV THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `&0 <= t0` THEN UNDISCH_TAC `t0 < t` THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `t0 < t` THEN UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(c:real->real^3) t0 = vec 0`; NORM_0;
                              P3S_RHO_0; REAL_SUB_RZERO]) THEN
  SUBGOAL_THEN
   `(mfd_speed (open_set_atlas (:real^3)) g0 c (&0) (&1))
    real_integrable_on real_interval[&0,&1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
    ASM_REWRITE_TAC[P2C_EUCLID_FACTS];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_integral (real_interval[t0,&1])
      (mfd_speed (open_set_atlas (:real^3)) g0 c (&0) (&1))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `&0 <= t0` THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "v" THEN BETA_TAC THEN
      MATCH_MP_TAC P3S_RAD_SPEED_GE THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `&0 <= t0` THEN UNDISCH_TAC `t0 <= t` THEN
      UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN UNDISCH_TAC `&0 <= t0` THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `&0 <= t0` THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC MFD_SPEED_POS_LE THEN
      EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS]]]);;

let P3S_SEG_FORM = prove
 (`!g0 A0 (x:real^3) t.
     p3_std_initial g0 A0 /\ &0 <= t
     ==> x dot (g0 (t % x) ** x) = p3s_rad_a g0 (t * norm x) * norm x pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_MUL_LZERO] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `x:real^3`]
           P3S_ROT_TIP) THEN
    ASM_REWRITE_TAC[NORM_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `t % x:real^3`; `x:real^3`]
         P3S_ROT_FORM) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_MUL; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD);;

let P3S_RAD_SEGMENT = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0
     ==> mfd_length (open_set_atlas (:real^3)) g0 (\t. t % x) (&0) (&1) =
         p3s_rad_rho g0 (norm x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `g0:real^3->real^3^3`;
                 `\t:real. t % (x:real^3)`; `&0`; `&1`] MFD_LENGTH_OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; P2C_SEGMENT_C1] THEN
  DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[&0,&1])
      (\t. sqrt(p3s_rad_a g0 (t * norm(x:real^3))) * norm x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[P2C_SEGMENT_VD] THEN
    SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `t:real`]
           P3S_SEG_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_INTEGRAL_0; P3S_RHO_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. p3s_rad_rho g0 (t * norm(x:real^3))`;
                 `\t. sqrt(p3s_rad_a g0 (t * norm(x:real^3))) * norm x`;
                 `&0`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. t * norm(x:real^3)`; `p3s_rad_rho g0`; `norm(x:real^3)`;
                   `sqrt(p3s_rad_a g0 (t * norm(x:real^3)))`; `t:real`;
                   `real_interval[&0,&1]`] REAL_DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `norm(x:real^3)`; `t:real`;
                     `real_interval[&0,&1]`] HAS_REAL_DERIVATIVE_RMUL_WITHIN) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_LID];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&0,norm(x:real^3)]` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P3S_RHO_DERIV_WITHIN THEN EXISTS_TAC `A0:real` THEN
        ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]];
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; P3S_RHO_0; REAL_SUB_RZERO]]);;

let P3S_ROT_DIST = prove
 (`!g0 A0 (x:real^3).
  p3_std_initial g0 A0 ==> p3_std_dist g0 x = p3s_rad_rho g0 (norm x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_std_dist; mfd_dist] THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN CONJ_TAC THENL
   [X_GEN_TAC `L:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x:real^3 = gamma(&1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P3S_RAD_LOWER THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    EXISTS_TAC `p3s_rad_rho g0 (norm(x:real^3))` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\t. t % (x:real^3)` THEN
    REWRITE_TAC[P2C_SEGMENT_C1; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3S_RAD_SEGMENT THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_RHO_UNBOUNDED = prove
 (`!g0 A0 M. p3_std_initial g0 A0 ==> ?r. &0 <= r /\ M < p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN
   `compact_in euclidean
      (mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) M)`
  MP_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial; mfd_complete] THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^3`; `M:real`] o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) M = (:real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM; IN_UNIV; P2C_RAD_JOINABLE] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[GSYM p3_std_dist] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `y:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `norm(y:real^3)`) THEN
    REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[NOT_BOUNDED_UNIV]]);;

let P3S_RINV = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 <= s
             ==> &0 <= p3s_rad_rinv g0 s /\ p3s_rad_rho g0 (p3s_rad_rinv g0 s) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3s_rad_rinv] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RHO_UNBOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p3s_rad_rho g0`; `&0`; `B:real`; `s:real`] REAL_IVT_INCREASING) THEN
  ASM_REWRITE_TAC[P3S_RHO_0; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RHO_CONT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    MESON_TAC[]]);;

let P3S_RINV_UNIQUE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 <= r
             ==> p3s_rad_rinv g0 (p3s_rad_rho g0 r) = r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rho g0 r`] P3S_RINV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_RHO_POS_LE THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 (p3s_rad_rho g0 r)`;
                `r:real`] P3S_RHO_LT_EQ) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`;
                `p3s_rad_rinv g0 (p3s_rad_rho g0 r)`] P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC);;

let P3S_RINV_POS = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s ==> &0 < p3s_rad_rinv g0 s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `p3s_rad_rho g0 (p3s_rad_rinv g0 s) = s` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[P3S_RHO_0] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_RHO_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {s | &0 < drop s} (lift o p3s_rad_rho g0 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_REAL_DERIVATIVE_1D THEN
  EXISTS_TAC `\u. sqrt(p3s_rad_a g0 u)` THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC P3S_RHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2C_S1_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3S_SQRTA_SMOOTH THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_ROT_RHO = prove
 (`!g0 A0. p3_std_initial g0 A0
  ==> p3s_rad_rho g0 (&0) = &0 /\
      (!r. &0 < r ==> (p3s_rad_rho g0 has_real_derivative sqrt(p3s_rad_a g0 r)) (atreal r)) /\
      (!r1 r2. &0 <= r1 /\ r1 < r2 ==> p3s_rad_rho g0 r1 < p3s_rad_rho g0 r2) /\
      (!s. &0 <= s ==> &0 <= p3s_rad_rinv g0 s /\ p3s_rad_rho g0 (p3s_rad_rinv g0 s) = s) /\
      (!r. &0 <= r ==> p3s_rad_rinv g0 (p3s_rad_rho g0 r) = r) /\
      smooth_map_on {s | &0 < drop s} (lift o p3s_rad_rho g0 o drop)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[P3S_RHO_0] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_RHO_DERIV THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_RHO_STRICT THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P3S_RINV THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_RINV_UNIQUE THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_RHO_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* d(x) = rho(|x|) is smooth away from the tip with derivative              *)
(* v -> sqrt(a(|x|)) (v.x)/|x| (so |grad d| = 1), and the warped form        *)
(*   v.g0(x)v = (Dd(x) v)^2 + f(d(x))^2 (|v|^2 - (v.x)^2/|x|^2)/|x|^2        *)
(* with f(rho(r)) = r sqrt(b(r)).                                            *)
(* ========================================================================= *)

let P3S_DIST_ALT = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> p3_std_dist g0 = (\x. p3s_rad_rho g0 (norm x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC P3S_ROT_DIST THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_OPEN_PUNCT = prove
 (`open((:real^3) DELETE vec 0)`,
  MATCH_MP_TAC OPEN_DELETE THEN REWRITE_TAC[OPEN_UNIV]);;

let P3S_DIST_HAS_DERIV = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ ~(x = vec 0)
     ==> ((\z. lift(p3_std_dist g0 z)) has_derivative
          (\v. lift(sqrt(p3s_rad_a g0 (norm x)) * (v dot x) / norm x))) (at x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP P3S_DIST_ALT) THEN BETA_TAC THEN
  MP_TAC(ISPECL [`p3s_rad_rho g0`; `sqrt(p3s_rad_a g0 (norm(x:real^3)))`;
                 `\z:real^3. lift(norm z)`; `\h:real^3. lift((x dot h) / norm x)`;
                 `x:real^3`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; P2C_NORM_DERIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC P3S_RHO_DERIV THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[NORM_POS_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ; DOT_SYM] THEN REAL_ARITH_TAC);;

let P3S_ROT_DIST_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
  ==> smooth_map_on ((:real^3) DELETE vec 0) (\x. lift(p3_std_dist g0 x)) /\
      (!x. ~(x = vec 0)
           ==> (frechet_derivative (\z. lift(p3_std_dist g0 z)) (at x) =
                (\v. lift(sqrt(p3s_rad_a g0 (norm x)) * (v dot x) / norm x))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP P3S_DIST_ALT) THEN BETA_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `{s:real^1 | &0 < drop s}`;
                   `\x:real^3. lift(norm x)`; `p3s_rad_rho g0`]
           SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
    REWRITE_TAC[P3S_OPEN_PUNCT; P2C_OPEN_DROP_GT; IN_ELIM_THM; IN_DELETE; IN_UNIV;
                LIFT_DROP; NORM_POS_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\x:real^3. x`] SMOOTH_MAP_ON_LIFT_NORM) THEN
      REWRITE_TAC[P3S_OPEN_PUNCT; SMOOTH_MAP_ON_ID; IN_DELETE; IN_UNIV] THEN
      REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC P3S_RHO_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC P3S_DIST_HAS_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_WARP_RHO = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 <= r
             ==> p3s_warp g0 (p3s_rad_rho g0 r) = r * sqrt(p3s_rad_b g0 r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_warp] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RINV_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let P3S_ROT_WARPED = prove
 (`!g0 A0 (x:real^3) v.
  p3_std_initial g0 A0 /\ ~(x = vec 0)
  ==> v dot (g0 x ** v) =
      drop(frechet_derivative (\z. lift(p3_std_dist g0 z)) (at x) v) pow 2 +
      p3s_warp g0 (p3_std_dist g0 x) pow 2 *
      (v dot v - (v dot x) pow 2 / norm x pow 2) / norm x pow 2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_DIST_SMOOTH) THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_WARP_RHO) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`]
         P3S_ROT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `sqrt(p3s_rad_a g0 (norm(x:real^3))) pow 2 = p3s_rad_a g0 (norm x) /\
                sqrt(p3s_rad_b g0 (norm(x:real^3))) pow 2 = p3s_rad_b g0 (norm x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Curvature of metrics of the form G = B delta + C y y^T at                *)
(* a point y (any dimension).  If w.G(y)v = B (w.v) + C (y.w)(y.v) and the  *)
(* derivative of the metric is w.(D_h G)v = pB (y.h)(w.v) + pC (y.h)(y.w)    *)
(* (y.v) + C ((h.w)(y.v) + (y.w)(h.v)), the Christoffel symbols are          *)
(*   Gamma(a,b) = m1 ((y.a) b + (y.b) a) + (m2 (a.b) + m3 (y.a)(y.b)) y      *)
(* with m1 = pB/(2B), m2 = (C - pB/2)/(B + C|y|^2), m3 = (pC/2 - pB C/B)/    *)
(* (B + C|y|^2).  For Christoffel symbols of this form near y with radial    *)
(* derivatives D m_i(h) = p_i (y.h) the curvature tensor is                  *)
(*   R(a,v)w = c1 ((a.w) v - (v.w) a) + c2 ((y.a)(y.w) v - (y.v)(y.w) a)     *)
(*             + c3 ((y.v)(a.w) - (y.a)(v.w)) y                              *)
(* with c1 = m1 - m2 - m1 m2 |y|^2, c2 = p1 - m1^2 - m3 - m1 m3 |y|^2 and    *)
(* c3 = m3 - m2^2 - p2 - m2 m3 |y|^2; if moreover c2 B = c3 (B + C |y|^2) +  *)
(* c1 C (true for the metrics of the form above), the sectional curvature    *)
(* is [K_tan T + K_rad (Gram - T)]/Gram with K_tan = -c1/B, K_rad =          *)
(* -(c1 + c3 |y|^2)/B and T = B^2 times the Euclidean Gram determinant of    *)
(* the projections of u, v orthogonal to y.                                  *)
(* ========================================================================= *)

let P3S_RS_CHRISTOFFEL = prove
 (`!(G:real^N->real^N^N) U y B C pB pC a b.
     metric_field U G /\ y IN U /\
     (!w v. w dot (G y ** v) = B * (w dot v) + C * (y dot w) * (y dot v)) /\
     (!h w v. w dot (mderiv G y h ** v) =
              pB * (y dot h) * (w dot v) + pC * (y dot h) * (y dot w) * (y dot v) +
              C * ((h dot w) * (y dot v) + (y dot w) * (h dot v))) /\
     &0 < B /\ &0 < B + C * (y dot y)
     ==> christoffel G y a b =
         (pB / (&2 * B)) % ((y dot a) % b + (y dot b) % a) +
         (((C - pB / &2) / (B + C * (y dot y))) * (a dot b) +
          ((pC / &2 - pB * C / B) / (B + C * (y dot y))) * (y dot a) * (y dot b)) % y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                  DOT_RADD; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN
  SUBGOAL_THEN `~(B = &0) /\ ~(B + C * ((y:real^N) dot y) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let P3S_LINEAR_LIFT_DOT_R = prove
 (`!a:real^N. linear (\x. lift(x dot a))`,
  REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL]);;

let P3S_HAS_DERIV_QUAD = prove
 (`!(m:real^N->real) p y a b.
     ((\z. lift(m z)) has_derivative (\h. lift(p * (y dot h)))) (at y)
     ==> ((\z. lift(m z * (z dot a) * (z dot b))) has_derivative
          (\h. lift(p * (y dot h) * (y dot a) * (y dot b) +
                    m y * ((h dot a) * (y dot b) + (y dot a) * (h dot b))))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. lift(((z:real^N) dot a) * (z dot b))) has_derivative
     (\h. lift((y dot a) * (h dot b) + (h dot a) * (y dot b)))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^N. z dot a`; `\h:real^N. h dot a`;
                   `\z:real^N. z dot b`; `\h:real^N. h dot b`; `y:real^N`]
                  LRG_HAS_DERIVATIVE_LIFT_MUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[P3S_LINEAR_LIFT_DOT_R];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->real`; `\h:real^N. p * (y dot h)`;
                 `\z:real^N. (z dot a) * (z dot b)`;
                 `\h:real^N. (y dot a) * (h dot b) + (h dot a) * (y dot b)`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_LIFT_MUL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN REAL_ARITH_TAC);;

let P3S_RAD3_DCHRISTOFFEL = prove
 (`!(G:real^N->real^N^N) S m1 m2 m3 p1 p2 p3 y a b u.
     open S /\ y IN S /\
     (!z a b. z IN S
              ==> christoffel G z a b =
                  m1 z % ((z dot a) % b + (z dot b) % a) +
                  (m2 z * (a dot b) + m3 z * (z dot a) * (z dot b)) % z) /\
     ((\z. lift(m1 z)) has_derivative (\h. lift(p1 * (y dot h)))) (at y) /\
     ((\z. lift(m2 z)) has_derivative (\h. lift(p2 * (y dot h)))) (at y) /\
     ((\z. lift(m3 z)) has_derivative (\h. lift(p3 * (y dot h)))) (at y)
     ==> frechet_derivative (\z. christoffel G z a b) (at y) u =
         m1 y % ((u dot a) % b + (u dot b) % a) +
         (p1 * (y dot u)) % ((y dot a) % b + (y dot b) % a) +
         (m2 y * (a dot b) + m3 y * (y dot a) * (y dot b)) % u +
         (p2 * (y dot u) * (a dot b) +
          p3 * (y dot u) * (y dot a) * (y dot b) +
          m3 y * ((u dot a) * (y dot b) + (y dot a) * (u dot b))) % y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. christoffel (G:real^N->real^N^N) z a b) (at y) =
    frechet_derivative
      (\z. (m1:real^N->real) z % ((z dot a) % b + (z dot b) % a) +
           ((m2:real^N->real) z * (a dot b) +
            (m3:real^N->real) z * (z dot a) * (z dot b)) % z)
      (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift((m2:real^N->real) z * (a dot b) +
               (m3:real^N->real) z * (z dot a) * (z dot b)))
     has_derivative
     (\h. lift(p2 * (y dot h) * (a dot b) +
               p3 * (y dot h) * (y dot a) * (y dot b) +
               m3 y * ((h dot a) * (y dot b) + (y dot a) * (h dot b))))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m3:real^N->real`; `p3:real`; `y:real^N`; `a:real^N`; `b:real^N`]
           P3S_HAS_DERIV_QUAD) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(BETA_RULE(ISPEC `(a:real^N) dot b` (MATCH_MP HAS_DERIVATIVE_CMUL
      (ASSUME `((\z. lift((m2:real^N->real) z)) has_derivative
                (\h. lift(p2 * (y dot h)))) (at y)`)))) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\z:real^N. (z dot a) % b + (z dot b) % a)` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LRG_LINEAR_DOT_SCALE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m1:real^N->real`; `\h:real^N. p1 * (y dot h)`;
                 `\z:real^N. (z dot a) % b + (z dot b) % a`;
                 `\z:real^N. (z dot a) % b + (z dot b) % a`; `y:real^N`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ASM_SIMP_TAC[o_DEF; HAS_DERIVATIVE_LINEAR] THEN DISCH_THEN(LABEL_TAC "D1") THEN
  MP_TAC(ISPECL [`\z:real^N. (m2:real^N->real) z * (a dot b) +
                             (m3:real^N->real) z * (z dot a) * (z dot b)`;
                 `\h:real^N. p2 * (y dot h) * (a dot b) +
                             p3 * (y dot h) * (y dot a) * (y dot b) +
                             (m3:real^N->real) y *
                             ((h dot a) * (y dot b) + (y dot a) * (h dot b))`;
                 `\z:real^N. z`; `\h:real^N. h`; `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF; HAS_DERIVATIVE_ID] THEN DISCH_THEN(LABEL_TAC "D2") THEN
  USE_THEN "D1" (fun d1 -> USE_THEN "D2" (fun d2 ->
    MP_TAC(BETA_RULE(MATCH_MP HAS_DERIVATIVE_ADD (CONJ d1 d2))))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[VECTOR_ADD_ASSOC]);;

let P3S_RAD3_RIEMANN = prove
 (`!(G:real^N->real^N^N) S m1 m2 m3 p1 p2 p3 y a v w.
     open S /\ y IN S /\
     (!z a b. z IN S
              ==> christoffel G z a b =
                  m1 z % ((z dot a) % b + (z dot b) % a) +
                  (m2 z * (a dot b) + m3 z * (z dot a) * (z dot b)) % z) /\
     ((\z. lift(m1 z)) has_derivative (\h. lift(p1 * (y dot h)))) (at y) /\
     ((\z. lift(m2 z)) has_derivative (\h. lift(p2 * (y dot h)))) (at y) /\
     ((\z. lift(m3 z)) has_derivative (\h. lift(p3 * (y dot h)))) (at y)
     ==> lriemann G y a v w =
         (m1 y - m2 y - m1 y * m2 y * (y dot y)) % ((a dot w) % v - (v dot w) % a) +
         (p1 - m1 y pow 2 - m3 y - m1 y * m3 y * (y dot y)) %
           (((y dot a) * (y dot w)) % v - ((y dot v) * (y dot w)) % a) +
         (m3 y - m2 y pow 2 - p2 - m2 y * m3 y * (y dot y)) %
           (((y dot v) * (a dot w) - (y dot a) * (v dot w)) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `S:real^N->bool`; `m1:real^N->real`;
                 `m2:real^N->real`; `m3:real^N->real`; `p1:real`; `p2:real`; `p3:real`;
                 `y:real^N`] P3S_RAD3_DCHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `t:real^N` THEN
  ASM_SIMP_TAC[lriemann] THEN
  REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL; DOT_LADD; DOT_LSUB; DOT_LMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING);;

let P3S_RS_SECTIONAL = prove
 (`!(G:real^N->real^N^N) y u v B C c1 c2 c3.
     (!w x. w dot (G y ** x) = B * (w dot x) + C * (y dot w) * (y dot x)) /\
     (!a v w. lriemann G y a v w =
              c1 % ((a dot w) % v - (v dot w) % a) +
              c2 % (((y dot a) * (y dot w)) % v - ((y dot v) * (y dot w)) % a) +
              c3 % (((y dot v) * (a dot w) - (y dot a) * (v dot w)) % y)) /\
     c2 * B = c3 * (B + C * (y dot y)) + c1 * C /\
     ~(B = &0) /\ ~(y = vec 0)
     ==> lsectional G y u v =
         ((--c1 / B) * (B pow 2 *
            ((u dot u - (u dot y) pow 2 / (y dot y)) *
             (v dot v - (v dot y) pow 2 / (y dot y)) -
             (u dot v - (u dot y) * (v dot y) / (y dot y)) pow 2)) +
          (--(c1 + c3 * (y dot y)) / B) *
          (((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2) -
           B pow 2 *
            ((u dot u - (u dot y) pow 2 / (y dot y)) *
             (v dot v - (v dot y) pow 2 / (y dot y)) -
             (u dot v - (u dot y) * (v dot y) / (y dot y)) pow 2))) /
         ((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL] THEN
  SUBGOAL_THEN `c2 = (c3 * (B + C * ((y:real^N) dot y)) + c1 * C) / B` SUBST1_TAC THENL
   [UNDISCH_TAC `c2 * B = c3 * (B + C * ((y:real^N) dot y)) + c1 * C` THEN
    UNDISCH_TAC `~(B = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) dot y = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(B = &0)` THEN REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The curvature of g0 away from the tip.  With B = b(r),                    *)
(* C = (a(r) - b(r))/r^2 (r = |y|) the metric has the form of the previous   *)
(* section; the coefficients m1, m2, m3 of its Christoffel symbols are the   *)
(* functions p3s_rs_m1/m2/m3 of r below, and K_tan, K_rad the functions      *)
(* p3s_rs_ktan and p3s_rs_krad.  Derivatives of the explicit one-variable    *)
(* expressions are computed by REAL_DIFF_CONV with the derivatives of a, a', *)
(* b, b' added for the call only to its theorem list (helper p3s_rdiff).     *)
(* ========================================================================= *)

let P3S_S1_RDERIV = prove
 (`!s g. open s /\ smooth_map_on s (lift o g o drop)
         ==> smooth_map_on s (lift o real_derivative g o drop) /\
             (!x. lift x IN s ==> (g has_real_derivative real_derivative g x) (atreal x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. lift x IN s ==> (g has_real_derivative real_derivative g x) (atreal x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2C_S1_DERIV THEN
    EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. frechet_derivative (lift o g o drop) (at y) (lift(&1))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop y`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID];
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;

let P3S_AB_DERIVS = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> (!x. (p3s_rad_a g0 has_real_derivative
                     real_derivative (p3s_rad_a g0) x) (atreal x)) /\
               (!x. (real_derivative (p3s_rad_a g0) has_real_derivative
                     real_derivative (real_derivative (p3s_rad_a g0)) x) (atreal x)) /\
               (!x. (p3s_rad_b g0 has_real_derivative
                     real_derivative (p3s_rad_b g0) x) (atreal x)) /\
               (!x. (real_derivative (p3s_rad_b g0) has_real_derivative
                     real_derivative (real_derivative (p3s_rad_b g0)) x) (atreal x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_rad_a g0`] P3S_S1_RDERIV) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_rad_b g0`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_rad_a g0)`] P3S_S1_RDERIV);
    MP_TAC(ISPECL [`(:real^1)`; `real_derivative (p3s_rad_b g0)`] P3S_S1_RDERIV)] THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV]);;

(* REAL_DIFF_CONV with extra derivative theorems |- !x. (f has_real_derivative *)
(* f' x) (atreal x), added in chain-rule form for the call only.              *)

let p3s_rdiff ths tm =
  let save = !real_differentiation_theorems in
  let chain th = CONJUNCTS(REWRITE_RULE[FORALL_AND_THM]
                   (MATCH_MP HAS_REAL_DERIVATIVE_CHAIN_UNIV th)) in
  try add_real_differentiation_theorems (List.concat (List.map chain ths));
      let res = REAL_DIFF_CONV tm in
      real_differentiation_theorems := save; res
  with e -> (real_differentiation_theorems := save; raise e);;

let P3S_RADIAL_DERIV = prove
 (`!(q:real->real) q' (y:real^N).
     ~(y = vec 0) /\ (q has_real_derivative q') (atreal (norm y))
     ==> ((\z. lift(q(norm z))) has_derivative
          (\h. lift((q' / norm y) * (y dot h)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real->real`; `q':real`; `\z:real^N. lift(norm z)`;
                 `\h:real^N. lift((y dot h) / norm y)`; `y:real^N`]
                LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; P2C_NORM_DERIV] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ; real_div] THEN REAL_ARITH_TAC);;

let p3s_rs_c = new_definition
 `p3s_rs_c (g0:real^3->real^3^3) (r:real) =
    (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2`;;

let p3s_rs_dc = new_definition
 `p3s_rs_dc (g0:real^3->real^3^3) (r:real) =
    (real_derivative (p3s_rad_a g0) r - real_derivative (p3s_rad_b g0) r) / r pow 2 -
    &2 * (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 3`;;

let p3s_rs_m1 = new_definition
 `p3s_rs_m1 (g0:real^3->real^3^3) (r:real) =
    (real_derivative (p3s_rad_b g0) r / r) / (&2 * p3s_rad_b g0 r)`;;

let p3s_rs_m2 = new_definition
 `p3s_rs_m2 (g0:real^3->real^3^3) (r:real) =
    (p3s_rs_c g0 r - (real_derivative (p3s_rad_b g0) r / r) / &2) /
    (p3s_rad_b g0 r + p3s_rs_c g0 r * r pow 2)`;;

let p3s_rs_m3 = new_definition
 `p3s_rs_m3 (g0:real^3->real^3^3) (r:real) =
    ((p3s_rs_dc g0 r / r) / &2 -
     (real_derivative (p3s_rad_b g0) r / r) * p3s_rs_c g0 r / p3s_rad_b g0 r) /
    (p3s_rad_b g0 r + p3s_rs_c g0 r * r pow 2)`;;

let P3S_RS_C_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> (p3s_rs_c g0 has_real_derivative p3s_rs_dc g0 r) (atreal r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_rs_c g0 = (\r. (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3s_rs_c]; ALL_TAC] THEN
  MP_TAC(DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL P3S_AB_DERIVS)))
    `((\r. (p3s_rad_a (g0:real^3->real^3^3) r - p3s_rad_b g0 r) / r pow 2)
      has_real_derivative f') (atreal r)`)) THEN
  ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p3s_rs_dc] THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let P3S_G0_BIL2 = prove
 (`!g0 A0 (z:real^3) w v.
     p3_std_initial g0 A0 /\ ~(z = vec 0)
     ==> w dot (g0 z ** v) =
         p3s_rad_b g0 (norm z) * (w dot v) +
         p3s_rs_c g0 (norm z) * (z dot w) * (z dot v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`; `w:real^3`; `v:real^3`]
         P3S_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p3s_rs_c; DOT_SYM] THEN
  SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

let P3S_G0_MDERIV = prove
 (`!g0 A0 (y:real^3) h w v.
     p3_std_initial g0 A0 /\ ~(y = vec 0)
     ==> w dot (mderiv g0 y h ** v) =
         (real_derivative (p3s_rad_b g0) (norm y) / norm y) * (y dot h) * (w dot v) +
         (p3s_rs_dc g0 (norm y) / norm y) * (y dot h) * (y dot w) * (y dot v) +
         p3s_rs_c g0 (norm y) * ((h dot w) * (y dot v) + (y dot w) * (h dot v))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_AB_DERIVS) THEN
  SUBGOAL_THEN `(vectorize o (g0:real^3->real^3^3)) differentiable at y` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `w:real^3`; `v:real^3`]
         LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "D1") THEN
  SUBGOAL_THEN
   `((\z. lift(p3s_rad_b g0 (norm z) * ((w:real^3) dot v) +
              p3s_rs_c g0 (norm z) * (z dot w) * (z dot v))) has_derivative
     (\h. lift((real_derivative (p3s_rad_b g0) (norm y) / norm y) * (y dot h) * (w dot v) +
               (p3s_rs_dc g0 (norm y) / norm y) * (y dot h) * (y dot w) * (y dot v) +
               p3s_rs_c g0 (norm y) * ((h dot w) * (y dot v) + (y dot w) * (h dot v)))))
    (at y)`
  (LABEL_TAC "D2") THENL
   [MP_TAC(ISPECL [`p3s_rad_b g0`; `real_derivative (p3s_rad_b g0) (norm(y:real^3))`;
                   `y:real^3`] P3S_RADIAL_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `(w:real^3) dot v` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
    MP_TAC(ISPECL [`p3s_rs_c g0`; `p3s_rs_dc g0 (norm(y:real^3))`; `y:real^3`]
           P3S_RADIAL_DERIV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_RS_C_DERIV THEN
      EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[NORM_POS_LT];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o SPECL [`w:real^3`; `v:real^3`] o
               MATCH_MP P3S_HAS_DERIV_QUAD) THEN
    REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift((w:real^3) dot ((g0:real^3->real^3^3) z ** v))) has_derivative
     (\h. lift((real_derivative (p3s_rad_b g0) (norm y) / norm y) * (y dot h) * (w dot v) +
               (p3s_rs_dc g0 (norm y) / norm y) * (y dot h) * (y dot w) * (y dot v) +
               p3s_rs_c g0 (norm y) * ((h dot w) * (y dot v) + (y dot w) * (h dot v)))))
    (at y)`
  (LABEL_TAC "D3") THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. lift(p3s_rad_b g0 (norm z) * ((w:real^3) dot v) +
                         p3s_rs_c g0 (norm z) * (z dot w) * (z dot v))` THEN
    EXISTS_TAC `norm(y:real^3)` THEN USE_THEN "D2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P3S_G0_BIL2 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `dist(z:real^3,y) < norm y` THEN
    ASM_REWRITE_TAC[DIST_0; DIST_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "D1" (fun d1 -> USE_THEN "D3" (fun d3 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ d1 d3)))) THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^3`) THEN REWRITE_TAC[LIFT_EQ]);;

let P3S_G0_CHRISTOFFEL = prove
 (`!g0 A0 (z:real^3) a b.
     p3_std_initial g0 A0 /\ ~(z = vec 0)
     ==> christoffel g0 z a b =
         p3s_rs_m1 g0 (norm z) % ((z dot a) % b + (z dot b) % a) +
         (p3s_rs_m2 g0 (norm z) * (a dot b) +
          p3s_rs_m3 g0 (norm z) * (z dot a) * (z dot b)) % z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_STD_METRIC_FIELD) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p3s_rad_b g0 (norm(z:real^3)) + p3s_rs_c g0 (norm z) * (z dot z) =
    p3s_rad_a g0 (norm z) /\
    p3s_rad_b g0 (norm(z:real^3)) + p3s_rs_c g0 (norm z) * norm z pow 2 =
    p3s_rad_a g0 (norm z)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p3s_rs_c; GSYM NORM_POW_2] THEN
    UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(:real^3)`; `z:real^3`;
                 `p3s_rad_b g0 (norm(z:real^3))`; `p3s_rs_c g0 (norm(z:real^3))`;
                 `real_derivative (p3s_rad_b g0) (norm(z:real^3)) / norm z`;
                 `p3s_rs_dc g0 (norm(z:real^3)) / norm z`; `a:real^3`; `b:real^3`]
                P3S_RS_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC P3S_G0_BIL2 THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MATCH_MP_TAC P3S_G0_MDERIV THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p3s_rs_m1; p3s_rs_m2; p3s_rs_m3] THEN ASM_REWRITE_TAC[]);;

let P3S_RS_SIDE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> ~(r = &0) /\ ~(r pow 2 = &0) /\ ~(r pow 3 = &0) /\
                 ~(p3s_rad_b g0 r = &0) /\ ~(&2 * p3s_rad_b g0 r = &0) /\
                 ~(p3s_rad_a g0 r = &0) /\
                 p3s_rad_b g0 r + (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 * r pow 2 =
                 p3s_rad_a g0 r /\
                 ~(p3s_rad_b g0 r + (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 * r pow 2 =
                   &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  SUBGOAL_THEN `&0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(r pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ; REAL_DIV_RMUL; REAL_ENTIRE] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_HAS_RD = prove
 (`!f f' x. (f has_real_derivative f') (atreal x)
            ==> (f has_real_derivative real_derivative f x) (atreal x)`,
  MESON_TAC[HAS_REAL_DERIVATIVE_DERIVATIVE]);;

let P3S_RS_M1_EQ = prove
 (`!g0. p3s_rs_m1 g0 =
        (\r. (real_derivative (p3s_rad_b g0) r / r) / (&2 * p3s_rad_b g0 r))`,
  REWRITE_TAC[FUN_EQ_THM; p3s_rs_m1]);;

let P3S_RS_M2_EQ = prove
 (`!g0. p3s_rs_m2 g0 =
        (\r. ((p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 -
              (real_derivative (p3s_rad_b g0) r / r) / &2) /
             (p3s_rad_b g0 r + (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 * r pow 2))`,
  REWRITE_TAC[FUN_EQ_THM; p3s_rs_m2; p3s_rs_c]);;

let P3S_RS_M3_EQ = prove
 (`!g0. p3s_rs_m3 g0 =
        (\r. ((((real_derivative (p3s_rad_a g0) r - real_derivative (p3s_rad_b g0) r) /
                r pow 2 - &2 * (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 3) / r) / &2 -
              (real_derivative (p3s_rad_b g0) r / r) *
              ((p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2) / p3s_rad_b g0 r) /
             (p3s_rad_b g0 r + (p3s_rad_a g0 r - p3s_rad_b g0 r) / r pow 2 * r pow 2))`,
  REWRITE_TAC[FUN_EQ_THM; p3s_rs_m3; p3s_rs_c; p3s_rs_dc]);;

let p3s_rs_dthm i =
  let eq = List.nth [P3S_RS_M1_EQ; P3S_RS_M2_EQ; P3S_RS_M3_EQ] (i - 1) in
  let lam = rhs(concl(SPEC `g0:real^3->real^3^3` eq)) in
  let tm = mk_comb(mk_comb(mk_comb(
             `(has_real_derivative):(real->real)->real->(real)net->bool`, lam),
             `f':real`), `atreal r`) in
  DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL P3S_AB_DERIVS))) tm);;

let P3S_RS_M_DERIVS = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> (p3s_rs_m1 g0 has_real_derivative real_derivative (p3s_rs_m1 g0) r)
                 (atreal r) /\
                 (p3s_rs_m2 g0 has_real_derivative real_derivative (p3s_rs_m2 g0) r)
                 (atreal r) /\
                 (p3s_rs_m3 g0 has_real_derivative real_derivative (p3s_rs_m3 g0) r)
                 (atreal r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P3S_RS_M1_EQ; P3S_RS_M2_EQ; P3S_RS_M3_EQ] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(p3s_rs_dthm 1); MP_TAC(p3s_rs_dthm 2); MP_TAC(p3s_rs_dthm 3)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP P3S_HAS_RD));;

let P3S_RS_RELATION = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
   ==> (real_derivative (p3s_rs_m1 g0) r / r - p3s_rs_m1 g0 r pow 2 - p3s_rs_m3 g0 r -
        p3s_rs_m1 g0 r * p3s_rs_m3 g0 r * r pow 2) * p3s_rad_b g0 r =
       (p3s_rs_m3 g0 r - p3s_rs_m2 g0 r pow 2 - real_derivative (p3s_rs_m2 g0) r / r -
        p3s_rs_m2 g0 r * p3s_rs_m3 g0 r * r pow 2) *
       (p3s_rad_b g0 r + p3s_rs_c g0 r * r pow 2) +
       (p3s_rs_m1 g0 r - p3s_rs_m2 g0 r - p3s_rs_m1 g0 r * p3s_rs_m2 g0 r * r pow 2) *
       p3s_rs_c g0 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(p3s_rs_dthm 1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_M1_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(p3s_rs_dthm 2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_M2_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3s_rs_m1; p3s_rs_m2; p3s_rs_m3; p3s_rs_c; p3s_rs_dc] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`aa = p3s_rad_a (g0:real^3->real^3^3) r`; `bb = p3s_rad_b (g0:real^3->real^3^3) r`;
    `a1 = real_derivative (p3s_rad_a (g0:real^3->real^3^3)) r`;
    `b1 = real_derivative (p3s_rad_b (g0:real^3->real^3^3)) r`;
    `b2 = real_derivative (real_derivative (p3s_rad_b (g0:real^3->real^3^3))) r`] THEN
  UNDISCH_TAC `~(r = &0)` THEN UNDISCH_TAC `~(aa = &0)` THEN UNDISCH_TAC `~(bb = &0)` THEN
  CONV_TAC REAL_FIELD);;

let P3S_G0_RIEMANN = prove
 (`!g0 A0 (y:real^3) a v w.
     p3_std_initial g0 A0 /\ ~(y = vec 0)
     ==> lriemann g0 y a v w =
         (p3s_rs_m1 g0 (norm y) - p3s_rs_m2 g0 (norm y) -
          p3s_rs_m1 g0 (norm y) * p3s_rs_m2 g0 (norm y) * (y dot y)) %
         ((a dot w) % v - (v dot w) % a) +
         (real_derivative (p3s_rs_m1 g0) (norm y) / norm y - p3s_rs_m1 g0 (norm y) pow 2 -
          p3s_rs_m3 g0 (norm y) -
          p3s_rs_m1 g0 (norm y) * p3s_rs_m3 g0 (norm y) * (y dot y)) %
         (((y dot a) * (y dot w)) % v - ((y dot v) * (y dot w)) % a) +
         (p3s_rs_m3 g0 (norm y) - p3s_rs_m2 g0 (norm y) pow 2 -
          real_derivative (p3s_rs_m2 g0) (norm y) / norm y -
          p3s_rs_m2 g0 (norm y) * p3s_rs_m3 g0 (norm y) * (y dot y)) %
         (((y dot v) * (a dot w) - (y dot a) * (v dot w)) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`] P3S_RS_M_DERIVS) THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `(:real^3) DELETE vec 0`;
                 `\z:real^3. p3s_rs_m1 g0 (norm z)`; `\z:real^3. p3s_rs_m2 g0 (norm z)`;
                 `\z:real^3. p3s_rs_m3 g0 (norm z)`;
                 `real_derivative (p3s_rs_m1 g0) (norm(y:real^3)) / norm y`;
                 `real_derivative (p3s_rs_m2 g0) (norm(y:real^3)) / norm y`;
                 `real_derivative (p3s_rs_m3 g0) (norm(y:real^3)) / norm y`;
                 `y:real^3`; `a:real^3`; `v:real^3`; `w:real^3`] P3S_RAD3_RIEMANN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[P3S_OPEN_PUNCT; IN_DELETE; IN_UNIV] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_G0_CHRISTOFFEL THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_RADIAL_DERIV THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P3S_RADIAL_DERIV THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC P3S_RADIAL_DERIV THEN ASM_REWRITE_TAC[ETA_AX]]);;

let p3s_rs_ktan = new_definition
 `p3s_rs_ktan (g0:real^3->real^3^3) (r:real) =
    --(p3s_rs_m1 g0 r - p3s_rs_m2 g0 r - p3s_rs_m1 g0 r * p3s_rs_m2 g0 r * r pow 2) /
    p3s_rad_b g0 r`;;

let p3s_rs_krad = new_definition
 `p3s_rs_krad (g0:real^3->real^3^3) (r:real) =
    --((p3s_rs_m1 g0 r - p3s_rs_m2 g0 r - p3s_rs_m1 g0 r * p3s_rs_m2 g0 r * r pow 2) +
       (p3s_rs_m3 g0 r - p3s_rs_m2 g0 r pow 2 - real_derivative (p3s_rs_m2 g0) r / r -
        p3s_rs_m2 g0 r * p3s_rs_m3 g0 r * r pow 2) * r pow 2) /
    p3s_rad_b g0 r`;;

let P3S_G0_SECTIONAL = prove
 (`!g0 A0 (y:real^3) u v.
     p3_std_initial g0 A0 /\ ~(y = vec 0)
     ==> mfd_sectional (open_set_atlas (:real^3)) g0 y u v =
         (p3s_rs_ktan g0 (norm y) * p3s_rad_b g0 (norm y) pow 2 *
            ((u dot u - (u dot y) pow 2 / norm y pow 2) *
             (v dot v - (v dot y) pow 2 / norm y pow 2) -
             (u dot v - (u dot y) * (v dot y) / norm y pow 2) pow 2) +
          p3s_rs_krad g0 (norm y) *
            ((u dot (g0 y ** u)) * (v dot (g0 y ** v)) - (u dot (g0 y ** v)) pow 2 -
             p3s_rad_b g0 (norm y) pow 2 *
             ((u dot u - (u dot y) pow 2 / norm y pow 2) *
              (v dot v - (v dot y) pow 2 / norm y pow 2) -
              (u dot v - (u dot y) * (v dot y) / norm y pow 2) pow 2))) /
         ((u dot (g0 y ** u)) * (v dot (g0 y ** v)) - (u dot (g0 y ** v)) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_OPEN_SET_MFD_SECTIONAL] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`] P3S_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`;
                 `p3s_rad_b g0 (norm(y:real^3))`; `p3s_rs_c g0 (norm(y:real^3))`;
                 `p3s_rs_m1 g0 (norm y) - p3s_rs_m2 g0 (norm y) -
                  p3s_rs_m1 g0 (norm y) * p3s_rs_m2 g0 (norm y) * ((y:real^3) dot y)`;
                 `real_derivative (p3s_rs_m1 g0) (norm y) / norm y -
                  p3s_rs_m1 g0 (norm y) pow 2 - p3s_rs_m3 g0 (norm y) -
                  p3s_rs_m1 g0 (norm y) * p3s_rs_m3 g0 (norm y) * ((y:real^3) dot y)`;
                 `p3s_rs_m3 g0 (norm y) - p3s_rs_m2 g0 (norm y) pow 2 -
                  real_derivative (p3s_rs_m2 g0) (norm y) / norm y -
                  p3s_rs_m2 g0 (norm y) * p3s_rs_m3 g0 (norm y) * ((y:real^3) dot y)`]
                P3S_RS_SECTIONAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC P3S_G0_BIL2 THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MATCH_MP_TAC P3S_G0_RIEMANN THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM NORM_POW_2] THEN MATCH_MP_TAC P3S_RS_RELATION THEN
      EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[p3s_rs_ktan; p3s_rs_krad; GSYM NORM_POW_2] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

(* ========================================================================= *)
(* The warping function.  f = H o rinv with H(r) = r sqrt(b r),              *)
(* rinv' = 1/sqrt(a(rinv)), so f'(rho r) = f1(r) = H'(r)/sqrt(a r) and       *)
(* f''(rho r) = f2(r) = f1'(r)/sqrt(a r); hence (1 - f'^2)/f^2 and -f''/f at *)
(* rho(r) are the coefficients K_tan(r), K_rad(r) of the previous section,   *)
(* and the exported sectional curvature formula follows.                     *)
(* ========================================================================= *)

let P3S_RINV_DERIV = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> (p3s_rad_rinv g0 has_real_derivative
                  inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 s)))) (atreal s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_INVERSE_STRONG_X THEN
  MAP_EVERY EXISTS_TAC [`p3s_rad_rho g0`; `{r:real | r > &0}`] THEN
  SUBGOAL_THEN `&0 < p3s_rad_rinv g0 s /\ p3s_rad_rho g0 (p3s_rad_rinv g0 s) = s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; real_gt; REAL_OPEN_HALFSPACE_GT] THEN
  REWRITE_TAC[GSYM real_gt; REAL_OPEN_HALFSPACE_GT] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `sqrt(p3s_rad_a g0 r)` THEN
    MATCH_MP_TAC P3S_RHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3S_RINV_UNIQUE THEN EXISTS_TAC `A0:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC P3S_RHO_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN ASM_REWRITE_TAC[]]);;

let p3s_rs_f1 = new_definition
 `p3s_rs_f1 (g0:real^3->real^3^3) (r:real) =
    (sqrt(p3s_rad_b g0 r) +
     r * real_derivative (p3s_rad_b g0) r * inv(&2 * sqrt(p3s_rad_b g0 r))) *
    inv(sqrt(p3s_rad_a g0 r))`;;

let p3s_rs_f2 = new_definition
 `p3s_rs_f2 (g0:real^3->real^3^3) (r:real) =
    real_derivative (p3s_rs_f1 g0) r * inv(sqrt(p3s_rad_a g0 r))`;;

let P3S_RS_F1_EQ = prove
 (`!g0. p3s_rs_f1 g0 =
        (\r. (sqrt(p3s_rad_b g0 r) +
              r * real_derivative (p3s_rad_b g0) r * inv(&2 * sqrt(p3s_rad_b g0 r))) *
             inv(sqrt(p3s_rad_a g0 r)))`,
  REWRITE_TAC[FUN_EQ_THM; p3s_rs_f1]);;

let p3s_rs_hthm () =
  DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL P3S_AB_DERIVS)))
    `((\r. r * sqrt(p3s_rad_b (g0:real^3->real^3^3) r)) has_real_derivative f')
     (atreal r)`);;

let p3s_rs_f1thm () =
  let lam = rhs(concl(SPEC `g0:real^3->real^3^3` P3S_RS_F1_EQ)) in
  let tm = mk_comb(mk_comb(mk_comb(
             `(has_real_derivative):(real->real)->real->(real)net->bool`, lam),
             `f':real`), `atreal r`) in
  DISCH_ALL(p3s_rdiff (CONJUNCTS(UNDISCH(SPEC_ALL P3S_AB_DERIVS))) tm);;

let P3S_RS_AB_SQRT = prove
 (`!g0 A0 r. p3_std_initial g0 A0
             ==> &0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r /\
                 &0 < sqrt(p3s_rad_a g0 r) /\ &0 < sqrt(p3s_rad_b g0 r) /\
                 ~(sqrt(p3s_rad_a g0 r) = &0) /\ ~(&2 * sqrt(p3s_rad_b g0 r) = &0) /\
                 sqrt(p3s_rad_a g0 r) pow 2 = p3s_rad_a g0 r /\
                 sqrt(p3s_rad_b g0 r) pow 2 = p3s_rad_b g0 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  SUBGOAL_THEN `&0 < p3s_rad_a g0 r /\ &0 < p3s_rad_b g0 r` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_IMP_NZ; REAL_ENTIRE] THEN
  REAL_ARITH_TAC);;

let P3S_H_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0
             ==> ((\r. r * sqrt(p3s_rad_b g0 r)) has_real_derivative
                  p3s_rs_f1 g0 r * sqrt(p3s_rad_a g0 r)) (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(p3s_rs_hthm ()) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p3s_rs_f1] THEN
  UNDISCH_TAC `~(sqrt(p3s_rad_a g0 r) = &0)` THEN
  UNDISCH_TAC `~(&2 * sqrt(p3s_rad_b g0 r) = &0)` THEN CONV_TAC REAL_FIELD);;

let P3S_RS_F1_DIFF = prove
 (`!g0 A0 r. p3_std_initial g0 A0
             ==> (p3s_rs_f1 g0 has_real_derivative real_derivative (p3s_rs_f1 g0) r)
                 (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P3S_RS_F1_EQ] THEN
  MP_TAC(p3s_rs_f1thm ()) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP P3S_HAS_RD));;

let P3S_WARP_D1 = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> (p3s_warp g0 has_real_derivative p3s_rs_f1 g0 (p3s_rad_rinv g0 s))
                 (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_warp g0 = (\r. r * sqrt(p3s_rad_b g0 r)) o p3s_rad_rinv g0`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; p3s_warp]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p3s_rad_rinv g0`; `\r. r * sqrt(p3s_rad_b g0 r)`;
                 `inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 s)))`;
                 `p3s_rs_f1 g0 (p3s_rad_rinv g0 s) * sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 s))`;
                 `s:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RINV_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3S_H_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 s)) = &0)` THEN
  CONV_TAC REAL_FIELD);;

let P3S_WARP_RD1 = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> real_derivative (p3s_warp g0) s = p3s_rs_f1 g0 (p3s_rad_rinv g0 s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC P3S_WARP_D1 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_WARP_D2 = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> (real_derivative (p3s_warp g0) has_real_derivative
                  p3s_rs_f2 g0 (p3s_rad_rinv g0 s)) (atreal s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`p3s_rs_f1 g0 o p3s_rad_rinv g0`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P3S_WARP_RD1 THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3s_rs_f2] THEN MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3S_RINV_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_RS_F1_DIFF THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_WARP_HD2 = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> higher_real_derivative 2 (p3s_warp g0) s =
                 p3s_rs_f2 g0 (p3s_rad_rinv g0 s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; higher_real_derivative] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC P3S_WARP_D2 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_RHO_POS = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r ==> &0 < p3s_rad_rho g0 r`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `g0:real^3->real^3^3` P3S_RHO_0)] THEN
  MATCH_MP_TAC P3S_RHO_STRICT THEN EXISTS_TAC `A0:real` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let P3S_SEC_TAN_RHO = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> p3s_sec_tan g0 (p3s_rad_rho g0 r) = p3s_rs_ktan g0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[p3s_sec_tan] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rho g0 r`] P3S_WARP_RD1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RINV_UNIQUE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_WARP_RHO) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3s_rs_f1; p3s_rs_ktan; p3s_rs_m1; p3s_rs_m2; p3s_rs_c] THEN
  MAP_EVERY ABBREV_TAC [`sa = sqrt(p3s_rad_a (g0:real^3->real^3^3) r)`;
                        `sb = sqrt(p3s_rad_b (g0:real^3->real^3^3) r)`] THEN
  SUBGOAL_THEN `p3s_rad_a (g0:real^3->real^3^3) r = sa pow 2 /\
                p3s_rad_b (g0:real^3->real^3^3) r = sb pow 2`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["sa"; "sb"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `b1 = real_derivative (p3s_rad_b (g0:real^3->real^3^3)) r` THEN
  SUBGOAL_THEN `~(r = &0) /\ ~(sa = &0) /\ ~(sb = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let P3S_SEC_RAD_RHO = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> p3s_sec_rad g0 (p3s_rad_rho g0 r) = p3s_rs_krad g0 r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[p3s_sec_rad] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rho g0 r`] P3S_WARP_HD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RINV_UNIQUE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_WARP_RHO) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3s_rs_f2; p3s_rs_krad] THEN
  MP_TAC(p3s_rs_f1thm ()) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_F1_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(p3s_rs_dthm 2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  REWRITE_TAC[GSYM P3S_RS_M2_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3s_rs_m1; p3s_rs_m2; p3s_rs_m3; p3s_rs_c; p3s_rs_dc] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`sa = sqrt(p3s_rad_a (g0:real^3->real^3^3) r)`;
                        `sb = sqrt(p3s_rad_b (g0:real^3->real^3^3) r)`] THEN
  SUBGOAL_THEN `p3s_rad_a (g0:real^3->real^3^3) r = sa pow 2 /\
                p3s_rad_b (g0:real^3->real^3^3) r = sb pow 2`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["sa"; "sb"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a1 = real_derivative (p3s_rad_a (g0:real^3->real^3^3)) r`;
    `b1 = real_derivative (p3s_rad_b (g0:real^3->real^3^3)) r`;
    `b2 = real_derivative (real_derivative (p3s_rad_b (g0:real^3->real^3^3))) r`] THEN
  SUBGOAL_THEN `~(r = &0) /\ ~(sa = &0) /\ ~(sb = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let P3S_ROT_SEC = prove
 (`!g0 A0 (x:real^3) u v.
  p3_std_initial g0 A0 /\ ~(x = vec 0) /\ ~collinear {vec 0,u,v}
  ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v =
      (p3s_sec_tan g0 (p3_std_dist g0 x) * p3s_rad_b g0 (norm x) pow 2 *
         ((u dot u - (u dot x) pow 2 / norm x pow 2) *
          (v dot v - (v dot x) pow 2 / norm x pow 2) -
          (u dot v - (u dot x) * (v dot x) / norm x pow 2) pow 2) +
       p3s_sec_rad g0 (p3_std_dist g0 x) *
         ((u dot (g0 x ** u)) * (v dot (g0 x ** v)) - (u dot (g0 x ** v)) pow 2 -
          p3s_rad_b g0 (norm x) pow 2 *
          ((u dot u - (u dot x) pow 2 / norm x pow 2) *
           (v dot v - (v dot x) pow 2 / norm x pow 2) -
           (u dot v - (u dot x) * (v dot x) / norm x pow 2) pow 2))) /
      ((u dot (g0 x ** u)) * (v dot (g0 x ** v)) - (u dot (g0 x ** v)) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
         P3S_G0_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_SEC_TAN_RHO) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3S_SEC_RAD_RHO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

(* ========================================================================= *)
(* The one-variable facts on the warping function f.  On the                *)
(* planes (e1,e2) and (e2,e3) at r e1 the sectional curvature is K_rad and  *)
(* K_tan at rho(r); so K_rad >= 0 (sec >= 0) gives f'' <= 0, and K_tan =    *)
(* 1/4 in the round cap; f is smooth (rinv is smooth by the inverse        *)
(* function theorem); f = sqrt 2 beyond A0 (the tangential coefficient of   *)
(* the cylinder pullback is 2/r^2); f -> 0 and f' -> 1 at 0 (a(0) = b(0));   *)
(* concavity then gives 0 <= f' <= 1 and f <= sqrt 2.                        *)
(* ========================================================================= *)

let P3S_NONCOLL_BASIS = prove
 (`~collinear {vec 0:real^3, basis 1, basis 2} /\
   ~collinear {vec 0:real^3, basis 2, basis 3}`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN CONJ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (MP_TAC o AP_TERM `\v:real^3. v$2, v$3`)) THEN
  SIMP_TAC[BASIS_COMPONENT; VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH; PAIR_EQ] THEN
  REAL_ARITH_TAC);;

let P3S_E1_FACTS = prove
 (`!g0 A0 r. p3_std_initial g0 A0
             ==> basis 1 dot (g0 (r % basis 1) ** basis 1) = p3s_rad_a g0 r /\
                 basis 2 dot (g0 (r % basis 1) ** basis 2) = p3s_rad_b g0 r /\
                 basis 3 dot (g0 (r % basis 1) ** basis 3) = p3s_rad_b g0 r /\
                 basis 1 dot (g0 (r % basis 1) ** basis 2) = &0 /\
                 basis 2 dot (g0 (r % basis 1) ** basis 3) = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(GEN `w:real^3` (GEN `v:real^3` (UNDISCH(ISPECL
    [`g0:real^3->real^3^3`; `A0:real`; `r:real`; `w:real^3`; `v:real^3`]
    P3S_ROT_E1_BIL)))) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[BASIS_COMPONENT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let P3S_SEC_RADIAL_PLANE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> mfd_sectional (open_set_atlas (:real^3)) g0 (r % basis 1)
                               (basis 1) (basis 2) =
                 p3s_sec_rad g0 (p3s_rad_rho g0 r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r % basis 1:real^3`;
                 `basis 1:real^3`; `basis 2:real^3`] P3S_ROT_SEC) THEN
  ASM_REWRITE_TAC[P3S_NONCOLL_BASIS; VECTOR_MUL_EQ_0] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r % basis 1:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_E1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DOT_RMUL; DOT_LMUL; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC [`aa = p3s_rad_a (g0:real^3->real^3^3) r`;
                        `bb = p3s_rad_b (g0:real^3->real^3^3) r`;
                        `kk = p3s_sec_rad g0 (p3s_rad_rho g0 r)`] THEN
  SUBGOAL_THEN `~(aa = &0) /\ ~(bb = &0) /\ ~(r = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]);;

let P3S_SEC_TANG_PLANE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> mfd_sectional (open_set_atlas (:real^3)) g0 (r % basis 1)
                               (basis 2) (basis 3) =
                 p3s_sec_tan g0 (p3s_rad_rho g0 r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r % basis 1:real^3`;
                 `basis 2:real^3`; `basis 3:real^3`] P3S_ROT_SEC) THEN
  ASM_REWRITE_TAC[P3S_NONCOLL_BASIS; VECTOR_MUL_EQ_0] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `r % basis 1:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_E1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DOT_RMUL; DOT_LMUL; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC [`aa = p3s_rad_a (g0:real^3->real^3^3) r`;
                        `bb = p3s_rad_b (g0:real^3->real^3^3) r`;
                        `kk = p3s_sec_tan g0 (p3s_rad_rho g0 r)`] THEN
  SUBGOAL_THEN `~(aa = &0) /\ ~(bb = &0) /\ ~(r = &0)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]);;

let P3S_RINV_FACTS = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> &0 < p3s_rad_rinv g0 s /\ p3s_rad_rho g0 (p3s_rad_rinv g0 s) = s`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC P3S_RINV_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let P3S_KRAD_NONNEG = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s ==> &0 <= p3s_sec_rad g0 s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`]
         P3S_SEC_RADIAL_PLANE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial] THEN
  DISCH_THEN(MP_TAC o SPECL [`p3s_rad_rinv g0 s % basis 1:real^3`; `basis 1:real^3`;
                             `basis 2:real^3`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[P3S_NONCOLL_BASIS]);;

let P3S_KTAN_CAP = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> ?r0. &0 < r0 /\ !s. &0 < s /\ s < r0 ==> p3s_sec_tan g0 s = &1 / &4`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [p3_std_initial]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`]
         P3S_SEC_TANG_PLANE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[P3S_NONCOLL_BASIS] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`;
                 `p3s_rad_rinv g0 s % basis 1:real^3`] P3S_ROT_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`]);;

let P3S_WARP_POS = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s ==> &0 < p3s_warp g0 s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_warp] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`] P3S_RS_AB_SQRT) THEN
  ASM_SIMP_TAC[]);;

let P3S_WARP_D2_NONPOS = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> higher_real_derivative 2 (p3s_warp g0) s <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_KRAD_NONNEG) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_WARP_POS) THEN
  ASM_REWRITE_TAC[p3s_sec_rad] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC);;

let P3S_RINV_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {s | &0 < drop s} (lift o p3s_rad_rinv g0 o drop)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `drop y`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r0 = p3s_rad_rinv g0 (drop y)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o p3s_rad_rho g0 o drop`; `{x:real^1 | &0 < drop x}`;
                 `lift r0`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RHO_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0:real`] P3S_RHO_DERIV) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DET_1; matrix] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; ARITH; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0:real`] P3S_RS_AB_SQRT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1->bool`; `u:real^1->bool`; `g:real^1->real^1`] THEN
  STRIP_TAC THEN EXISTS_TAC `u:real^1->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(lift o p3s_rad_rho g0 o drop) (lift r0) IN u` THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^1->real^1` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^1. z IN t /\ w = (lift o p3s_rad_rho g0 o drop) z`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < drop(z:real^1)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `drop(z:real^1)`] P3S_RINV_UNIQUE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; LIFT_DROP]);;

let P3S_H_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on (:real^1) (lift o (\r. r * sqrt(p3s_rad_b g0 r)) o drop)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[OPEN_UNIV; P2C_S1_ID] THEN
  MP_TAC(ISPECL [`(:real^1)`; `lift o p3s_rad_b g0 o drop`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; o_THM; LIFT_DROP] THEN
  REWRITE_TAC[o_DEF]);;

let P3S_WARP_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {s | &0 < drop s} (lift o p3s_warp g0 o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{s:real^1 | &0 < drop s}`; `(:real^1)`;
                 `lift o p3s_rad_rinv g0 o drop`; `\r. r * sqrt(p3s_rad_b g0 r)`]
                SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
  REWRITE_TAC[P2C_OPEN_DROP_GT; OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P3S_RINV_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3S_H_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; p3s_warp]]);;

(* REAL_DIFF_CONV with extra derivative theorems, unconditional             *)
(* (|- !x. (f has_real_derivative f' x) (atreal x)) or conditional          *)
(* (|- !x. P x ==> (f has_real_derivative f' x) (atreal x)).                 *)

let p3s_rdiffc ths tm =
  let save = !real_differentiation_theorems in
  let chain th =
    let ch = if is_imp(snd(strip_forall(concl th)))
             then HAS_REAL_DERIVATIVE_CHAIN else HAS_REAL_DERIVATIVE_CHAIN_UNIV in
    CONJUNCTS(REWRITE_RULE[FORALL_AND_THM] (MATCH_MP ch th)) in
  try add_real_differentiation_theorems (List.concat (List.map chain ths));
      let res = REAL_DIFF_CONV tm in
      real_differentiation_theorems := save; res
  with e -> (real_differentiation_theorems := save; raise e);;

let P3S_NC_EQ = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> p3_std_nc g0 A0 =
               (\z. (exp((A0 + &4 - p3s_rad_rho g0 (norm z)) / sqrt(&2)) * inv(norm z)) % z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; p3_std_nc; VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_DIST_ALT th]));;

let P3S_NC_K_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> ?k'. ((\r. exp((A0 + &4 - p3s_rad_rho g0 r) / sqrt(&2)) * inv r)
                       has_real_derivative k') (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(p3s_rdiffc
    [GEN `r:real` (UNDISCH(SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_RHO_DERIV))))]
    `((\r. exp((A0 + &4 - p3s_rad_rho (g0:real^3->real^3^3) r) / sqrt(&2)) * inv r)
      has_real_derivative f') (atreal r)`)) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MESON_TAC[]);;

let P3S_B_CYL = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r /\ A0 < p3s_rad_rho g0 r
             ==> p3s_rad_b g0 r = &2 / r pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x:real^3 = r % basis 1` THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0) /\ norm(x:real^3) = r /\ x dot basis 2 = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH;
             DOT_LMUL; DOT_BASIS_BASIS] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g0:real^3->real^3^3) x = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) x`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [p3_std_initial]) THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_ROT_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_E1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `kk = \t. exp((A0 + &4 - p3s_rad_rho g0 t) / sqrt(&2)) * inv t` THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 = (\z:real^3. kk(norm z) % z)` SUBST1_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[] THEN MATCH_MP_TAC P3S_NC_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_NC_K_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k':real`) THEN
  SUBGOAL_THEN `((kk:real->real) has_real_derivative k') (atreal (norm(x:real^3)))`
  ASSUME_TAC THENL [EXPAND_TAC "kk" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:real->real`; `k':real`; `x:real^3`] P3S_RADIAL_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. (kk:real->real)(norm z)`;
                 `\h:real^3. (k' / norm(x:real^3)) * (x dot h)`;
                 `\z:real^3. z`; `\h:real^3. h`; `x:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF; HAS_DERIVATIVE_ID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. (kk:real->real)(norm z) % z`; `cylinder_flow (&0)`;
                 `x:real^3`; `basis 2:real^3`; `basis 2:real^3`] LRG_MPULLBACK_DOT) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_SYM; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ASM_REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL;
                  DOT_LMUL; NORM_MUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `&0 < (kk:real->real) r` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_LT_INV_EQ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
  UNDISCH_TAC `&0 < (kk:real->real) r` THEN UNDISCH_TAC `&0 < r` THEN
  CONV_TAC REAL_FIELD);;

let P3S_WARP_CYL = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ A0 < s ==> p3s_warp g0 s = sqrt(&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                CONJUNCT2 o GEN_REWRITE_RULE I [p3_std_initial]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = p3s_rad_rinv g0 s` THEN STRIP_TAC THEN
  REWRITE_TAC[p3s_warp] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_B_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SQRT_DIV] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let P3S_A0_POS = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> &0 < A0`,
  SIMP_TAC[p3_std_initial]);;

let P3S_WARP_GE_A0 = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ A0 <= s ==> p3s_warp g0 s = sqrt(&2)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `A0 < s` THENL
   [MATCH_MP_TAC P3S_WARP_CYL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) = A0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  SUBGOAL_THEN `(p3s_warp g0) real_continuous atreal A0` MP_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `p3s_rs_f1 g0 (p3s_rad_rinv g0 A0)` THEN
    MATCH_MP_TAC P3S_WARP_D1 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs(p3s_warp g0 A0 - sqrt(&2))`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A0 + d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p3s_warp g0 (A0 + d / &2) = sqrt(&2)` SUBST1_TAC THENL
   [MATCH_MP_TAC P3S_WARP_CYL THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P3S_RINV_SMALL = prove
 (`!g0 A0 e. p3_std_initial g0 A0 /\ &0 < e
             ==> ?d. &0 < d /\ !s. &0 < s /\ s < d ==> p3s_rad_rinv g0 s < e`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `p3s_rad_rho g0 e` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P3S_RHO_POS THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 s`; `e:real`]
         P3S_RHO_LT_EQ) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P3S_S1_CONT_SUB = prove
 (`!s (g:real->real) a b.
     open s /\ smooth_map_on s (lift o g o drop) /\
     (!x. a <= x /\ x <= b ==> lift x IN s)
     ==> g real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^1->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]);;

let P3S_WARP_LIM0 = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> ((p3s_warp g0) ---> &0) (atreal (&0) within {s | &0 < s})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
  MP_TAC(ISPECL [`p3s_rad_b g0`; `real_interval[&0,&1]`] REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_NE_EMPTY; REAL_POS] THEN
    MATCH_MP_TAC P2C_S1_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = sqrt(p3s_rad_b g0 t1) + &1` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MP_TAC(SPEC `p3s_rad_b g0 t1` SQRT_POS_LE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `min (&1) (e / M)`] P3S_RINV_SMALL) THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = p3s_rad_rinv g0 s` THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[p3s_warp] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(p3s_rad_b g0 r) < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x < y + &1`) THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(p3s_rad_b g0 r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r < e / M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * sqrt(p3s_rad_b g0 r) <= (e / M) * M` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `&0 <= r * sqrt(p3s_rad_b g0 r)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r * sqrt(p3s_rad_b g0 r) < (e / M) * M` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC]);;

let P3S_WARP_D1_FAR = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ A0 < s
             ==> real_derivative (p3s_warp g0) s = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\x:real. sqrt(&2)`; `s - A0`] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P3S_WARP_GE_A0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_WARP_D2_FAR = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ A0 < s
             ==> higher_real_derivative 2 (p3s_warp g0) s = &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; higher_real_derivative] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\x:real. &0`; `s - A0`] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P3S_WARP_D1_FAR THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_WARP_HAS_D2 = prove
 (`!g0 A0 x. p3_std_initial g0 A0 /\ &0 < x
             ==> (real_derivative (p3s_warp g0) has_real_derivative
                  higher_real_derivative 2 (p3s_warp g0) x) (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real`] P3S_WARP_HD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P3S_WARP_D2 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3S_WARPD_DECR = prove
 (`!g0 A0 s t. p3_std_initial g0 A0 /\ &0 < s /\ s <= t
               ==> real_derivative (p3s_warp g0) t <= real_derivative (p3s_warp g0) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --(real_derivative (p3s_warp g0) x)`;
                 `\x. --(higher_real_derivative 2 (p3s_warp g0) x)`;
                 `real_interval[s,t]`; `s:real`; `t:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THEN X_GEN_TAC `x:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P3S_WARP_HAS_D2 THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_NEG_GE0] THEN MATCH_MP_TAC P3S_WARP_D2_NONPOS THEN
      EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let P3S_WARPD_NONNEG = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> &0 <= real_derivative (p3s_warp g0) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `max s A0 + &1`] P3S_WARP_D1_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC P3S_WARPD_DECR THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3S_WARPD_LIM0 = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> ((real_derivative (p3s_warp g0)) ---> &1)
               (atreal (&0) within {s | &0 < s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p3s_rs_f1 g0 (&0) = &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`] P3S_RS_AB_SQRT) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_ROT_AB) THEN
    ASM_REWRITE_TAC[p3s_rs_f1; REAL_MUL_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_RINV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p3s_rs_f1 g0) real_continuous atreal (&0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
    REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `real_derivative (p3s_rs_f1 g0) (&0)` THEN
    MATCH_MP_TAC P3S_RS_F1_DIFF THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN DISCH_TAC THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `d1:real`] P3S_RINV_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_WARP_RD1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC);;

let P3S_WARPD_LE1 = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s
             ==> real_derivative (p3s_warp g0) s <= &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3S_WARPD_LIM0) THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `real_derivative (p3s_warp g0) s - &1`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min s d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `min s d / &2`; `s:real`]
         P3S_WARPD_DECR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P3S_WARP_INCR = prove
 (`!g0 A0 s t. p3_std_initial g0 A0 /\ &0 < s /\ s <= t
               ==> p3s_warp g0 s <= p3s_warp g0 t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p3s_warp g0`; `real_derivative (p3s_warp g0)`;
                 `real_interval[s,t]`; `s:real`; `t:real`]
                HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THEN X_GEN_TAC `x:real` THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC P3S_HAS_RD THEN EXISTS_TAC `p3s_rs_f1 g0 (p3s_rad_rinv g0 x)` THEN
    MATCH_MP_TAC P3S_WARP_D1 THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P3S_WARPD_NONNEG THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3S_WARP_LE = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 < s ==> p3s_warp g0 s <= sqrt(&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `max s A0 + &1`] P3S_WARP_GE_A0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC P3S_WARP_INCR THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3S_WARPD2_BOUND = prove
 (`!g0 A0 e. p3_std_initial g0 A0 /\ &0 < e
             ==> ?B. !s. e <= s ==> abs(higher_real_derivative 2 (p3s_warp g0) s) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_WARP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{s:real^1 | &0 < drop s}`; `p3s_warp g0`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[P2C_OPEN_DROP_GT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{s:real^1 | &0 < drop s}`; `real_derivative (p3s_warp g0)`]
         P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[P2C_OPEN_DROP_GT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `real_derivative (real_derivative (p3s_warp g0)) real_continuous_on
    real_interval[e,A0 + &1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_S1_CONT_SUB THEN EXISTS_TAC `{s:real^1 | &0 < drop s}` THEN
    ASM_REWRITE_TAC[P2C_OPEN_DROP_GT; IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (real_derivative (real_derivative (p3s_warp g0)))
                      (real_interval[e,A0 + &1])` REAL_COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `abs B` THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; higher_real_derivative] THEN
  ASM_CASES_TAC `s <= A0 + &1` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_WARP_D2_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; higher_real_derivative] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P3S_WARP = prove
 (`!g0 A0. p3_std_initial g0 A0
  ==> smooth_map_on {s | &0 < drop s} (lift o p3s_warp g0 o drop) /\
      (!s. &0 < s ==> &0 < p3s_warp g0 s /\ p3s_warp g0 s <= sqrt(&2)) /\
      (!s. &0 < s ==> &0 <= real_derivative (p3s_warp g0) s /\
                      real_derivative (p3s_warp g0) s <= &1) /\
      (!s. &0 < s ==> higher_real_derivative 2 (p3s_warp g0) s <= &0) /\
      (!e. &0 < e ==> ?B. !s. e <= s
                              ==> abs(higher_real_derivative 2 (p3s_warp g0) s) <= B) /\
      (!s. A0 <= s ==> p3s_warp g0 s = sqrt(&2)) /\
      ((p3s_warp g0) ---> &0) (atreal (&0) within {s | &0 < s}) /\
      ((real_derivative (p3s_warp g0)) ---> &1) (atreal (&0) within {s | &0 < s})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_WARP_SMOOTH THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC P3S_WARP_POS; MATCH_MP_TAC P3S_WARP_LE] THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC P3S_WARPD_NONNEG; MATCH_MP_TAC P3S_WARPD_LE1] THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_WARP_D2_NONPOS THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_WARPD2_BOUND THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_WARP_GE_A0 THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_WARP_LIM0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_WARPD_LIM0 THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]]);;

let P3S_ROT_SEC_TAN_POS = prove
 (`!g0 A0 e. p3_std_initial g0 A0 /\ &0 < e
  ==> ?c. &0 < c /\ !s. e <= s ==> c <= p3s_sec_tan g0 s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3S_KTAN_CAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = min e (r0 / &2)` THEN
  SUBGOAL_THEN `&0 < m /\ m < r0 /\ m <= e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = real_derivative (p3s_warp g0) m` THEN
  SUBGOAL_THEN `&0 <= d /\ d pow 2 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_WARPD_NONNEG THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:real`) THEN ASM_REWRITE_TAC[p3s_sec_tan] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`] P3S_WARP_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < p3s_warp g0 m pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - d pow 2) / &2` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p3s_sec_tan] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_WARP_POS) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_WARP_LE) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3S_WARPD_NONNEG) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `m:real`; `s:real`] P3S_WARPD_DECR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ds = real_derivative (p3s_warp g0) s` THEN
  ABBREV_TAC `fs = p3s_warp g0 s` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < fs pow 2 /\ fs pow 2 <= &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    SUBGOAL_THEN `sqrt(&2) pow 2 = &2` (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `ds pow 2 <= d pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `(&1 - d pow 2) / &2 * &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* MT Lemma 12.37 for every g0 (P2_LEMMA_12_37_STATEMENT).  The              *)
(* radial map is y -> (R/|y|) y with R = rinv(A0 + 4 - sqrt 2 log|y|); its   *)
(* derivative maps the radial part of v exactly onto the cylinder radial    *)
(* part (rinv' = 1/sqrt(a)), and scales tangential vectors by R/|y|, where   *)
(* g0 has the coefficient b(R) with R^2 b(R) = f^2 <= 2.                     *)
(* ========================================================================= *)

let P3S_RADIAL_EQ = prove
 (`!g0 A0 (y:real^3).
     p3_std_initial g0 A0 /\ ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4
     ==> p3_std_radial g0 A0 y =
         (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) * inv(norm y)) % y`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[p3_std_radial; GSYM REAL_NOT_LT] THEN
  ABBREV_TAC `c = A0 + &4 - sqrt(&2) * log(norm(y:real^3))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `x:real^3` THEN
  SUBGOAL_THEN `!z:real^3. p3_std_dist g0 z = p3s_rad_rho g0 (norm z)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P3S_ROT_DIST THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) = p3s_rad_rinv g0 c` ASSUME_TAC THENL
     [SUBGOAL_THEN `p3s_rad_rho g0 (norm(x:real^3)) = c` MP_TAC THENL
       [UNDISCH_TAC `A0 + &4 - sqrt (&2) * log (norm(y:real^3)) = c` THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P3S_RINV_UNIQUE THEN EXISTS_TAC `A0:real` THEN
      ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm(x:real^3) % (inv(norm x) % x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
      SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
      ONCE_REWRITE_TAC[ASSUME `inv(norm x) % x = inv(norm y) % (y:real^3)`] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC]];
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `norm((p3s_rad_rinv g0 c * inv(norm y)) % (y:real^3)) = p3s_rad_rinv g0 c`
    ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_ENTIRE; REAL_INV_EQ_0; NORM_EQ_0;
                    VECTOR_MUL_ASSOC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < p3s_rad_rinv g0 c` THEN UNDISCH_TAC `&0 < norm(y:real^3)` THEN
      CONV_TAC REAL_FIELD;
      UNDISCH_TAC `A0 + &4 - sqrt (&2) * log (norm(y:real^3)) = c` THEN
      REAL_ARITH_TAC]]);;

let P3S_RPROF_DERIV = prove
 (`!g0 A0 t. p3_std_initial g0 A0 /\ &0 < t /\ sqrt(&2) * log t < A0 + &4
     ==> ((\t. p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log t)) has_real_derivative
          (inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log t)))) *
           --(sqrt(&2) * inv t))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. A0 + &4 - sqrt(&2) * log t`; `p3s_rad_rinv g0`;
                 `--(sqrt(&2) * inv t)`;
                 `inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log t))))`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(DISCH_ALL(REAL_DIFF_CONV
      `((\t. A0 + &4 - sqrt(&2) * log t) has_real_derivative f') (atreal t)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC P3S_RINV_DERIV THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let P3S_RADMAP_DERIV = prove
 (`!g0 A0 (y:real^3).
     p3_std_initial g0 A0 /\ ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4
     ==> ((\z. (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm z)) * inv(norm z)) % z)
          has_derivative
          (\h. (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) * inv(norm y)) % h +
               (((inv(sqrt(p3s_rad_a g0
                    (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y))))) *
                  --(sqrt(&2) * inv(norm y))) * inv(norm y) +
                 p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) *
                 --inv(norm y pow 2)) * ((y dot h) / norm y)) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `R = \t. p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log t)` THEN
  SUBGOAL_THEN
   `((\t. R t * inv t) has_real_derivative
     ((inv(sqrt(p3s_rad_a g0 (R(norm(y:real^3))))) * --(sqrt(&2) * inv(norm y))) *
      inv(norm y) + R(norm y) * --inv(norm y pow 2))) (atreal (norm y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:real->real`;
                   `inv(sqrt(p3s_rad_a g0 (R(norm(y:real^3))))) * --(sqrt(&2) * inv(norm y))`;
                   `inv:real->real`; `--inv(norm(y:real^3) pow 2)`; `norm(y:real^3)`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "R" THEN BETA_TAC THEN MATCH_MP_TAC P3S_RPROF_DERIV THEN
        ASM_REWRITE_TAC[];
        MP_TAC(SPEC `norm(y:real^3)` HAS_REAL_DERIVATIVE_INV_BASIC) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (R:real->real) t * inv t`;
                 `(inv(sqrt(p3s_rad_a g0 (R(norm(y:real^3))))) * --(sqrt(&2) * inv(norm y))) *
                  inv(norm y) + R(norm y) * --inv(norm y pow 2)`;
                 `\z:real^3. lift(norm z)`; `\h:real^3. lift((y dot h) / norm y)`;
                 `y:real^3`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; P2C_NORM_DERIV] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. (R:real->real)(norm z) * inv(norm z)`;
                 `\h:real^3. ((inv(sqrt(p3s_rad_a g0 (R(norm(y:real^3))))) *
                               --(sqrt(&2) * inv(norm y))) * inv(norm y) +
                              R(norm y) * --inv(norm y pow 2)) * ((y dot h) / norm y)`;
                 `\z:real^3. z`; `\h:real^3. h`; `y:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; o_DEF] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL];
    EXPAND_TAC "R" THEN REWRITE_TAC[]]);;

let P3S_LEMMA_12_37_ALL = prove
 (`!g0 A0 y v.
          p3_std_initial g0 A0 /\
          ~(y = vec 0) /\
          sqrt (&2) * log (norm y) < A0 + &4
          ==> (jacobian (p3_std_radial g0 A0) (at y) ** v) dot
              (g0 (p3_std_radial g0 A0 y) **
               jacobian (p3_std_radial g0 A0) (at y) **
               v) <=
              v dot (cylinder_flow (&0) y ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `E = exp((A0 + &4) / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. &0 < norm z
               ==> (sqrt(&2) * log(norm z) < A0 + &4 <=> norm z < E)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E" THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM(MATCH_MP EXP_LOG
      (ASSUME `&0 < norm(z:real^3)`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) < E` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `Phi = \z:real^3. (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm z)) *
                      inv(norm z)) % z` THEN
  ABBREV_TAC
   `D = \h:real^3. (p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) *
                    inv(norm y)) % h +
                   (((inv(sqrt(p3s_rad_a g0 (p3s_rad_rinv g0 (A0 + &4 -
                                         sqrt(&2) * log(norm y))))) *
                      --(sqrt(&2) * inv(norm y))) * inv(norm y) +
                     p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y)) *
                     --inv(norm y pow 2)) * ((y dot h) / norm y)) % y` THEN
  SUBGOAL_THEN `((Phi:real^3->real^3) has_derivative D) (at y)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"; "D"] THEN MATCH_MP_TAC P3S_RADMAP_DERIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((p3_std_radial g0 A0) has_derivative D) (at y) /\
    p3_std_radial g0 A0 y = Phi y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `min (norm(y:real^3)) (E - norm y)`] THEN
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      EXPAND_TAC "Phi" THEN MATCH_MP_TAC P3S_RADIAL_EQ THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < norm(z:real^3) /\ norm z < E` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `dist(z:real^3,y) < norm y /\ dist(z,y) < E - norm y` THEN
        NORM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM NORM_POS_LT];
      EXPAND_TAC "Phi" THEN MATCH_MP_TAC P3S_RADIAL_EQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(D:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_HAS_DERIVATIVE_IMP_LINEAR]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT
      (ASSUME `((p3_std_radial g0 A0) has_derivative D) (at y)`))]) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  ABBREV_TAC `c = A0 + &4 - sqrt(&2) * log(norm(y:real^3))` THEN
  ABBREV_TAC `R = p3s_rad_rinv g0 c` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((Phi:real^3->real^3) y) = R /\ ~(Phi y = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                VECTOR_MUL_EQ_0; REAL_ENTIRE; REAL_INV_EQ_0; NORM_EQ_0] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `(Phi:real^3->real^3) y`;
                 `(D:real^3->real^3) v`] P3S_ROT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  MAP_EVERY EXPAND_TAC ["D"; "Phi"] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[DOT_SYM] THEN
  SUBGOAL_THEN `(y:real^3) dot y = norm y pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `R:real`] P3S_RS_AB_SQRT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `R pow 2 * p3s_rad_b g0 R <= &2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`] P3S_WARP_LE) THEN
    ASM_REWRITE_TAC[p3s_warp] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(R * sqrt(p3s_rad_b g0 R)) pow 2 <= sqrt(&2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((v:real^3) dot y) pow 2 <= norm(y:real^3) pow 2 * (v dot v)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN
    REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) pow 2 = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`t = norm(y:real^3)`; `n = (v:real^3) dot v`; `p = (v:real^3) dot y`;
    `aa = p3s_rad_a g0 R`; `bb = p3s_rad_b g0 R`; `sa = sqrt aa`; `s2 = sqrt(&2)`] THEN
  MATCH_MP_TAC(REAL_ARITH `!c. x = b - c /\ &0 <= c ==> x <= b`) THEN
  EXISTS_TAC `(&2 - R pow 2 * bb) * ((n - p pow 2 / t pow 2) / t pow 2)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `sa pow 2 = aa` THEN UNDISCH_TAC `s2 pow 2 = &2` THEN
    SUBGOAL_THEN `~(t = &0) /\ ~(sa = &0) /\ ~(R = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]]]);;

let P3S_LEMMA_12_37 = prove
 (`P2_LEMMA_12_37_STATEMENT`,
  REWRITE_TAC[P2_LEMMA_12_37_STATEMENT; P3S_LEMMA_12_37_ALL]);;

