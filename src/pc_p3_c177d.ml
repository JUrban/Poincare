(* ========================================================================= *)
(* Unit pc_p3_c177d: MT Lemma 17.7, case (2b) (p. 405-406),                 *)
(* the axial estimate for far necks of the standard solution: a far        *)
(* evolving eps_in-neck at (q,tp) of normalized length tp R < 1 + eps_in    *)
(* reaching back to time 0 has its centre at distance > A0 + 5 + 2/e2 from *)
(* the tip, and the distance from the tip moves by less than 2/e2 on its   *)
(* e2-subneck (P3H_177_AXIAL_STATEMENT, proved as P3H_177_AXIAL from       *)
(* Thm 12.5 and the regularity of flow views).                             *)
(* ========================================================================= *)

needs "src/pc_p3_c177c.ml";;
needs "src/pc_p3_s16lim.ml";;
needs "src/pc_p2c_flconv.ml";;
needs "src/pc_p2c_stdgeom.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The axial estimate for the far necks of the standard solution in case    *)
(* (2b) of MT Lemma 17.7, as a statement: a far evolving eps_in-neck at     *)
(* (q,tp) reaching back to time 0 with tp R < 1 + eps_in has its centre far *)
(* from the cap and moves the distance from the tip by less than 2/e2 on    *)
(* its e2-subneck (the initial metric is the exact cylinder there and the   *)
(* flow nearly preserves axial lengths).                                    *)
(* ========================================================================= *)

let P3H_177_AXIAL_STATEMENT = new_definition
 `P3H_177_AXIAL_STATEMENT <=>
    !g0 A0. p3_std_initial g0 A0
      ==> !e2. &0 < e2 /\ e2 <= &1 / &100
          ==> ?KA. &1 <= KA /\
                !eps_in (G:real->real^3->real^3^3) q tp (e:real^3->real^3).
                   &0 < eps_in /\ KA * eps_in <= e2 /\ p3_std_flow g0 (&1) G /\
                   &0 < tp /\ tp < &1 /\
                   rfs_evolving_neck
                     (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                    {s | &0 <= s /\ s < &1} G)
                     eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
                   (!z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) /\
                   tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q < &1 + eps_in
                   ==> &9 / &10 <= mfd_scalar (open_set_atlas (:real^3)) (G tp) q /\
                       A0 + &4 + &2 / e2 + &1 < p3_std_dist g0 q /\
                       (!v. v IN rfs_neck_dom e2
                            ==> abs(p3_std_dist g0 (e v) - p3_std_dist g0 q) < &2 / e2)`;;

(* ========================================================================= *)
(* AXIAL, A5: quadratic-form comparisons of the cylinder flow metrics: for   *)
(* s <= 0, cylinder_flow 0 <= cylinder_flow s <= (1 - s) cylinder_flow 0     *)
(* (the radial part is ds^2 at all times, the sphere part grows by 1 - s).   *)
(* ========================================================================= *)

let P3H_CYL_QF = prove
 (`!s (y:real^3) v.
     ~(y = vec 0)
     ==> v dot (cylinder_flow s y ** v) =
         (&2 / norm y pow 2) * ((&1 - s) * (v dot v) + (s / norm y pow 2) * (y dot v) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cylinder_flow] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_LID;
              DOT_RADD; DOT_RMUL] THEN
  SUBGOAL_THEN `((lambda i j. (y:real^3)$i * y$j):real^3^3) ** v = (y dot v) % y`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; VECTOR_MUL_COMPONENT; dot] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RMUL; DOT_SYM] THEN REAL_ARITH_TAC);;

let P3H_DOT_CS = prove
 (`!(y:real^3) v. (y dot v) pow 2 <= norm y pow 2 * (v dot v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DOT_SQUARE_NORM] THEN
  MP_TAC(ISPECL [`y:real^3`; `v:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  REWRITE_TAC[GSYM DOT_SQUARE_NORM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((y:real^3) dot v) pow 2 = abs(y dot v) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
  SUBGOAL_THEN `(y dot y) * (v dot v) = (norm(y:real^3) * norm(v:real^3)) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; NORM_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let P3H_CYL_COMPARE = prove
 (`!s (y:real^3) v.
     s <= &0 /\ ~(y = vec 0)
     ==> v dot (cylinder_flow (&0) y ** v) <= v dot (cylinder_flow s y ** v) /\
         v dot (cylinder_flow s y ** v) <= (&1 - s) * (v dot (cylinder_flow (&0) y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[P3H_CYL_QF] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`y:real^3`; `v:real^3`] P3H_DOT_CS) THEN DISCH_TAC THEN
  ABBREV_TAC `n2 = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `p = (y:real^3) dot v` THEN ABBREV_TAC `w = (v:real^3) dot v` THEN
  SUBGOAL_THEN `&0 <= &2 / n2 /\ p pow 2 / n2 <= w /\ &0 <= p pow 2 / n2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; REAL_LE_POW_2; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s / n2) * p pow 2 = s * (p pow 2 / n2)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LZERO; real_div; REAL_MUL_LZERO; REAL_ADD_RID;
              REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --s * (w - q) ==> w <= (&1 - s) * w + s * q`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(&1 - s) * (&2 / n2 * w) = &2 / n2 * ((&1 - s) * w)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `s * q <= &0 ==> a + s * q <= a`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --s * q ==> s * q <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* AXIAL, A4: an inequality |a - b| <= c b that holds near s0 from the       *)
(* right passes to right limits at s0; applied to the family closeness of    *)
(* a far neck of the standard solution as t -> 0+ it gives the C^0           *)
(* closeness of R e^* g0 to cylinder_flow(-tp R).                            *)
(* ========================================================================= *)

let P3H_RIGHT_LIMIT_LE = prove
 (`!a b c s0 s1 A B.
     s0 < s1 /\ &0 <= c /\
     (!s. s0 < s /\ s <= s1 ==> abs(a s - b s) <= c * b s) /\
     (!e. &0 < e ==> ?d. &0 < d /\
                         !s. s0 < s /\ s < s0 + d ==> abs(a s - A) < e /\ abs(b s - B) < e)
     ==> abs(A - B) <= c * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `dd = abs(A - B) - c * B` THEN
  SUBGOAL_THEN `&0 < dd / (&3 * (&1 + c))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dd / (&3 * (&1 + c))`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = s0 + min d (s1 - s0) / &2` THEN
  SUBGOAL_THEN `s0 < s /\ s <= s1 /\ s < s0 + d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + c) * dd / (&3 * (&1 + c)) = dd / &3` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * abs(b(s:real) - B) <= c * dd / (&3 * (&1 + c))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * dd / (&3 * (&1 + c)) <= dd / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + c) * dd / (&3 * (&1 + c))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * b(s:real) <= c * B + c * abs(b s - B)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dd / (&3 * (&1 + c)) <= dd / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + c) * dd / (&3 * (&1 + c))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* AXIAL, A1: the scalar curvature of a standard flow at a fixed point is   *)
(* right-continuous at t = 0 (C^infinity convergence of G(t_n) to g0 near   *)
(* the point, P3N_RF_MNEAR and P2CM_LCK_NEAR2, and curvature stability).    *)

let P3H_SCALAR_TIME0 = prove
 (`!g0 A0 (G:real->real^3->real^3^3) (z:real^3) alpha.
     p3_std_initial g0 A0 /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\ G (&0) = g0 /\
     &0 < alpha
     ==> ?mu. &0 < mu /\
              !t. &0 <= t /\ t < mu ==> abs(lscalar (G t) z - lscalar g0 z) <= alpha`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P2CN_STD_RMD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C0:real` o SPEC `0`) THEN
  MP_TAC(SPECL [`sqrt(abs C0)`; `alpha:real`] (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "stab"))) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (:real^3) (g0:real^3->real^3^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(G:real->real^3->real^3^3) (&0) = g0`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)` o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `tt:num->real` (LABEL_TAC "tt")) THEN
  SUBGOAL_THEN `!n:num. &0 <= (tt:num->real) n /\ tt n < &1` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "tt" (MP_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `inv(&n + &1) <= &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> ?N. !n. N <= n ==> abs((tt:num->real) n - &0) < e` ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "tt" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y z e:real. &0 <= x /\ x < y /\ y <= z /\ z < e ==> abs x < e`) THEN
    EXISTS_TAC `inv(&n + &1)` THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    UNDISCH_TAC `~(N = 0)` THEN UNDISCH_TAC `N <= n:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&1`; `G:real->real^3->real^3^3`; `&0`; `tt:num->real`; `z:real^3`]
                P3N_RF_MNEAR) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z:real^3`; `\n:num. (g0:real^3->real^3^3)`;
                 `\n:num. (G:real->real^3->real^3^3) (tt n)`;
                 `g0:real^3->real^3^3`; `2`] P2CM_LCK_NEAR2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[p2cm_mnear] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`&1`; `0`] THEN
        SUBGOAL_THEN `metric_field (ball(z:real^3,&1)) (g0:real^3->real^3^3)` ASSUME_TAC THENL
         [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[OPEN_BALL; SUBSET_UNIV];
          ASM_REWRITE_TAC[REAL_LT_01]];
        MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
        UNDISCH_TAC `metric_field (:real^3) (g0:real^3->real^3^3)` THEN
        REWRITE_TAC[metric_field] THEN STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]];
      UNDISCH_TAC `p2cm_mnear (z:real^3) (\n. (G:real->real^3->real^3^3) (tt n)) g0` THEN
      REWRITE_TAC[p2cm_mnear] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `eta pow 2` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPECL [`N:num`; `z:real^3`])) THEN
  ASM_REWRITE_TAC[LE_REFL; CENTRE_IN_BALL; VECTOR_SUB_RZERO; NORM_LIFT] THEN DISCH_TAC THEN
  USE_THEN "stab" (MP_TAC o SPECL [`(:real^3)`; `g0:real^3->real^3^3`;
                                   `(G:real->real^3->real^3^3) (tt(N:num))`; `z:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  USE_THEN "tt" (MP_TAC o SPEC `N:num`) THEN REAL_ARITH_TAC);;

(* A quadratic form with small entries is small. *)

let P3H_QF_ENTRY_BOUND = prove
 (`!(M:real^3^3) w e.
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> abs(M$i$j) <= e)
     ==> abs(w dot (M ** w)) <= &9 * e * (w dot w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `M:real^3^3` ONORM_LE_MATRIX_COMPONENT_SUM) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_TAC THEN
  SUBGOAL_THEN `onorm(\x:real^3. (M:real^3^3) ** x) <= &9 * e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs((M:real^3^3)$1$1) + abs(M$1$2) + abs(M$1$3)) +
                (abs(M$2$1) + abs(M$2$2) + abs(M$2$3)) +
                (abs(M$3$1) + abs(M$3$2) + abs(M$3$3))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a1 a2 a3 a4 a5 a6 a7 a8 a9 e:real.
      a1 <= e /\ a2 <= e /\ a3 <= e /\ a4 <= e /\ a5 <= e /\ a6 <= e /\ a7 <= e /\ a8 <= e /\
      a9 <= e ==> (a1 + a2 + a3) + (a4 + a5 + a6) + (a7 + a8 + a9) <= &9 * e`) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x:real^3. (M:real^3^3) ** x` ONORM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`w:real^3`; `(M:real^3^3) ** w`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `w dot (w:real^3) = norm w pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(w:real^3) * norm((M:real^3^3) ** w)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(w:real^3) * onorm(\x:real^3. (M:real^3^3) ** x) * norm w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `norm(w:real^3) * onorm(\x:real^3. (M:real^3^3) ** x) * norm w =
                  onorm(\x. M ** x) * (norm w * norm w)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&9 * e * norm(w:real^3) * norm w = (&9 * e) * (norm w * norm w)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_SQUARE]]);;

(* ========================================================================= *)
(* AXIAL support: quadratic forms of the metric along the standard flow.    *)
(* t -> w G(t) w is continuous on [0,b] and, when the sectional curvature   *)
(* is nonnegative for t > 0 (P2_THM_12_5), nonincreasing (dG/dt = -2 Ric).  *)
(* The far scalar curvature of g0 is 1, and the arithmetic of the R bounds. *)
(* ========================================================================= *)

let P3H_QF_EXPAND = prove
 (`!(M:real^3^3) (w:real^3).
     w dot (M ** w) = sum(1..3) (\i. sum(1..3) (\j. (w$i * w$j) * M$i$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_3; SUM_3] THEN
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3] THEN
  REAL_ARITH_TAC);;

let P3H_ARITH_FRAC9 = prove
 (`!e q. &0 < e /\ &0 <= q ==> &9 * (e / (&9 * (&1 + q))) * q < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&9 * (e / (&9 * (&1 + q))) * q = (e * q) / (&1 + q)` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(&1 + q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= q ==> &0 < &1 + q`] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_RF_QF_CONT = prove
 (`!T0 (G:real->real^3->real^3^3) b x w.
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) T0 G /\ b < T0
     ==> (\s. w dot (G s x ** w)) real_continuous_on real_interval[&0,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`T0:real`; `G:real->real^3->real^3^3`; `&0`; `b:real`; `{x:real^3}`]
                P3N_RF_UC) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; COMPACT_SING; IN_SING; DIMINDEX_3] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
  REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (w:real^3) dot w` ASSUME_TAC THENL [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (&9 * (&1 + (w:real^3) dot w))`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t':real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real->real^3->real^3^3) t' x - G t x`; `w:real^3`;
                 `e / (&9 * (&1 + (w:real^3) dot w))`] P3H_QF_ENTRY_BOUND) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_SUB_COMPONENT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB] THEN
  MP_TAC(SPECL [`e:real`; `(w:real^3) dot w`] P3H_ARITH_FRAC9) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3H_RF_QF_NONINCR = prove
 (`!T0 (G:real->real^3->real^3^3) t x w.
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) T0 G /\
     (!s y u v. &0 < s /\ s < T0 /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (G s) y u v) /\
     &0 <= t /\ t < T0
     ==> w dot (G t x ** w) <= w dot (G (&0) x ** w)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) T0
                   (G:real->real^3->real^3^3)`) THEN
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. w dot ((G:real->real^3->real^3^3) s x ** w)`;
                 `\s. --(&2) * (w dot (mfd_ricci_matrix (open_set_atlas (:real^3))
                                         ((G:real->real^3->real^3^3) s) x ** w))`;
                 `&0`; `t:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3H_RF_QF_CONT THEN EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[P3H_QF_EXPAND] THEN
      SUBGOAL_THEN
       `--(&2) * sum(1..3) (\i. sum(1..3) (\j. ((w:real^3)$i * w$j) *
          mfd_ricci_matrix (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) z) x$i$j)) =
        sum(1..3) (\i. sum(1..3) (\j. (w$i * w$j) *
          (--(&2) * mfd_ricci_matrix (open_set_atlas (:real^3)) (G z) x$i$j)))`
      SUBST1_TAC THENL [REWRITE_TAC[SUM_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `has_real_derivative`)) (concl th))) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; DIMINDEX_3] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= w dot (mfd_ricci_matrix (open_set_atlas (:real^3))
                              ((G:real->real^3->real^3^3) z) x ** w)` ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_ricci_matrix (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) z) x =
                  pde_lricci_matrix (G z) x` SUBST1_TAC THENL
     [REWRITE_TAC[mfd_ricci_matrix; pde_lricci_matrix] THEN
      SIMP_TAC[RFB_OPEN_SET_MFD_RICCI; OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^3)`; `(G:real->real^3->real^3^3) z`; `x:real^3`;
                   `w:real^3`; `w:real^3`] PDE_LRICCI_MATRIX_DOT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_UNIV] THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `T0:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(G:real->real^3->real^3^3) z`; `x:real^3`; `&0`; `w:real^3`]
                  CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      SIMP_TAC[RFB_OPEN_SET_MFD_RICCI; OPEN_UNIV; IN_UNIV; REAL_MUL_LZERO; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term (fun t -> t = `t - &0`)) (concl th))) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&2 * (w dot (mfd_ricci_matrix (open_set_atlas (:real^3))
                              ((G:real->real^3->real^3^3) z) x ** w))) * t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* A2: the scalar curvature of g0 in the far region is that of the cylinder. *)

let P3H_STD_FAR_SCALAR = prove
 (`!g0 A0 (x:real^3).
     p3_std_initial g0 A0 /\ A0 < p3_std_dist g0 x ==> lscalar g0 x = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P2CN_STD_FAR_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` (X_CHOOSE_THEN `W:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 (x:real^3) IN W /\ ~(p3_std_nc g0 A0 x = vec 0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on V W (p3_std_nc g0 A0) (p3s_ncinv g0 A0)` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    UNDISCH_TAC `W SUBSET (:real^3) DELETE vec 0` THEN UNDISCH_TAC `(x:real^3) IN V` THEN
    UNDISCH_TAC `IMAGE (p3_std_nc g0 A0) V = W` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lscalar (mpullback (p3_std_nc g0 A0) (cylinder_flow (&0))) (x:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `V:real^3->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `V:real^3->bool`; `p3_std_nc g0 A0`; `p3s_ncinv g0 A0`;
                 `cylinder_flow (&0)`; `x:real^3`] LSCALAR_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC P3N_CYL0_SCALAR THEN ASM_REWRITE_TAC[]);;

(* A3 arithmetic: |X - 1| <= 1/100 and |X / R - 1/u| <= 1/100 with         *)
(* 1 <= u <= 201/100 give 9/10 <= R <= 21/10.                              *)

let P3H_RB_ARITH = prove
 (`!X R u. &0 < R /\ &1 <= u /\ u <= &201 / &100 /\ abs(X - &1) <= &1 / &100 /\
           abs(X / R - &1 / u) <= &1 / &100
           ==> &9 / &10 <= R /\ R <= &21 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = X / R` THEN
  SUBGOAL_THEN `X = p * R` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / u <= &1 /\ &100 / &201 <= &1 / u` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&100 * inv(&201) = inv(&201 / &100)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_DIV; real_div]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= &101 / &100 /\ &9799 / &20100 <= p` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p * R <= &101 / &100 * R /\ &9799 / &20100 * R <= p * R`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The evolving neck of the standard flow view, unfolded. *)

let P3H_FLOW_ENECK_UNFOLD = prove
 (`!(G:real->real^3->real^3^3) eps q tp a (e:real^3->real^3).
     &0 <= tp /\ tp < &1 /\
     rfs_evolving_neck
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       eps q tp a e
     ==> rfs_neck (euclidean,open_set_atlas (:real^3)) (G tp) eps q e /\ &0 < a /\
         ?d. d < eps pow 2 /\
             !s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
                   ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                         (\z. mfd_scalar (open_set_atlas (:real^3)) (G tp) q %%
                              rfs_pullback (open_set_atlas (:real^3)) e
                                (G (tp + s / mfd_scalar (open_set_atlas (:real^3)) (G tp) q))
                                z) y <= d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_evolving_neck
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       eps q tp a (e:real^3->real^3)` THEN
  ASM_REWRITE_TAC[rfs_evolving_neck; rfs_flow_view; rfs_close_fam; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* AXIAL, A4: the family closeness of a far neck of the standard solution   *)
(* passes to the initial time: R e^* g0 is C^0-close to cylinder_flow(-tp R) *)
(* (P3H_RIGHT_LIMIT_LE with the right continuity of both sides at -tp R).   *)
(* ========================================================================= *)

let P3H_MPB_QF = prove
 (`!R (J:real^3^3) (M:real^3^3) w.
     w dot ((R %% (transp J ** M ** J)) ** w) = R * ((J ** w) dot (M ** (J ** w)))`,
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; GSYM MATRIX_VECTOR_MUL_ASSOC;
              DOT_MATRIX_TRANSP_RMUL]);;

let P3H_CYL_QF_POS = prove
 (`!s (y:real^3) w. s <= &0 /\ ~(y = vec 0) ==> &0 <= w dot (cylinder_flow s y ** w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `w dot (cylinder_flow (&0) y ** w)` THEN
  ASM_SIMP_TAC[P3H_CYL_COMPARE] THEN REWRITE_TAC[P3H_CYL0_QF] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2]);;

let P3H_CYL_QF_AFFINE = prove
 (`!s s0 (y:real^3) w.
     ~(y = vec 0)
     ==> abs(w dot (cylinder_flow s y ** w) - w dot (cylinder_flow s0 y ** w)) <=
         abs(s - s0) * (&2 / norm y pow 2 * (w dot w + (y dot w) pow 2 / norm y pow 2))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P3H_CYL_QF] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (w:real^3) dot w` ASSUME_TAC THENL [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `n2 = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `p = (y:real^3) dot w` THEN ABBREV_TAC `ww = (w:real^3) dot w` THEN
  SUBGOAL_THEN `&2 / n2 * ((&1 - s) * ww + s / n2 * p pow 2) -
                &2 / n2 * ((&1 - s0) * ww + s0 / n2 * p pow 2) =
                (s - s0) * (&2 / n2 * (p pow 2 / n2 - ww))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  SUBGOAL_THEN `&0 <= &2 / n2 /\ &0 <= p pow 2 / n2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&2 / n2) = &2 / n2` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3H_ARITH_FRAC1 = prove
 (`!ee c x. &0 < ee /\ &0 <= c /\ &0 <= x /\ x < ee / (&1 + c) ==> x * c < ee`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `ee / (&1 + c) * c` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `ee / (&1 + c) * c = (ee * c) / (&1 + c)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= c ==> &0 < &1 + c`] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_RF_QF_RIGHT = prove
 (`!(G:real->real^3->real^3^3) tp R (z:real^3) u ee.
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
     &0 < tp /\ tp < &1 /\ &0 < R /\ &0 < ee
     ==> ?dd. &0 < dd /\
              !s. --(tp * R) < s /\ s < --(tp * R) + dd
                  ==> abs(R * (u dot (G (tp + s / R) z ** u)) -
                          R * (u dot (G (&0) z ** u))) < ee`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1`; `G:real->real^3->real^3^3`; `tp:real`; `z:real^3`; `u:real^3`]
                P3H_RF_QF_CONT) THEN
  ASM_REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ee / R`) THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = min del tp` THEN
  SUBGOAL_THEN `&0 < m /\ m <= del /\ m <= tp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `R * m` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tp + s / R /\ tp + s / R < m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!x tp. --tp < x ==> &0 < tp + x`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `!x tp m. x < m - tp ==> tp + x < m`) THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tp + s / R`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]);;

let P3H_TIME0_QF = prove
 (`!(G:real->real^3->real^3^3) k tp R (e:real^3->real^3) S d.
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
     &0 < tp /\ tp < &1 /\ &0 < R /\ open S /\ (!y. y IN S ==> ~(y = vec 0)) /\
     mfd_param euclidean (open_set_atlas (:real^3)) S e /\
     (!s y. --(tp * R) < s /\ s <= &0 /\ y IN S
            ==> lck_dist2 k (cylinder_flow s)
                  (\z. R %% rfs_pullback (open_set_atlas (:real^3)) e (G (tp + s / R)) z) y
                <= d) /\
     &0 <= d
     ==> !y w. y IN S
               ==> abs(w dot ((R %% mpullback e (G (&0)) y) ** w) -
                       w dot (cylinder_flow (--(tp * R)) y ** w))
                   <= sqrt d * (w dot (cylinder_flow (--(tp * R)) y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN X_GEN_TAC `w:real^3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < &1 ==> metric_field (:real^3) ((G:real->real^3->real^3^3) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                   (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[ricci_flow_from; ricci_flow_on];
    ALL_TAC] THEN
  ABBREV_TAC `J = matrix(frechet_derivative (e:real^3->real^3) (at y))` THEN
  SUBGOAL_THEN `!t. w dot ((R %% mpullback (e:real^3->real^3)
                                  ((G:real->real^3->real^3^3) t) y) ** w) =
                    R * ((J ** w) dot (G t (e y) ** (J ** w)))` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "J" THEN REWRITE_TAC[mpullback; P3H_MPB_QF]; ALL_TAC] THEN
  MATCH_MP_TAC P3H_RIGHT_LIMIT_LE THEN
  EXISTS_TAC `\s. w dot ((R %% mpullback (e:real^3->real^3)
                                  ((G:real->real^3->real^3^3) (tp + s / R)) y) ** w)` THEN
  EXISTS_TAC `\s. w dot (cylinder_flow s (y:real^3) ** w)` THEN
  EXISTS_TAC `--(tp * R)` THEN EXISTS_TAC `&0` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < &0`) THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
    (* the closeness for s in (-tp R, 0] *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= tp + s / R /\ tp + s / R < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `!x tp. --tp < x ==> &0 <= tp + x`) THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `!x tp. x <= &0 /\ tp < &1 ==> tp + x < &1`) THEN
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `metric_field S (cylinder_flow s) /\
      metric_field S (\z. R %% rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3)
                                 ((G:real->real^3->real^3^3) (tp + s / R)) z)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN
        MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LRG_METRIC_FIELD_SCALE THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN
        REWRITE_TAC[OPEN_UNIV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `lck_dist2 k (cylinder_flow s)
        (\z. R %% rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3)
                   ((G:real->real^3->real^3^3) (tp + s / R)) z) y <= d`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `S:real^3->bool`; `cylinder_flow s`;
                   `\z. R %% rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3)
                              ((G:real->real^3->real^3^3) (tp + s / R)) z`;
                   `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3)
                    ((G:real->real^3->real^3^3) (tp + s / R)) y =
                  mpullback e (G (tp + s / R)) y` SUBST1_TAC THENL
     [MATCH_MP_TAC P3H_PULLBACK_OSA_SET THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3H_CYL_QF_POS THEN ASM_REWRITE_TAC[]];
    (* right continuity at -tp R *)
    X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `tp:real`; `R:real`; `(e:real^3->real^3) y`;
                   `(J:real^3^3) ** (w:real^3)`; `ee:real`] P3H_RF_QF_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `Cy = &2 / norm(y:real^3) pow 2 *
                     ((w:real^3) dot w + (y dot w) pow 2 / norm y pow 2)` THEN
    SUBGOAL_THEN `&0 <= Cy` ASSUME_TAC THENL
     [EXPAND_TAC "Cy" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
        MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[DOT_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < ee / (&1 + Cy)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `min d1 (ee / (&1 + Cy))` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s < --(tp * R) + min d1 (ee / (&1 + Cy))` THEN
      REWRITE_TAC[REAL_LT_ADD_SUB; REAL_LT_MIN] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`s:real`; `--(tp * R)`; `y:real^3`; `w:real^3`] P3H_CYL_QF_AFFINE) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `!a b c:real. b < c ==> a <= b ==> a < c`) THEN
      MATCH_MP_TAC P3H_ARITH_FRAC1 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      UNDISCH_TAC `s < --(tp * R) + min d1 (ee / (&1 + Cy))` THEN
      UNDISCH_TAC `--(tp * R) < s` THEN
      REWRITE_TAC[REAL_LT_ADD_SUB; REAL_LT_MIN] THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* AXIAL, A3: bounds 9/10 <= R <= 21/10 for the scalar curvature R at the   *)
(* centre of a far evolving neck of the standard flow with normalized       *)
(* length tp R < 1 + eps_in reaching back to time 0 (P3H_NECK_SCALAR near   *)
(* the initial time, the right continuity of R at t = 0 and R(g0) = 1).     *)
(* ========================================================================= *)

let P3H_AXIAL_RBOUNDS = prove
 (`?eps3. &0 < eps3 /\ eps3 <= &1 / &100 /\
     !g0 A0 eps_in (G:real->real^3->real^3^3) q tp (e:real^3->real^3).
        P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
        p3_std_initial g0 A0 /\
        ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
        G (&0) = g0 /\ &0 < eps_in /\ eps_in <= eps3 /\ &0 < tp /\ tp < &1 /\
        rfs_evolving_neck
          (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
          eps_in q tp (tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q) e /\
        A0 < p3_std_dist g0 q /\
        tp * mfd_scalar (open_set_atlas (:real^3)) (G tp) q < &1 + eps_in
        ==> &9 / &10 <= mfd_scalar (open_set_atlas (:real^3)) (G tp) q /\
            mfd_scalar (open_set_atlas (:real^3)) (G tp) q <= &21 / &10`,
  MP_TAC(SPEC `&1 / &100` (INST_TYPE [`:real^3`,`:A`] P3H_NECK_SCALAR)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NS"))) THEN
  EXISTS_TAC `min eps2 (&1 / &100)` THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_MIN] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `eps_in:real`; `q:real^3`; `tp:real`;
                 `tp * R`; `e:real^3->real^3`] P3H_FLOW_ENECK_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) tp) eps_in q e` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN sphere(vec 0,&1) /\ (e:real^3->real^3) y0 = q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) tp) eps_in q e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps_in` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps_in:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`; `q:real^3`;
                `&1 / &100`] P3H_SCALAR_TIME0) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `q:real^3`] P3H_STD_FAR_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `t1 = min mu tp / &2` THEN
  SUBGOAL_THEN `&0 < t1 /\ t1 < mu /\ t1 < tp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN
    SUBGOAL_THEN `&0 < min mu tp /\ min mu tp <= mu /\ min mu tp <= tp` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s1 = (t1 - tp) * R` THEN
  SUBGOAL_THEN `tp + s1 / R = t1` ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `--(tp * R) < s1 /\ s1 <= &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `--(tp * R) = (&0 - tp) * R`] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= (tp - t1) * R ==> (t1 - tp) * R <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "NS" (MP_TAC o SPECL
   [`rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1}
       (G:real->real^3->real^3^3)`;
    `eps_in:real`; `q:real^3`; `tp:real`; `tp * R`; `e:real^3->real^3`; `s1:real`;
    `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[P2C_FLOW_VIEW_REGULAR_STATEMENT] o check (fun th ->
      can (find_term (fun t -> is_const t &&
                     fst(dest_const t) = "P2C_FLOW_VIEW_REGULAR_STATEMENT")) (concl th))) THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_vscalar; rfs_flow_view] THEN
  SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; OPEN_UNIV; IN_UNIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC P3H_RB_ARITH THEN
  EXISTS_TAC `lscalar ((G:real->real^3->real^3^3) t1) q` THEN EXISTS_TAC `&1 - s1` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ========================================================================= *)
(* AXIAL, A6-A8: the centre of the far neck is far from the tip (exit bound *)
(* at time tp, lengths do not grow backwards along the standard flow since  *)
(* the curvature is nonnegative), and the distance from the tip moves by    *)
(* less than 2/e2 on the e2-subneck (the time-0 metric is at most 5/2 times *)
(* the cylinder metric there; model paths of APX_MODEL_PATH).               *)
(* ========================================================================= *)

let P3H_AXIAL_EXIT_ARITH = prove
 (`!eps R. &0 < eps /\ eps <= &1 / &100 /\ &0 < R /\ R <= &21 / &10
           ==> inv(&2 * eps) <= sqrt(&1 - eps) * inv(sqrt R) * (inv eps - &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM real_div; GSYM SQRT_DIV] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]);;

let P3H_AXIAL_EXIT = prove
 (`!g0 A0 eps_in (G:real->real^3->real^3^3) q tp (e:real^3->real^3).
     p3_std_initial g0 A0 /\
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\ G (&0) = g0 /\
     (!s y u v. &0 < s /\ s < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) (G s) y u v) /\
     &0 < eps_in /\ eps_in <= &1 / &100 /\ &0 <= tp /\ tp < &1 /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) (G tp) eps_in q e /\
     (!z. z IN IMAGE e (rfs_neck_dom eps_in) ==> A0 + &5 <= p3_std_dist g0 z) /\
     mfd_scalar (open_set_atlas (:real^3)) (G tp) q <= &21 / &10
     ==> inv(&2 * eps_in) <= p3_std_dist g0 q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
  MP_TAC(ASSUME `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) tp) eps_in q e`) THEN
  REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN sphere(vec 0,&1) /\ (e:real^3->real^3) y0 = q`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps_in /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps_in:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3) /\
                &0 < A0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC P3N_RF_FIELD THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the exit bound at time tp for curves from q to the tip *)
  SUBGOAL_THEN
   `sqrt(&1 - eps_in) * inv(sqrt R) * (inv eps_in - abs(apx_sval (y0:real^3))) <=
    mfd_dist (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q (vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_DIST_GE_CURVES THEN REWRITE_TAC[P2C_RAD_JOINABLE] THEN
    X_GEN_TAC `gamma:real->real^3` THEN STRIP_TAC THEN
    EXPAND_TAC "R" THEN MATCH_MP_TAC APX_NECK_EXIT THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `e:real^3->real^3`] THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
      can (find_term (fun t -> t = `A0 + &5`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p3_std_dist g0 (vec 0) = &0` SUBST1_TAC THENL
     [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* lengths at time tp are at most those at time 0 *)
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `(G:real->real^3->real^3^3) tp`; `&1`;
                 `q:real^3`; `vec 0:real^3`] P3N_DIST_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; P2C_RAD_JOINABLE; REAL_MUL_LID] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(G:real->real^3->real^3^3) (&0) = g0`)) THEN
    MATCH_MP_TAC P3H_RF_QF_NONINCR THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_dist (euclidean,open_set_atlas (:real^3)) g0 q (vec 0) =
                p3_std_dist g0 q` ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_dist] THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps_in:real`; `R:real`] P3H_AXIAL_EXIT_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt(&1 - eps_in) * inv(sqrt R) * (inv eps_in - abs(apx_sval (y0:real^3))) <=
    mfd_dist (euclidean,open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q (vec 0)` THEN
  ASM_REWRITE_TAC[REAL_ABS_0] THEN ASM_REAL_ARITH_TAC);;

(* A7 arithmetic: sqrt(5/2) (a + sqrt 2 pi) < 2 / e2 for a < 1/e2, e2 <= 1/100. *)

let P3H_UPPER_ARITH = prove
 (`!e2 a. &0 < e2 /\ e2 <= &1 / &100 /\ &0 <= a /\ a < inv e2
          ==> sqrt(&5 / &2) * (a + sqrt(&2) * pi) < &2 / e2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&5 / &2) <= &8 / &5` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * pi <= &6 /\ &0 <= sqrt(&2) * pi` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) <= &3 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `pi <= &4` ASSUME_TAC THENL
     [MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[PI_POS_LE];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[PI_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&100 <= inv e2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &100)` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&8 / &5 * (a + sqrt(&2) * pi)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC);;

(* A4 consequence: the pullback of g0 is at most 5/2 times the cylinder.   *)

let P3H_PB_UPPER_ARITH = prove
 (`!R Q C1 C0 sd L.
     &9 / &10 <= R /\ &0 <= sd /\ sd <= &1 / &100 /\ &0 <= L /\ L <= &101 / &100 /\
     &0 <= C0 /\ C0 <= C1 /\ C1 <= (&1 + L) * C0 /\ abs(R * Q - C1) <= sd * C1
     ==> Q <= &5 / &2 * C0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sd * C1 <= &1 / &100 * C1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + L) * C0 <= &201 / &100 * C0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * (&5 / &2 * R - &9 / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R * Q <= R * (&5 / &2 * C0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN
  ASM_REAL_ARITH_TAC);;

let P3H_TIME0_PB_UPPER = prove
 (`!(G:real->real^3->real^3^3) eps_in tp R (e:real^3->real^3) d.
     ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1) G /\
     &0 < eps_in /\ eps_in <= &1 / &100 /\ &0 < tp /\ tp < &1 /\
     &9 / &10 <= R /\ tp * R < &1 + eps_in /\
     mfd_param euclidean (open_set_atlas (:real^3)) (rfs_neck_dom eps_in) e /\
     (!s y. --(tp * R) < s /\ s <= &0 /\ y IN rfs_neck_dom eps_in
            ==> lck_dist2 (rfs_kreg eps_in) (cylinder_flow s)
                  (\z. R %% rfs_pullback (open_set_atlas (:real^3)) e (G (tp + s / R)) z) y
                <= d) /\
     &0 <= d /\ d < eps_in pow 2
     ==> !y w. y IN rfs_neck_dom eps_in
               ==> w dot (rfs_pullback (open_set_atlas (:real^3)) e (G (&0)) y ** w) <=
                   &5 / &2 * (w dot (cylinder_flow (&0) y ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `rfs_kreg eps_in`; `tp:real`; `R:real`;
                 `e:real^3->real^3`; `rfs_neck_dom eps_in`; `d:real`] P3H_TIME0_QF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[APX_SVAL_NECK_DOM]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `w:real^3`]) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[P3H_PULLBACK_OSA_SET; OPEN_UNIV; IN_UNIV] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tp * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`--(tp * R)`; `y:real^3`; `w:real^3`] P3H_CYL_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - --x = &1 + x`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt d /\ sqrt d <= &1 / &100` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps_in pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC P3H_PB_UPPER_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`R:real`; `w dot (cylinder_flow (--(tp * R)) y ** w)`; `sqrt d`; `tp * R`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`&0`; `y:real^3`; `w:real^3`] P3H_CYL_QF_POS) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P3H_AXIAL_UPPER = prove
 (`!g0 A0 eps_in e2 (G:real->real^3->real^3^3) q tp (e:real^3->real^3) v.
     p3_std_initial g0 A0 /\
     &0 < eps_in /\ eps_in <= e2 /\ e2 <= &1 / &100 /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) (G tp) eps_in q e /\
     (!y w. y IN rfs_neck_dom eps_in
            ==> w dot (rfs_pullback (open_set_atlas (:real^3)) e g0 y ** w) <=
                &5 / &2 * (w dot (cylinder_flow (&0) y ** w))) /\
     v IN rfs_neck_dom e2
     ==> abs(p3_std_dist g0 (e v) - p3_std_dist g0 q) < &2 / e2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ASSUME `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) tp) eps_in q e`) THEN
  REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN sphere(vec 0,&1) /\ (e:real^3->real^3) y0 = q`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps_in /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps_in:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps_in` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps_in:real`; `e2:real`] APX_NECK_DOM_MONO) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  ABBREV_TAC `D = rfs_neck_dom eps_in` THEN
  SUBGOAL_THEN `open (D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[APX_NECK_DOM_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^3->bool`; `y0:real^3`; `v:real^3`] APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    UNDISCH_TAC `(y0:real^3) IN D` THEN UNDISCH_TAC `(v:real^3) IN D` THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (D:real^3->bool))
                                      (open_set_atlas D)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `D:real^3->bool`; `e:real^3->real^3`;
                 `rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3) g0`;
                 `c:real->real^3`; `&0`; `&1`] MFD_PARAM_C1_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[rfs_pullback] THEN REWRITE_TAC[GSYM rfs_pullback] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> (c:real->real^3) t IN D` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                   `c:real->real^3`; `&0`; `&1`; `t:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_REAL_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                 `cylinder_flow (&0)`;
                 `rfs_pullback (open_set_atlas (:real^3)) (e:real^3->real^3) g0`;
                 `&5 / &2`; `c:real->real^3`; `&0`; `&1`] MFD_LENGTH_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "D" THEN REWRITE_TAC[APX_NECK_CYL_FIELD];
      MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `&5 / &2`)) (concl th))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `(e:real^3->real^3) o (c:real->real^3)`;
                 `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `vec 0:real^3`; `(e:real^3->real^3) v`;
                 `vec 0:real^3`; `q:real^3`] MFD_DIST_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[P2C_RAD_JOINABLE] THEN
  SUBGOAL_THEN `mfd_dist (euclidean,open_set_atlas (:real^3)) g0 (vec 0) (vec 0:real^3) = &0 /\
                mfd_dist (euclidean,open_set_atlas (:real^3)) g0 ((e:real^3->real^3) v) q =
                mfd_dist (euclidean,open_set_atlas (:real^3)) g0 q (e v)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_REFL THEN ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
      MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p3_std_dist; REAL_ADD_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(apx_sval (v:real^3)) < inv e2` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(SPECL [`e2:real`; `abs(apx_sval (v:real^3))`] P3H_UPPER_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&5 / &2) * mfd_length (open_set_atlas D) (cylinder_flow (&0)) (c:real->real^3) (&0) (&1)
    <= sqrt(&5 / &2) * (abs(apx_sval (v:real^3)) + sqrt(&2) * pi)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      UNDISCH_TAC `mfd_length (open_set_atlas D) (cylinder_flow (&0)) (c:real->real^3) (&0) (&1)
                   <= abs(apx_sval y0 - apx_sval v) + sqrt(&2) * pi` THEN
      ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* AXIAL assembled: P3H_177_AXIAL_STATEMENT from Thm 12.5 (nonnegative      *)
(* curvature of the standard flow) and the regularity of flow views.        *)
(* ========================================================================= *)

let P3H_KA_ARITH = prove
 (`!e2 eps3 A0 eps_in.
     &0 < e2 /\ &0 < eps3 /\ &0 < eps_in /\ &0 < A0 /\
     (&1 + e2 / eps3 + &2 * e2 * (A0 + &6) + &4) * eps_in <= e2
     ==> eps_in <= eps3 /\ eps_in <= e2 /\ A0 + &4 + &2 / e2 + &1 < inv(&2 * eps_in)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= e2 / eps3 * eps_in /\ &0 <= &2 * e2 * (A0 + &6) * eps_in`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * e2 * (A0 + &6) * eps_in + &4 * eps_in <= e2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `e2 * (eps_in / eps3) <= e2 * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e2 / eps3 * eps_in` THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&2 * (A0 + &6) * eps_in + &4 * eps_in / e2 <= &1` ASSUME_TAC THENL
     [SUBGOAL_THEN `&2 * (A0 + &6) * eps_in + &4 * eps_in / e2 =
                    (&2 * e2 * (A0 + &6) * eps_in + &4 * eps_in) / e2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < e2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &2 * eps_in` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC]);;

let P3H_177_AXIAL = prove
 (`P2_THM_12_5_STATEMENT /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)
   ==> P3H_177_AXIAL_STATEMENT`,
  STRIP_TAC THEN REWRITE_TAC[P3H_177_AXIAL_STATEMENT] THEN
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RB"))) P3H_AXIAL_RBOUNDS THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  X_GEN_TAC `e2:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  EXISTS_TAC `&1 + e2 / eps3 + &2 * e2 * (A0 + &6) + &4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!a b. &0 <= a /\ &0 <= b ==> &1 <= &1 + a + b + &4`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps_in:real`; `G:real->real^3->real^3^3`; `q:real^3`; `tp:real`;
                       `e:real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`e2:real`; `eps3:real`; `A0:real`; `eps_in:real`] P3H_KA_ARITH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) (&1)
                  (G:real->real^3->real^3^3) /\ G (&0) = g0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_flow g0 (&1) (G:real->real^3->real^3^3)` THEN
    SIMP_TAC[p3_std_flow; p3_partial_std];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s y u v. &0 < s /\ s < &1 /\ ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional (open_set_atlas (:real^3))
                                     ((G:real->real^3->real^3^3) s) y u v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o
      REWRITE_RULE[P2_THM_12_5_STATEMENT] o check (fun th ->
        concl th = `P2_THM_12_5_STATEMENT`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1`; `G:real->real^3->real^3^3`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar (open_set_atlas (:real^3)) ((G:real->real^3->real^3^3) tp) q` THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `eps_in:real`; `q:real^3`; `tp:real`;
                 `tp * R`; `e:real^3->real^3`] P3H_FLOW_ENECK_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `A0 < p3_std_dist g0 q` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) tp) eps_in q e` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3` o check (fun th ->
      can (find_term (fun t -> t = `A0 + &5`)) (concl th))) THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `eps_in:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "RB" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps_in:real`;
    `G:real->real^3->real^3^3`; `q:real^3`; `tp:real`; `e:real^3->real^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps_in:real`;
                  `G:real->real^3->real^3^3`; `q:real^3`; `tp:real`; `e:real^3->real^3`]
                 P3H_AXIAL_EXIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps_in:real`; `e2:real`;
                `G:real->real^3->real^3^3`; `q:real^3`; `tp:real`; `e:real^3->real^3`;
                `v:real^3`] P3H_AXIAL_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `(G:real->real^3->real^3^3) (&0) = g0`)) THEN
  MATCH_MP_TAC P3H_TIME0_PB_UPPER THEN
  MAP_EVERY EXISTS_TAC [`tp:real`; `R:real`; `max d (&0)`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_MAX_LT; REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3))
                   ((G:real->real^3->real^3^3) tp) eps_in q e` THEN
    SIMP_TAC[rfs_neck];
    REPEAT STRIP_TAC THEN DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]]);;

