(* ========================================================================= *)
(* Unit pc_p2a_wk3: the derivative of the reduced distance of a flow at its  *)
(* differentiability points: the combined comparison family of pc_p2a_wk2 is *)
(* an upper barrier at the end point of a minimizer with an explicit first   *)
(* order expansion (first variation through the Euler-Lagrange identity, and *)
(* the Hamiltonian along L-geodesics), so at a point where l is              *)
(* differentiable, dl = G X and l_tau = (R - X.G X)/2 - l/(2 tau) with X the *)
(* tau-velocity of the minimizer at its end.  Headlines: the two statements  *)
(* P2AW_FLOW_LX_DERIV_STATEMENT and P2AW_FLOW_MIN_END_STATEMENT of           *)
(* pc_p2a_lxreq.                                                             *)
(* ========================================================================= *)

needs "src/pc_p2a_wk2.ml";;
needs "src/pc_p2a_smz.ml";;
needs "src/pc_p2a_lxreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A lower bound of the scalar curvature of a flow with bounded curvature    *)
(* (abs R <= 6 abs Rm, P2AZ_MFD_SCALAR_ABS).                                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_CBFLOW_METRICS = prove
 (`!top atlas a b (g:real->A->real^3^3).
     p2a_cbflow (top,atlas) a b g
     ==> smooth_manifold_atlas top atlas /\
         (!t. a <= t /\ t <= b ==> riemannian_metric atlas (g t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_cbflow; ricci_flow_from; p2a_flow_upto; ricci_flow_on] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2AW_CBFLOW_SCAL_LOWER = prove
 (`!top atlas a b (g:real->A->real^3^3).
     p2a_cbflow (top,atlas) a b g
     ==> ?m. !t y. a <= t /\ t <= b /\ y IN topspace top ==> m <= mfd_scalar atlas (g t) y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_CBFLOW_METRICS) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `K:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
                CONJUNCT2 o GEN_REWRITE_RULE I [p2a_cbflow]) THEN
  EXISTS_TAC `--(&6 * K)` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `y:A`] P2AZ_MFD_SCALAR_ABS) THEN
  ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:A`] o check (fun th ->
    can (find_term ((=) `K:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The first order expansion of the s-form length of the                     *)
(* combined family p2aw_cfam y s1 sb w k at (w,k) = (0,1): the error is     *)
(* quadratic in (abs(k - 1) + norm w), and the linear part is               *)
(*   (k - 1) * p2aw_cfk + p2aw_cfw w                                          *)
(* (integrals of lagf and of its directional derivatives along the curve).  *)
(* ------------------------------------------------------------------------- *)

let p2aw_zc = new_definition
 `p2aw_zc (y:real^1->real^N) (A:real^1->real^N) (tt:real) (s:real) =
    pastecart (pastecart (lift(tt - s pow 2)) (y(lift s))) (A(lift s))`;;

let p2aw_cfk = new_definition
 `p2aw_cfk (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) (A:real^1->real^N) s1 sb =
    real_integral (real_interval[s1,sb])
      (\s. p2aw_lagf Gt tt (p2aw_zc y A tt s) +
           p2aw_d1 (p2aw_lagf Gt tt)
             (pastecart (pastecart (lift(--(&2 * s * (s - s1)))) (vec 0)) (--(A(lift s))))
             (p2aw_zc y A tt s))`;;

let p2aw_cfw = new_definition
 `p2aw_cfw (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) (A:real^1->real^N) s1 sb
           (w:real^N) =
    real_integral (real_interval[s1,sb])
      (\s. p2aw_d1 (p2aw_lagf Gt tt)
             (pastecart (pastecart (vec 0) (((s - s1) / (sb - s1)) % w)) (inv(sb - s1) % w))
             (p2aw_zc y A tt s))`;;

let P2AW_D1_PATH_CONT = prove
 (`!(s:real^M->bool) (f:real^M->real) (Z:real^1->real^M) (E:real^1->real^M) k.
     open s /\ smooth_map_on s (\y. lift(f y)) /\
     Z continuous_on k /\ E continuous_on k /\ (!v. v IN k ==> Z v IN s)
     ==> (\v. lift(p2aw_d1 f (E v) (Z v))) continuous_on k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\v. vsum(1..dimindex(:M))
                    (\i. (E:real^1->real^M) v$i %
                         lift(p2aw_d1 (f:real^M->real) (basis i) ((Z:real^1->real^M) v)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^M->real`; `(E:real^1->real^M) v`; `(Z:real^1->real^M) v`]
                  P2AW_D1_EXPAND) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL];
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(\v. lift(p2aw_d1 (f:real^M->real) (basis i) ((Z:real^1->real^M) v))) =
                    (\y. lift(p2aw_d1 f (basis i) y)) o Z` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC P2AW_D1_SMOOTH THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]]]);;

let P2AW_INTEGRAL_DIFF4 = prove
 (`!f g h j c a b C.
     a <= b /\ &0 <= C /\
     f real_integrable_on real_interval[a,b] /\ g real_integrable_on real_interval[a,b] /\
     h real_integrable_on real_interval[a,b] /\ j real_integrable_on real_interval[a,b] /\
     (!s. a <= s /\ s <= b ==> abs(f s - g s - (c * h s + j s)) <= C)
     ==> abs(real_integral (real_interval[a,b]) f - real_integral (real_interval[a,b]) g -
             (c * real_integral (real_interval[a,b]) h + real_integral (real_interval[a,b]) j))
         <= C * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (f:real->real) s - g s - (c * h s + j s)`; `\s:real. &0`; `a:real`; `b:real`;
                 `C:real`] P2AW_INTEGRAL_DIFF1) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_LMUL;
               REAL_INTEGRABLE_0; REAL_SUB_RZERO; ETA_AX] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_SUB; REAL_INTEGRAL_ADD; REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_ADD;
               REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_SUB; REAL_INTEGRAL_0; REAL_SUB_RZERO;
               ETA_AX]);;

let P2AW_D1_COMB = prove
 (`!(f:real^M->real) a u v x.
     (\y. lift(f y)) differentiable (at x)
     ==> p2aw_d1 f (a % u + v) x = a * p2aw_d1 f u x + p2aw_d1 f v x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL]);;

let P2AW_NORM_PASTECART3 = prove
 (`!(a:real^M) (b:real^N) (c:real^P) x.
     norm a + norm b + norm c <= x ==> norm(pastecart (pastecart a b) c) <= x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`pastecart (a:real^M) (b:real^N)`; `c:real^P`] NORM_PASTECART_LE) THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^N`] NORM_PASTECART_LE) THEN ASM_REAL_ARITH_TAC);;

let P2AW_ZC_CONT = prove
 (`!(y:real^1->real^N) A tt a b.
     y continuous_on interval[lift a,lift b] /\ A continuous_on interval[lift a,lift b]
     ==> (\v. p2aw_zc y A tt (drop v)) continuous_on interval[lift a,lift b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_zc; LIFT_DROP; ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP; CONTINUOUS_ON_ID]);;

let P2AW_LAGF_D1_CURVE_CONT = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A
    (E:real^1->real^((1,N)finite_sum,N)finite_sum) a b.
     lrg_lsmooth U ta tb Gt /\
     y continuous_on interval[lift a,lift b] /\ A continuous_on interval[lift a,lift b] /\
     E continuous_on interval[lift a,lift b] /\
     (!s. a <= s /\ s <= b
          ==> pastecart (lift(tt - s pow 2)) (y(lift s)) IN interval(lift ta,lift tb) PCROSS U)
     ==> (\s. p2aw_d1 (p2aw_lagf Gt tt) (E(lift s)) (p2aw_zc y A tt s))
         real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                               ((E:real^1->real^((1,N)finite_sum,N)finite_sum) v)
                               (p2aw_zc (y:real^1->real^N) A tt (drop v))`;
                 `a:real`; `b:real`] P2A_REAL_CONT_OF_VEC) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2AW_D1_PATH_CONT THEN
  EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; P2AW_LAGF_SMOOTH; P2AW_ZC_CONT] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; p2aw_zc; PASTECART_IN_PCROSS; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th))) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]);;

let P2AW_LAGF_D1_CURVE_INTEGRABLE = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A
    (E:real^1->real^((1,N)finite_sum,N)finite_sum) a b.
     lrg_lsmooth U ta tb Gt /\
     y continuous_on interval[lift a,lift b] /\ A continuous_on interval[lift a,lift b] /\
     E continuous_on interval[lift a,lift b] /\
     (!s. a <= s /\ s <= b
          ==> pastecart (lift(tt - s pow 2)) (y(lift s)) IN interval(lift ta,lift tb) PCROSS U)
     ==> (\s. p2aw_d1 (p2aw_lagf Gt tt) (E(lift s)) (p2aw_zc y A tt s))
         real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MP_TAC(ISPECL [`\v:real^1. p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                               ((E:real^1->real^((1,N)finite_sum,N)finite_sum) v)
                               (p2aw_zc (y:real^1->real^N) A tt (drop v))`;
                 `a:real`; `b:real`] P2A_REAL_CONT_OF_VEC) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2AW_D1_PATH_CONT THEN
  EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; P2AW_LAGF_SMOOTH; P2AW_ZC_CONT] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; p2aw_zc; PASTECART_IN_PCROSS; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th))) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]);;

let P2AW_MU_CONT = prove
 (`!s1 sb (w:real^N) k. (\v:real^1. ((drop v - s1) / (sb - s1)) % w) continuous_on k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `v:real^1` THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
  EXISTS_TAC `inv(sb - s1) % (w:real^N)` THEN
  MP_TAC(ISPECL [`w:real^N`; `inv(sb - s1)`; `--(s1 * inv(sb - s1))`; `at(v:real^1)`]
                P2AW_AFFINE_VDERIV) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2AW_CFAM_TAYLOR = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt K0 M (y:real^1->real^N) A s1 sb.
     lrg_lsmooth U ta tb Gt /\ compact K0 /\ K0 SUBSET interval(lift ta,lift tb) PCROSS U /\
     &0 <= M /\ &0 <= s1 /\ s1 < sb /\
     (!s. s1 <= s /\ s <= sb
          ==> pastecart (lift(tt - s pow 2)) (y(lift s)) IN K0 /\ norm(A(lift s)) <= M /\
              (y has_vector_derivative A(lift s)) (at (lift s))) /\
     A continuous_on interval[lift s1,lift sb]
     ==> ?d C. &0 < d /\ &0 <= C /\
           !w k. abs(k - &1) <= d /\ norm w <= d
                 ==> abs(p2a_cL Gt tt (p2aw_cfam y s1 sb w k) s1 (s1 + k * (sb - s1)) -
                         p2a_cL Gt tt y s1 sb -
                         ((k - &1) * p2aw_cfk Gt tt y A s1 sb + p2aw_cfw Gt tt y A s1 sb w))
                     <= C * (abs(k - &1) + norm w) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  ABBREV_TAC `K1 = (K0:real^(1,N)finite_sum->bool) PCROSS cball(vec 0:real^N,M)` THEN
  SUBGOAL_THEN `compact(K1:real^((1,N)finite_sum,N)finite_sum->bool) /\
                K1 SUBSET (interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; ASSUME `compact(K0:real^(1,N)finite_sum->bool)`] THEN
    REWRITE_TAC[SUBSET_PCROSS; SUBSET_UNIV;
                ASSUME `K0 SUBSET interval(lift ta,lift tb) PCROSS (U:real^N->bool)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `open((interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)) /\
                smooth_map_on ((interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N))
                  (\z. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt z))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; P2AW_LAGF_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `K1:real^((1,N)finite_sum,N)finite_sum->bool`] P2AW_SMOOTH_DIFF_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))))) THEN
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `K1:real^((1,N)finite_sum,N)finite_sum->bool`] P2AW_HESS_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HB"))) THEN
  ABBREV_TAC `Ce = &3 * sb pow 2 + &2 * M + &1 + &2 / (sb - s1)` THEN
  SUBGOAL_THEN `&0 < Ce /\ &0 < sb - s1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN EXPAND_TAC "Ce" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 < a + b + &1 + c`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2; REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min (inv(&2)) (d1 / (&2 * Ce))`;
                        `(sb - s1) * (&2 * B * Ce pow 2 + &2 * B2 * Ce)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `k:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(k - &1) <= inv(&2) /\ abs(k - &1) <= d1 / (&2 * Ce) /\
                norm(w:real^N) <= inv(&2) /\ norm w <= d1 / (&2 * Ce)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < k /\ k <= &2 /\ inv k <= &2 /\ abs(inv k - &1) <= &2 * abs(k - &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 / &2 <= k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      SUBGOAL_THEN `inv k - &1 = (&1 - k) * inv k` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD `~(k = &0) ==> inv k - &1 = (&1 - k) * inv k`) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH `abs(&1 - k) = abs(k - &1)`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x /\ x <= &2 ==> abs x <= &2`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]]];
    ALL_TAC] THEN
  ABBREV_TAC `tq = abs(k - &1) + norm(w:real^N)` THEN
  SUBGOAL_THEN `&0 <= tq /\ abs(k - &1) <= tq /\ norm(w:real^N) <= tq /\
                abs(k - &1) pow 2 <= tq pow 2 /\ abs(k - &1) * norm w <= tq pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tq" THEN
    SUBGOAL_THEN `&0 <= abs(k - &1) /\ &0 <= norm(w:real^N)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the pointwise estimate *)
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                      ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w)
              IN interval(lift ta,lift tb) PCROSS U /\
            abs(k * p2aw_lagf (Gt:real->real^N->real^N^N) tt
                      (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                            (y(lift s) + ((s - s1) / (sb - s1)) % w))
                                 (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))) -
                p2aw_lagf Gt tt (p2aw_zc y A tt s) -
                ((k - &1) *
                 (p2aw_lagf Gt tt (p2aw_zc y A tt s) +
                  p2aw_d1 (p2aw_lagf Gt tt)
                    (pastecart (pastecart (lift(--(&2 * s * (s - s1)))) (vec 0)) (--(A(lift s))))
                    (p2aw_zc y A tt s)) +
                 p2aw_d1 (p2aw_lagf Gt tt)
                   (pastecart (pastecart (vec 0) (((s - s1) / (sb - s1)) % w)) (inv(sb - s1) % w))
                   (p2aw_zc y A tt s)))
            <= (&2 * B * Ce pow 2 + &2 * B2 * Ce) * tq pow 2`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K0:real^(1,N)finite_sum->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `r = s1 + k * (s - s1)` THEN
    SUBGOAL_THEN `&0 <= (s - s1) / (sb - s1) /\ (s - s1) / (sb - s1) <= &1 /\
                  &0 <= s - s1 /\ s - s1 <= sb /\ &0 <= s /\ s <= sb`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    (* time component *)
    SUBGOAL_THEN `s pow 2 - r pow 2 = --((k - &1) * (s - s1) * (&2 * s + (k - &1) * (s - s1))) /\
                  s pow 2 - r pow 2 - (k - &1) * --(&2 * s * (s - s1)) =
                  --((k - &1) pow 2 * (s - s1) pow 2)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `abs(s pow 2 - r pow 2) <= &3 * sb pow 2 * abs(k - &1) /\
                  abs(s pow 2 - r pow 2 - (k - &1) * --(&2 * s * (s - s1))) <=
                  sb pow 2 * abs(k - &1) pow 2`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL; REAL_ABS_POW] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `abs(s - s1) <= sb /\ abs(&2 * s + (k - &1) * (s - s1)) <= &3 * sb`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `abs((k - &1) * (s - s1)) <= sb` MP_TAC THENL
           [REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
            MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(k - &1) * sb * (&3 * sb)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
          REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* velocity component *)
    SUBGOAL_THEN
     `norm(inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) - A(lift s))
      <= &2 * M * abs(k - &1) + &2 / (sb - s1) * norm(w:real^N) /\
      norm(inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w) - A(lift s) -
           ((k - &1) % --(A(lift s)) + inv(sb - s1) % w))
      <= &2 * M * abs(k - &1) pow 2 + &2 / (sb - s1) * abs(k - &1) * norm(w:real^N)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= inv k /\ &0 <= inv(sb - s1)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH
          `c % (a + d % w) - a:real^N = (c - &1) % a + (c * d) % w`] THEN
        MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
        REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * abs(k - &1)) * M` THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
            REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_MUL] THEN
          ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
          REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
        `c % (a + d % w) - a - ((k - &1) % --a + d % w):real^N =
         (c - &1 + (k - &1)) % a + ((c - &1) * d) % w`] THEN
      SUBGOAL_THEN `inv k - &1 + (k - &1) = (k - &1) pow 2 * inv k` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH `norm(a:real^N) <= x /\ norm(b) <= y ==> norm(a + b) <= x + y`) THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_POW] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs(k - &1) pow 2 * &2) * M` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
          REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&2 * abs(k - &1)) * inv(sb - s1) * norm(w:real^N)` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    (* the points and the displacements *)
    ABBREV_TAC `x = p2aw_zc (y:real^1->real^N) A tt s` THEN
    ABBREV_TAC `z = pastecart (pastecart (lift(tt - r pow 2))
                                         ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                              (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))` THEN
    ABBREV_TAC `et = pastecart (pastecart (lift(--(&2 * s * (s - s1)))) (vec 0:real^N))
                               (--((A:real^1->real^N)(lift s)))` THEN
    ABBREV_TAC `ew = pastecart (pastecart (vec 0:real^1) (((s - s1) / (sb - s1)) % w))
                               (inv(sb - s1) % (w:real^N))` THEN
    SUBGOAL_THEN
     `norm(z - x:real^((1,N)finite_sum,N)finite_sum) <= Ce * tq /\
      norm(z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum) <= Ce * tq pow 2`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["z"; "x"; "et"; "ew"] THEN
      REWRITE_TAC[p2aw_zc; GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_SUB] THEN
      REWRITE_TAC[GSYM LIFT_SUB; GSYM LIFT_CMUL; GSYM LIFT_ADD; VECTOR_MUL_RZERO;
                  VECTOR_ADD_RID; VECTOR_ADD_LID; VECTOR_ARITH `(a + b) - a:real^N = b`;
                  VECTOR_SUB_REFL; REAL_ARITH `(tt - r) - (tt - s):real = s - r`] THEN
      CONJ_TAC THEN
      MATCH_MP_TAC P2AW_NORM_PASTECART3 THEN
      REWRITE_TAC[NORM_LIFT; NORM_0; NORM_MUL] THENL
       [EXPAND_TAC "Ce" THEN EXPAND_TAC "tq" THEN
        SUBGOAL_THEN `abs((s - s1) / (sb - s1)) * norm(w:real^N) <= norm w` ASSUME_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= abs(k - &1) * (&2 / (sb - s1)) /\ &0 <= &2 / (sb - s1) /\
                      &0 <= norm w * (&3 * sb pow 2 + &2 * M) /\
                      &0 <= abs(k - &1) * &1 /\ &0 <= norm(w:real^N) * &1`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
          REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
          TRY(MATCH_MP_TAC REAL_LE_DIV) THEN TRY ASM_REAL_ARITH_TAC THEN
          MATCH_MP_TAC REAL_LE_ADD THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2];
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "Ce" THEN
        SUBGOAL_THEN `&0 <= &2 / (sb - s1) * tq pow 2 /\ &0 <= sb pow 2 * tq pow 2 /\
                      &0 <= M * tq pow 2 /\ &0 <= tq pow 2 /\ &0 <= &2 / (sb - s1)`
        STRIP_ASSUME_TAC THENL
         [SUBGOAL_THEN `&0 <= &2 / (sb - s1)` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
          ALL_TAC] THEN
        SUBGOAL_THEN `&2 / (sb - s1) * abs(k - &1) * norm(w:real^N) <= &2 / (sb - s1) * tq pow 2 /\
                      sb pow 2 * abs(k - &1) pow 2 <= sb pow 2 * tq pow 2 /\
                      (&2 * M) * abs(k - &1) pow 2 <= (&2 * M) * tq pow 2`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_POS] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^((1,N)finite_sum,N)finite_sum) IN K1 /\
                  norm(z - x:real^((1,N)finite_sum,N)finite_sum) <= d1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY EXPAND_TAC ["x"; "K1"] THEN
        REWRITE_TAC[p2aw_zc; PASTECART_IN_PCROSS; IN_CBALL_0] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ce * tq` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ce * (&2 * d1 / (&2 * Ce))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          EXPAND_TAC "tq" THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Ce` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    USE_THEN "DB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `z - x:real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `x + (z - x):real^N = z`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `z IN (interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
      EXPAND_TAC "z" THEN SIMP_TAC[PASTECART_IN_PCROSS];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\y. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt y)) differentiable
                  (at (x:real^((1,N)finite_sum,N)finite_sum))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt) (z - x) x =
      (k - &1) * p2aw_d1 (p2aw_lagf Gt tt) et x + p2aw_d1 (p2aw_lagf Gt tt) ew x +
      p2aw_d1 (p2aw_lagf Gt tt) (z - x - ((k - &1) % et + ew)) x`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p2aw_lagf (Gt:real->real^N->real^N^N) tt`; `&1`;
                     `z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum`;
                     `(k - &1) % et + ew:real^((1,N)finite_sum,N)finite_sum`;
                     `x:real^((1,N)finite_sum,N)finite_sum`] P2AW_D1_COMB) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `&1 % (a - b - c) + c:real^N = a - b`] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[P2AW_D1_COMB] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "HB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    USE_THEN "HB" (MP_TAC o SPECL [`x:real^((1,N)finite_sum,N)finite_sum`;
                                   `z - x:real^((1,N)finite_sum,N)finite_sum`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    ABBREV_TAC `nz = norm(z - x:real^((1,N)finite_sum,N)finite_sum)` THEN
    ABBREV_TAC `nzl = norm(z - x - ((k - &1) % et + ew):real^((1,N)finite_sum,N)finite_sum)` THEN
    SUBGOAL_THEN `&0 <= nz /\ &0 <= nzl` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nz"; "nzl"] THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `k * B * nz pow 2 <= &2 * B * Ce pow 2 * tq pow 2 /\
                  abs(k - &1) * B2 * nz <= B2 * Ce * tq pow 2 /\
                  B2 * nzl <= B2 * Ce * tq pow 2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * B * nz pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
          REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tq * B2 * Ce * tq` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
          CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `abs(p2aw_lagf (Gt:real->real^N->real^N^N) tt z - p2aw_lagf Gt tt x -
                     p2aw_d1 (p2aw_lagf Gt tt) (z - x) x) <= B * nz pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt) (z - x) x) <= B2 * nz` THEN
    UNDISCH_TAC `abs(p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                       (z - x - ((k - &1) % et + ew)) x) <= B2 * nzl` THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `k * (B * nz pow 2) + abs(k - &1) * (B2 * nz) + B2 * nzl` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `k * p2aw_lagf (Gt:real->real^N->real^N^N) tt z - p2aw_lagf Gt tt x -
        ((k - &1) * (p2aw_lagf Gt tt x + p2aw_d1 (p2aw_lagf Gt tt) et x) +
         p2aw_d1 (p2aw_lagf Gt tt) ew x) =
        k * (p2aw_lagf Gt tt z - p2aw_lagf Gt tt x - p2aw_d1 (p2aw_lagf Gt tt) (z - x) x) +
        (k - &1) * p2aw_d1 (p2aw_lagf Gt tt) (z - x) x +
        p2aw_d1 (p2aw_lagf Gt tt) (z - x - ((k - &1) % et + ew)) x`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                                   (z - x:real^((1,N)finite_sum,N)finite_sum) x`)) THEN
        CONV_TAC REAL_RING;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs a <= x /\ abs b <= y /\ abs c <= z ==> abs(a + b + c) <= x + y + z`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      UNDISCH_TAC `k * B * nz pow 2 <= &2 * B * Ce pow 2 * tq pow 2` THEN
      UNDISCH_TAC `abs(k - &1) * B2 * nz <= B2 * Ce * tq pow 2` THEN
      UNDISCH_TAC `B2 * nzl <= B2 * Ce * tq pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* integration *)
  SUBGOAL_THEN `(y:real^1->real^N) continuous_on interval[lift s1,lift sb]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    EXISTS_TAC `(A:real^1->real^N)(lift s)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s))
            IN interval(lift ta,lift tb) PCROSS U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      concl th = `K0 SUBSET interval(lift ta,lift tb) PCROSS (U:real^N->bool)`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `s1:real`; `sb:real`; `w:real^N`;
                 `k:real`] P2AW_CFAM_CL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "PT" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 sb =
    real_integral (real_interval[s1,sb])
      (\s. p2aw_lagf Gt tt (p2aw_zc (y:real^1->real^N) A tt s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2aw_zc] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM P2AW_SFAM_ZERO] THEN
    MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                   `s1:real`; `sb:real`; `vec 0:real^N`] P2AW_SFAM_CL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
           (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                 ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                      (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w))))
    real_integrable_on real_interval[s1,sb]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `\v:real^1. pastecart (pastecart (lift(tt - (s1 + k * (drop v - s1)) pow 2))
                                 ((y:real^1->real^N) v + ((drop v - s1) / (sb - s1)) % w))
                                 (inv k % ((A:real^1->real^N) v + inv(sb - s1) % w))`;
                   `s1:real`; `sb:real`] P2AW_LAGF_PATH_INTEGRABLE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[P2AW_TIME_PATH_CONT] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[ETA_AX; P2AW_MU_CONT];
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX]];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "PT" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `k * real_integral (real_interval[s1,sb])
          (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                 (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                       ((y:real^1->real^N)(lift s) + ((s - s1) / (sb - s1)) % w))
                            (inv k % ((A:real^1->real^N)(lift s) + inv(sb - s1) % w)))) =
    real_integral (real_interval[s1,sb])
          (\s. k * p2aw_lagf Gt tt
                 (pastecart (pastecart (lift(tt - (s1 + k * (s - s1)) pow 2))
                                       (y(lift s) + ((s - s1) / (sb - s1)) % w))
                            (inv k % (A(lift s) + inv(sb - s1) % w))))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2aw_cfk; p2aw_cfw] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&2 * B * Ce pow 2 + &2 * B2 * Ce) * tq pow 2) * (sb - s1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_INTEGRAL_DIFF4 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[p2aw_zc] THEN MATCH_MP_TAC P2AW_LAGF_CURVE_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[p2aw_zc] THEN MATCH_MP_TAC P2AW_LAGF_CURVE_INTEGRABLE THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                       `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                       `\v:real^1. pastecart (pastecart (lift(--(&2 * drop v * (drop v - s1))))
                                                        (vec 0:real^N))
                                             (--((A:real^1->real^N) v))`;
                       `s1:real`; `sb:real`] P2AW_LAGF_D1_CURVE_INTEGRABLE) THEN
        REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          REWRITE_TAC[LIFT_NEG; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
          MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
          REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; LIFT_SUB] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
          MATCH_MP_TAC CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[ETA_AX]]];
      MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                     `\v:real^1. pastecart (pastecart (vec 0:real^1)
                                                      (((drop v - s1) / (sb - s1)) % (w:real^N)))
                                           (inv(sb - s1) % w)`;
                     `s1:real`; `sb:real`] P2AW_LAGF_D1_CURVE_INTEGRABLE) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST; P2AW_MU_CONT];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "PT" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of the s-form Lagrangian (as a function of                 *)
(* ((t,y),A)) in a direction with no time component: the first variation    *)
(* integrand of P2A_WEAK_EL,                                                 *)
(*   (1/2) A.(dG(dy)) A + 2 (tt - t) dR(dy) + dA.(G A).                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_HAS_DERIV_EQ_IMP = prove
 (`!(h:real^M->real^N) f g (net:(real^M)net).
     f = g ==> (h has_derivative f) net ==> (h has_derivative g) net`,
  SIMP_TAC[]);;

let P2AW_HAS_DERIV_EQ = prove
 (`!(h:real^M->real^N) f g (net:(real^M)net).
     f = g /\ (h has_derivative f) net ==> (h has_derivative g) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ACCEPT_TAC));;

let P2AW_VDERIV_LIFT_UNIQUE = prove
 (`!(f:real^1->real^1) x a b.
     (f has_vector_derivative lift a) (at x) /\ (f has_vector_derivative lift b) (at x)
     ==> a = b`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`f:real^1->real^1`; `x:real^1`] THEN ASM_REWRITE_TAC[]);;

let P2AW_LAGF_D1_YA = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt t y A dy dA.
     lrg_lsmooth U ta tb Gt /\ ta < t /\ t < tb /\ y IN U
     ==> p2aw_d1 (p2aw_lagf Gt tt) (pastecart (pastecart (vec 0) dy) dA)
                 (pastecart (pastecart (lift t) y) A) =
         inv(&2) * (A dot (mderiv (Gt t) y dy ** A)) +
         &2 * (tt - t) * drop(frechet_derivative (\z. lift(lscalar (Gt t) z)) (at y) dy) +
         dA dot (Gt t y ** A)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Z = pastecart (pastecart (lift t) (y:real^N)) (A:real^N)` THEN
  ABBREV_TAC `e = pastecart (pastecart (vec 0:real^1) (dy:real^N)) (dA:real^N)` THEN
  SUBGOAL_THEN `!u. Z + u % e = pastecart (pastecart (lift t) ((y:real^N) + u % dy))
                                          ((A:real^N) + u % dA)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["Z"; "e"] THEN
    REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  (* the derivative along the line from the general fact *)
  MP_TAC(ISPECL [`(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)`;
                 `p2aw_lagf (Gt:real->real^N->real^N^N) tt`;
                 `Z:real^((1,N)finite_sum,N)finite_sum`;
                 `e:real^((1,N)finite_sum,N)finite_sum`; `&0`] P2AW_LINE_DERIV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL; P2AW_LAGF_SMOOTH; ETA_AX] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP;
                    VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC P2AW_VDERIV_LIFT_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`lift o (\u. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                   ((Z:real^((1,N)finite_sum,N)finite_sum) + u % e)) o drop`;
    `lift(&0)`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the explicit derivative *)
  ASM_REWRITE_TAC[o_DEF; p2aw_lagf; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o (Gt:real->real^N->real^N^N) t)
      differentiable (at y) /\
    (\z. lift(lscalar ((Gt:real->real^N->real^N^N) t) z)) differentiable (at y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN
    UNDISCH_TAC `metric_field U ((Gt:real->real^N->real^N^N) t)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  ABBREV_TAC `Dg = frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                       (Gt:real->real^N->real^N^N) t) (at y)` THEN
  ABBREV_TAC `Dr = frechet_derivative (\z. lift(lscalar ((Gt:real->real^N->real^N^N) t) z))
                                      (at y)` THEN
  SUBGOAL_THEN
   `(((vectorize:real^N^N->real^(N,N)finite_prod) o (Gt:real->real^N->real^N^N) t)
       has_derivative Dg) (at y) /\
    ((\z. lift(lscalar ((Gt:real->real^N->real^N^N) t) z)) has_derivative Dr) (at y) /\
    linear Dg /\ linear Dr`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Dg"; "Dr"] THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS; LINEAR_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\v:real^1. (y:real^N) + drop v % dy) has_derivative (\h. drop h % dy)) (at (lift(&0))) /\
    ((\v:real^1. (A:real^N) + drop v % dA) has_derivative (\h. drop h % dA)) (at (lift(&0)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\v:real^1. (y:real^N)`; `\h:real^1. vec 0:real^N`;
                     `\v:real^1. drop v % (dy:real^N)`; `\h:real^1. drop h % (dy:real^N)`;
                     `at(lift(&0))`] HAS_DERIVATIVE_ADD);
      MP_TAC(ISPECL [`\v:real^1. (A:real^N)`; `\h:real^1. vec 0:real^N`;
                     `\v:real^1. drop v % (dA:real^N)`; `\h:real^1. drop h % (dA:real^N)`;
                     `at(lift(&0))`] HAS_DERIVATIVE_ADD)] THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  (* the quadratic part *)
  SUBGOAL_THEN
   `((\v:real^1. lift(((A:real^N) + drop v % dA) dot
                       ((Gt:real->real^N->real^N^N) t ((y:real^N) + drop v % dy) **
                        (A + drop v % dA))))
     has_vector_derivative
     lift(dA dot (Gt t y ** A) + A dot (mderiv (Gt t) y dy ** A) + A dot (Gt t y ** dA)))
    (at (lift(&0)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN
    MP_TAC(ISPECL [`\v:real^1. (Gt:real->real^N->real^N^N) t ((y:real^N) + drop v % dy)`;
                   `\h:real^1. (Dg:real^N->real^(N,N)finite_prod) (drop h % dy)`;
                   `\v:real^1. (A:real^N) + drop v % dA`; `\h:real^1. drop h % (dA:real^N)`;
                   `\v:real^1. (A:real^N) + drop v % dA`; `\h:real^1. drop h % (dA:real^N)`;
                   `lift(&0)`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(vectorize:real^N^N->real^(N,N)finite_prod) o
                    (\v:real^1. (Gt:real->real^N->real^N^N) t ((y:real^N) + drop v % dy)) =
                    (vectorize o Gt t) o (\v:real^1. y + drop v % dy)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `(\h:real^1. (Dg:real^N->real^(N,N)finite_prod) (drop h % dy)) =
                    Dg o (\h. drop h % dy)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO;
                                                     VECTOR_ADD_RID; LIFT_DROP];
      ALL_TAC] THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    MATCH_MP_TAC P2AW_HAS_DERIV_EQ_IMP THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear (Dg:real^N->real^(N,N)finite_prod)`)] THEN
    REWRITE_TAC[MATRIFY_CMUL; mderiv] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; DOT_RADD;
                GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scalar curvature part *)
  SUBGOAL_THEN
   `((\v:real^1. lift(lscalar ((Gt:real->real^N->real^N^N) t) ((y:real^N) + drop v % dy)))
     has_vector_derivative (Dr:real^N->real^1) dy) (at (lift(&0)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\v:real^1. lift(lscalar ((Gt:real->real^N->real^N^N) t) ((y:real^N) + drop v % dy))) =
                  (\z. lift(lscalar (Gt t) z)) o (\v:real^1. y + drop v % dy)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC P2AW_HAS_DERIV_EQ THEN
    EXISTS_TAC `(Dr:real^N->real^1) o (\h:real^1. drop h % dy)` THEN CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
      REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear (Dr:real^N->real^1)`)];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^N) dot ((Gt:real->real^N->real^N^N) t y ** dA) = dA dot (Gt t y ** A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x:real^1. inv(&2) % lift(((A:real^N) + drop x % dA) dot
                                 ((Gt:real->real^N->real^N^N) t ((y:real^N) + drop x % dy) **
                                  (A + drop x % dA))) +
                 (&2 * (tt - t)) % lift(lscalar (Gt t) (y + drop x % dy)))
     has_vector_derivative
     (inv(&2) % lift(dA dot (Gt t y ** A) + A dot (mderiv (Gt t) y dy ** A) +
                     A dot (Gt t y ** dA)) +
      (&2 * (tt - t)) % (Dr:real^N->real^1) dy)) (at (lift(&0)))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL; VECTOR_MUL_ASSOC];
    ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives along an L-geodesic chart curve: the chain rule for the       *)
(* Lagrangian along the curve, the derivative of A.G A (Euler-Lagrange), and *)
(* the Hamiltonian H = A.G A - lagf, whose derivative is minus the explicit  *)
(* s-derivative of the Lagrangian.                                           *)
(* ------------------------------------------------------------------------- *)

let P2AW_LRICCI_LSMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N). lricci_flow U a b G ==> lrg_lsmooth U a b G`,
  REWRITE_TAC[lricci_flow; lrg_lsmooth] THEN SIMP_TAC[]);;

let P2AW_VDERIV_PASTECART = prove
 (`!(f:real^1->real^M) (g:real^1->real^N) f' g' net.
     (f has_vector_derivative f') net /\ (g has_vector_derivative g') net
     ==> ((\x. pastecart (f x) (g x)) has_vector_derivative pastecart f' g') net`,
  REWRITE_TAC[has_vector_derivative] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(real^1)net`; `f:real^1->real^M`; `g:real^1->real^N`;
                 `\x:real^1. drop x % (f':real^M)`; `\x:real^1. drop x % (g':real^N)`]
                HAS_DERIVATIVE_PASTECART) THEN
  ASM_REWRITE_TAC[PASTECART_CMUL]);;

let P2AW_LAGF_CURVE_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A A' s.
     lrg_lsmooth U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative A') (at (lift s))
     ==> ((\r. p2aw_lagf Gt tt (p2aw_zc y A tt r)) has_real_derivative
          p2aw_d1 (p2aw_lagf Gt tt) (pastecart (pastecart (lift(--(&2 * s))) (A(lift s))) A')
                  (p2aw_zc y A tt s)) (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\r. p2aw_lagf (Gt:real->real^N->real^N^N) tt (p2aw_zc (y:real^1->real^N) A tt r)) o
     drop) =
    (\z. lift(p2aw_lagf Gt tt z)) o
    (\v. pastecart (pastecart (lift(tt - drop v pow 2)) (y v)) ((A:real^1->real^N) v))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; p2aw_zc; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\v:real^1. pastecart (pastecart (lift(tt - drop v pow 2)) ((y:real^1->real^N) v))
                           ((A:real^1->real^N) v))
     has_vector_derivative pastecart (pastecart (lift(--(&2 * s))) (A(lift s))) A')
    (at (lift s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_VDERIV_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AW_VDERIV_PASTECART THEN ASM_REWRITE_TAC[P2A_TIME_SQ_VDERIV; ETA_AX];
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt z)) differentiable
                (at (p2aw_zc (y:real^1->real^N) A tt s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
    ASM_SIMP_TAC[P2AW_LAGF_SMOOTH; OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL] THEN
    REWRITE_TAC[p2aw_zc; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  ABBREV_TAC `D = frechet_derivative (\z. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt z))
                                     (at (p2aw_zc (y:real^1->real^N) A tt s))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `linear (D:real^((1,N)finite_sum,N)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2aw_d1] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC P2AW_HAS_DERIV_EQ THEN
  EXISTS_TAC `(D:real^((1,N)finite_sum,N)finite_sum->real^1) o
              (\h:real^1. drop h % pastecart (pastecart (lift(--(&2 * s))) (A(lift s))) A')` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    ASM_SIMP_TAC[LINEAR_CMUL];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    UNDISCH_TAC `((\v:real^1. pastecart (pastecart (lift(tt - drop v pow 2)) ((y:real^1->real^N) v))
                                        ((A:real^1->real^N) v))
                  has_vector_derivative pastecart (pastecart (lift(--(&2 * s))) (A(lift s))) A')
                 (at (lift s))` THEN
    REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((\z. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt z)) has_derivative D)
                 (at (p2aw_zc (y:real^1->real^N) A tt s))` THEN
    REWRITE_TAC[p2aw_zc; LIFT_DROP]]);;

let P2AW_KIN_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s))
     ==> ((\r. A(lift r) dot (Gt(tt - r pow 2) (y(lift r)) ** A(lift r))) has_real_derivative
          p2aw_d1 (p2aw_lagf Gt tt)
            (pastecart (pastecart (vec 0) (A(lift s))) (p2a_lacc Gt tt s (y(lift s)) (A(lift s))))
            (p2aw_zc y A tt s)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `s:real`] P2A_EL_VECTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. (A:real^1->real^N)(lift r)`;
                 `\r. (Gt:real->real^N->real^N^N)(tt - r pow 2) ((y:real^1->real^N)(lift r)) **
                      (A:real^1->real^N)(lift r)`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                           ((A:real^1->real^N)(lift s))`;
                 `(lambda k. inv(&2) * ((A:real^1->real^N)(lift s) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                               ((y:real^1->real^N)(lift s)) (basis k) ** A(lift s))) +
                       &2 * s pow 2 *
                       drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                               (at (y(lift s))) (basis k))):real^N`;
                 `s:real`] CMPF_DOT_DERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  MATCH_MP_TAC(MESON[]
   `!(f:real^1->real^1) a b. a = b ==> (f has_vector_derivative a) (at (lift s)) ==>
                             (f has_vector_derivative b) (at (lift s))`) THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `tt - s pow 2`; `(y:real^1->real^N)(lift s)`; `(A:real^1->real^N)(lift s)`;
                 `(A:real^1->real^N)(lift s)`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                           ((A:real^1->real^N)(lift s))`] P2AW_LAGF_D1_YA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[p2aw_zc; th]) THEN
  REWRITE_TAC[REAL_ARITH `tt - (tt - x:real) = x`] THEN
  MP_TAC(ISPECL [`\w:real^N. lift(inv(&2) * ((A:real^1->real^N)(lift s) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                               ((y:real^1->real^N)(lift s)) w ** A(lift s))) +
                       &2 * s pow 2 *
                       drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                               (at (y(lift s))) w))`;
                 `(A:real^1->real^N)(lift s)`] P2A_DOT_LAMBDA_LINEAR) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [MATCH_MP_TAC P2A_LLAG_DY_LINEAR THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`;
                 `(y:real^1->real^N)(lift s)`;
                 `(A:real^1->real^N)(lift s)`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                           ((A:real^1->real^N)(lift s))`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2AW_HAM_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s))
     ==> ((\r. A(lift r) dot (Gt(tt - r pow 2) (y(lift r)) ** A(lift r)) -
               p2aw_lagf Gt tt (p2aw_zc y A tt r)) has_real_derivative
          --(p2aw_d1 (p2aw_lagf Gt tt) (pastecart (pastecart (lift(--(&2 * s))) (vec 0)) (vec 0))
                     (p2aw_zc y A tt s))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH) THEN
  SUBGOAL_THEN `(\y. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt y)) differentiable
                (at (p2aw_zc (y:real^1->real^N) A tt s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
    ASM_SIMP_TAC[P2AW_LAGF_SMOOTH; OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL] THEN
    REWRITE_TAC[p2aw_zc; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2aw_lagf (Gt:real->real^N->real^N^N) tt`; `&1`;
                 `pastecart (pastecart (lift(--(&2 * s))) (vec 0:real^N)) (vec 0:real^N)`;
                 `pastecart (pastecart (vec 0:real^1) ((A:real^1->real^N)(lift s)))
                            (p2a_lacc (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                                      (A(lift s)))`;
                 `p2aw_zc (y:real^1->real^N) A tt s`] P2AW_D1_COMB) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID; PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `--(p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
          (pastecart (pastecart (lift(--(&2 * s))) (vec 0)) (vec 0))
          (p2aw_zc (y:real^1->real^N) A tt s)) =
    p2aw_d1 (p2aw_lagf Gt tt)
      (pastecart (pastecart (vec 0) (A(lift s))) (p2a_lacc Gt tt s (y(lift s)) (A(lift s))))
      (p2aw_zc y A tt s) -
    p2aw_d1 (p2aw_lagf Gt tt)
      (pastecart (pastecart (lift(--(&2 * s))) (A(lift s))) (p2a_lacc Gt tt s (y(lift s)) (A(lift s))))
      (p2aw_zc y A tt s)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_KIN_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AW_LAGF_CURVE_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the linear part of the expansion along an L-geodesic chart  *)
(* curve on [s1,sb]: the spatial part is w.G A at the end (first variation,  *)
(* P2A_EL_IDENTITY), the time part is minus (sb - s1) times the Hamiltonian  *)
(* A.G A - lagf at the end (P2AW_HAM_DERIV).                                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_LAGF_D1_DY = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt t y A c w d dA.
     lrg_lsmooth U ta tb Gt /\ ta < t /\ t < tb /\ y IN U
     ==> p2aw_d1 (p2aw_lagf Gt tt) (pastecart (pastecart (vec 0) (c % w)) (d % dA))
                 (pastecart (pastecart (lift t) y) A) =
         c * (inv(&2) * (A dot (mderiv (Gt t) y w ** A)) +
              &2 * (tt - t) * drop(frechet_derivative (\z. lift(lscalar (Gt t) z)) (at y) w)) +
         d * (dA dot (Gt t y ** A))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `t:real`; `y:real^N`; `A:real^N`; `c % (w:real^N)`; `d % (dA:real^N)`]
                P2AW_LAGF_D1_YA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N) t`; `y:real^N`; `A:real^N`;
                 `tt - t`] P2A_LLAG_DY_LINEAR) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`c:real`; `w:real^N`] o MATCH_MP LINEAR_CMUL) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; DOT_LMUL] THEN REAL_ARITH_TAC);;

let P2AW_CFW_EVAL = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s1 sb w.
     lricci_flow U ta tb Gt /\ s1 < sb /\
     (!s. s1 <= s /\ s <= sb ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U) /\
     y continuous_on interval[lift s1,lift sb] /\ A continuous_on interval[lift s1,lift sb] /\
     (!s. s1 < s /\ s < sb
          ==> (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)))
     ==> p2aw_cfw Gt tt y A s1 sb w = w dot (Gt(tt - sb pow 2) (y(lift sb)) ** A(lift sb))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= sb
                    ==> pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s))
                        IN interval(lift ta,lift tb) PCROSS U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> w dot ((Gt:real->real^N->real^N^N)(tt - s pow 2) ((y:real^1->real^N)(lift s)) **
                   (A:real^1->real^N)(lift s)) =
            p2aw_d1 (p2aw_lagf Gt tt) (pastecart (pastecart (vec 0) (&0 % w)) (&1 % w))
                    (p2aw_zc y A tt s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_zc] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                   `tt:real`; `tt - s pow 2`; `(y:real^1->real^N)(lift s)`;
                   `(A:real^1->real^N)(lift s)`; `&0`; `w:real^N`; `&1`; `w:real^N`]
                  P2AW_LAGF_D1_DY) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2aw_cfw] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
   `w dot ((Gt:real->real^N->real^N^N)(tt - sb pow 2) ((y:real^1->real^N)(lift sb)) **
           (A:real^1->real^N)(lift sb)) =
    (\s. ((s - s1) / (sb - s1)) * (w dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))) sb -
    (\s. ((s - s1) / (sb - s1)) * (w dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))) s1`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `(sb - s1) * inv(sb - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\s. ((s - s1) / (sb - s1)) *
                    p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                      (pastecart (pastecart (vec 0) (&0 % w)) (&1 % (w:real^N)))
                      (p2aw_zc (y:real^1->real^N) A tt s)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_d1")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
        MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                       `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                       `\v:real^1. pastecart (pastecart (vec 0:real^1) (&0 % (w:real^N)))
                                             (&1 % w)`;
                       `s1:real`; `sb:real`] P2AW_LAGF_D1_CURVE_CONT) THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the derivative *)
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (y:real^1->real^N)(lift s) IN U`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ta:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((y:real^1->real^N) has_vector_derivative A(lift s)) (at (lift s)) /\
    ((A:real^1->real^N) has_vector_derivative
       p2a_lacc (Gt:real->real^N->real^N^N) tt s (y(lift s)) (A(lift s))) (at (lift s))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `s:real`; `w:real^N`] P2A_EL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\r. w dot ((Gt:real->real^N->real^N^N)(tt - r pow 2) ((y:real^1->real^N)(lift r)) **
                 (A:real^1->real^N)(lift r))) has_real_derivative
     (inv(&2) * (A(lift s) dot (mderiv (Gt(tt - s pow 2)) (y(lift s)) w ** A(lift s))) +
      &2 * s pow 2 *
      drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at (y(lift s))) w)))
    (atreal s)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\r. (r - s1) / (sb - s1)) has_real_derivative inv(sb - s1)) (atreal s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\r:real. r - s1`; `&1 - &0`; `inv(sb - s1)`; `s:real`]
                  HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST];
      REWRITE_TAC[real_div; REAL_SUB_RZERO; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
      (pastecart (pastecart (vec 0) (((s - s1) / (sb - s1)) % w)) (inv(sb - s1) % w))
      (p2aw_zc (y:real^1->real^N) A tt s) =
    (s - s1) / (sb - s1) *
    (inv(&2) * (A(lift s) dot (mderiv (Gt(tt - s pow 2)) (y(lift s)) w ** A(lift s))) +
     &2 * s pow 2 *
     drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at (y(lift s))) w)) +
    inv(sb - s1) * (w dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2aw_zc] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                   `tt:real`; `tt - s pow 2`; `(y:real^1->real^N)(lift s)`;
                   `(A:real^1->real^N)(lift s)`; `(s - s1) / (sb - s1)`; `w:real^N`;
                   `inv(sb - s1)`; `w:real^N`] P2AW_LAGF_D1_DY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ARITH `tt - (tt - x:real) = x`];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[]);;

let P2AW_LAGF_CURVE_CONT = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) (A:real^1->real^N) a b.
     lrg_lsmooth U ta tb Gt /\
     Y continuous_on interval[lift a,lift b] /\ A continuous_on interval[lift a,lift b] /\
     (!s. a <= s /\ s <= b
          ==> pastecart (lift(tt - s pow 2)) (Y(lift s)) IN interval(lift ta,lift tb) PCROSS U)
     ==> (\s. p2aw_lagf Gt tt (pastecart (pastecart (lift(tt - s pow 2)) (Y(lift s))) (A(lift s))))
         real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  SUBGOAL_THEN
   `(lift o (\s. p2aw_lagf (Gt:real->real^N->real^N^N) tt
                   (pastecart (pastecart (lift(tt - s pow 2)) ((Y:real^1->real^N)(lift s)))
                              ((A:real^1->real^N)(lift s)))) o drop) =
    (\z. lift(p2aw_lagf Gt tt z)) o
    (\v. pastecart (pastecart (lift(tt - drop v pow 2)) (Y v)) (A v))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC P2AW_LAGF_SMOOTH THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; PASTECART_IN_PCROSS; IN_UNIV;
                LIFT_DROP] THEN
    X_GEN_TAC `v:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop v`) THEN
    ASM_REWRITE_TAC[LIFT_DROP; PASTECART_IN_PCROSS; IN_INTERVAL_1; DROP_VEC]]);;

let P2AW_CFK_EVAL = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s1 sb.
     lricci_flow U ta tb Gt /\ s1 < sb /\
     (!s. s1 <= s /\ s <= sb ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U) /\
     y continuous_on interval[lift s1,lift sb] /\ A continuous_on interval[lift s1,lift sb] /\
     (!s. s1 < s /\ s < sb
          ==> (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)))
     ==> p2aw_cfk Gt tt y A s1 sb =
         --((sb - s1) * (A(lift sb) dot (Gt(tt - sb pow 2) (y(lift sb)) ** A(lift sb)) -
                         p2aw_lagf Gt tt (p2aw_zc y A tt sb)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lrg_lsmooth]) THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= sb
                    ==> pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s))
                        IN interval(lift ta,lift tb) PCROSS U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> (A:real^1->real^N)(lift s) dot
            ((Gt:real->real^N->real^N^N)(tt - s pow 2) ((y:real^1->real^N)(lift s)) ** A(lift s)) =
            p2aw_d1 (p2aw_lagf Gt tt)
              (pastecart (pastecart (vec 0) (&0 % A(lift s))) (&1 % A(lift s)))
              (p2aw_zc y A tt s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_zc] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                   `tt:real`; `tt - s pow 2`; `(y:real^1->real^N)(lift s)`;
                   `(A:real^1->real^N)(lift s)`; `&0`; `(A:real^1->real^N)(lift s)`; `&1`;
                   `(A:real^1->real^N)(lift s)`] P2AW_LAGF_D1_DY) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `H = \r. (A:real^1->real^N)(lift r) dot
            ((Gt:real->real^N->real^N^N)(tt - r pow 2) ((y:real^1->real^N)(lift r)) ** A(lift r)) -
            p2aw_lagf Gt tt (p2aw_zc y A tt r)` THEN
  REWRITE_TAC[p2aw_cfk] THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
   `--((sb - s1) * ((A:real^1->real^N)(lift sb) dot
                     ((Gt:real->real^N->real^N^N)(tt - sb pow 2) ((y:real^1->real^N)(lift sb)) **
                      A(lift sb)) - p2aw_lagf Gt tt (p2aw_zc y A tt sb))) =
    (\r. --((r - s1) * (H:real->real) r)) sb - (\r. --((r - s1) * H r)) s1`
  SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[REAL_SUB_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
      ALL_TAC] THEN
    EXPAND_TAC "H" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `\s. p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                        (pastecart (pastecart (vec 0) (&0 % (A:real^1->real^N)(lift s)))
                                   (&1 % A(lift s)))
                        (p2aw_zc (y:real^1->real^N) A tt s)` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2aw_d1")) (concl th))) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                       `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                       `\v:real^1. pastecart (pastecart (vec 0:real^1) (&0 % (A:real^1->real^N) v))
                                             (&1 % A v)`;
                       `s1:real`; `sb:real`] P2AW_LAGF_D1_CURVE_CONT) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; ETA_AX] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_CONST; ETA_AX]];
      REWRITE_TAC[p2aw_zc] THEN MATCH_MP_TAC P2AW_LAGF_CURVE_CONT THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the derivative *)
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (y:real^1->real^N)(lift s) IN U`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ta:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "PCROSS")) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((y:real^1->real^N) has_vector_derivative A(lift s)) (at (lift s)) /\
    ((A:real^1->real^N) has_vector_derivative
       p2a_lacc (Gt:real->real^N->real^N^N) tt s (y(lift s)) (A(lift s))) (at (lift s))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `s:real`] P2AW_HAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((H:real->real) has_real_derivative
                 --(p2aw_d1 (p2aw_lagf (Gt:real->real^N->real^N^N) tt)
                      (pastecart (pastecart (lift(--(&2 * s))) (vec 0)) (vec 0))
                      (p2aw_zc (y:real^1->real^N) A tt s))) (atreal s)`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\r. r - s1) has_real_derivative &1) (atreal s)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 = &1 - &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2aw_lagf (Gt:real->real^N->real^N^N) tt (p2aw_zc (y:real^1->real^N) A tt s) +
    p2aw_d1 (p2aw_lagf Gt tt)
      (pastecart (pastecart (lift(--(&2 * s * (s - s1)))) (vec 0)) (--(A(lift s))))
      (p2aw_zc y A tt s) =
    --((s - s1) *
       --(p2aw_d1 (p2aw_lagf Gt tt) (pastecart (pastecart (lift(--(&2 * s))) (vec 0)) (vec 0))
                  (p2aw_zc y A tt s)) + &1 * H s)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(\z. lift(p2aw_lagf (Gt:real->real^N->real^N^N) tt z)) differentiable
                  (at (p2aw_zc (y:real^1->real^N) A tt s))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(interval(lift ta,lift tb) PCROSS (U:real^N->bool)) PCROSS (:real^N)` THEN
      ASM_SIMP_TAC[P2AW_LAGF_SMOOTH; OPEN_PCROSS; OPEN_UNIV; OPEN_INTERVAL] THEN
      REWRITE_TAC[p2aw_zc; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2aw_lagf (Gt:real->real^N->real^N^N) tt`; `s - s1`;
                   `pastecart (pastecart (lift(--(&2 * s))) (vec 0:real^N)) (vec 0:real^N)`;
                   `pastecart (pastecart (vec 0:real^1) (&0 % (A:real^1->real^N)(lift s)))
                              (--(&1) % A(lift s))`;
                   `p2aw_zc (y:real^1->real^N) A tt s`] P2AW_D1_COMB) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; GSYM LIFT_CMUL; VECTOR_MUL_RZERO;
                VECTOR_ADD_LID; VECTOR_ADD_RID; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[VECTOR_ARITH `--(&1) % a:real^N = --a`;
                REAL_ARITH `(s - s1) * --(&2 * s) = --(&2 * s * (s - s1))`] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[p2aw_zc] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                   `tt:real`; `tt - s pow 2`; `(y:real^1->real^N)(lift s)`;
                   `(A:real^1->real^N)(lift s)`; `&0`; `(A:real^1->real^N)(lift s)`; `--(&1)`;
                   `(A:real^1->real^N)(lift s)`] P2AW_LAGF_D1_DY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ARITH `--(&1) % a:real^N = --a`] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[p2aw_zc] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A differentiable function touched from above at z by a function with a    *)
(* first order expansion L + O(|h|^2) has derivative L at z                  *)
(* (DIFFERENTIAL_ZERO_MAXMIN), and the pullback of a matrix field by a map   *)
(* that is the identity near the point.                                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_HAS_DERIVATIVE_TRANSL = prove
 (`!(c:real^M) (net:(real^M)net). ((\w. w - c) has_derivative (\h. h)) net`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\w:real^M. w`; `\h:real^M. h`; `\w:real^M. (c:real^M)`;
                 `\h:real^M. vec 0:real^M`; `net:(real^M)net`] HAS_DERIVATIVE_SUB) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO]);;

let P2AW_TOUCH_DERIV = prove
 (`!(f:real^M->real) (L:real^M->real^1) z d C.
     &0 < d /\ linear L /\ (\w. lift(f w)) differentiable (at z) /\
     (!h. norm h < d ==> f(z + h) <= f z + drop(L h) + C * norm h pow 2)
     ==> frechet_derivative (\w. lift(f w)) (at z) = L`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative (\w. lift((f:real^M->real) w)) (at z)` THEN
  SUBGOAL_THEN `((\w. lift((f:real^M->real) w)) has_derivative D) (at z)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. lift((f:real^M->real) w) - lift(f z) - (L:real^M->real^1)(w - z) -
          C % lift(norm(w - z) pow 2)) has_derivative
     (\h. D h - vec 0 - L h - C % (&2 % lift((z - z) dot h)))) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST];
        SUBGOAL_THEN `(\w:real^M. (L:real^M->real^1)(w - z)) = L o (\w. w - z)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        SUBGOAL_THEN `(L:real^M->real^1) = L o (\h. h)` (fun th ->
          GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN
        REWRITE_TAC[P2AW_HAS_DERIVATIVE_TRANSL]];
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
      SUBGOAL_THEN `(\w:real^M. lift(norm(w - z) pow 2)) = (\x. lift(norm x pow 2)) o (\w. w - z)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `(\h:real^M. &2 % lift((z - z) dot h)) =
                    (\x. &2 % lift((z - z) dot x)) o (\h. h)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [REWRITE_TAC[P2AW_HAS_DERIVATIVE_TRANSL];
        REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. lift((f:real^M->real) w) - lift(f z) - (L:real^M->real^1)(w - z) -
                     C % lift(norm(w - z) pow 2)`;
                 `\h. (D:real^M->real^1) h - vec 0 - (L:real^M->real^1) h -
                      C % (&2 % lift((z - z) dot h))`;
                 `z:real^M`; `ball(z:real^M,d)`] DIFFERENTIAL_ZERO_MAXMIN) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; OPEN_BALL] THEN ANTS_TAC THENL
   [DISJ1_TAC THEN X_GEN_TAC `w:real^M` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_SUB; DROP_CMUL; LIFT_DROP; VECTOR_SUB_REFL; NORM_0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[DROP_VEC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w - z:real^M`) THEN
    REWRITE_TAC[VECTOR_ARITH `z + (w - z):real^M = w`] THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_REFL; DOT_LZERO; LIFT_NUM; VECTOR_MUL_RZERO;
              VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_SUB_EQ] THEN SIMP_TAC[]);;

let P2AW_MPULLBACK_LOCAL_ID = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) z s.
     open s /\ z IN s /\ (!x. x IN s ==> h x = x) ==> mpullback h G z = G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (h:real^N->real^N) (at z) = (\x. x)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `s:real^N->bool`] THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* The chart identification for a flow (the local metric of the region view  *)
(* in a chart of the atlas is the chart metric, its scalar curvature is the  *)
(* manifold scalar curvature), the second order Taylor bound of the square   *)
(* root, and the arithmetic of the touching inequality.                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_RLOCAL_ID = prove
 (`!top atlas a b (g:real->A->real^3^3) U (phi:A->real^3) t q.
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas /\ a < t /\ t <= b /\ q IN U
     ==> p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi) t (phi q) =
         metric_local atlas (U,phi) (g t) (phi q) /\
         lscalar (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g) U b (U,phi) t)
                 (phi q) =
         mfd_scalar atlas (g t) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`; `t:real`;
                   `(U:A->bool),(phi:A->real^3)`; `q:A`] P2A_RLOCAL_SLICE) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT; FST] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[p2a_flow_view; p2a_vmetric] THEN
    MATCH_MP_TAC P2AW_MPULLBACK_LOCAL_ID THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; chart_trans; SND];
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `U:A->bool`; `a:real`; `b:real`; `t:real`; `U:A->bool`; `phi:A->real^3`;
                   `q:A`] P2AZ_RLOCAL_SLICE_FACTS) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
    ANTS_TAC THENL [REWRITE_TAC[p2a_flow_view; rfs_vatlas] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[p2a_flow_view; rfs_vatlas; rfs_vmetric]]);;

let P2AW_SQRT_TAYLOR_ALG = prove
 (`!u v. &0 <= u /\ &0 < v
         ==> abs(u - v - (u pow 2 - v pow 2) / (&2 * v))
             <= (u pow 2 - v pow 2) pow 2 / (&2 * v pow 2 * v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u - v - (u pow 2 - v pow 2) / (&2 * v) = --((u - v) pow 2 / (&2 * v))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < v` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (u - v) pow 2 / (&2 * v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_NEG; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN
   `(u pow 2 - v pow 2) pow 2 / (&2 * v pow 2 * v) - (u - v) pow 2 / (&2 * v) =
    (u - v) pow 2 * (u * (u + &2 * v)) / (&2 * v pow 3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < v` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (u - v) pow 2 * (u * (u + &2 * v)) / (&2 * v pow 3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let P2AW_SQRT_TAYLOR = prove
 (`!t t'. &0 < t /\ &0 <= t'
          ==> abs(sqrt t' - sqrt t - (t' - t) / (&2 * sqrt t))
              <= (t' - t) pow 2 / (&2 * t * sqrt t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sqrt t'`; `sqrt t`] P2AW_SQRT_TAYLOR_ALG) THEN
  ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]);;

let P2AW_TOUCH_ARITH = prove
 (`!f0 f1 Lg cLc cLy k cfk cfw C D st st' dt nh nw tau.
     &0 < D /\ &0 < st /\ &0 < tau /\ &0 <= C /\
     f1 <= Lg + cLc /\ f0 = Lg + cLy /\
     abs(cLc - cLy - ((k - &1) * cfk + cfw)) <= C * (abs(k - &1) + nw) pow 2 /\
     k - &1 = (st' - st) / D /\
     abs(st' - st - dt / (&2 * st)) <= dt pow 2 / (&2 * tau * st) /\
     abs(k - &1) <= nh / (st * D) /\ &0 <= nw /\ nw <= nh /\ abs dt <= nh
     ==> f1 <= f0 + (cfw + cfk / (&2 * st * D) * dt) +
               (abs cfk / D / (&2 * tau * st) + C * (inv(st * D) + &1) pow 2) * nh pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(k - &1) * cfk = cfk / D * (st' - st)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `cfk / D * (st' - st) <= cfk / D * (dt / (&2 * st)) +
                abs cfk / D * (dt pow 2 / (&2 * tau * st))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(x - y) <= e ==> x <= y + e`) THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(cfk / D) = abs cfk / D` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_DIV] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < D ==> abs D = D`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `cfk / D * (dt / (&2 * st)) = cfk / (&2 * st * D) * dt` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * tau * st` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs cfk / D * (dt pow 2 / (&2 * tau * st)) <=
                abs cfk / D / (&2 * tau * st) * nh pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs cfk / D * (dt pow 2 / (&2 * tau * st)) =
                  abs cfk / D / (&2 * tau * st) * dt pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; REAL_LT_IMP_LE];
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * (abs(k - &1) + nw) pow 2 <= C * (inv(st * D) + &1) pow 2 * nh pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nh / (st * D) = inv(st * D) * nh` ASSUME_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= x * nh /\ nw <= nh ==> a + nw <= (x + &1) * nh`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(abs cfk / D / (&2 * tau * st) + C * (inv(st * D) + &1) pow 2) * nh pow 2 =
                abs cfk / D / (&2 * tau * st) * nh pow 2 +
                C * (inv(st * D) + &1) pow 2 * nh pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cLc - cLy - ((k - &1) * cfk + cfw) <= C * (abs(k - &1) + nw) pow 2`
  MP_TAC THENL [ASM_MESON_TAC[REAL_ARITH `abs x <= e ==> x <= e`]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`f1 <= Lg + cLc`; `f0 = Lg + cLy`; `(k - &1) * cfk = cfk / D * (st' - st)`;
    `cfk / D * (st' - st) <= cfk / D * (dt / (&2 * st)) +
     abs cfk / D * (dt pow 2 / (&2 * tau * st))`;
    `cfk / D * (dt / (&2 * st)) = cfk / (&2 * st * D) * dt`;
    `abs cfk / D * (dt pow 2 / (&2 * tau * st)) <= abs cfk / D / (&2 * tau * st) * nh pow 2`;
    `C * (abs(k - &1) + nw) pow 2 <= C * (inv(st * D) + &1) pow 2 * nh pow 2`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The end window of a minimizer of a flow: near its end point in a chart,   *)
(* the chart curve s -> phi(gamma(s^2)) is C^1 up to s = sqrt(tau) and its   *)
(* velocity solves the L-geodesic equation; the end velocity as a one-sided  *)
(* derivative on the set 0 <= s, s^2 <= tau.                                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_MIN_WINDOW = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ gamma tau IN U
     ==> ?s0 A. &0 < s0 /\ s0 < sqrt tau /\
                (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U) /\
                A continuous_on interval[lift s0,lift(sqrt tau)] /\
                (!s. s0 < s /\ s < sqrt tau
                     ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s))
                           (at (lift s))) /\
                ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
                  (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
                (!s. s0 <= s /\ s <= sqrt tau
                     ==> (A has_vector_derivative
                            p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                                 U b (U,phi)) b s
                                     (phi(gamma(s pow 2))) (A(lift s)))
                         (at (lift s) within interval[lift s0,lift(sqrt tau)]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`sqrt tau`; `U:A->bool`] o MATCH_MP P2A_ADM_SCONT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) (b - tau) = top`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s0 = max (sqrt tau / &2) (sqrt tau - e / &2)` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 < sqrt tau /\ sqrt tau - s0 < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 <= s /\ s <= sqrt tau ==> (gamma:real->A)(s pow 2) IN U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `s pow 2 <= sqrt tau pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s0:real`] P2AW_FLOW_MIN_CHART) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s0:real`; `A:real^1->real^3`] THEN ASM_REWRITE_TAC[]);;

let P2AW_VDERIV_END_SET = prove
 (`!(f:real^1->real^N) f' s0 tau.
     &0 < tau /\ &0 < s0 /\ s0 < sqrt tau /\
     (f has_vector_derivative f') (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)])
     ==> (f has_vector_derivative f')
           (at (lift(sqrt tau)) within {v | &0 <= drop v /\ drop v pow 2 <= tau})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `\x:real^1. drop x % (f':real^N)`; `lift(sqrt tau)`;
                 `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= tau} INTER
                  ball(lift(sqrt tau),sqrt tau - s0)`;
                 `{v:real^1 | &0 <= drop v /\ drop v pow 2 <= tau}`]
                HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL; LIFT_DROP] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `interval[lift s0,lift(sqrt tau)]` THEN
  ASM_REWRITE_TAC[GSYM has_vector_derivative] THEN
  REWRITE_TAC[SUBSET; FORALL_LIFT; IN_INTER; IN_ELIM_THM; IN_BALL; IN_INTERVAL_1; LIFT_DROP;
              DIST_LIFT] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]]);;

let P2AW_FLOW_MIN_END = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) (c:(A->bool)#(A->real^3)).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ gamma tau IN FST c
     ==> ?s0 A. &0 < s0 /\ s0 < sqrt tau /\
                (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN FST c) /\
                A continuous_on interval[lift s0,lift(sqrt tau)] /\
                (!s. s0 < s /\ s < sqrt tau
                     ==> ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative A(lift s))
                           (at (lift s))) /\
                ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
                  (at (lift(sqrt tau)) within {v | &0 <= drop v /\ drop v pow 2 <= tau}) /\
                (!s. s0 <= s /\ s <= sqrt tau
                     ==> (A has_vector_derivative
                            p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                                 (FST c) b c) b s
                                     (SND c (gamma(s pow 2))) (A(lift s)))
                         (at (lift s) within interval[lift s0,lift(sqrt tau)]))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`; `phi:A->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`] P2AW_FLOW_MIN_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`s0:real`; `A:real^1->real^3`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AW_VDERIV_END_SET THEN EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[p2a_min; p2a_adm]);;

(* ------------------------------------------------------------------------- *)
(* The first order comparison bound at one point.  For an L-geodesic Y with  *)
(* velocity A of a local Ricci flow, C^1 up to s = sb, the combined family   *)
(* of its extension has the second order expansion of P2AW_CFAM_TAYLOR with  *)
(* the first order terms evaluated (P2AW_CFK_EVAL, P2AW_CFW_EVAL); for a     *)
(* minimizer of a flow this bounds the reduced length at nearby points from  *)
(* above, with the chart metric and the scalar curvature at the end point.   *)
(* ------------------------------------------------------------------------- *)

let P2AW_LOCAL_KBAR = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (Y:real^1->real^N) A s0 s1 sb.
     lricci_flow U ta tb Gt /\ &0 < s0 /\ s0 < s1 /\ s1 < sb /\
     (!s. s0 <= s /\ s <= sb ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ Y(lift s) IN U) /\
     A continuous_on interval[lift s0,lift sb] /\
     (!s. s0 < s /\ s < sb ==> (Y has_vector_derivative A(lift s)) (at (lift s))) /\
     (Y has_vector_derivative A(lift sb)) (at (lift sb) within interval[lift s0,lift sb]) /\
     (!s. s0 <= s /\ s <= sb
          ==> (A has_vector_derivative p2a_lacc Gt tt s (Y(lift s)) (A(lift s)))
                (at (lift s) within interval[lift s0,lift sb]))
     ==> ?d C. &0 < d /\ &0 <= C /\
           !w k. abs(k - &1) <= d /\ norm w <= d
                 ==> (!s. s1 <= s /\ s <= sb
                          ==> p2aw_rext Y A sb (lift s) + ((s - s1) / (sb - s1)) % w IN U) /\
                     abs(p2a_cL Gt tt (p2aw_cfam (p2aw_rext Y A sb) s1 sb w k) s1
                                (s1 + k * (sb - s1)) -
                         p2a_cL Gt tt Y s1 sb -
                         ((k - &1) *
                          ((sb - s1) *
                           (&2 * sb pow 2 * lscalar (Gt(tt - sb pow 2)) (Y(lift sb)) -
                            inv(&2) * (A(lift sb) dot
                                       (Gt(tt - sb pow 2) (Y(lift sb)) ** A(lift sb))))) +
                          w dot (Gt(tt - sb pow 2) (Y(lift sb)) ** A(lift sb))))
                     <= C * (abs(k - &1) + norm w) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `A:real^1->real^N`; `s0:real`; `sb:real`]
                P2AW_C1_EXTEND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `Y:real^1->real^N`;
                 `A:real^1->real^N`; `s0:real`; `s1:real`; `sb:real`] P2AW_REXT_CL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `y = p2aw_rext (Y:real^1->real^N) A sb` THEN
  ABBREV_TAC `Ad = p2aw_dext (A:real^1->real^N) sb` THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (Y:real^1->real^N)(lift s) IN U /\
            (y:real^1->real^N)(lift s) = Y(lift s) /\ (Ad:real^1->real^N)(lift s) = A(lift s) /\
            (y has_vector_derivative Ad(lift s)) (at (lift s))`
  (LABEL_TAC "W1") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `s:real` (ASSUME
     `!s. s0 <= s /\ s <= sb
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (Y:real^1->real^N)(lift s) IN U`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^1->real^N) continuous_on interval[lift s1,lift sb] /\
                (Ad:real^1->real^N) continuous_on interval[lift s1,lift sb]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `(Ad:real^1->real^N)(lift s)` THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 < s /\ s < sb
        ==> ((Ad:real^1->real^N) has_vector_derivative
             p2a_lacc Gt tt s ((y:real^1->real^N)(lift s)) (Ad(lift s))) (at (lift s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "W1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`A:real^1->real^N`; `sb - s`] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; DIST_LIFT] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      EXPAND_TAC "Ad" THEN REWRITE_TAC[p2aw_dext; LIFT_DROP] THEN
      SUBGOAL_THEN `r <= sb` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2AW_VDERIV_INTERIOR THEN
      MAP_EVERY EXISTS_TAC [`s0:real`; `sb:real`] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2AW_LRICCI_LSMOOTH) THEN
  SUBGOAL_THEN `ta < tt - sb pow 2 /\ tt - s1 pow 2 < tb /\ s1 pow 2 <= sb pow 2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "W1" (MP_TAC o SPEC `sb:real`) THEN USE_THEN "W1" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K0 = interval[lift(tt - sb pow 2),lift(tt - s1 pow 2)] PCROSS
                   IMAGE (y:real^1->real^N) (interval[lift s1,lift sb])` THEN
  SUBGOAL_THEN `compact(K0:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K0:real^(1,N)finite_sum->bool) SUBSET interval(lift ta,lift tb) PCROSS U`
  ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN REWRITE_TAC[SUBSET_PCROSS] THEN DISJ2_TAC THEN DISJ2_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "W1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sb
        ==> pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)) IN K0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K0" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `s1 pow 2 <= s pow 2 /\ s pow 2 <= sb pow 2` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 < M /\ !s. s1 <= s /\ s <= sb ==> norm((Ad:real^1->real^N)(lift s)) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Ad:real^1->real^N`; `interval[lift s1,lift sb]`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `K0:real^(1,N)finite_sum->bool`; `M:real`; `y:real^1->real^N`;
                 `Ad:real^1->real^N`; `s1:real`; `sb:real`] P2AW_CFAM_TAYLOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      USE_THEN "W1" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `dt:real` (X_CHOOSE_THEN `Ct:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TAY")))))] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `K0:real^(1,N)finite_sum->bool`; `M:real`; `sb - s1`; `sb:real`]
                P2AW_CFAM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `db:real` (X_CHOOSE_THEN `Cb:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CB")))))] THEN
  SUBGOAL_THEN
   `lricci_flow U ta tb (Gt:real->real^N->real^N^N) /\ s1 < sb /\
    (!s. s1 <= s /\ s <= sb
         ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ (y:real^1->real^N)(lift s) IN U) /\
    y continuous_on interval[lift s1,lift sb] /\
    (Ad:real^1->real^N) continuous_on interval[lift s1,lift sb] /\
    (!s. s1 < s /\ s < sb
         ==> (y has_vector_derivative Ad(lift s)) (at (lift s)) /\
             (Ad has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (Ad(lift s))) (at (lift s)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [USE_THEN "W1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]];
      CONJ_TAC THENL
       [USE_THEN "W1" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. p2aw_cfw Gt tt (y:real^1->real^N) Ad s1 sb w =
        w dot (Gt(tt - sb pow 2) (y(lift sb)) ** Ad(lift sb))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2AW_CFW_EVAL THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^1->real^N)(lift sb) = Y(lift sb) /\
                (Ad:real^1->real^N)(lift sb) = A(lift sb)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "W1" (MP_TAC o SPEC `sb:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2aw_cfk Gt tt (y:real^1->real^N) Ad s1 sb =
    (sb - s1) * (&2 * sb pow 2 * lscalar (Gt(tt - sb pow 2)) (Y(lift sb)) -
                 inv(&2) * (A(lift sb) dot (Gt(tt - sb pow 2) (Y(lift sb)) ** A(lift sb))))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP
     (ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
              `y:real^1->real^N`; `Ad:real^1->real^N`; `s1:real`; `sb:real`] P2AW_CFK_EVAL)) THEN
    ASM_REWRITE_TAC[p2aw_lagf; p2aw_zc; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min dt db`; `Ct:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `k:real`] THEN STRIP_TAC THEN CONJ_TAC THENL
   [USE_THEN "CB" (MP_TAC o SPECL [`y:real^1->real^N`; `Ad:real^1->real^N`; `s1:real`; `sb:real`;
                                   `w:real^N`; `k:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      USE_THEN "W1" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN MESON_TAC[]];
    USE_THEN "TAY" (MP_TAC o SPECL [`w:real^N`; `k:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let P2AW_FLOW_PT_KBAR = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) s0 s1 A.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     tau < b - a /\ &0 < s0 /\ s0 < s1 /\ s1 < sqrt tau /\
     (!s. s0 <= s /\ s <= sqrt tau ==> gamma(s pow 2) IN U) /\
     A continuous_on interval[lift s0,lift(sqrt tau)] /\
     (!s. s0 < s /\ s < sqrt tau
          ==> ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift s)) (at (lift s))) /\
     ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A(lift(sqrt tau)))
       (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
     (!s. s0 <= s /\ s <= sqrt tau
          ==> (A has_vector_derivative
                 p2a_lacc (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                      U b (U,phi)) b s
                          (phi(gamma(s pow 2))) (A(lift s)))
              (at (lift s) within interval[lift s0,lift(sqrt tau)]))
     ==> ?d C. &0 < d /\ &0 <= C /\
           !w k. abs(k - &1) <= d /\ norm w <= d /\ &0 < k /\
                 (s1 + k * (sqrt tau - s1)) pow 2 < b - a
                 ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                       ((s1 + k * (sqrt tau - s1)) pow 2)
                       (chart_inv (U,phi) (phi(gamma tau) + w))
                     <= p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                          (gamma tau) +
                        ((k - &1) *
                         ((sqrt tau - s1) *
                          (&2 * tau * mfd_scalar atlas (g(b - tau)) (gamma tau) -
                           inv(&2) * (A(lift(sqrt tau)) dot
                                      (metric_local atlas (U,phi) (g(b - tau)) (phi(gamma tau)) **
                                       A(lift(sqrt tau)))))) +
                         w dot (metric_local atlas (U,phi) (g(b - tau)) (phi(gamma tau)) **
                                A(lift(sqrt tau)))) +
                        C * (abs(k - &1) + norm w) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN U` ASSUME_TAC THENL
   [MP_TAC(SPEC `sqrt tau` (ASSUME
     `!s. s0 <= s /\ s <= sqrt tau ==> (gamma:real->A)(s pow 2) IN U`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`; `b - tau`;
                 `(gamma:real->A) tau`] P2AW_FLOW_RLOCAL_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `b:real`;
                 `p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                (g:real->A->real^3^3)) U b (U,phi)`;
                 `b:real`; `\v. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A:real^1->real^3`; `s0:real`; `s1:real`; `sqrt tau`] P2AW_LOCAL_KBAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `s pow 2 <= sqrt tau pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KB")))))] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`w:real^3`; `k:real`] THEN STRIP_TAC THEN
  USE_THEN "KB" (MP_TAC o SPECL [`w:real^3`; `k:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s0:real`; `s1:real`; `A:real^1->real^3`] P2AW_FLOW_CUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `b:real`; `p:A`; `tau:real`; `gamma:real->A`] P2A_MIN_LX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `tau:real`; `gamma:real->A`;
                 `U:A->bool`; `phi:A->real^3`; `s0:real`; `s1:real`; `A:real^1->real^3`;
                 `w:real^3`; `k:real`] P2AW_FLOW_CMP) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x - y - l) <= e ==> g + x <= (g + y) + l + e`) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The touching inequality for the reduced length of a flow at the end point *)
(* (q, tau) of a minimizer, read in a chart: in space-time chart coordinates *)
(* z = (x, tau), L(z + h) <= L(z) + dL(h) + C |h|^2 with dL(h) = h_x . G A0  *)
(* + (4 tau R - A0 . G A0) / (4 sqrt tau) h_tau, A0 the end velocity of the  *)
(* chart curve s -> phi(gamma(s^2)).                                         *)
(* ------------------------------------------------------------------------- *)

let P2AW_TOUCH_ARITH2 = prove
 (`!f0 f1 k cfk cfw C D st st' dt nh nw tau.
     &0 < D /\ &0 < st /\ &0 < tau /\ &0 <= C /\
     f1 <= f0 + ((k - &1) * cfk + cfw) + C * (abs(k - &1) + nw) pow 2 /\
     k - &1 = (st' - st) / D /\
     abs(st' - st - dt / (&2 * st)) <= dt pow 2 / (&2 * tau * st) /\
     abs(k - &1) <= nh / (st * D) /\ &0 <= nw /\ nw <= nh /\ abs dt <= nh
     ==> f1 <= f0 + (cfw + cfk / (&2 * st * D) * dt) +
               (abs cfk / D / (&2 * tau * st) + C * (inv(st * D) + &1) pow 2) * nh pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_TOUCH_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`f0:real`; `((k - &1) * cfk + cfw) + C * (abs(k - &1) + nw) pow 2`; `&0`; `k:real`;
    `st':real`; `nw:real`] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> abs((x + y) - x) <= y`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let P2AW_FLOW_PT_TOUCH = prove
 (`!top atlas a b (g:real->A->real^3^3) p tau (gamma:real->A) U (phi:A->real^3) x.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     x IN IMAGE phi U /\ tau < b - a /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     gamma tau = chart_inv (U,phi) x
     ==> ?s0 A0 d C. &0 < s0 /\ s0 < sqrt tau /\ &0 < d /\
           ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A0)
             (at (lift(sqrt tau)) within interval[lift s0,lift(sqrt tau)]) /\
           !h. norm h < d
               ==> p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                     (drop(sndcart(pastecart x (lift tau) + h)))
                     (chart_inv (U,phi) (fstcart(pastecart x (lift tau) + h))) <=
                   p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau
                     (chart_inv (U,phi) x) +
                   (fstcart h dot (metric_local atlas (U,phi) (g(b - tau)) x ** A0) +
                    (&4 * tau * mfd_scalar atlas (g(b - tau)) (chart_inv (U,phi) x) -
                     A0 dot (metric_local atlas (U,phi) (g(b - tau)) x ** A0)) /
                    (&4 * sqrt tau) * drop(sndcart h)) +
                   C * norm h pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U,phi) x IN U /\ (phi:A->real^3)(chart_inv (U,phi) x) = x`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_adm (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3))
                        b p tau gamma` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_min]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`] P2AW_FLOW_MIN_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `A:real^1->real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `s1 = (s0 + sqrt tau) / &2` THEN
  SUBGOAL_THEN `s0 < s1 /\ s1 < sqrt tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `s0:real`; `s1:real`; `A:real^1->real^3`]
                P2AW_FLOW_PT_KBAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `C1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KB"))))) THEN
  SUBGOAL_THEN `&0 < sqrt tau - s1 /\ &0 < sqrt tau * (sqrt tau - s1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `cfk0 = (sqrt tau - s1) *
           (&2 * tau * mfd_scalar atlas ((g:real->A->real^3^3)(b - tau)) (chart_inv (U,phi) x) -
            inv(&2) * ((A:real^1->real^3)(lift(sqrt tau)) dot
                       (metric_local atlas (U,phi) (g(b - tau)) x ** A(lift(sqrt tau)))))` THEN
  MAP_EVERY EXISTS_TAC
   [`s0:real`; `(A:real^1->real^3)(lift(sqrt tau))`;
    `min (min d1 (sqrt tau * (sqrt tau - s1) * d1))
         (min (sqrt tau * (sqrt tau - s1) / &2) (min tau (b - a - tau)))`;
    `abs cfk0 / (sqrt tau - s1) / (&2 * tau * sqrt tau) +
     C1 * (inv(sqrt tau * (sqrt tau - s1)) + &1) pow 2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^(3,1)finite_sum` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_LT_MIN]) THEN
  REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_PASTECART; SNDCART_PASTECART; DROP_ADD;
              LIFT_DROP] THEN
  SUBGOAL_THEN `norm(fstcart(h:real^(3,1)finite_sum)) <= norm h /\
                abs(drop(sndcart h)) <= norm h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_FSTCART; ABS_DROP; NORM_SNDCART]; ALL_TAC] THEN
  ABBREV_TAC `w = fstcart(h:real^(3,1)finite_sum)` THEN
  ABBREV_TAC `e = drop(sndcart(h:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `&0 <= tau + e /\ tau + e < b - a` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = &1 + (sqrt(tau + e) - sqrt tau) / (sqrt tau - s1)` THEN
  SUBGOAL_THEN `s1 + k * (sqrt tau - s1) = sqrt(tau + e)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN UNDISCH_TAC `&0 < sqrt tau - s1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sqrt(tau + e) - sqrt tau) <= abs e / sqrt tau` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tau:real`; `tau + e`; `tau:real`] P2AW_SQRT_DIFF_LE) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ARITH `(tau + e) - tau = e`];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(k - &1) <= norm(h:real^(3,1)finite_sum) / (sqrt tau * (sqrt tau - s1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `k - &1 = (sqrt(tau + e) - sqrt tau) / (sqrt tau - s1)` SUBST1_TAC THENL
     [EXPAND_TAC "k" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `norm(h:real^(3,1)finite_sum) / (sqrt tau * (sqrt tau - s1)) =
                  (norm h / sqrt tau) / (sqrt tau - s1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs e / sqrt tau` THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(h:real^(3,1)finite_sum) / (sqrt tau * (sqrt tau - s1)) < d1 /\
                norm h / (sqrt tau * (sqrt tau - s1)) < &1 / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "KB" (MP_TAC o SPECL [`w:real^3`; `k:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tau:real`; `tau + e`] P2AW_SQRT_TAYLOR) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(tau + e) - tau = e`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p tau
           (chart_inv (U,phi) (x:real^3))`;
    `p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
           (tau + e) (chart_inv (U,phi) ((x:real^3) + w))`;
    `k:real`; `cfk0:real`;
    `w dot (metric_local atlas (U,phi) ((g:real->A->real^3^3)(b - tau)) x **
            (A:real^1->real^3)(lift(sqrt tau)))`;
    `C1:real`; `sqrt tau - s1`; `sqrt tau`; `sqrt(tau + e)`; `e:real`;
    `norm(h:real^(3,1)finite_sum)`; `norm(w:real^3)`; `tau:real`] P2AW_TOUCH_ARITH2) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  ANTS_TAC THENL [EXPAND_TAC "k" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `cfk0 / (&2 * sqrt tau * (sqrt tau - s1)) =
    (&4 * tau * mfd_scalar atlas ((g:real->A->real^3^3)(b - tau)) (chart_inv (U,phi) x) -
     (A:real^1->real^3)(lift(sqrt tau)) dot
     (metric_local atlas (U,phi) (g(b - tau)) x ** A(lift(sqrt tau)))) / (&4 * sqrt tau)`
  SUBST1_TAC THENL
   [EXPAND_TAC "cfk0" THEN
    MAP_EVERY UNDISCH_TAC [`&0 < sqrt tau - s1`; `&0 < sqrt tau`] THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* From the touching inequality for L = 2 sqrt(tau) l to the partial         *)
(* derivatives of l at a point where l is differentiable (product rule with  *)
(* 2 sqrt(tau), then P2AW_TOUCH_DERIV).                                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_SQRT_SNDCART_DERIV = prove
 (`!(z:real^(N,1)finite_sum).
     &0 < drop(sndcart z)
     ==> ((lift o (\w:real^(N,1)finite_sum. &2 * sqrt(drop(sndcart w)))) has_derivative
          (lift o (\h. inv(sqrt(drop(sndcart z))) * drop(sndcart h)))) (at z)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t0 = drop(sndcart(z:real^(N,1)finite_sum))` THEN
  SUBGOAL_THEN `&0 < sqrt t0` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sndcart(z:real^(N,1)finite_sum) = lift t0` ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(SPEC `t0:real` HAS_REAL_DERIVATIVE_SQRT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&2` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sndcart:real^(N,1)finite_sum->real^1`;
                 `lift o (\x. &2 * sqrt x) o drop`;
                 `sndcart:real^(N,1)finite_sum->real^1`;
                 `\x:real^1. (&2 * inv(&2 * sqrt t0)) % x`; `z:real^(N,1)finite_sum`]
                DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART]; ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (\x. &2 * sqrt x) o drop) o (sndcart:real^(N,1)finite_sum->real^1) =
                lift o (\w. &2 * sqrt(drop(sndcart w)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^1. (&2 * inv(&2 * sqrt t0)) % x) o (sndcart:real^(N,1)finite_sum->real^1) =
                lift o (\h. inv(sqrt t0) * drop(sndcart h))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL; LIFT_DROP] THEN GEN_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < sqrt t0` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[]]);;

let P2AW_TOUCH_SQRT_DERIV = prove
 (`!(l:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real) z P Q d C.
     &0 < drop(sndcart z) /\ &0 < d /\
     (!w. &0 < drop(sndcart w) ==> f w = &2 * sqrt(drop(sndcart w)) * l w) /\
     (\w. lift(l w)) differentiable (at z) /\
     (!h. norm h < d
          ==> f(z + h) <= f z + (fstcart h dot P + Q * drop(sndcart h)) + C * norm h pow 2)
     ==> (!i. 1 <= i /\ i <= dimindex(:N)
              ==> &2 * sqrt(drop(sndcart z)) * wan_xder i l z = P$i) /\
         &2 * sqrt(drop(sndcart z)) * wan_tder l z + l z / sqrt(drop(sndcart z)) = Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `dl = frechet_derivative (\w. lift((l:real^(N,1)finite_sum->real) w)) (at z)` THEN
  SUBGOAL_THEN `((\w. lift((l:real^(N,1)finite_sum->real) w)) has_derivative dl) (at z)`
  ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^(N,1)finite_sum. &2 * sqrt(drop(sndcart w))`;
                 `\h:real^(N,1)finite_sum. inv(sqrt(drop(sndcart(z:real^(N,1)finite_sum)))) *
                                          drop(sndcart h)`;
                 `\w. lift((l:real^(N,1)finite_sum->real) w)`; `dl:real^(N,1)finite_sum->real^1`;
                 `z:real^(N,1)finite_sum`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_SIMP_TAC[P2AW_SQRT_SNDCART_DERIV] THEN DISCH_TAC THEN
  ABBREV_TAC
   `D = \h:real^(N,1)finite_sum.
          (&2 * sqrt(drop(sndcart(z:real^(N,1)finite_sum)))) % dl h +
          (inv(sqrt(drop(sndcart z))) * drop(sndcart h)) % lift((l:real^(N,1)finite_sum->real) z)` THEN
  SUBGOAL_THEN `((\w. lift((f:real^(N,1)finite_sum->real) w)) has_derivative D) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\w:real^(N,1)finite_sum. (&2 * sqrt(drop(sndcart w))) %
                                         lift((l:real^(N,1)finite_sum->real) w)` THEN
    EXISTS_TAC `drop(sndcart(z:real^(N,1)finite_sum))` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < drop(sndcart(y:real^(N,1)finite_sum))` ASSUME_TAC THENL
     [MP_TAC(ISPEC `sndcart(y - z:real^(N,1)finite_sum)` ABS_DROP) THEN
      MP_TAC(ISPEC `y - z:real^(N,1)finite_sum` NORM_SNDCART) THEN
      UNDISCH_TAC `dist(y:real^(N,1)finite_sum,z) < drop(sndcart z)` THEN
      REWRITE_TAC[dist; SNDCART_SUB; DROP_SUB] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM LIFT_CMUL; REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(N,1)finite_sum->real`;
                 `\h:real^(N,1)finite_sum. lift(fstcart h dot P + Q * drop(sndcart h))`;
                 `z:real^(N,1)finite_sum`; `d:real`; `C:real`] P2AW_TOUCH_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
     [REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL; DOT_LADD;
                  DOT_LMUL; DROP_ADD; DROP_CMUL; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[differentiable] THEN EXISTS_TAC `D:real^(N,1)finite_sum->real^1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[wan_xder; wan_tder] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `drop` o SPEC `pastecart (basis i:real^N) (vec 0:real^1)`) THEN
    ASM_SIMP_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC;
                 DOT_BASIS] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o AP_TERM `drop` o SPEC `pastecart (vec 0:real^N) (lift(&1))`) THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART;
                DOT_LZERO] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The pointwise first variation of the reduced length of a flow: at a point *)
(* (x, tau) of a chart where l is differentiable, every minimizer gamma to   *)
(* (chart_inv c x, tau) has tau-velocity X at tau with dl = G X and 2 l_tau  *)
(* + |X|^2 - R + l/tau = 0 (Perelman (7.6)); this is                         *)
(* P2AW_FLOW_LX_DERIV_STATEMENT of pc_p2a_lxreq.                             *)
(* ------------------------------------------------------------------------- *)

let P2AW_TDER_ARITH = prove
 (`!st tau R KK lz W.
     &0 < st /\ st pow 2 = tau /\
     &2 * st * W + lz / st = (&4 * tau * R - KK) / (&4 * st)
     ==> W = (R - inv(&2 * st) * inv(&2 * st) * KK) / &2 - lz / (&2 * tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `&2 * st * W + lz / st = (&4 * tau * R - KK) / (&4 * st)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `&0 < st` THEN CONV_TAC REAL_FIELD);;

let P2AW_FLOW_LX_DERIV = prove
 (`!top atlas a b (g:real->A->real^3^3) p (c:(A->bool)#(A->real^3)) x tau (gamma:real->A).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
     x IN IMAGE (SND c) (FST c) /\ &0 < tau /\ tau < b - a /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p tau gamma /\
     gamma tau = chart_inv c x /\
     (\w. lift(p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) w))
       differentiable (at (pastecart x (lift tau)))
     ==> ?X. ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative (&2 * sqrt tau) % X)
               (at (lift(sqrt tau)) within {v | &0 <= drop v /\ drop v pow 2 <= tau}) /\
             (!i. 1 <= i /\ i <= 3
                  ==> wan_xder i
                        (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                             b p))
                        (pastecart x (lift tau)) =
                      (p2bw_cmet atlas c b g (pastecart x (lift tau)) ** X)$i) /\
             wan_tder
               (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
               (pastecart x (lift tau)) =
             (p2bw_cscal atlas c b g (pastecart x (lift tau)) -
              X dot (p2bw_cmet atlas c b g (pastecart x (lift tau)) ** X)) / &2 -
             p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)
                       (pastecart x (lift tau)) / (&2 * tau)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `p:A`; `U:A->bool`; `phi:A->real^3`; `x:real^3`; `tau:real`;
    `gamma:real->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt tau /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `tau:real`; `gamma:real->A`; `U:A->bool`;
                 `phi:A->real^3`; `x:real^3`] P2AW_FLOW_PT_TOUCH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `A0:real^3`
    (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL
   [`p2bw_cfun (U,(phi:A->real^3)) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                 (g:real->A->real^3^3)) b p)`;
    `\w:real^(3,1)finite_sum.
       p2a_Lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
              (drop(sndcart w)) (chart_inv (U,phi) (fstcart w))`;
    `pastecart (x:real^3) (lift tau)`;
    `metric_local atlas (U,phi) ((g:real->A->real^3^3)(b - tau)) x ** A0`;
    `(&4 * tau * mfd_scalar atlas ((g:real->A->real^3^3)(b - tau)) (chart_inv (U,phi) x) -
      A0 dot (metric_local atlas (U,phi) (g(b - tau)) x ** A0)) / (&4 * sqrt tau)`;
    `d:real`; `C:real`] P2AW_TOUCH_SQRT_DERIV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[p2bw_cfun; p2a_lx] THEN
    SUBGOAL_THEN `&0 < sqrt(drop(sndcart(w:real^(3,1)finite_sum)))` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP; DIMINDEX_3] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(&2 * sqrt tau) % (A0:real^3)` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(&2 * sqrt tau) % inv(&2 * sqrt tau) % (A0:real^3) = A0` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(&2 * sqrt tau) * inv(&2 * sqrt tau) = &1`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P2AW_VDERIV_END_SET THEN EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[p2bw_cmet; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_COMPONENT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sqrt tau` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[p2bw_cmet; p2bw_cscal; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC P2AW_TDER_ARITH THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The headline theorems, the two statements of pc_p2a_lxreq.                *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_LX_DERIV_THM = prove
 (`!u:A->bool. P2AW_FLOW_LX_DERIV_STATEMENT u`,
  REWRITE_TAC[P2AW_FLOW_LX_DERIV_STATEMENT; P2AW_FLOW_LX_DERIV]);;

let P2AW_FLOW_MIN_END_THM = prove
 (`!u:A->bool. P2AW_FLOW_MIN_END_STATEMENT u`,
  REWRITE_TAC[P2AW_FLOW_MIN_END_STATEMENT; P2AW_FLOW_MIN_END]);;

