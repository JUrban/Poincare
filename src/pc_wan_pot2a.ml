(* ========================================================================= *)
(* pc_wan_pot2a: pointwise jet expansions for smooth functions with          *)
(* controlled Laplacian, by a Caffarelli-type iteration: at each scale the   *)
(* function is replaced by its Poisson integral (barrier estimate) and the   *)
(* Poisson integral by a harmonic polynomial (truncated Poisson kernel).     *)
(*   - the Poisson integral of continuous circle data, truncation;           *)
(*   - harmonic polynomial jets;                                             *)
(*   - the iteration;                                                        *)
(*   - the limit polynomial and the expansion (WANL_PT_EXPAND).              *)
(* ========================================================================= *)

needs "src/pc_wan_lap2e.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Poisson integral of continuous scalar data on a circle, and its     *)
(* approximation by the harmonic polynomial of the truncated kernel.        *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_CIRCLE_CONT = prove
 (`!(x0:real^2) rho (v:real^2->real).
     &0 < rho /\ (\y. lift(v y)) continuous_on sphere(x0,rho)
     ==> (\s. lift(v(x0 + rho % cexp(ii * Cx(drop s))))) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\s. lift((v:real^2->real)(x0 + rho % cexp(ii * Cx(drop s))))) =
    (\y. lift(v y)) o (\s. x0 + rho % cexp(ii * Cx(drop s)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[WANL_PE_CEXP_CONT];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(x0:real^2,rho)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_SPHERE; dist] THEN
    GEN_TAC THEN REWRITE_TAC[VECTOR_ARITH `x0 - (x0 + x):real^N = --x`; NORM_NEG; NORM_MUL;
                             NORM_CEXP_II; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC]);;

let WANL_PT_DSOL_INTEGRAL = prove
 (`!(x0:real^2) rho (v:real^2->real) x.
     &0 < rho /\ (\y. lift(v y)) continuous_on sphere(x0,rho) /\ x IN ball(x0,rho)
     ==> drop(wanl_dsol x0 rho (\y. lift(v y)) x) =
         inv(&2 * pi) *
         drop(integral (interval[vec 0,lift(&2 * pi)])
                (\s. lift(wanl_poisson_kernel (inv rho % (x - x0)) (drop s) *
                          v(x0 + rho % cexp(ii * Cx(drop s))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(inv rho % (x - x0):complex) < &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x0:real^2`; `rho:real`; `x:real^2`] WANL_UNIT_SCALE) THEN
    ASM_REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w:complex = inv rho % (x - x0)` THEN
  ASM_SIMP_TAC[wanl_dsol; drop; LAMBDA_BETA; DIMINDEX_1; LE_REFL; wanl_poisson_integral;
               RE_MUL_CX] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `drop(integral (interval[vec 0,lift(&2 * pi)])
                (\s. lift(Re(Cx(wanl_poisson_kernel w (drop s)) *
                             Cx((v:real^2->real)(x0 + rho % cexp(ii * Cx(drop s))))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_PE_RE_INTEGRAL THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      ASM_SIMP_TAC[WANL_POISSON_KERNEL_CONTINUOUS; SUBSET_UNIV];
      REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^1)` THEN ASM_SIMP_TAC[WANL_PT_CIRCLE_CONT; SUBSET_UNIV]];
    REWRITE_TAC[RE_CX; GSYM CX_MUL]]);;

let WANL_PT_TRUNC = prove
 (`!(x0:real^2) rho (v:real^2->real) x N s0 B.
     &0 < rho /\ (\y. lift(v y)) continuous_on sphere(x0,rho) /\
     x IN ball(x0,rho) /\ norm(x - x0) <= s0 * rho /\ s0 < &1 /\
     (!y. y IN sphere(x0,rho) ==> abs(v y) <= B)
     ==> abs(drop(wanl_dsol x0 rho (\y. lift(v y)) x) -
             wanl_pe_poly (\t. v(x0 + rho % cexp(ii * Cx t))) N x0 rho x)
         <= B * &2 * s0 pow (N + 1) / (&1 - s0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. lift((v:real^2->real)(x0 + rho % cexp(ii * Cx(drop s))))) continuous_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[WANL_PT_CIRCLE_CONT; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\t. (v:real^2->real)(x0 + rho % cexp(ii * Cx t))`; `N:num`;
                           `x0:real^2`; `rho:real`; `x:real^2`] WANL_PE_POLY_INTEGRAL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[WANL_PT_DSOL_INTEGRAL] THEN
  SUBGOAL_THEN `norm(inv rho % (x - x0):complex) <= s0 /\ norm(inv rho % (x - x0):complex) < &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `(x:real^2) IN ball(x0,rho)` THEN REWRITE_TAC[IN_BALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w:complex = inv rho % (x - x0)` THEN
  SUBGOAL_THEN `(\s. lift(wanl_poisson_kernel w (drop s))) continuous_on
                interval[vec 0,lift(&2 * pi)] /\
                (\s. lift(&1 + &2 * sum(1..N)
                       (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n)))) continuous_on
                interval[vec 0,lift(&2 * pi)]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV; WANL_PE_PN_CONT] THEN
    REWRITE_TAC[GSYM CONTINUOUS_ON_CX_LIFT] THEN
    ASM_SIMP_TAC[WANL_POISSON_KERNEL_CONTINUOUS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM DROP_SUB] THEN
  W(fun (asl,w) -> let t = find_term (fun u -> is_comb u &&
      (try fst(dest_const(rator(rator u))) = "vector_sub" with _ -> false) &&
      (try fst(dest_const(fst(strip_comb(rand(rator u))))) = "integral" with _ -> false)) w in
      SUBGOAL_THEN (mk_eq(t, `integral (interval[vec 0,lift(&2 * pi)])
         (\s. lift((wanl_poisson_kernel w (drop s) -
                    (&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n)))) *
                   (v:real^2->real)(x0 + rho % cexp(ii * Cx(drop s)))))`)) SUBST1_TAC) THENL
   [REWRITE_TAC[REAL_SUB_RDISTRIB; LIFT_SUB] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN interval[vec 0,lift(&2 * pi)]
                    ==> abs((v:real^2->real)(x0 + rho % cexp(ii * Cx(drop s)))) <= B`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SPHERE; dist; VECTOR_ARITH `x0 - (x0 + x):real^N = --x`; NORM_NEG;
                NORM_MUL; NORM_CEXP_II; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((v:real^2->real)(x0 + rho % cexp(ii * Cx(drop(vec 0:real^1)))))` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bw = &2 * norm(w:complex) pow (N + 1) / (&1 - norm w)` THEN
  SUBGOAL_THEN `Bw <= &2 * s0 pow (N + 1) / (&1 - s0)` ASSUME_TAC THENL
   [EXPAND_TAC "Bw" THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. wanl_poisson_kernel w (drop s) -
         (&1 + &2 * sum(1..N) (\n. Re((w * cnj(cexp(ii * Cx(drop s)))) pow n)))`;
    `\s. (v:real^2->real)(x0 + rho % cexp(ii * Cx(drop s)))`; `Bw:real`; `B:real`]
   WANL_PE_INT_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
       [EXPAND_TAC "Bw" THEN MATCH_MP_TAC WANL_PE_KERNEL_TRUNC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(inv(&2 * pi)) = inv(&2 * pi) /\ &0 < &2 * pi` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN MATCH_MP_TAC REAL_LE_INV THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * pi) * (&2 * pi * (Bw * B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * pi) * (&2 * pi * (Bw * B)) = B * Bw` SUBST1_TAC THENL
   [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Harmonic polynomial jets Re(sum_(n <= N) c_n (x - x0)^n) and the         *)
(* coefficients of the truncated Poisson kernel of circle data.             *)
(* ------------------------------------------------------------------------- *)

let wanl_pt_hp = new_definition
 `wanl_pt_hp (c:num->complex) N (x0:real^2) (x:real^2) =
    Re(vsum(0..N) (\n. c n * (x - x0) pow n))`;;

let wanl_pt_pc = new_definition
 `wanl_pt_pc (phi:real->real) rho n =
    if n = 0 then Cx(inv(&2 * pi)) * wanl_pe_fc phi 0
    else Cx(inv pi) * wanl_pe_fc phi n * Cx(inv rho) pow n`;;

let WANL_PT_PE_HP = prove
 (`!(phi:real->real) N (x0:real^2) rho x.
     wanl_pe_poly phi N x0 rho x = wanl_pt_hp (wanl_pt_pc phi rho) N x0 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wanl_pe_poly; wanl_pt_hp] THEN AP_TERM_TAC THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  REWRITE_TAC[wanl_pt_pc; complex_pow; COMPLEX_MUL_RID] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_POW_MUL] THEN CONV_TAC COMPLEX_RING);;

let WANL_PT_HP_ADD = prove
 (`!(c:num->complex) d N (x0:real^2) x.
     wanl_pt_hp (\n. c n + d n) N x0 x = wanl_pt_hp c N x0 x + wanl_pt_hp d N x0 x`,
  REWRITE_TAC[wanl_pt_hp; COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC[VSUM_ADD; FINITE_NUMSEG; RE_ADD]);;

let WANL_PT_HP_SUB = prove
 (`!(c:num->complex) d N (x0:real^2) x.
     wanl_pt_hp (\n. c n - d n) N x0 x = wanl_pt_hp c N x0 x - wanl_pt_hp d N x0 x`,
  REWRITE_TAC[wanl_pt_hp; COMPLEX_SUB_RDISTRIB] THEN
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG; RE_SUB]);;

let WANL_PT_HP_ZERO = prove
 (`!N (x0:real^2) x. wanl_pt_hp (\n. Cx(&0)) N x0 x = &0`,
  REWRITE_TAC[wanl_pt_hp; COMPLEX_MUL_LZERO] THEN REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; RE_CX]);;

let WANL_PT_HP_HOLO = prove
 (`!(c:num->complex) N (x0:real^2).
     (\x. vsum(0..N) (\n. c n * (x - x0) pow n)) holomorphic_on (:complex)`,
  REPEAT GEN_TAC THEN SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z:complex` THEN
  EXISTS_TAC `vsum(0..N) (\n. c n * (Cx(&n) * (z - x0) pow (n - 1) * Cx(&1)))` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let WANL_PT_HP_SMOOTH = prove
 (`!(c:num->complex) N (x0:real^2).
     smooth_map_on (:real^2) (\x. lift(wanl_pt_hp c N x0 x)) /\
     (!x. llap (\y:real^2. mat 1) (wanl_pt_hp c N x0) x = &0)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Q = \x:complex. vsum(0..N) (\n. (c:num->complex) n * (x - x0) pow n)` THEN
  SUBGOAL_THEN `wanl_pt_hp c N x0 = (\y. Re((Q:complex->complex) y))` SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[FUN_EQ_THM; wanl_pt_hp]; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:complex->complex) holomorphic_on (:complex)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[WANL_PT_HP_HOLO]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. lift((\y. Re((Q:complex->complex) y)) x)) = (\z. lift(Re z)) o Q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[OPEN_UNIV; WANL_HOLOMORPHIC_SMOOTH] THEN
    REWRITE_TAC[linear; RE_ADD; RE_CMUL; LIFT_ADD; LIFT_CMUL];
    GEN_TAC THEN MATCH_MP_TAC WANL_RE_HOLOMORPHIC_HARMONIC THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]]);;

let WANL_PT_HP_BOUND = prove
 (`!(c:num->complex) N (x0:real^2) x.
     abs(wanl_pt_hp c N x0 x) <= sum(0..N) (\n. norm(c n) * norm(x - x0) pow n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wanl_pt_hp] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vsum(0..N) (\n. (c:num->complex) n * (x - x0) pow n))` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; REAL_LE_REFL]);;

let WANL_PT_FC_BOUND = prove
 (`!(phi:real->real) n B.
     (\s. lift(phi(drop s))) continuous_on interval[vec 0,lift(&2 * pi)] /\
     (!s. s IN interval[vec 0,lift(&2 * pi)] ==> abs(phi(drop s)) <= B)
     ==> norm(wanl_pe_fc phi n) <= &2 * pi * B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_pe_fc] THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((phi:real->real)(drop(vec 0:real^1)))` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. Cx((phi:real->real)(drop s)) * cnj(cexp(ii * Cx(drop s)) pow n)`;
                 `vec 0:real^1`; `lift(&2 * pi)`;
                 `integral (interval[vec 0,lift(&2 * pi)])
                    (\s. Cx((phi:real->real)(drop s)) * cnj(cexp(ii * Cx(drop s)) pow n))`;
                 `B:real`] HAS_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CX_LIFT] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[LINEAR_CNJ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN REWRITE_TAC[WANL_PE_CEXP_CONT];
      X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_CNJ; COMPLEX_NORM_POW;
                  NORM_CEXP_II; REAL_POW_ONE; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `content(interval[vec 0:real^1,lift(&2 * pi)]) = &2 * pi` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; REAL_SUB_RZERO;
                 REAL_ARITH `&0 < pi ==> &0 <= &2 * pi`];
    REAL_ARITH_TAC]);;

let WANL_PT_PC_BOUND = prove
 (`!(phi:real->real) rho n B.
     &0 < rho /\
     (\s. lift(phi(drop s))) continuous_on interval[vec 0,lift(&2 * pi)] /\
     (!s. s IN interval[vec 0,lift(&2 * pi)] ==> abs(phi(drop s)) <= B)
     ==> norm(wanl_pt_pc phi rho n) <= &2 * B * inv rho pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`phi:real->real`; `n:num`; `B:real`] WANL_PT_FC_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((phi:real->real)(drop(vec 0:real^1)))` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv rho pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[wanl_pt_pc] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_RID; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < pi ==> abs(&2 * pi) = &2 * pi`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 * pi) * (&2 * pi * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `inv(&2 * pi) * (&2 * pi * B) = B` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < pi` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_POW] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < pi ==> abs pi = pi`;
                 REAL_ARITH `&0 < r ==> abs r = r`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv pi * (&2 * pi * B) * inv rho pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < pi` THEN CONV_TAC REAL_FIELD]]);;

(* ------------------------------------------------------------------------- *)
(* The iteration.  The residual of the jet C is v - (c/4)|x-x0|^2 - hp C.  *)
(* At scale rho_k = rho0 lam^k the circle data of the residual define the   *)
(* next harmonic polynomial (wanl_pt_it).  WANL_PT_STEP is one scale        *)
(* (barrier plus truncated kernel); WANL_PT_INV is the invariant            *)
(* |residual| <= K rho_k^sigma on cball(x0,rho_k), sigma = N + al.          *)
(* ------------------------------------------------------------------------- *)

let wanl_pt_res = new_definition
 `wanl_pt_res (v:real^2->real) c (C:num->complex) N (x0:real^2) (x:real^2) =
    v x - c / &4 * norm(x - x0) pow 2 - wanl_pt_hp C N x0 x`;;

let wanl_pt_step = new_definition
 `wanl_pt_step (v:real^2->real) c N (x0:real^2) rho (C:num->complex) =
    (\n. C n + wanl_pt_pc (\t. wanl_pt_res v c C N x0 (x0 + rho % cexp(ii * Cx t))) rho n)`;;

let wanl_pt_it = new_recursive_definition num_RECURSION
 `(wanl_pt_it (v:real^2->real) c N (x0:real^2) rho0 lam 0 = (\n:num. Cx(&0))) /\
  (wanl_pt_it v c N x0 rho0 lam (SUC k) =
     wanl_pt_step v c N x0 (rho0 * lam pow k) (wanl_pt_it v c N x0 rho0 lam k))`;;

let WANL_PT_RES_SUC = prove
 (`!(v:real^2->real) c N (x0:real^2) rho0 lam k x.
     wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam (SUC k)) N x0 x =
     wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam k) N x0 x -
     wanl_pe_poly (\t. wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam k) N x0
                         (x0 + (rho0 * lam pow k) % cexp(ii * Cx t)))
                  N x0 (rho0 * lam pow k) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT2 wanl_pt_it; wanl_pt_step] THEN
  GEN_REWRITE_TAC LAND_CONV [wanl_pt_res] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [wanl_pt_res] THEN
  REWRITE_TAC[WANL_PT_HP_ADD; WANL_PT_PE_HP] THEN
  REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC);;

let WANL_PT_RES_ZERO = prove
 (`!(v:real^2->real) c N (x0:real^2) rho0 lam x.
     wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam 0) N x0 x =
     v x - c / &4 * norm(x - x0) pow 2`,
  REWRITE_TAC[wanl_pt_res; CONJUNCT1 wanl_pt_it; WANL_PT_HP_ZERO; REAL_SUB_RZERO]);;

let WANL_PT_RES_SMOOTH = prove
 (`!(U:real^2->bool) (v:real^2->real) c C N x0.
     open U /\ smooth_map_on U (\x. lift(v x))
     ==> smooth_map_on U (\x. lift(wanl_pt_res v c C N x0 x)) /\
         (!x. x IN U
              ==> llap (\y:real^2. mat 1) (wanl_pt_res v c C N x0) x =
                  llap (\y:real^2. mat 1) v x - c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on U (\x. lift(c / &4 * norm(x - x0) pow 2 + &0)) /\
    smooth_map_on U (\x. lift(wanl_pt_hp C N x0 x))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WANL_DD_QUAD_SMOOTH] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN REWRITE_TAC[SUBSET_UNIV; WANL_PT_HP_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wanl_pt_res v c C N x0 =
    (\x. &1 * (\x. v x - (c / &4 * norm(x - x0) pow 2 + &0)) x +
         --(&1) * wanl_pt_hp C N x0 x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wanl_pt_res] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\x. lift((v:real^2->real) x - (c / &4 * norm(x - x0) pow 2 + &0)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`;
                 `\x. (v:real^2->real) x - (c / &4 * norm(x - x0) pow 2 + &0)`;
                 `wanl_pt_hp C N x0`; `&1`; `--(&1)`; `x:real^2`] WANL_LLAP_LINEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WANL_PT_HP_SMOOTH] THEN
  SUBGOAL_THEN
   `(\x. (v:real^2->real) x - (c / &4 * norm(x - x0) pow 2 + &0)) =
    (\x. &1 * v x + --(&1) * (\x. c / &4 * norm(x - x0) pow 2 + &0) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `v:real^2->real`;
                 `\x. c / &4 * norm(x - (x0:real^2)) pow 2 + &0`; `&1`; `--(&1)`;
                 `x:real^2`] WANL_LLAP_LINEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WANL_DD_LLAP_QUAD; DIMINDEX_2] THEN
  ABBREV_TAC `Lv = llap (\y:real^2. mat 1) v x` THEN REAL_ARITH_TAC);;

let WANL_PT_STEP = prove
 (`!(U:real^2->bool) (e:real^2->real) x0 rho lam N L E.
     open U /\ cball(x0,rho) SUBSET U /\ &0 < rho /\ smooth_map_on U (\x. lift(e x)) /\
     &0 < lam /\ lam < &1 /\
     (!x. x IN ball(x0,rho) ==> abs(llap (\y:real^2. mat 1) e x) <= L) /\
     (!x. x IN cball(x0,rho) ==> abs(e x) <= E)
     ==> !x. x IN cball(x0,lam * rho)
             ==> abs(e x - wanl_pe_poly (\t. e(x0 + rho % cexp(ii * Cx t))) N x0 rho x)
                 <= L * rho pow 2 / &4 + E * &2 * lam pow (N + 1) / (&1 - lam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. lift((e:real^2->real) x)) continuous_on cball(x0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((e:real^2->real) x)) continuous_on sphere(x0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(x0:real^2,rho)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x0:real^2`; `rho:real`; `\x. lift((e:real^2->real) x)`] WANL_DSOL_CONTINUOUS) THEN
  MP_TAC(ISPECL [`x0:real^2`; `rho:real`; `\x. lift((e:real^2->real) x)`] WANL_DSOL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `H = wanl_dsol x0 rho (\x. lift((e:real^2->real) x))` THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (ball(x0,rho)) (\x. lift((e:real^2->real) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(x0,rho)) (\x. lift(drop((H:real^2->real^1) x)))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x0:real^2`; `rho:real`; `\x. (e:real^2->real) x - drop((H:real^2->real^1) x)`;
                 `L:real`] WANL_DD_BARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL; ETA_AX] THEN
      ASM_MESON_TAC[LIFT_DROP; ETA_AX];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ball(x0:real^2,rho)`; `e:real^2->real`;
                     `\x. drop((H:real^2->real^1) x)`; `&1`; `--(&1)`; `y:real^2`]
             WANL_LLAP_LINEAR) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      SUBGOAL_THEN `(\z. &1 * (e:real^2->real) z + --(&1) * drop((H:real^2->real^1) z)) =
                    (\x. e x - drop(H x))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `llap (\z:real^2. mat 1) (\x. drop((H:real^2->real^1) x)) y = &0`
      SUBST1_TAC THENL
       [REWRITE_TAC[drop] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_LID] THEN ASM_SIMP_TAC[];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(H:real^2->real^1) y = lift(e y)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  SUBGOAL_THEN `(x:real^2) IN cball(x0,rho) /\ x IN ball(x0,rho) /\ norm(x - x0) <= lam * rho`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN cball(x0,lam * rho)` THEN
    REWRITE_TAC[IN_CBALL; IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    SUBGOAL_THEN `lam * rho < &1 * rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x0:real^2`; `rho:real`; `e:real^2->real`; `x:real^2`; `N:num`; `lam:real`;
                 `E:real`] WANL_PT_TRUNC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SPHERE_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `L / (&2 * &2) * (rho pow 2 - norm(x - x0) pow 2) <= L * rho pow 2 / &4`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(llap (\y:real^2. mat 1) (e:real^2->real) x0)` THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    MP_TAC(SPEC `norm(x - x0:real^2)` REAL_LE_POW_2) THEN
    REWRITE_TAC[real_div] THEN DISCH_TAC THEN
    SUBGOAL_THEN `L * inv(&2 * &2) * norm(x - x0:real^2) pow 2 >= &0` MP_TAC THENL
     [REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WANL_PT_INV = prove
 (`!(U:real^2->bool) (v:real^2->real) c N x0 rho0 lam al A K.
     open U /\ cball(x0,rho0) SUBSET U /\ &0 < rho0 /\ smooth_map_on U (\x. lift(v x)) /\
     &0 < lam /\ lam < &1 /\ &0 <= K /\
     &2 * lam pow (N + 1) / (&1 - lam) <= lam rpow (&N + al) / &2 /\
     A / &4 <= K / &2 * lam rpow (&N + al) /\
     (!rho x. &0 < rho /\ rho <= rho0 /\ x IN ball(x0,rho)
              ==> abs(llap (\y:real^2. mat 1) v x - c) <= A * rho rpow (&N + al - &2)) /\
     (!x. x IN cball(x0,rho0)
          ==> abs(v x - c / &4 * norm(x - x0) pow 2) <= K * rho0 rpow (&N + al))
     ==> !k x. x IN cball(x0,rho0 * lam pow k)
               ==> abs(wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam k) N x0 x)
                   <= K * (rho0 * lam pow k) rpow (&N + al)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[WANL_PT_RES_ZERO; real_pow; REAL_MUL_RID] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `rho = rho0 * lam pow k` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= rho0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho0 * lam pow (SUC k) = lam * rho` SUBST1_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WANL_PT_RES_SUC] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e = wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam k) N x0` THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`;
                 `wanl_pt_it v c N x0 rho0 lam k`; `N:num`; `x0:real^2`] WANL_PT_RES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(x0:real^2,rho) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,rho0)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `e:real^2->real`; `x0:real^2`; `rho:real`; `lam:real`;
                 `N:num`; `A * rho rpow (&N + al - &2)`; `K * rho rpow (&N + al)`]
         WANL_PT_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN U` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^2` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `rho rpow (&N + al - &2) * rho pow 2 = rho rpow (&N + al)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_MUL] THEN
  ABBREV_TAC `P = rho rpow (&N + al)` THEN
  ABBREV_TAC `Q = rho rpow (&N + al - &2)` THEN
  ABBREV_TAC `R = lam rpow (&N + al)` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A * Q * rho pow 2 = A * P` ASSUME_TAC THENL
   [UNDISCH_TAC `Q * rho pow 2 = P` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(A / &4) * P <= (K / &2 * R) * P /\
                (K * P) * (&2 * lam pow (N + 1) / (&1 - lam)) <= (K * P) * (R / &2)`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `A * Q * rho pow 2 = A * P` THEN REAL_ARITH_TAC);;

let WANL_PT_INC = prove
 (`!(U:real^2->bool) (v:real^2->real) c N x0 rho0 lam al A K k n.
     open U /\ cball(x0,rho0) SUBSET U /\ &0 < rho0 /\ smooth_map_on U (\x. lift(v x)) /\
     &0 < lam /\ lam < &1 /\ &0 <= K /\
     &2 * lam pow (N + 1) / (&1 - lam) <= lam rpow (&N + al) / &2 /\
     A / &4 <= K / &2 * lam rpow (&N + al) /\
     (!rho x. &0 < rho /\ rho <= rho0 /\ x IN ball(x0,rho)
              ==> abs(llap (\y:real^2. mat 1) v x - c) <= A * rho rpow (&N + al - &2)) /\
     (!x. x IN cball(x0,rho0)
          ==> abs(v x - c / &4 * norm(x - x0) pow 2) <= K * rho0 rpow (&N + al))
     ==> norm(wanl_pt_it v c N x0 rho0 lam (SUC k) n - wanl_pt_it v c N x0 rho0 lam k n)
         <= &2 * (K * (rho0 * lam pow k) rpow (&N + al)) * inv(rho0 * lam pow k) pow n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`] WANL_PT_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  REWRITE_TAC[CONJUNCT2 wanl_pt_it; wanl_pt_step; VECTOR_ARITH `(a + b) - a:real^N = b`] THEN
  ABBREV_TAC `rho = rho0 * lam pow k` THEN
  ABBREV_TAC `e = wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam k) N x0` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= rho0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`;
                 `wanl_pt_it v c N x0 rho0 lam k`; `N:num`; `x0:real^2`] WANL_PT_RES_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC WANL_PT_PC_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC WANL_PT_CIRCLE_CONT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,rho0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^2,rho)` THEN
    ASM_SIMP_TAC[SPHERE_SUBSET_CBALL; SUBSET_CBALL];
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL; dist; VECTOR_ARITH `x0 - (x0 + x):real^N = --x`; NORM_NEG;
                NORM_MUL; NORM_CEXP_II; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The limit jet.  Geometric increments give a limit of the coefficients;   *)
(* comparing with the jet at the scale rho_k >= |x - x0| > rho_(k+1) gives  *)
(* the expansion |residual(x)| <= K' |x - x0|^(N + al).                     *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_RPOW_SCALE = prove
 (`!rho0 lam s k n.
     &0 < rho0 /\ &0 < lam
     ==> (rho0 * lam pow k) rpow s * inv(rho0 * lam pow k) pow n =
         rho0 rpow (s - &n) * (lam rpow (s - &n)) pow k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho0 * lam pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ABBREV_TAC `rho = rho0 * lam pow k` THEN
  SUBGOAL_THEN `rho rpow s * inv rho pow n = rho rpow (s - &n)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RPOW_SUB; REAL_POW_INV; GSYM RPOW_POW; real_div]; ALL_TAC] THEN
  EXPAND_TAC "rho" THEN REWRITE_TAC[RPOW_MUL] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW; REAL_LT_IMP_LE] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let WANL_PT_GEOM_LIMIT = prove
 (`!(C:num->complex) B0 mu.
     &0 <= B0 /\ &0 <= mu /\ mu < &1 /\ (!k. norm(C(SUC k) - C k) <= B0 * mu pow k)
     ==> ?l. (C --> l) sequentially /\ !k. norm(l - C k) <= B0 * mu pow k / (&1 - mu)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k d. norm((C:num->complex)(k + d) - C k) <= B0 * (mu pow k - mu pow (k + d)) / (&1 - mu)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; VECTOR_SUB_REFL; NORM_0; REAL_SUB_REFL; REAL_MUL_RZERO;
                  real_div; REAL_MUL_LZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((C:num->complex)(SUC(k + d)) - C(k + d)) + norm(C(k + d) - C k)` THEN
    CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B0 * mu pow (k + d) + B0 * (mu pow k - mu pow (k + d)) / (&1 - mu)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_pow] THEN
    SUBGOAL_THEN `~(&1 - mu = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k d. norm((C:num->complex)(k + d) - C k) <= B0 * mu pow k / (&1 - mu)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B0 * (mu pow k - mu pow (k + d)) / (&1 - mu)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`mu:real`; `k + d:num`] REAL_POW_LE) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?l. ((C:num->complex) --> l) sequentially` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`mu:real`; `e * (&1 - mu) / (&2 * (B0 + &1))`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE; LE_EXISTS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d1:num`) (X_CHOOSE_TAC `d2:num`)) THEN
    ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((C:num->complex)(N0 + d1) - C N0) + norm(C(N0 + d2) - C N0)` THEN
    CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * (B0 * mu pow N0 / (&1 - mu))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= c /\ b <= c ==> a + b <= &2 * c`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - mu /\ &0 <= mu pow N0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `B0 * mu pow N0 <= (B0 + &1) * mu pow N0 /\
                  (B0 + &1) * mu pow N0 < (B0 + &1) * (e * (&1 - mu) / (&2 * (B0 + &1)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(B0 + &1) * (e * (&1 - mu) / (&2 * (B0 + &1))) = e * (&1 - mu) / &2`
    SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `~(B0 + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `B0 * mu pow N0 / (&1 - mu) < e / &2` MP_TAC THENL
     [SUBGOAL_THEN `B0 * mu pow N0 / (&1 - mu) = (B0 * mu pow N0) / (&1 - mu)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `l:complex` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\m. (C:num->complex) m - C k` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  EXISTS_TAC `k:num` THEN X_GEN_TAC `m:num` THEN REWRITE_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN ASM_REWRITE_TAC[]);;

let WANL_PT_RPOW_SCALE0 = prove
 (`!rho0 lam t k.
     &0 <= lam ==> (rho0 * lam pow k) rpow t = rho0 rpow t * (lam rpow t) pow k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RPOW_MUL] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM RPOW_POW; RPOW_RPOW] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let wanl_pt_lim = new_definition
 `wanl_pt_lim (v:real^2->real) c N (x0:real^2) rho0 lam =
    \n. lim sequentially (\k. wanl_pt_it v c N x0 rho0 lam k n)`;;

let WANL_PT_LAM_FACTS = prove
 (`!lam al s. &0 < lam /\ lam < &1 /\ &0 < al /\ al <= s
              ==> &0 < lam rpow s /\ lam rpow s <= lam rpow al /\ lam rpow al < &1`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT];
    MATCH_MP_TAC RPOW_MONO_INV THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`lam:real`; `&1`; `al:real`] RPOW_LT2) THEN
    ASM_REWRITE_TAC[RPOW_ONE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let WANL_PT_TAIL = prove
 (`!(U:real^2->bool) (v:real^2->real) c N x0 rho0 lam al A K n.
     open U /\ cball(x0,rho0) SUBSET U /\ &0 < rho0 /\ smooth_map_on U (\x. lift(v x)) /\
     &0 < lam /\ lam < &1 /\ &0 <= K /\ &0 < al /\
     &2 * lam pow (N + 1) / (&1 - lam) <= lam rpow (&N + al) / &2 /\
     A / &4 <= K / &2 * lam rpow (&N + al) /\
     (!rho x. &0 < rho /\ rho <= rho0 /\ x IN ball(x0,rho)
              ==> abs(llap (\y:real^2. mat 1) v x - c) <= A * rho rpow (&N + al - &2)) /\
     (!x. x IN cball(x0,rho0)
          ==> abs(v x - c / &4 * norm(x - x0) pow 2) <= K * rho0 rpow (&N + al)) /\
     n <= N
     ==> ((\k. wanl_pt_it v c N x0 rho0 lam k n) --> wanl_pt_lim v c N x0 rho0 lam n)
         sequentially /\
         !k. norm(wanl_pt_lim v c N x0 rho0 lam n - wanl_pt_it v c N x0 rho0 lam k n)
             <= &2 * K * (rho0 * lam pow k) rpow (&N + al - &n) / (&1 - lam rpow al)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `mu = lam rpow (&N + al - &n)` THEN
  SUBGOAL_THEN `&0 < mu /\ mu <= lam rpow al /\ lam rpow al < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC WANL_PT_LAM_FACTS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `n <= N:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B0 = &2 * K * rho0 rpow (&N + al - &n)` THEN
  SUBGOAL_THEN `&0 <= B0` ASSUME_TAC THENL
   [EXPAND_TAC "B0" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`\k. wanl_pt_it (v:real^2->real) c N x0 rho0 lam k n`; `B0:real`; `mu:real`]
         WANL_PT_GEOM_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`rho0:real`; `lam:real`; `&N + al`; `k:num`; `n:num`] WANL_PT_RPOW_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_ARITH `(a + b) - c:real = a + b - c`])] THEN
    MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                  `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`; `k:num`; `n:num`]
           WANL_PT_INC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
    MAP_EVERY EXPAND_TAC ["B0"; "mu"] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:complex` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN `wanl_pt_lim (v:real^2->real) c N x0 rho0 lam n = l` SUBST1_TAC THENL
   [REWRITE_TAC[wanl_pt_lim] THEN MATCH_MP_TAC TENDSTO_LIM THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B0 * mu pow k / (&1 - mu)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(rho0 * lam pow k) rpow (&N + al - &n) = rho0 rpow (&N + al - &n) * mu pow k`
  SUBST1_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC WANL_PT_RPOW_SCALE0 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mu pow k /\ &0 < &1 - mu /\ &0 < &1 - lam rpow al`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * K * (rho0 rpow (&N + al - &n) * mu pow k) / (&1 - lam rpow al) =
                (B0 * mu pow k) * inv(&1 - lam rpow al) /\
                B0 * mu pow k / (&1 - mu) = (B0 * mu pow k) * inv(&1 - mu)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "B0" THEN REWRITE_TAC[real_div] THEN CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_NEAR = prove
 (`!(U:real^2->bool) (v:real^2->real) c N x0 rho0 lam al A K k x.
     open U /\ cball(x0,rho0) SUBSET U /\ &0 < rho0 /\ smooth_map_on U (\x. lift(v x)) /\
     &0 < lam /\ lam < &1 /\ &0 <= K /\ &0 < al /\
     &2 * lam pow (N + 1) / (&1 - lam) <= lam rpow (&N + al) / &2 /\
     A / &4 <= K / &2 * lam rpow (&N + al) /\
     (!rho x. &0 < rho /\ rho <= rho0 /\ x IN ball(x0,rho)
              ==> abs(llap (\y:real^2. mat 1) v x - c) <= A * rho rpow (&N + al - &2)) /\
     (!x. x IN cball(x0,rho0)
          ==> abs(v x - c / &4 * norm(x - x0) pow 2) <= K * rho0 rpow (&N + al)) /\
     norm(x - x0) <= rho0 * lam pow k
     ==> abs(wanl_pt_res v c (wanl_pt_lim v c N x0 rho0 lam) N x0 x)
         <= K * (&1 + &2 * &(N + 1) / (&1 - lam rpow al)) * (rho0 * lam pow k) rpow (&N + al)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `rho = rho0 * lam pow k` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - lam rpow al` ASSUME_TAC THENL
   [MP_TAC(SPECL [`lam:real`; `al:real`; `al:real`] WANL_PT_LAM_FACTS) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wanl_pt_res v c (wanl_pt_lim v c N x0 rho0 lam) N x0 x =
    wanl_pt_res v c (wanl_pt_it v c N x0 rho0 lam k) N x0 x -
    wanl_pt_hp (\n. wanl_pt_lim v c N x0 rho0 lam n - wanl_pt_it v c N x0 rho0 lam k n) N x0 x`
  SUBST1_TAC THENL
   [REWRITE_TAC[wanl_pt_res; WANL_PT_HP_SUB; ETA_AX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b p q r. abs a <= p /\ abs b <= q /\ p + q = r ==> abs(a - b) <= r`) THEN
  EXISTS_TAC `K * rho rpow (&N + al)` THEN
  EXISTS_TAC `&(N + 1) * (&2 * K * rho rpow (&N + al) / (&1 - lam rpow al))` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                  `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`] WANL_PT_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`k:num`; `x:real^2`]) THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[real_div] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..N) (\n. norm(wanl_pt_lim v c N x0 rho0 lam n -
                                  wanl_pt_it v c N x0 rho0 lam k n) * norm(x - x0) pow n)` THEN
  REWRITE_TAC[WANL_PT_HP_BOUND] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..N) (\n. &2 * K * rho rpow (&N + al) / (&1 - lam rpow al))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `norm(wanl_pt_lim v c N x0 rho0 lam n - wanl_pt_it v c N x0 rho0 lam k n) <=
      &2 * K * rho rpow (&N + al - &n) / (&1 - lam rpow al)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                    `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`; `n:num`]
             WANL_PT_TAIL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(x - x0:real^2) pow n <= rho pow n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * K * rho rpow (&N + al - &n) / (&1 - lam rpow al)) * rho pow n` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `rho rpow (&N + al - &n) * rho pow n = rho rpow (&N + al)` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_LE_REFL]);;

let WANL_PT_SCALES = prove
 (`!rho0 lam s K1 d f.
     &0 < rho0 /\ &0 < lam /\ lam < &1 /\ &0 <= K1 /\ &0 < s /\ &0 <= d /\ d <= rho0 /\
     (!k. d <= rho0 * lam pow k ==> abs f <= K1 * (rho0 * lam pow k) rpow s)
     ==> abs f <= K1 / lam rpow s * d rpow s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < lam rpow s /\ lam rpow s < &1 /\ &0 < rho0 rpow s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT] THEN MP_TAC(SPECL [`lam:real`; `&1`; `s:real`] RPOW_LT2) THEN
    ASM_REWRITE_TAC[RPOW_ONE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `d = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ; REAL_MUL_RZERO] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`lam rpow s`; `abs f / (K1 * rho0 rpow s + &1)`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POW_LE] THEN
    ASM_SIMP_TAC[WANL_PT_RPOW_SCALE0; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 < K1 * rho0 rpow s + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(K1 * rho0 rpow s + &1) * lam rpow s pow k < abs f` MP_TAC THENL
     [UNDISCH_TAC `lam rpow s pow k < abs f / (K1 * rho0 rpow s + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lam rpow s pow k` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?m. rho0 * lam pow m < d` MP_TAC THENL
   [MP_TAC(SPECL [`lam:real`; `d / rho0`] REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_RDIV_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[num_WOP] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m = 0)` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `rho0 * lam pow 0 < d` THEN REWRITE_TAC[real_pow] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    MATCH_MP (MESON[num_CASES] `~(m = 0) ==> ?k. m = SUC k`)) THEN
  SUBGOAL_THEN `d <= rho0 * lam pow k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `R = rho0 * lam pow k` THEN
  SUBGOAL_THEN `lam * R < d` ASSUME_TAC THENL
   [UNDISCH_TAC `rho0 * lam pow SUC k < d` THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` (ASSUME `!k. d <= rho0 * lam pow k
                                    ==> abs f <= K1 * (rho0 * lam pow k) rpow s`)) THEN
  REWRITE_TAC[ASSUME `rho0 * lam pow k = R`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `R rpow s <= (d * inv lam) rpow s` MP_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_MUL; RPOW_INV] THEN DISCH_TAC THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(K1 * i) * x:real = K1 * (x * i)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let WANL_PT_EXPANSION = prove
 (`!(U:real^2->bool) (v:real^2->real) c N x0 rho0 lam al A K.
     open U /\ cball(x0,rho0) SUBSET U /\ &0 < rho0 /\ smooth_map_on U (\x. lift(v x)) /\
     &0 < lam /\ lam < &1 /\ &0 <= K /\ &0 < al /\
     &2 * lam pow (N + 1) / (&1 - lam) <= lam rpow (&N + al) / &2 /\
     A / &4 <= K / &2 * lam rpow (&N + al) /\
     (!rho x. &0 < rho /\ rho <= rho0 /\ x IN ball(x0,rho)
              ==> abs(llap (\y:real^2. mat 1) v x - c) <= A * rho rpow (&N + al - &2)) /\
     (!x. x IN cball(x0,rho0)
          ==> abs(v x - c / &4 * norm(x - x0) pow 2) <= K * rho0 rpow (&N + al))
     ==> (!n. n <= N
              ==> norm(wanl_pt_lim v c N x0 rho0 lam n)
                  <= &2 * K * rho0 rpow (&N + al - &n) / (&1 - lam rpow al)) /\
         (!x. x IN cball(x0,rho0)
              ==> abs(wanl_pt_res v c (wanl_pt_lim v c N x0 rho0 lam) N x0 x)
                  <= (K * (&1 + &2 * &(N + 1) / (&1 - lam rpow al))) / lam rpow (&N + al) *
                     norm(x - x0) rpow (&N + al))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                  `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`; `n:num`]
           WANL_PT_TAIL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2) THEN
    REWRITE_TAC[CONJUNCT1 wanl_pt_it; real_pow; REAL_MUL_RID; VECTOR_SUB_RZERO;
                GSYM COMPLEX_VEC_0];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC WANL_PT_SCALES THEN
  EXISTS_TAC `rho0:real` THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MP_TAC(SPECL [`lam:real`; `al:real`; `al:real`] WANL_PT_LAM_FACTS) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 < y ==> &0 < x + y`) THEN
    ASM_REWRITE_TAC[REAL_POS];
    UNDISCH_TAC `(x:real^2) IN cball(x0,rho0)` THEN REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                  `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`; `k:num`; `x:real^2`]
           WANL_PT_NEAR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC]]);;

let WANL_PT_LAM_CHOICE = prove
 (`!al. &0 < al /\ al < &1
        ==> &0 < inv(&8) rpow inv(&1 - al) /\ inv(&8) rpow inv(&1 - al) <= inv(&8) /\
            (inv(&8) rpow inv(&1 - al)) rpow (&1 - al) = inv(&8)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN REWRITE_TAC[GSYM RPOW_POW] THEN
    MATCH_MP_TAC RPOW_MONO_INV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[RPOW_RPOW; REAL_LE_INV_EQ; REAL_POS] THEN
    SUBGOAL_THEN `inv(&1 - al) * (&1 - al) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_POW; REAL_POW_1]]]);;

let WANL_PT_LAM_COND = prove
 (`!al lam N.
     &0 < al /\ al < &1 /\ &0 < lam /\ lam <= inv(&8) /\ lam rpow (&1 - al) = inv(&8)
     ==> &2 * lam pow (N + 1) / (&1 - lam) <= lam rpow (&N + al) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lam pow (N + 1) = lam rpow (&N + al) * inv(&8)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
    REWRITE_TAC[GSYM RPOW_POW; GSYM REAL_OF_NUM_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam rpow (&N + al) /\ &0 < &1 - lam` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT] THEN UNDISCH_TAC `lam <= inv(&8)` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = lam rpow (&N + al)` THEN
  SUBGOAL_THEN `inv(&1 - lam) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(inv(&2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `lam <= inv(&8)` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `P * inv(&1 - lam) <= P * &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let WANL_PT_EXPAND = prove
 (`!N al. &0 < al /\ al < &1
     ==> ?C. &0 < C /\
             !(U:real^2->bool) (v:real^2->real) c x0 rho0 A B.
                open U /\ cball(x0,rho0) SUBSET U /\ &0 < rho0 /\
                smooth_map_on U (\x. lift(v x)) /\ &0 <= A /\
                (!rho x. &0 < rho /\ rho <= rho0 /\ x IN ball(x0,rho)
                         ==> abs(llap (\y:real^2. mat 1) v x - c)
                             <= A * rho rpow (&N + al - &2)) /\
                (!x. x IN cball(x0,rho0) ==> abs(v x - c / &4 * norm(x - x0) pow 2) <= B)
                ==> ?cf. (!n. n <= N
                              ==> norm(cf n) <= C * (B / rho0 rpow (&N + al) + A) *
                                                 rho0 rpow (&N + al - &n)) /\
                         (!x. x IN cball(x0,rho0)
                              ==> abs(v x - c / &4 * norm(x - x0) pow 2 -
                                      wanl_pt_hp cf N x0 x)
                                  <= C * (B / rho0 rpow (&N + al) + A) *
                                     norm(x - x0) rpow (&N + al))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `al:real` WANL_PT_LAM_CHOICE) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `lam = inv(&8) rpow inv(&1 - al)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `lam < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `lam <= inv(&8)` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = lam rpow (&N + al)` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - lam rpow al` ASSUME_TAC THENL
   [MP_TAC(SPECL [`lam:real`; `al:real`; `al:real`] WANL_PT_LAM_FACTS) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C0 = &1 + inv(&2 * L)` THEN
  SUBGOAL_THEN `&1 <= C0 /\ inv(&2 * L) <= C0 /\ &0 <= inv(&2 * L)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C0" THEN
    SUBGOAL_THEN `&0 <= inv(&2 * L)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `X = &2 * &(N + 1) / (&1 - lam rpow al)` THEN
  ABBREV_TAC `Y = &2 / (&1 - lam rpow al)` THEN
  SUBGOAL_THEN `&0 <= X /\ &0 <= Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + X) / L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `C0 * (Y + (&1 + X) / L)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((v:real^2->real) x0 - c / &4 * norm(x0 - x0:real^2) pow 2)` THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P0 = rho0 rpow (&N + al)` THEN
  SUBGOAL_THEN `&0 < P0` ASSUME_TAC THENL
   [EXPAND_TAC "P0" THEN ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `S = B / P0 + A` THEN
  SUBGOAL_THEN `&0 <= B / P0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = B / P0 + A * inv(&2 * L)` THEN
  SUBGOAL_THEN `&0 <= K /\ K <= C0 * S` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "S"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `B / P0 <= C0 * (B / P0) /\ A * inv(&2 * L) <= C0 * A` MP_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A * C0` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`U:real^2->bool`; `v:real^2->real`; `c:real`; `N:num`; `x0:real^2`;
                `rho0:real`; `lam:real`; `al:real`; `A:real`; `K:real`] WANL_PT_EXPANSION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`al:real`; `lam:real`; `N:num`] WANL_PT_LAM_COND) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "K" THEN
      SUBGOAL_THEN `(A * inv(&2 * L)) / &2 * L = A / &4` MP_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (B / P0) / &2 * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "K" THEN
      SUBGOAL_THEN `(B / P0) * P0 = B /\ &0 <= (A * inv(&2 * L)) * P0` MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `&0 < P0` THEN CONV_TAC REAL_FIELD;
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `wanl_pt_lim (v:real^2->real) c N x0 rho0 lam` THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    ABBREV_TAC `Q = rho0 rpow (&N + al - &n)` THEN
    SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * K * Q / (&1 - lam rpow al) = Y * K * Q` SUBST1_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Y * K * Q <= Y * (C0 * S) * Q /\ Y * (C0 * S) * Q <= (C0 * (Y + (&1 + X) / L)) * S * Q`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `&0 <= C0 * S * Q * ((&1 + X) / L)` MP_TAC THENL
         [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
          EXPAND_TAC "S" THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[wanl_pt_res] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  ABBREV_TAC `D = norm(x - x0:real^2) rpow (&N + al)` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(K * (&1 + X)) / L * D = ((&1 + X) / L) * K * D` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + X) / L) * K * D <= ((&1 + X) / L) * (C0 * S) * D /\
                ((&1 + X) / L) * (C0 * S) * D <= (C0 * (Y + (&1 + X) / L)) * S * D`
  MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&0 <= C0 * S * D * Y` MP_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "S" THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

