(* ========================================================================= *)
(* Unit pc_cmw_p15: CMW_P15_STATEMENT (pc_cmw_defs): CM Prop 1.5 (energy     *)
(* sweepouts of slice energy at most the area width, through the conformal   *)
(* reparametrization of CM Lemma D.7, proved in pc_an_beltrami) together     *)
(* with CM footnote 8 (no slice is harmonic, by a cap collapse and           *)
(* CM_CRITICAL_ISOLATED).                                                    *)
(*                                                                           *)
(* Sweepouts with jointly continuous slice Jacobians.                        *)
(* ========================================================================= *)

needs "src/pc_cmw_reg.ml";;

prioritize_real();;
type_invention_error := true;;

(* A jointly C^1 sweepout has C^1 slices with jointly continuous Jacobians. *)

let CMW_C1_IMP_C1SWEEP = prove
 (`!(W:real^3->real->real^K).
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))
        ==> cmw_c1sweep W`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cmw_c1sweep] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_SWEEP_C1_SLICE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CMW_CD1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K`
    STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `ss = {x:real^(3,1)finite_sum |
            ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN
   `!x. x IN ss
        ==> jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                     (at (fstcart x)) =
            matrix(\h. (FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K) x
                           (pastecart h (vec 0)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[jacobian] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN `~(fstcart(x:real^(3,1)finite_sum) = vec 0) /\
                  drop(sndcart x) IN real_interval[&0,&1]` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^(3,1)finite_sum) IN ss` THEN EXPAND_TAC "ss" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`wan_rext (\y. (W:real^3->real->real^K) y
                                     (drop(sndcart(x:real^(3,1)finite_sum))))`;
                   `\h:real^3. (FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K) x
                                 (pastecart h (vec 0))`;
                   `fstcart(x:real^(3,1)finite_sum)`; `{z:real^3 | ~(z = vec 0)}`]
                  HAS_DERIVATIVE_WITHIN_OPEN) THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN
     `wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart(x:real^(3,1)finite_sum)))) =
      (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) o
      (\z. pastecart z (sndcart x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_rext; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h:real^3. (FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K) x
                    (pastecart h (vec 0))) =
      FD x o (\h. pastecart h (vec 0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      ALL_TAC] THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `ss:real^(3,1)finite_sum->bool` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> can (find_term ((=) `FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K`)) (concl th) && is_forall(concl th) &&
                         can (find_term (fun u -> is_const u && fst(dest_const u) = "has_derivative")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "ss" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ss:real^(3,1)finite_sum->bool` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "ss" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[P4_SPHERE_NONZERO]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. lift(((FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K) x
                          (pastecart (basis j) (vec 0)))$i)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[matrix; LAMBDA_BETA; DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(((FD:real^(3,1)finite_sum->real^(3,1)finite_sum->real^K) x
                 (pastecart (basis j) (vec 0)))$i)) =
    (\v:real^K. lift(v$i)) o (\x. FD x (pastecart (basis j) (vec 0)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_LIFT_COMPONENT]);;

let CMW_SHELL_MEASURABLE = prove
 (`measurable wan_shell /\ &0 <= measure wan_shell`,
  SUBGOAL_THEN `measurable wan_shell` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_OPEN THEN REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED];
    ASM_SIMP_TAC[MEASURE_POS_LE]]);;

(* The Dirichlet integral of the difference of two C^1 radial extensions is *)
(* controlled by the sup of the difference of their Jacobians on S^2.        *)

let CMW_REXT_DIFF_DIR_BOUND = prove
 (`!(u:real^3->real^K) v e.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext v) /\
        (!y. y IN sphere(vec 0,&1)
             ==> norm(vectorize(jacobian (wan_rext u) (at y) - jacobian (wan_rext v) (at y)))
                 <= e)
        ==> wan_dir wan_shell (\z. wan_rext u z - wan_rext v z) <=
            &12 * measure wan_shell * e pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(jacobian (wan_rext (u:real^3->real^K)) (at (basis 1)) -
                               jacobian (wan_rext (v:real^3->real^K)) (at (basis 1))))` THEN
    REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `dd = \y. (u:real^3->real^K) y - v y` THEN
  SUBGOAL_THEN `(\z. wan_rext (u:real^3->real^K) z - wan_rext v z) = wan_rext dd`
  SUBST1_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[FUN_EQ_THM; wan_rext]; ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                  (wan_rext (dd:real^3->real^K))` ASSUME_TAC THENL
   [SUBGOAL_THEN `wan_rext (dd:real^3->real^K) =
                  (\z. wan_rext (u:real^3->real^K) z - wan_rext v z)` SUBST1_TAC THENL
     [EXPAND_TAC "dd" THEN REWRITE_TAC[FUN_EQ_THM; wan_rext]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `dd:real^3->real^K` CMW_S2_C1_DIR) THEN ASM_REWRITE_TAC[wan_s2_dir] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(fun th -> SUBST1_TAC(MATCH_MP (REAL_ARITH
    `&2 / &3 * x = &2 / &3 * y ==> x = y`) th)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..3) (\i. &4 * measure wan_shell * e pow 2)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (dd:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (v:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm(partial_derivative i (wan_rext (dd:real^3->real^K)) x) pow 2))
    integrable_on wan_shell`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN
    SUBGOAL_THEN
     `(\x. lift(norm(partial_derivative i (wan_rext (dd:real^3->real^K)) x) pow 2)) =
      (\y:real^K. lift(norm y pow 2)) o (\x. partial_derivative i (wan_rext dd) x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    REWRITE_TAC[CMW_SQNORM_CONT; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC CMW_SHELL_MEASURABLE THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral wan_shell (\x:real^3. lift(&4 * e pow 2)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[INTEGRABLE_ON_CONST; LIFT_DROP] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0) /\ &1 / &2 < norm x` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN wan_shell` THEN REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm x) % x IN sphere(vec 0:real^3,&1) /\
                  ~(inv(norm x) % x = vec 0) /\ x = norm x % inv(norm x) % x`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[P4_RADIAL_SPHERE; VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0;
                   VECTOR_MUL_LID] THEN
      MATCH_MP_TAC P4_SPHERE_NONZERO THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `partial_derivative i (wan_rext (dd:real^3->real^K)) x =
      inv(norm x) %
      ((jacobian (wan_rext (u:real^3->real^K)) (at (inv(norm x) % x)) -
        jacobian (wan_rext (v:real^3->real^K)) (at (inv(norm x) % x))) ** basis i)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`dd:real^3->real^K`; `i:num`; `norm(x:real^3)`; `inv(norm x) % x:real^3`]
                    CMT_REXT_PD_HOMOG) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) o
        check (fun th -> concl th = `x = norm x % inv(norm x) % (x:real^3)`)) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `wan_rext (dd:real^3->real^K) =
                    (\z. wan_rext (u:real^3->real^K) z - wan_rext v z)` SUBST1_TAC THENL
       [EXPAND_TAC "dd" THEN REWRITE_TAC[FUN_EQ_THM; wan_rext]; ALL_TAC] THEN
      ASM_SIMP_TAC[PARTIAL_DERIVATIVE_SUB; ETA_AX] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC(REAL_ARITH `x pow 2 <= (&2 * e) pow 2 ==> x pow 2 <= &4 * e pow 2`) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_INV_EQ; NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize(jacobian (wan_rext (u:real^3->real^K)) (at (inv(norm x) % x)) -
                                 jacobian (wan_rext (v:real^3->real^K)) (at (inv(norm x) % x)))) *
                  norm(basis i:real^3)` THEN
      REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
      ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; REAL_MUL_RID]];
    ASM_SIMP_TAC[INTEGRAL_CONST_GEN; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

let CMW_SLAB_COMPACT = prove
 (`compact {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                     drop(sndcart x) IN real_interval[&0,&1]}`,
  SUBGOAL_THEN
   `{x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                              drop(sndcart x) IN real_interval[&0,&1]} =
    (sphere(vec 0:real^3,&1)) PCROSS (interval[vec 0:real^1,vec 1])`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_REAL_INTERVAL; IN_INTERVAL_1;
                DROP_VEC];
    MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_SPHERE; COMPACT_INTERVAL]]);;

(* Clause 3 of cm_sweep from jointly continuous slice Jacobians. *)

let CMW_C1SWEEP_DIR_CONT = prove
 (`!(W:real^3->real->real^K).
        cmw_c1sweep W
        ==> !t. t IN real_interval[&0,&1]
                ==> ((\s. wan_dir wan_shell
                           (\z. wan_rext (\y. W y s) z - wan_rext (\y. W y t) z)) ---> &0)
                    (atreal t within real_interval[&0,&1])`,
  GEN_TAC THEN REWRITE_TAC[cmw_c1sweep] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "jc")) THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ABBREV_TAC `KK = {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN `compact (KK:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN REWRITE_TAC[CMW_SLAB_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. vectorize(jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                           (at (fstcart x)))) continuous_on KK`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE; DIMINDEX_3] THEN
    REPEAT STRIP_TAC THEN USE_THEN "jc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. vectorize(jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                           (at (fstcart x)))`; `KK:real^(3,1)finite_sum->bool`]
   COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(LABEL_TAC "uc") THEN
  REWRITE_TAC[REALLIM_WITHINREAL; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  MP_TAC CMW_SHELL_MEASURABLE THEN STRIP_TAC THEN
  SUBGOAL_THEN `?e. &0 < e /\ &12 * measure wan_shell * e pow 2 < e'` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) (e' / (&12 * measure wan_shell + &1))` THEN
    SUBGOAL_THEN `&0 < &12 * measure wan_shell + &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < min (&1) (e' / (&12 * measure wan_shell + &1)) /\
      min (&1) (e' / (&12 * measure wan_shell + &1)) <= &1 /\
      min (&1) (e' / (&12 * measure wan_shell + &1)) * (&12 * measure wan_shell + &1) <= e'`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_01; REAL_LT_DIV; GSYM REAL_LE_RDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `c = min (&1) (e' / (&12 * measure wan_shell + &1))` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c pow 2 * measure wan_shell <= c * measure wan_shell` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `c * c <= c * &1 ==> c * c <= c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "uc" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))) THEN
  EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
      (wan_rext (\y. (W:real^3->real->real^K) y s)) /\
    continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (\y. W y t))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!b. &0 <= x /\ x <= b /\ b < e ==> abs x < e`) THEN
  EXISTS_TAC `&12 * measure wan_shell * e pow 2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
    ASM_SIMP_TAC[CMW_REXT_C1_W12; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CMW_REXT_DIFF_DIR_BOUND THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTORIZE_SUB] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  USE_THEN "dd" (MP_TAC o SPECL [`pastecart (y:real^3) (lift t)`;
                                 `pastecart (y:real^3) (lift s)`]) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; dist] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [EXPAND_TAC "KK" THEN
      REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; GSYM LIFT_SUB; NORM_PASTECART; NORM_0;
                  NORM_LIFT] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
      REWRITE_TAC[REAL_ADD_LID; POW_2_SQRT_ABS; REAL_ABS_ABS] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

let CMW_C1_REXT_SMAP = prove
 (`!S (u:real^3->real^K).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        (!y. y IN sphere(vec 0,&1) ==> u y IN S)
        ==> cm_smap S u`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cm_smap; wan_s2_w12; CMW_REXT_C1_W12] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `wan_rext (u:real^3->real^K)` THEN
  CONJ_TAC THENL [SIMP_TAC[CM_REXT_SPHERE]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[P4_SPHERE_NONZERO]]);;

let CMW_C1SWEEP_CM_SWEEP = prove
 (`!S (W:real^3->real->real^K).
        cmw_c1sweep W /\
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t) /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> W y t IN S) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> W y (&0) = W y' (&0) /\ W y (&1) = W y' (&1))
        ==> cm_sweep S W`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_sweep] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMW_C1_REXT_SMAP THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `cmw_c1sweep (W:real^3->real->real^K)` THEN
      REWRITE_TAC[cmw_c1sweep] THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC CMW_C1SWEEP_DIR_CONT THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The embedded image W0 = f o sigma of a Part 4 sweepout, and               *)
(* the Part 4 area of its slices (CMW_EMB_INV_SPHERE and CMW_P4_SLICE moved *)
(* here from pc_cm_width).                                                   *)
(* ========================================================================= *)

let CMW_P4_SWEEPOUT_EQ = prove
 (`!top atlas (s1:real^3->real->A) s2.
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> s1 y t = s2 y t)
        ==> (p4_sweepout (top,atlas:((A->bool)#(A->real^N))->bool) s1 <=>
             p4_sweepout (top,atlas) s2)`,
  SUBGOAL_THEN
   `!top atlas (s1:real^3->real->A) s2.
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> s1 y t = s2 y t) /\
        p4_sweepout (top,atlas:((A->bool)#(A->real^N))->bool) s1
        ==> p4_sweepout (top,atlas) s2`
  (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_sweepout] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\(y,t). (s2:real^3->real->A) y t) = (\p. s2 (FST p) (SND p))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `\p. (s1:real^3->real->A) (FST p) (SND p)` THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; FST; SND;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(\p. (s1:real^3->real->A) (FST p) (SND p)) = (\(y,t). s1 y t)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]; ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x:real^(3,1)finite_sum.
        ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]
        ==> (s2:real^3->real->A) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) =
            s1 (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[P4_RADIAL_SPHERE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x:real^(3,1)finite_sum |
         ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
         (s2:real^3->real->A) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN
         FST (c:(A->bool)#(A->real^N))} =
      {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
           s1 (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN FST c}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P4_C1_EQ_WITHIN THEN
    EXISTS_TAC `\x:real^(3,1)finite_sum.
                  SND (c:(A->bool)#(A->real^N))
                    ((s1:real^3->real->A) (inv(norm(fstcart x)) % fstcart x)
                                          (drop(sndcart x)))` THEN
    ASM_SIMP_TAC[IN_ELIM_THM]]);;

let CMW_FRECHET_EQ_OPEN = prove
 (`!(f:real^M->real^N) g s y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z)
        ==> frechet_derivative f (at y) = frechet_derivative g (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN EQ_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THENL
   [MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`];
    MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `s:real^M->bool`]] THEN
  ASM_SIMP_TAC[]);;

let CMW_P4_AREA_SPHERE_EQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (u:real^3->A) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y)
        ==> p4_s2_area atlas g u = p4_s2_area atlas g u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_s2_area] THEN MATCH_MP_TAC P4_S2_INTEGRAL_EQ THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[p4_s2_density; p4_s2_gram; p4_s2_jac; jacobian] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `y IN sphere(vec 0:real^3,&1)`)]) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((u':real^3->A) y))
                ((u:real^3->A) (inv(norm z) % z))) (at y) =
    frechet_derivative
      (\z. SND (chart_at atlas ((u':real^3->A) y)) (u' (inv(norm z) % z))) (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC CMW_FRECHET_EQ_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[P4_SPHERE_NONZERO; P4_RADIAL_SPHERE]);;

let CMW_EMB_INV_SPHERE = prove
 (`!top (f:A->real^K) (w:real^3->real^K).
        (!y. y IN sphere(vec 0,&1) ==> w y IN IMAGE f (topspace top))
        ==> (!y. y IN sphere(vec 0,&1)
                 ==> mfd_emb_inv top f (w y) IN topspace top /\
                     (f o (mfd_emb_inv top f o w)) y = w y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CMT_EMB_INV_RIGHT]);;

(* The Part 4 area and trace of the slices of mfd_emb_inv o W, for W       *)
(* jointly C^1 with values in f(M), are the CM ones of the slices of W.    *)

let CMW_P4_SLICE = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
   (R:A->real^N^N) (Q:real^K->real^K^K) (W:real^3->real->real^K) t.
     cm_emb (top,atlas) g f G d /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     (!z. transp(Q z) = Q z) /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Q(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     continuously_differentiable 1
       {x:real^(3,1)finite_sum |
          ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
       (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
            ==> W y t IN IMAGE f (topspace top)) /\
     t IN real_interval[&0,&1]
     ==> p4_s2_c1 (top,atlas) (\y. mfd_emb_inv top f (W y t)) /\
         p4_s2_area atlas g (\y. mfd_emb_inv top f (W y t)) = cm_sarea G (\y. W y t) /\
         p4_s2_trint atlas g R (\y. mfd_emb_inv top f (W y t)) =
         cm_strace G Q (\y. W y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. mfd_emb_inv top (f:A->real^K) ((W:real^3->real->real^K) y t)) =
    mfd_emb_inv top f o (\y. W y t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^3->real->real^K`; `t:real`] CMW_SWEEP_C1_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `\y. (W:real^3->real->real^K) y t`]
                CM_EMB_TO_P4) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `R:A->real^N^N`;
                 `Q:real^K->real^K^K`;
                 `mfd_emb_inv top (f:A->real^K) o (\y. (W:real^3->real->real^K) y t)`]
                CM_P4_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`; `\y. (W:real^3->real->real^K) y t`]
                CMW_EMB_INV_SPHERE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:A->real^K) (topspace top)`; `G:real^K->real^K^K`;
                 `Q:real^K->real^K^K`;
                 `(f:A->real^K) o (mfd_emb_inv top f o (\y. (W:real^3->real->real^K) y t))`;
                 `\y. (W:real^3->real->real^K) y t`] CM_SPHERE_ONLY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]]);;

(* The embedded image of a Part 4 sweepout. *)

let CMW_P15_W0 = prove
 (`!top atlas (g:A->real^3^3) (f:A->real^K) G d U sigma.
        cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
        p4_sweepout_in (top,atlas) U sigma
        ==> continuously_differentiable 1
              {x:real^(3,1)finite_sum |
                 ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
              (\x. f(sigma (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))) /\
            (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                   ==> f(sigma y t) IN IMAGE f U) /\
            (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                    ==> f(sigma y (&0)) = f(sigma y' (&0)) /\
                        f(sigma y (&1)) = f(sigma y' (&1))) /\
            (!t. t IN real_interval[&0,&1]
                 ==> cm_sarea G (\y. f(sigma y t)) = p4_s2_area atlas g (\y. sigma y t)) /\
            p4_essential (subtopology top U)
              (p4_susp (\y t. mfd_emb_inv top f (f(sigma y t))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "emb") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[p4_sweepout_in] THEN STRIP_TAC THEN
  USE_THEN "emb" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_emb]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real^K`;
                 `sigma:real^3->real->A`; `U:A->bool`] CMW_EMB_SELF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "self") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `continuously_differentiable 1
      {x:real^(3,1)finite_sum |
         ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
      (\x. (f:A->real^K)((sigma:real^3->real->A)
                           (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `f:A->real^K`;
                   `\y t. (f:A->real^K)((sigma:real^3->real->A) y t)`] CMT_SWEEP_TO_C1) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `sigma:real^3->real->A`;
                     `\y t. mfd_emb_inv top (f:A->real^K) (f((sigma:real^3->real->A) y t))`]
                    CMW_P4_SWEEPOUT_EQ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    UNDISCH_TAC `p4_sweepout (top,atlas:((A->bool)#(A->real^3))->bool) sigma` THEN
    REWRITE_TAC[p4_sweepout] THEN MESON_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `g:A->real^3^3`;
                   `G:real^K->real^K^K`; `\y t. (f:A->real^K)((sigma:real^3->real->A) y t)`;
                   `t:real`] CMW_P4_SLICE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
    MATCH_MP_TAC CMW_P4_AREA_SPHERE_EQ THEN ASM_MESON_TAC[]]);;


(* ========================================================================= *)
(* The pullback metric family of a jointly C^1 sweepout and                  *)
(* its symmetric polynomial approximation (Stone-Weierstrass).              *)
(* ========================================================================= *)

let cmw_pmet = new_definition
 `cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t (y:real^3) =
    transp(jacobian (wan_rext (\y. W y t)) (at y)) ** G(W y t) **
    jacobian (wan_rext (\y. W y t)) (at y)`;;

let CMW_C1_CONT_SLAB = prove
 (`!(W:real^3->real->real^K).
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))
        ==> (\x:real^(3,1)finite_sum. W (fstcart x) (drop(sndcart x))) continuous_on
            {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x:real^(3,1)finite_sum.
                (W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; P4_RADIAL_FIX]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{x:real^(3,1)finite_sum |
                 ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[P4_SPHERE_NONZERO]]);;

let CMW_PMET_FACTS = prove
 (`!S (G:real^K->real^K^K) d (W:real^3->real->real^K).
        cm_target S G d /\
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))
        ==> (\x. vectorize(cmw_pmet G W (drop(sndcart x)) (fstcart x))) continuous_on
            {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
            (!t y. transp(cmw_pmet G W t y) = cmw_pmet G W t y) /\
            (!t y v. &0 <= v dot (cmw_pmet G W t y ** v)) /\
            (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
                   ==> cmw_pmet G W t y ** y = vec 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tg") ASSUME_TAC) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMW_C1_IMP_C1SWEEP) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cmw_pmet] THEN MATCH_MP_TAC P4_GRAM_CONTINUOUS THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE; DIMINDEX_3] THEN
      UNDISCH_TAC `cmw_c1sweep (W:real^3->real->real^K)` THEN
      REWRITE_TAC[cmw_c1sweep] THEN SIMP_TAC[];
      SUBGOAL_THEN
       `(\x:real^(3,1)finite_sum. vectorize((G:real^K->real^K^K)
                                    ((W:real^3->real->real^K) (fstcart x) (drop(sndcart x))))) =
        ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o
        (\x. W (fstcart x) (drop(sndcart x)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[CMW_C1_CONT_SLAB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    REPEAT GEN_TAC THEN REWRITE_TAC[cmw_pmet; MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    USE_THEN "tg" (fun th -> REWRITE_TAC[REWRITE_RULE[cm_target] th]);
    REPEAT GEN_TAC THEN
    REWRITE_TAC[cmw_pmet; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_pmet; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`\y. (W:real^3->real->real^K) y t`; `y:real^3`; `&1`] CM_REXT_JACOBIAN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[P4_SPHERE_NONZERO; REAL_LT_01] THEN
      MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_SIMP_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM; P4_SPHERE_NONZERO] THEN
      UNDISCH_TAC `cmw_c1sweep (W:real^3->real->real^K)` THEN
      REWRITE_TAC[cmw_c1sweep] THEN ASM_SIMP_TAC[];
      SIMP_TAC[MATRIX_VECTOR_MUL_RZERO]]]);;

(* A continuous family of symmetric matrices on a compact set is uniformly  *)
(* close to a symmetric family with polynomial entries.                      *)

let CMW_SYM_POLY_APPROX = prove
 (`!(M:real^(3,1)finite_sum->real^3^3) KK e.
        compact KK /\ (\x. vectorize(M x)) continuous_on KK /\
        (!x. x IN KK ==> transp(M x) = M x) /\ &0 < e
        ==> ?P:real^(3,1)finite_sum->real^3^3.
               (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                      ==> real_polynomial_function (\x. P x$i$j)) /\
               (!x. transp(P x) = P x) /\
               (!x. x IN KK ==> norm(vectorize(P x - M x)) < e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. vectorize((M:real^(3,1)finite_sum->real^3^3) x)`;
                 `KK:real^(3,1)finite_sum->bool`; `e:real`]
                STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(3,1)finite_sum->real^(3,3)finite_prod`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. inv(&2) %% (matrify((g:real^(3,1)finite_sum->real^(3,3)finite_prod) x) +
                              transp(matrify(g x)))` THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT; MATRIX_ADD_COMPONENT; TRANSP_COMPONENT] THEN
    ASM_SIMP_TAC[MATRIFY_COMPONENT; DIMINDEX_3] THEN
    UNDISCH_TAC `vector_polynomial_function
                   (g:real^(3,1)finite_sum->real^(3,3)finite_prod)` THEN
    REWRITE_TAC[vector_polynomial_function; DIMINDEX_FINITE_PROD; DIMINDEX_3] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_MUL THEN
    CONJ_TAC THENL [REWRITE_TAC[real_polynomial_function_RULES]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_ADD THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MATRIX_ADD; TRANSP_TRANSP] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MATRIX_ADD_SYM;
    X_GEN_TAC `x:real^(3,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `inv(&2) %% (matrify((g:real^(3,1)finite_sum->real^(3,3)finite_prod) x) +
                  transp(matrify(g x))) - (M:real^(3,1)finite_sum->real^3^3) x =
      inv(&2) %% ((matrify(g x) - M x) + transp(matrify(g x) - M x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[TRANSP_MATRIX_SUB] THEN ASM_SIMP_TAC[] THEN MATRIX_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VECTORIZE_CMUL; VECTORIZE_ADD; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(inv(&2)) *
                (norm(vectorize(matrify((g:real^(3,1)finite_sum->real^(3,3)finite_prod) x) -
                                (M:real^(3,1)finite_sum->real^3^3) x)) +
                 norm(vectorize(transp(matrify(g x) - M x))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; NORM_TRIANGLE];
      REWRITE_TAC[NORM_VECTORIZE_TRANSP; VECTORIZE_SUB; VECTORIZE_MATRIFY] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(3,1)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC]]);;


(* ========================================================================= *)
(* Jointly smooth families are jet families (bel_jfam), and                  *)
(* the hypotheses of CM Lemma D.7 for metric families with polynomial      *)
(* entries.                                                                  *)
(* ========================================================================= *)

let CMW_BASIS_PASTECART_FST = prove
 (`!i. 1 <= i /\ i <= dimindex(:M)
       ==> (basis i:real^(M,N)finite_sum) = pastecart (basis i:real^M) (vec 0:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[CART_EQ; fstcart; sndcart; LAMBDA_BETA; VEC_COMPONENT] THEN CONJ_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_FINITE_SUM;
                 ARITH_RULE `j <= m ==> j <= m + n:num`];
    SUBGOAL_THEN `1 <= j + dimindex(:M) /\ j + dimindex(:M) <= dimindex(:(M,N)finite_sum)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let CMW_PD_PASTECART_FST = prove
 (`!(FF:real^(M,N)finite_sum->real^P) z c i.
        FF differentiable at (pastecart z c) /\ 1 <= i /\ i <= dimindex(:M)
        ==> partial_derivative i (\z. FF(pastecart z c)) z =
            partial_derivative i FF (pastecart z c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  SUBGOAL_THEN
   `((\z. (FF:real^(M,N)finite_sum->real^P)(pastecart z c)) has_derivative
     (\h. frechet_derivative FF (at (pastecart z c)) (pastecart h (vec 0)))) (at z)`
  MP_TAC THENL
   [SUBGOAL_THEN `(\z. (FF:real^(M,N)finite_sum->real^P)(pastecart z c)) =
                  FF o (\z. pastecart z c)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. frechet_derivative (FF:real^(M,N)finite_sum->real^P) (at (pastecart z c))
             (pastecart h (vec 0))) =
      frechet_derivative FF (at (pastecart z c)) o (\h. pastecart h (vec 0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    ASM_SIMP_TAC[CMW_BASIS_PASTECART_FST]]);;

let CMW_OPEN_FSTCART_PREIMAGE = prove
 (`!U:real^M->bool. open U ==> open {x:real^(M,1)finite_sum | fstcart x IN U}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART]);;

(* A family z |-> FF(z,t) given by a jointly smooth FF is a jet family. *)

let CMW_JFAM_JOINT = prove
 (`!m (FF:real^(M,1)finite_sum->real^N) U.
        open U /\ smooth_map_on {x | fstcart x IN U} FF
        ==> bel_jfam m U (\t z. FF(pastecart z (lift t)))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `open {x:real^(M,1)finite_sum | fstcart x IN U}` ASSUME_TAC THENL
    [ASM_SIMP_TAC[CMW_OPEN_FSTCART_PREIMAGE]; ALL_TAC]) THENL
   [REWRITE_TAC[BEL_JFAM_0] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\z. (FF:real^(M,1)finite_sum->real^N)(pastecart z (lift t))) =
                    FF o (\z. pastecart z (lift t))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{x:real^(M,1)finite_sum | fstcart x IN U}` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART] THEN
        SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
        ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `FF:real^(M,1)finite_sum->real^N` THEN
      CONJ_TAC THENL [SIMP_TAC[LIFT_DROP; PASTECART_FST_SND]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^(M,1)finite_sum | fstcart x IN U}` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_ELIM_THM] THEN SIMP_TAC[]];
    ASM_SIMP_TAC[BEL_JFAM_SUC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `m:num` THEN REWRITE_TAC[LE_0] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
    EXISTS_TAC `\t z. partial_derivative i (FF:real^(M,1)finite_sum->real^N)
                        (pastecart z (lift t))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^M`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMW_PD_PASTECART_FST THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{x:real^(M,1)finite_sum | fstcart x IN U}` THEN
      ASM_REWRITE_TAC[GSYM smooth_map_on; IN_ELIM_THM; FSTCART_PASTECART];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]]]);;

(* The hypotheses of D.7 (except symmetry and positivity) for a metric    *)
(* family whose entries are polynomials in (y,t).                           *)

let CMW_D7_REG_HYPS = prove
 (`!(P:real^(3,1)finite_sum->real^3^3).
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> real_polynomial_function (\x. P x$i$j))
        ==> (!t i j. t IN real_interval[&0,&1] /\
                     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                     ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                           (\z. lift(P(pastecart (inv(norm z) % z) (lift t))$i$j))) /\
            (!l i j. ALL (\k. 1 <= k /\ k <= 3) l /\
                     1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                     ==> (\x:real^(3,1)finite_sum.
                            iterated_partial l
                              (\z. lift(P(pastecart (inv(norm z) % z)
                                                    (lift(drop(sndcart x))))$i$j))
                              (fstcart x))
                         continuous_on
                         {x | ~(fstcart x = vec 0) /\
                              drop(sndcart x) IN real_interval[&0,&1]})`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i j m. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
            ==> bel_jfam m {z:real^3 | ~(z = vec 0)}
                  (\t z. lift((P:real^(3,1)finite_sum->real^3^3)
                                (pastecart (inv(norm z) % z) (lift t))$i$j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`;
                   `\x:real^(3,1)finite_sum.
                      lift((P:real^(3,1)finite_sum->real^3^3)
                             (pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))$i$j)`;
                   `{z:real^3 | ~(z = vec 0)}`] CMW_JFAM_JOINT) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; CMT_OPEN_NONZERO] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `(\x:real^(3,1)finite_sum.
         lift((P:real^(3,1)finite_sum->real^3^3)
                (pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))$i$j)) =
      (\w. lift(P w$i$j)) o
      (\x. pastecart (inv(norm(fstcart x)) % fstcart x) (sndcart x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `{z:real^3 | ~(z = vec 0)}` CMW_OPEN_FSTCART_PREIMAGE) THEN
      REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC SMO_REAL_POLYNOMIAL_SMOOTH THEN ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `open {x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}` ASSUME_TAC THENL
     [MP_TAC(ISPEC `{z:real^3 | ~(z = vec 0)}` CMW_OPEN_FSTCART_PREIMAGE) THEN
      REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\x:real^(3,1)finite_sum. inv(norm(fstcart x)) % fstcart x) =
        (\z:real^3. inv(norm z) % z) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
        REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
        ASM_REWRITE_TAC[LINEAR_FSTCART]];
      REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
      ASM_REWRITE_TAC[LINEAR_SNDCART; ETA_AX]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`0`; `{z:real^3 | ~(z = vec 0)}`;
                   `\t z. lift((P:real^(3,1)finite_sum->real^3^3)
                                 (pastecart (inv(norm z) % z) (lift t))$i$j)`; `t:real`]
                  BEL_JFAM_SMOOTH) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`; `LENGTH(l:num list)`]) THEN
    ASM_REWRITE_TAC[bel_jfam; BEL_DOM_NONZERO; DIMINDEX_3] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[LE_REFL]]);;


(* ========================================================================= *)
(* Matrix algebra for the conformal reparametrization: outer                 *)
(* products, e2(A) = det(A + y y^T) for A symmetric with A y = 0, |y| = 1, *)
(* the Jacobian identity for H(z) = |z| h(z/|z|), and the Gram matrix of a *)
(* conformal map.                                                            *)
(* ========================================================================= *)

let cmw_outer = new_definition
 `cmw_outer (a:real^N) (b:real^M) = (lambda i j. a$i * b$j):real^M^N`;;

let CMW_OUTER_COMPONENT = prove
 (`!(a:real^N) (b:real^M) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:M)
        ==> (cmw_outer a b)$i$j = a$i * b$j`,
  SIMP_TAC[cmw_outer; LAMBDA_BETA]);;

let CMW_E2_DET_TRICK = prove
 (`!(A:real^3^3) (y:real^3).
        transp A = A /\ A ** y = vec 0 /\ y dot y = &1
        ==> p4_e2 A = det(A + cmw_outer y y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
  SIMP_TAC[TRANSP_COMPONENT; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH; DOT_3] THEN
  STRIP_TAC THEN
  REWRITE_TAC[p4_e2; DET_3; trace; DIMINDEX_3; SUM_3; MATRIX_ADD_COMPONENT] THEN
  SIMP_TAC[CMW_OUTER_COMPONENT; matrix_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

let CMW_OUTER_ALGEBRA = prove
 (`(!(a:real^N) (b:real^M) v. cmw_outer a b ** v = (b dot v) % a) /\
   (!(a:real^N) (b:real^M). transp(cmw_outer a b) = cmw_outer b a) /\
   (!(A:real^N^P) (a:real^N) (b:real^M). A ** cmw_outer a b = cmw_outer (A ** a) b) /\
   (!(a:real^N) (b:real^M) (A:real^Q^M). cmw_outer a b ** A = cmw_outer a (transp A ** b)) /\
   (!(b:real^M). cmw_outer (vec 0:real^N) b = mat 0) /\
   (!(a:real^N). cmw_outer a (vec 0:real^M) = mat 0) /\
   (!c (a:real^N) (b:real^M). cmw_outer (c % a) b = c %% cmw_outer a b)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; cmw_outer; LAMBDA_BETA; matrix_vector_mul; matrix_mul; transp;
           VECTOR_MUL_COMPONENT; MATRIX_CMUL_COMPONENT; VEC_COMPONENT; MAT_COMPONENT;
           dot; REAL_MUL_LZERO; REAL_MUL_RZERO; COND_ID] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  TRY(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[]) THEN
  REAL_ARITH_TAC);;

let CMW_OUTER_MV = prove
 (`!(a:real^N) (b:real^M) v. cmw_outer a b ** v = (b dot v) % a`,
  REWRITE_TAC[CMW_OUTER_ALGEBRA]);;

let CMW_OUTER_TRANSP = prove
 (`!(a:real^N) (b:real^M). transp(cmw_outer a b) = cmw_outer b a`,
  REWRITE_TAC[CMW_OUTER_ALGEBRA]);;

let CMW_MUL_OUTER = prove
 (`!(A:real^N^P) (a:real^N) (b:real^M). A ** cmw_outer a b = cmw_outer (A ** a) b`,
  REWRITE_TAC[CMW_OUTER_ALGEBRA]);;

let CMW_OUTER_MUL_MAT = prove
 (`!(a:real^N) (b:real^M) (A:real^Q^M). cmw_outer a b ** A = cmw_outer a (transp A ** b)`,
  REWRITE_TAC[CMW_OUTER_ALGEBRA]);;

let CMW_OUTER_ZERO = prove
 (`(!(b:real^M). cmw_outer (vec 0:real^N) b = mat 0) /\
   (!(a:real^N). cmw_outer a (vec 0:real^M) = mat 0)`,
  REWRITE_TAC[CMW_OUTER_ALGEBRA]);;

let CMW_OUTER_MUL = prove
 (`!(a:real^N) (b:real^M) (c:real^M) (d:real^P).
        cmw_outer a b ** cmw_outer c d = (b dot c) %% cmw_outer a d`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; cmw_outer; LAMBDA_BETA; matrix_mul; MATRIX_CMUL_COMPONENT; dot] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The Gram identity behind the Jacobian of H(z) = |z| h(z/|z|):            *)
(* DH^T (Pi X Pi + h h^T) DH = J^T X J + y y^T, with DH = J + h y^T.         *)

let CMW_DH_GRAM = prove
 (`!(J:real^3^3) (X:real^3^3) (h:real^3) (y:real^3).
        J ** y = vec 0 /\ transp J ** h = vec 0 /\ h dot h = &1
        ==> transp(J + cmw_outer h y) **
            ((mat 1 - cmw_outer h h) ** X ** (mat 1 - cmw_outer h h) + cmw_outer h h) **
            (J + cmw_outer h y) =
            transp J ** X ** J + cmw_outer y y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P:real^3^3 = mat 1 - cmw_outer h h` THEN
  SUBGOAL_THEN `(P:real^3^3) ** h = vec 0 /\ transp P = P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID; CMW_OUTER_MV;
                TRANSP_MATRIX_SUB; TRANSP_MAT; CMW_OUTER_TRANSP] THEN
    REWRITE_TAC[ASSUME `(h:real^3) dot h = &1`; VECTOR_MUL_LID; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^3^3) ** (J:real^3^3) = J` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `mat 1 - cmw_outer h h = (P:real^3^3)`)] THEN
    REWRITE_TAC[MATRIX_SUB_RDISTRIB; MATRIX_MUL_LID; CMW_OUTER_MUL_MAT] THEN
    REWRITE_TAC[ASSUME `transp(J:real^3^3) ** h = vec 0`; CMW_OUTER_ZERO;
                MATRIX_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp (J:real^3^3) ** (P:real^3^3) = transp J` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `transp:real^3^3->real^3^3`) THEN
    ASM_REWRITE_TAC[MATRIX_TRANSP_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^3^3) ** cmw_outer h (y:real^3) = mat 0 /\
                cmw_outer (y:real^3) (h:real^3) ** P = mat 0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CMW_MUL_OUTER; CMW_OUTER_MUL_MAT; CMW_OUTER_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `cmw_outer (h:real^3) h ** (J:real^3^3) = mat 0 /\
                transp J ** cmw_outer h (y:real^3) = mat 0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CMW_MUL_OUTER; CMW_OUTER_MUL_MAT; CMW_OUTER_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `cmw_outer (h:real^3) h ** cmw_outer h (y:real^3) = cmw_outer h y /\
                cmw_outer (y:real^3) h ** cmw_outer h y = cmw_outer y y`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CMW_OUTER_MUL; MATRIX_CMUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((P:real^3^3) ** (X:real^3^3) ** P + cmw_outer (h:real^3) h) **
    ((J:real^3^3) + cmw_outer h (y:real^3)) =
    P ** X ** J + cmw_outer h y`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB; GSYM MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_RZERO; MATRIX_ADD_RID; MATRIX_ADD_LID];
    ALL_TAC] THEN
  REWRITE_TAC[TRANSP_MATRIX_ADD; CMW_OUTER_TRANSP; MATRIX_ADD_LDISTRIB;
              MATRIX_ADD_RDISTRIB] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  MATRIX_ARITH_TAC);;

(* e2 of a Gram matrix J^T X J (with J y = 0, J^T h = 0) through the       *)
(* Jacobian determinant of DH = J + h y^T.                                  *)

let CMW_E2_CHANGE = prove
 (`!(J:real^3^3) (X:real^3^3) (h:real^3) (y:real^3).
        transp X = X /\ J ** y = vec 0 /\ transp J ** h = vec 0 /\
        h dot h = &1 /\ y dot y = &1
        ==> p4_e2(transp J ** X ** J) =
            det(J + cmw_outer h y) pow 2 *
            p4_e2((mat 1 - cmw_outer h h) ** X ** (mat 1 - cmw_outer h h))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(mat 1 - cmw_outer h h) ** (h:real^3) = vec 0 /\
                transp(mat 1 - cmw_outer h h) = mat 1 - cmw_outer (h:real^3) h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID; CMW_OUTER_MV;
                TRANSP_MATRIX_SUB; TRANSP_MAT; CMW_OUTER_TRANSP] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`transp(J:real^3^3) ** (X:real^3^3) ** J`; `y:real^3`] CMW_E2_DET_TRICK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_MUL_ASSOC;
                    GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RZERO];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`J:real^3^3`; `X:real^3^3`; `h:real^3`; `y:real^3`] CMW_DH_GRAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
  MP_TAC(ISPECL [`(mat 1 - cmw_outer h h) ** (X:real^3^3) ** (mat 1 - cmw_outer h h)`;
                 `h:real^3`] CMW_E2_DET_TRICK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC;
                    GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RZERO];
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

(* The Gram matrix of a conformal map of S^2 at y: lam times the tangent   *)
(* projection.                                                               *)

let CMW_CONF_GRAM = prove
 (`!(J:real^3^3) (X:real^3^3) (y:real^3) lam.
        J ** y = vec 0 /\ y dot y = &1 /\
        (!v w. v dot y = &0 /\ w dot y = &0
               ==> (J ** v) dot (X ** (J ** w)) = lam * (v dot w))
        ==> transp J ** X ** J = lam %% (mat 1 - cmw_outer y y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= 3
        ==> (J:real^3^3) ** basis k = J ** (basis k - (y:real^3)$k % y) /\
            (basis k - y$k % y) dot y = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                 VECTOR_MUL_RZERO; VECTOR_SUB_RZERO; DOT_LSUB; DOT_LMUL; DOT_BASIS;
                 DIMINDEX_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((transp J ** X ** J):real^3^3)$i$j =
                (J ** basis i) dot ((X:real^3^3) ** ((J:real^3^3) ** basis j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMT_GRAM_ENTRY THEN ASM_REWRITE_TAC[DIMINDEX_3]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT; MATRIX_SUB_COMPONENT; MAT_COMPONENT; DIMINDEX_3;
               CMW_OUTER_COMPONENT] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
  ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; BASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^3) dot y = &1` THEN CONV_TAC REAL_RING);;

let CMW_PROJ_TRACE_E2 = prove
 (`!(y:real^3) lam.
        y dot y = &1
        ==> trace(lam %% (mat 1 - cmw_outer y y)) = &2 * lam /\
            p4_e2(lam %% (mat 1 - cmw_outer y y)) = lam pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DOT_3] THEN DISCH_TAC THEN
  REWRITE_TAC[p4_e2; trace; DIMINDEX_3; SUM_3] THEN
  SIMP_TAC[matrix_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3; MATRIX_CMUL_COMPONENT;
           MATRIX_SUB_COMPONENT; MAT_COMPONENT; CMW_OUTER_COMPONENT] THEN
  UNDISCH_TAC `(y:real^3)$1 * y$1 + y$2 * y$2 + y$3 * y$3 = &1` THEN
  CONV_TAC REAL_RING);;

let CMW_TRACE_GRAM_LE = prove
 (`!(J:real^3^3) (M:real^3^3) X.
        (!v. v dot (M ** v) <= v dot (X ** v))
        ==> trace(transp J ** M ** J) <= trace(transp J ** X ** J)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CMT_GRAM_ENTRY]);;


(* ========================================================================= *)
(* Change of variables on S^2 for a C^1 bijection h of S^2,                  *)
(* through H(z) = |z| h(z/|z|) on the punctured unit ball.                  *)
(* ========================================================================= *)

let CMW_NORM_HAS_DERIVATIVE = prove
 (`!a:real^N. ~(a = vec 0)
        ==> ((lift o (\z. norm z)) has_derivative (lift o (\v. (a dot v) / norm a))) (at a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(a:real^N)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(INST [`norm(a:real^N) pow 2`,`s:real`]
     (DISCH_ALL(REAL_DIFF_CONV `((\s. sqrt s) has_real_derivative f') (atreal s)`))) THEN
  ASM_SIMP_TAC[POW_2_SQRT; NORM_POS_LE; REAL_POW_LT] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `a:real^N` HAS_DERIVATIVE_SQNORM_AT) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. lift(norm x pow 2)`; `lift o (\s. sqrt s) o drop`;
                 `\x:real^N. &2 % lift(a dot x)`;
                 `\x:real^1. (&1 * inv(&2 * norm(a:real^N))) % x`;
                 `a:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^N` THENL
   [SIMP_TAC[POW_2_SQRT; NORM_POS_LE];
    REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
    UNDISCH_TAC `&0 < norm(a:real^N)` THEN CONV_TAC REAL_FIELD]);;

let CMW_H_DERIVATIVE = prove
 (`!(h:real^3->real^3) z.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext h) /\
        ~(z = vec 0)
        ==> ((\z. norm z % wan_rext h z) has_derivative
             (\v. (jacobian (wan_rext h) (at (inv(norm z) % z)) +
                   cmw_outer (h(inv(norm z) % z)) (inv(norm z) % z)) ** v)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext (h:real^3->real^3) differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. norm z`; `\v:real^3. ((z:real^3) dot v) / norm z`;
                 `wan_rext (h:real^3->real^3)`;
                 `\v. jacobian (wan_rext (h:real^3->real^3)) (at z) ** v`; `z:real^3`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ASM_SIMP_TAC[CMW_NORM_HAS_DERIVATIVE; GSYM JACOBIAN_WORKS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^3` THEN
  SUBGOAL_THEN `~(inv(norm z) % z:real^3 = vec 0) /\ norm z % inv(norm z) % z = z`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC;
                 REAL_MUL_RINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^3->real^3`; `1`; `norm(z:real^3)`; `inv(norm z) % z:real^3`]
                CMT_REXT_PD_HOMOG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; CMW_OUTER_MV; MATRIX_VECTOR_LMUL;
              VECTOR_MUL_ASSOC; DOT_LMUL; wan_rext] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_SYM] THEN VECTOR_ARITH_TAC);;

let CMW_S2_CHANGE = prove
 (`!(h:real^3->real^3) (ff:real^3->real).
        (!y. y IN sphere(vec 0,&1) ==> h y IN sphere(vec 0,&1)) /\
        (!x. x IN sphere(vec 0,&1) ==> ?!y. y IN sphere(vec 0,&1) /\ h y = x) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext h) /\
        (\y. lift(ff y)) continuous_on sphere(vec 0,&1)
        ==> p4_s2_integral
              (\y. ff(h y) * abs(det(jacobian (wan_rext h) (at y) + cmw_outer (h y) y))) =
            p4_s2_integral ff`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bij")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  ABBREV_TAC `s = ball(vec 0:real^3,&1) DIFF {vec 0}` THEN
  SUBGOAL_THEN `!z:real^3. z IN s <=> ~(z = vec 0) /\ norm z < &1` (LABEL_TAC "ins") THENL
   [REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN REWRITE_TAC[IN_DIFF; IN_BALL_0; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> inv(norm z) % z IN sphere(vec 0,&1) /\
                                             norm(norm z % wan_rext (h:real^3->real^3) z) =
                                             norm z`
  (LABEL_TAC "rad") THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_NORM; wan_rext] THEN
    SUBGOAL_THEN `(h:real^3->real^3)(inv(norm z) % z) IN sphere(vec 0,&1)` MP_TAC THENL
     [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; SIMP_TAC[IN_SPHERE_0; REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (s:real^3->bool) /\ negligible {vec 0:real^3}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN REWRITE_TAC[NEGLIGIBLE_SING] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible(ball(vec 0:real^3,&1) DIFF s UNION s DIFF ball(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN SET_TAC[];
    ALL_TAC] THEN
  (* injectivity *)
  SUBGOAL_THEN
   `!z1 z2:real^3. z1 IN s /\ z2 IN s /\
                   norm z1 % wan_rext (h:real^3->real^3) z1 = norm z2 % wan_rext h z2
                   ==> z1 = z2`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z1:real^3`; `z2:real^3`] THEN
    USE_THEN "ins" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(z1:real^3) = norm(z2:real^3)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^3)(inv(norm z1) % z1) = h(inv(norm z2) % z2)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `norm(z1:real^3) % wan_rext (h:real^3->real^3) z1 =
                    norm(z2:real^3) % wan_rext h z2` THEN
      ASM_REWRITE_TAC[wan_rext; VECTOR_MUL_LCANCEL; NORM_EQ_0] THEN
      ASM_MESON_TAC[NORM_EQ_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm z1) % z1 = inv(norm z2) % (z2:real^3)` MP_TAC THENL
     [USE_THEN "bij" (MP_TAC o SPEC `(h:real^3->real^3)(inv(norm z1) % z1)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_SIMP_TAC[P4_RADIAL_SPHERE];
      ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0; NORM_EQ_0]];
    ALL_TAC] THEN
  (* the image *)
  SUBGOAL_THEN `IMAGE (\z:real^3. norm z % wan_rext (h:real^3->real^3) z) s = s`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      USE_THEN "ins" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[VECTOR_MUL_EQ_0; NORM_EQ_0; DE_MORGAN_THM] THEN
      ASM_REWRITE_TAC[wan_rext] THEN
      SUBGOAL_THEN `(h:real^3->real^3)(inv(norm z) % z) IN sphere(vec 0,&1)` MP_TAC THENL
       [ASM_SIMP_TAC[P4_RADIAL_SPHERE];
        REWRITE_TAC[IN_SPHERE_0] THEN CONV_TAC NORM_ARITH];
      USE_THEN "ins" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      USE_THEN "bij" (MP_TAC o C MATCH_MP
        (MATCH_MP P4_RADIAL_SPHERE (ASSUME `~(w:real^3 = vec 0)`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o CONJUNCT1 o
        GEN_REWRITE_RULE I [EXISTS_UNIQUE_THM]) THEN
      EXISTS_TAC `norm(w:real^3) % y:real^3` THEN
      SUBGOAL_THEN `norm(y:real^3) = &1` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < norm(w:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      SUBGOAL_THEN `norm(norm(w:real^3) % y:real^3) = norm w` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_NORM; REAL_MUL_RID]; ALL_TAC] THEN
      SUBGOAL_THEN `inv(norm(norm(w:real^3) % y:real^3)) % (norm w % y) = y` ASSUME_TAC THENL
       [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[wan_rext; VECTOR_MUL_EQ_0; NORM_EQ_0; DE_MORGAN_THM] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      UNDISCH_TAC `norm(y:real^3) = &1` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  (* the integrand f is absolutely integrable on s *)
  ABBREV_TAC `f = \w:real^3. lift((ff:real^3->real)(inv(norm w) % w))` THEN
  SUBGOAL_THEN `(f:real^3->real^1) absolutely_integrable_on s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^3. lift(ff y)`; `sphere(vec 0:real^3,&1)`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\w:real^3. lift B` THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN USE_THEN "ins" (fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[LIFT_DROP] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN SET_TAC[];
        EXPAND_TAC "f" THEN MATCH_MP_TAC P4_S2_INTEGRABLE THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN
      REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN MATCH_MP_TAC MEASURABLE_OPEN THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&1)` THEN
        REWRITE_TAC[BOUNDED_BALL] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_SING]]];
    ALL_TAC] THEN
  (* the change of variables *)
  DISCH_THEN(LABEL_TAC "inj") THEN
  MP_TAC(ISPECL [`f:real^3->real^1`; `\z:real^3. norm z % wan_rext (h:real^3->real^3) z`;
                 `\z v. (jacobian (wan_rext (h:real^3->real^3)) (at (inv(norm z) % z)) +
                         cmw_outer (h(inv(norm z) % z)) (inv(norm z) % z)) ** v`;
                 `s:real^3->bool`; `integral s (f:real^3->real^1)`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC; REWRITE_TAC[] THEN FIRST_ASSUM MATCH_ACCEPT_TAC] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC CMW_H_DERIVATIVE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN s` THEN USE_THEN "ins" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  REMOVE_THEN "inj" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN s
        ==> abs(det(jacobian (wan_rext (h:real^3->real^3)) (at (inv(norm z) % z)) +
                    cmw_outer (h(inv(norm z) % z)) (inv(norm z) % z))) %
            (f:real^3->real^1)(norm z % wan_rext h z) =
            lift((\y. (ff:real^3->real)(h y) *
                       abs(det(jacobian (wan_rext h) (at y) + cmw_outer (h y) y)))
                 (inv(norm z) % z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN USE_THEN "ins" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    USE_THEN "rad" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `~(z:real^3 = vec 0)`)) THEN
    SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[wan_rext; LIFT_CMUL] THEN REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\z:real^3. abs(det(jacobian (wan_rext (h:real^3->real^3))
                                            (at (inv(norm z) % z)) +
                    cmw_outer (h(inv(norm z) % z)) (inv(norm z) % z))) %
            (f:real^3->real^1)(norm z % wan_rext h z)) =
    integral (ball(vec 0,&1))
      (\z. lift((\y. (ff:real^3->real)(h y) *
                      abs(det(jacobian (wan_rext h) (at y) + cmw_outer (h y) y)))
                (inv(norm z) % z)))`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `integral s
        (\z:real^3. lift((\y. (ff:real^3->real)((h:real^3->real^3) y) *
                                   abs(det(jacobian (wan_rext h) (at y) +
                                           cmw_outer (h y) y)))
                     (inv(norm z) % z)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral s (f:real^3->real^1) =
                integral (ball(vec 0,&1)) (\z:real^3. lift((ff:real^3->real)(inv(norm z) % z)))`
  SUBST1_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SYM(ASSUME `ball(vec 0:real^3,&1) DIFF {vec 0} = s`)] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p4_s2_integral] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;


(* ========================================================================= *)
(* Tools for the reparametrized sweepout W1(y,t) = W0(h_t y,t):              *)
(* the chain rule for Jacobians, continuity from the slab, the tangency of  *)
(* the range of a sphere map, projections, uniform continuity of sqrt o e2. *)
(* ========================================================================= *)

let CMW_JACOBIAN_CHAIN = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x.
        f differentiable at x /\ g differentiable at (f x)
        ==> jacobian (g o f) (at x) = jacobian g (at (f x)) ** jacobian f (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN
   `frechet_derivative ((g:real^N->real^P) o (f:real^M->real^N)) (at x) =
    frechet_derivative g (at (f x)) o frechet_derivative f (at x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    MATCH_MP_TAC MATRIX_COMPOSE THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]]);;

let CMW_SLAB_CONTINUOUS_MAP = prove
 (`!(W:real^3->real->real^K).
        (\x:real^(3,1)finite_sum. W (fstcart x) (drop(sndcart x))) continuous_on
        {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]}
        ==> continuous_map
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
              (\(y,t). W y t)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\(y,t). (W:real^3->real->real^K) y t) =
                (\x. W (fstcart x) (drop(sndcart x))) o
                (\p:real^3#real. pastecart (FST p) (lift(SND p)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
                {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                          drop(sndcart x) IN real_interval[&0,&1]}` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_PASTED] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`;
                   `subtopology euclideanreal (real_interval[&0,&1])`]
                       CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX];
    SUBGOAL_THEN `(\x:real^3#real. lift(SND x)) = lift o SND` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM CONTINUOUS_MAP_EQ_LIFT] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`;
                   `subtopology euclideanreal (real_interval[&0,&1])`]
                       CONTINUOUS_MAP_SND) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND] THEN
    SIMP_TAC[]]);;

(* The derivative of a map of S^2 into S^2 (radially extended) is tangent: *)
(* its transpose kills the value.                                            *)

let CMW_RANGE_TANGENT = prove
 (`!(k:real^3->real^3) y.
        (!z. ~(z = vec 0) ==> norm(wan_rext k z) = &1) /\ ~(y = vec 0) /\
        wan_rext k differentiable at y
        ==> transp(jacobian (wan_rext k) (at y)) ** wan_rext k y = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. lift(norm(wan_rext (k:real^3->real^3) z) pow 2)) has_derivative
     (\v. &2 % lift(wan_rext k y dot (jacobian (wan_rext k) (at y) ** v)))) (at y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift(norm(wan_rext (k:real^3->real^3) z) pow 2)) =
      (\w:real^3. lift(norm w pow 2)) o wan_rext k`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. &2 % lift(wan_rext (k:real^3->real^3) y dot (jacobian (wan_rext k) (at y) ** v))) =
      (\x. &2 % lift(wan_rext k y dot x)) o (\v. jacobian (wan_rext k) (at y) ** v)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM JACOBIAN_WORKS; HAS_DERIVATIVE_SQNORM_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(norm(wan_rext (k:real^3->real^3) z) pow 2)) has_derivative
     (\v. vec 0)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. lift(&1)`; `{z:real^3 | ~(z = vec 0)}`] THEN
    ASM_SIMP_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM; HAS_DERIVATIVE_CONST] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT o
    CONJ (ASSUME `((\z. lift(norm(wan_rext (k:real^3->real^3) z) pow 2)) has_derivative
     (\v. &2 % lift(wan_rext k y dot (jacobian (wan_rext k) (at y) ** v)))) (at y)`)) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `transp(jacobian (wan_rext (k:real^3->real^3)) (at y)) **
                            wan_rext k y`) THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; LIFT_EQ; LIFT_NUM; REAL_OF_NUM_EQ; ARITH] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
  ONCE_REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN REWRITE_TAC[DOT_EQ_0]);;

(* The tangent projection Pi = I - w w^T at a unit vector w. *)

let CMW_PROJ_FACTS = prove
 (`!w:real^3. w dot w = &1
        ==> transp(mat 1 - cmw_outer w w) = mat 1 - cmw_outer w w /\
            (mat 1 - cmw_outer w w) ** w = vec 0 /\
            norm(vectorize(mat 1 - cmw_outer w w)) <= &2 /\
            !M:real^3^3. transp M = M /\ M ** w = vec 0
                         ==> (mat 1 - cmw_outer w w) ** M ** (mat 1 - cmw_outer w w) = M`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[TRANSP_MATRIX_SUB; TRANSP_MAT; CMW_OUTER_TRANSP];
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LID; CMW_OUTER_MV;
                    VECTOR_MUL_LID; VECTOR_SUB_REFL];
    SUBGOAL_THEN `norm(vectorize(mat 1 - cmw_outer (w:real^3) w)) pow 2 = &2` MP_TAC THENL
     [REWRITE_TAC[NORM_POW_2; DOT_VECTORIZE] THEN
      REWRITE_TAC[trace; DIMINDEX_3; SUM_3] THEN
      SIMP_TAC[matrix_mul; transp; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3;
               MATRIX_SUB_COMPONENT; MAT_COMPONENT; CMW_OUTER_COMPONENT] THEN
      UNDISCH_TAC `(w:real^3) dot w = &1` THEN REWRITE_TAC[DOT_3] THEN CONV_TAC REAL_RING;
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[REAL_POS; ARITH] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `cmw_outer (w:real^3) w ** (M:real^3^3) = mat 0 /\
                  M ** cmw_outer w w = mat 0`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[CMW_OUTER_MUL_MAT; CMW_MUL_OUTER] THEN
      ASM_REWRITE_TAC[CMW_OUTER_ZERO];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_LID; MATRIX_MUL_RID] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_MUL_RZERO; MATRIX_SUB_REFL; MATRIX_SUB_RZERO]]);;

(* sqrt o e2 is uniformly continuous on bounded sets of 3x3 matrices. *)

let CMW_SQRT_E2_UNIF = prove
 (`!R e. &0 < e
         ==> ?r. &0 < r /\
                 !X Y:real^3^3. norm(vectorize X) <= R /\ norm(vectorize Y) <= R /\
                                norm(vectorize X - vectorize Y) < r
                                ==> abs(sqrt(p4_e2 X) - sqrt(p4_e2 Y)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^(3,3)finite_prod. lift(sqrt(p4_e2(matrify v)))`;
                 `cball(vec 0:real^(3,3)finite_prod,R)`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CMT_CONT_E2 THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIFY_COMPONENT; DIMINDEX_3] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
    REWRITE_TAC[DIMINDEX_FINITE_PROD; DIMINDEX_3] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vectorize(Y:real^3^3)`; `vectorize(X:real^3^3)`]) THEN
  ASM_REWRITE_TAC[IN_CBALL_0; MATRIFY_VECTORIZE; DIST_LIFT; dist]);;

(* Pointwise bound for the energy density of the reparametrized slice:    *)
(* with A = Du(k y), J = Dk(y) conformal for X >= A^T Gm A, the density   *)
(* tr((AJ)^T Gm (AJ))/2 is at most |det(J + k y y^T)| sqrt(e2(Pi X Pi)).  *)

let CMW_SQRT_LAM = prove
 (`!lam d e. &0 < lam /\ lam pow 2 = d pow 2 * e ==> lam = abs d * sqrt e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sqrt(lam pow 2)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SQRT_MUL] THEN REWRITE_TAC[POW_2_SQRT_ABS]]);;

let CMW_DENSITY_REPARAM_LE = prove
 (`!(A:real^3^K) (Gm:real^K^K) (J:real^3^3) (X:real^3^3) (x:real^3) (y:real^3) lam.
        J ** y = vec 0 /\ transp J ** x = vec 0 /\ x dot x = &1 /\ y dot y = &1 /\
        transp X = X /\ &0 < lam /\
        (!v. v dot ((transp A ** Gm ** A) ** v) <= v dot (X ** v)) /\
        (!v w. v dot y = &0 /\ w dot y = &0
               ==> (J ** v) dot (X ** (J ** w)) = lam * (v dot w))
        ==> trace(transp(A ** J) ** Gm ** (A ** J)) / &2 <=
            abs(det(J + cmw_outer x y)) *
            sqrt(p4_e2((mat 1 - cmw_outer x x) ** X ** (mat 1 - cmw_outer x x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((A:real^3^K) ** (J:real^3^3)) ** (Gm:real^K^K) ** (A ** J) =
                transp J ** (transp A ** Gm ** A) ** J` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^3^3`; `X:real^3^3`; `y:real^3`; `lam:real`] CMW_CONF_GRAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`y:real^3`; `lam:real`] CMW_PROJ_TRACE_E2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real^3^3`; `transp(A:real^3^K) ** (Gm:real^K^K) ** A`; `X:real^3^3`]
    CMW_TRACE_GRAM_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`J:real^3^3`; `X:real^3^3`; `x:real^3`; `y:real^3`] CMW_E2_CHANGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lam:real`; `det((J:real^3^3) + cmw_outer (x:real^3) (y:real^3))`;
                 `p4_e2((mat 1 - cmw_outer (x:real^3) x) ** (X:real^3^3) **
                        (mat 1 - cmw_outer x x))`] CMW_SQRT_LAM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_REAL_ARITH_TAC);;

(* Jacobians at x only depend on the map near x. *)

let CMW_JACOBIAN_LOCAL_EQ = prove
 (`!(f:real^M->real^N) g s x.
        open s /\ x IN s /\ (!z. z IN s ==> f z = g z) /\ f differentiable at x
        ==> g differentiable at x /\ jacobian g (at x) = jacobian f (at x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((g:real^M->real^N) has_derivative frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]);;

(* Radial extensions of compositions with a map of S^2 into S^2. *)

let CMW_REXT_COMPOSE = prove
 (`!(u:real^3->real^K) (k:real^3->real^3) z.
        (!y. y IN sphere(vec 0,&1) ==> k y IN sphere(vec 0,&1)) /\ ~(z = vec 0)
        ==> wan_rext (\y. u(k y)) z = (wan_rext u o wan_rext k) z /\
            ~(wan_rext k z = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->real^3)(inv(norm(z:real^3)) % z) IN sphere(vec 0,&1)`
  MP_TAC THENL [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
  REWRITE_TAC[IN_SPHERE_0; wan_rext; o_THM] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC);;

let CMW_SLICE_REPARAM = prove
 (`!(u:real^3->real^K) (k:real^3->real^3).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext k) /\
        (!y. y IN sphere(vec 0,&1) ==> k y IN sphere(vec 0,&1))
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (wan_rext (\y. u(k y))) /\
            !y. y IN sphere(vec 0,&1)
                ==> jacobian (wan_rext (\y. u(k y))) (at y) =
                    jacobian (wan_rext u) (at (k y)) ** jacobian (wan_rext k) (at y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. z IN {z:real^3 | ~(z = vec 0)}
                           ==> (wan_rext u o wan_rext k) z =
                               wan_rext (\y. (u:real^3->real^K)(k y)) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `k:real^3->real^3`; `z:real^3`] CMW_REXT_COMPOSE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC `wan_rext (u:real^3->real^K) o wan_rext (k:real^3->real^3)` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `k:real^3->real^3`; `z:real^3`] CMW_REXT_COMPOSE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ wan_rext (k:real^3->real^3) y = k y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; wan_rext] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((k:real^3->real^3) y = vec 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^3->real^K`; `k:real^3->real^3`; `y:real^3`] CMW_REXT_COMPOSE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext (k:real^3->real^3) differentiable at y /\
                wan_rext (u:real^3->real^K) differentiable at (k y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_rext (u:real^3->real^K) o wan_rext (k:real^3->real^3)`;
                 `wan_rext (\y. (u:real^3->real^K)(k y))`;
                 `{z:real^3 | ~(z = vec 0)}`; `y:real^3`] CMW_JACOBIAN_LOCAL_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`wan_rext (k:real^3->real^3)`; `wan_rext (u:real^3->real^K)`; `y:real^3`]
    CMW_JACOBIAN_CHAIN) THEN
  ASM_REWRITE_TAC[]);;

(* Continuity of Jacobian entries, of the energy and area densities of a    *)
(* C^1 radial extension, and of the projected area density of a field X.    *)

let CMW_C1_JAC_ENTRY_CONT = prove
 (`!s (U:real^M->real^N).
        open s /\ continuously_differentiable 1 s U
        ==> !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:M)
                  ==> (\x. lift(jacobian U (at x)$i$j)) continuous_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CMT_C1_FACTS) THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. lift((partial_derivative j (U:real^M->real^N) x)$i)` THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX]]);;

let CMW_DENS_CONT = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)
        ==> (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                   ==> (\y. lift((transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                                  jacobian (wan_rext u) (at y))$i$j))
                       continuous_on sphere(vec 0,&1)) /\
            (\y. lift(trace(transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                            jacobian (wan_rext u) (at y)) / &2))
            continuous_on sphere(vec 0,&1) /\
            (\y. lift(sqrt(p4_e2(transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                                 jacobian (wan_rext u) (at y)))))
            continuous_on sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o REWRITE_RULE[ETA_AX])))) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    continuous_on (:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `smooth_map_on (:real^K)
                   ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))` THEN
    SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (\y. lift((transp(jacobian (wan_rext (u:real^3->real^K)) (at y)) **
                         (G:real^K->real^K^K)(u y) **
                         jacobian (wan_rext u) (at y))$i$j))
              continuous_on sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                         ((G:real^K->real^K^K)(wan_rext u x) **
                          partial_derivative j (wan_rext u) x))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[P4_SPHERE_NONZERO]; ALL_TAC] THEN
      ASM_SIMP_TAC[CM_REXT_SPHERE] THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`jacobian (wan_rext (u:real^3->real^K)) (at x)`;
                     `(G:real^K->real^K^K)((u:real^3->real^K) x)`;
                     `i:num`; `j:num`] CMT_GRAM_ENTRY) THEN
      ASM_SIMP_TAC[DIMINDEX_3];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; P4_SPHERE_NONZERO] THEN
      MATCH_MP_TAC CMT_CONT_QUAD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CMT_CONT_TRACE THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CMT_CONT_E2 THEN ASM_REWRITE_TAC[]]);;

let CMW_PROJ_DENS_CONT = prove
 (`!(X:real^3->real^3^3) s.
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(X x$i$j)) continuous_on s)
        ==> (\x. lift(sqrt(p4_e2((mat 1 - cmw_outer x x) ** X x **
                                 (mat 1 - cmw_outer x x))))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (\x:real^3. lift((mat 1 - cmw_outer x x:real^3^3)$i$j)) continuous_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MAT_COMPONENT; CMW_OUTER_COMPONENT; DIMINDEX_3;
                 LIFT_SUB; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (\x:real^3. lift(((X:real^3->real^3^3) x ** (mat 1 - cmw_outer x x))$i$j))
              continuous_on s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `X:real^3->real^3^3`;
                   `\x:real^3. (mat 1 - cmw_outer x x):real^3^3`] CMT_CONT_MATMUL) THEN
    REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC CMT_CONT_E2 THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\x:real^3. (mat 1 - cmw_outer x x):real^3^3`;
                 `\x:real^3. (X:real^3->real^3^3) x ** (mat 1 - cmw_outer x x)`]
                CMT_CONT_MATMUL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* The energy of the reparametrized slice u o k: if k is a C^1 bijection of *)
(* S^2, conformal for a field X dominating the pullback metric of u, and    *)
(* the projected area density of X exceeds that of u by at most c, then     *)
(* E(u o k) <= Area(u) + 4 pi c (4 pi written as 3 |B|).                     *)

let CMW_SPHERE_MAP_CONT = prove
 (`!(k:real^3->real^N).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext k)
        ==> k continuous_on sphere(vec 0,&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `wan_rext (k:real^3->real^N)` THEN
  SIMP_TAC[CM_REXT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; P4_SPHERE_NONZERO] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
  EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]);;

let CMW_TRANSPORT_DENS_CONT = prove
 (`!(k:real^3->real^3) (FF:real^3->real).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext k) /\
        (!y. y IN sphere(vec 0,&1) ==> k y IN sphere(vec 0,&1)) /\
        (\x. lift(FF x)) continuous_on sphere(vec 0,&1)
        ==> (\y. lift(FF(k y) * abs(det(jacobian (wan_rext k) (at y) + cmw_outer (k y) y))))
            continuous_on sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->real^3) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_SPHERE_MAP_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `lift o (\y. (FF:real^3->real)((k:real^3->real^3) y)) =
                  (\x. lift(FF x)) o k` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN
  REWRITE_TAC[DIMINDEX_3] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; CMW_OUTER_COMPONENT; DIMINDEX_3; LIFT_ADD;
               LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; P4_SPHERE_NONZERO] THEN
    MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (k:real^3->real^3)`]
      CMW_C1_JAC_ENTRY_CONT) THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; DIMINDEX_3] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX];
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_3]]);;

let CMW_SLICE_ENERGY_REPARAM = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) (k:real^3->real^3) (X:real^3->real^3^3) c.
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext k) /\
        (!y. y IN sphere(vec 0,&1) ==> k y IN sphere(vec 0,&1)) /\
        (!x. x IN sphere(vec 0,&1) ==> ?!y. y IN sphere(vec 0,&1) /\ k y = x) /\
        (!y. y IN sphere(vec 0,&1)
             ==> ?lam. &0 < lam /\
                       !v w. v dot y = &0 /\ w dot y = &0
                             ==> (jacobian (wan_rext k) (at y) ** v) dot
                                 (X(k y) ** (jacobian (wan_rext k) (at y) ** w)) =
                                 lam * (v dot w)) /\
        (!x. x IN sphere(vec 0,&1) ==> transp(X x) = X x) /\
        (!x v. x IN sphere(vec 0,&1)
               ==> v dot ((transp(jacobian (wan_rext u) (at x)) ** G(u x) **
                           jacobian (wan_rext u) (at x)) ** v) <= v dot (X x ** v)) /\
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(X x$i$j)) continuous_on sphere(vec 0,&1)) /\
        (!x. x IN sphere(vec 0,&1)
             ==> sqrt(p4_e2((mat 1 - cmw_outer x x) ** X x ** (mat 1 - cmw_outer x x))) <=
                 sqrt(p4_e2(transp(jacobian (wan_rext u) (at x)) ** G(u x) **
                            jacobian (wan_rext u) (at x))) + c)
        ==> cm_sen G (\y. u(k y)) <=
            cm_sarea G u + &3 * measure(ball(vec 0:real^3,&1)) * c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["GS";"UC";"KC";"KS";"KB";"KCONF";"XS";"XM";"XC";"XA"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `k:real^3->real^3`] CMW_SLICE_REPARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "VC") (LABEL_TAC "VJ")) THEN
  MP_TAC(BETA_RULE(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`;
                           `\y:real^3. (u:real^3->real^K)((k:real^3->real^3) y)`] CM_CLASSICAL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`; `u:real^3->real^K`]
    CM_CLASSICAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC)) THEN
  MP_TAC(BETA_RULE(ISPECL [`G:real^K->real^K^K`; `\y:real^3. (u:real^3->real^K)((k:real^3->real^3) y)`]
    CMW_DENS_CONT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "E1C") (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`] CMW_DENS_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "AC"))) THEN
  ABBREV_TAC
   `FF = \x:real^3. sqrt(p4_e2((mat 1 - cmw_outer x x) ** (X:real^3->real^3^3) x **
                               (mat 1 - cmw_outer x x)))` THEN
  SUBGOAL_THEN `(\x. lift((FF:real^3->real) x)) continuous_on sphere(vec 0:real^3,&1)`
  (LABEL_TAC "FC") THENL
   [EXPAND_TAC "FF" THEN MATCH_MP_TAC CMW_PROJ_DENS_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the pointwise bound *)
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0:real^3,&1)
        ==> trace(transp(jacobian (wan_rext (\y. (u:real^3->real^K)(k y))) (at y)) **
                  (G:real^K->real^K^K)(u(k y)) **
                  jacobian (wan_rext (\y. u(k y))) (at y)) / &2 <=
            (FF:real^3->real)((k:real^3->real^3) y) *
            abs(det(jacobian (wan_rext k) (at y) + cmw_outer (k y) y))`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "VJ" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `y IN sphere(vec 0:real^3,&1)`)]) THEN
    EXPAND_TAC "FF" THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SUBGOAL_THEN `(k:real^3->real^3) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [USE_THEN "KS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ (y:real^3) dot y = &1 /\
                  (k:real^3->real^3) y dot k y = &1 /\
                  wan_rext k differentiable at y`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_1; GSYM IN_SPHERE_0] THEN
      ASM_SIMP_TAC[P4_SPHERE_NONZERO] THEN MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_SIMP_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM; P4_SPHERE_NONZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `jacobian (wan_rext (k:real^3->real^3)) (at y) ** y = vec 0`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:real^3->real^3`; `y:real^3`; `&1`] CM_REXT_JACOBIAN) THEN
      ASM_SIMP_TAC[REAL_LT_01];
      ALL_TAC] THEN
    SUBGOAL_THEN `transp(jacobian (wan_rext (k:real^3->real^3)) (at y)) ** k y = vec 0`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:real^3->real^3`; `y:real^3`] CMW_RANGE_TANGENT) THEN
      ASM_SIMP_TAC[CM_REXT_SPHERE] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[wan_rext; GSYM IN_SPHERE_0] THEN
      USE_THEN "KS" MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
      ALL_TAC] THEN
    USE_THEN "KCONF" (fun th -> MP_TAC(MATCH_MP th (ASSUME `y IN sphere(vec 0:real^3,&1)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CMW_DENSITY_REPARAM_LE THEN EXISTS_TAC `lam:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "XS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN USE_THEN "XM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_integral (\y. (FF:real^3->real)((k:real^3->real^3) y) *
                abs(det(jacobian (wan_rext k) (at y) + cmw_outer (k y) y)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMW_TRANSPORT_DENS_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p4_s2_integral (\y. (FF:real^3->real)((k:real^3->real^3) y) *
                abs(det(jacobian (wan_rext k) (at y) + cmw_outer (k y) y))) =
    p4_s2_integral FF`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMW_S2_CHANGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_integral (\y. sqrt(p4_e2(transp(jacobian (wan_rext (u:real^3->real^K))
                                                         (at y)) **
                                        (G:real^K->real^K^K)(u y) **
                                        jacobian (wan_rext u) (at y))) + c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[LIFT_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      EXPAND_TAC "FF" THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "XA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. sqrt(p4_e2(transp(jacobian (wan_rext (u:real^3->real^K)) (at y)) **
                                 (G:real^K->real^K^K)(u y) **
                                 jacobian (wan_rext u) (at y)))`;
                 `\y:real^3. (c:real)`] P4_S2_INTEGRAL_ADD) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[P4_S2_INTEGRAL_CONST] THEN REAL_ARITH_TAC);;

(* Algebra for the approximating metric Gd = P0 + 2 d I of the pullback M:  *)
(* Gd dominates M with margin d, and Pi Gd Pi is within 20 d of M.          *)

let CMW_QUAD_VEC_BOUND = prove
 (`!(A:real^N^N) v. abs(v dot (A ** v)) <= norm(vectorize A) * (v dot v)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm((A:real^N^N) ** v)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm(vectorize(A:real^N^N)) * norm v` THEN
  SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE] THEN
  REWRITE_TAC[GSYM NORM_POW_2; REAL_POW_2] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

let CMW_MAT1_NORM3 = prove
 (`norm(vectorize(mat 1:real^3^3)) <= &2`,
  SUBGOAL_THEN `norm(vectorize(mat 1:real^3^3)) pow 2 = &3` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_VECTORIZE; TRANSP_MAT; MATRIX_MUL_LID; TRACE_I;
                DIMINDEX_3];
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let CMW_GD_FORM = prove
 (`!(M:real^3^3) (P0:real^3^3) d v.
        norm(vectorize(P0 - M)) < d
        ==> v dot (M ** v) + d * (v dot v) <= v dot ((P0 + (&2 * d) %% mat 1) ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P0 - M:real^3^3`; `v:real^3`] CMW_QUAD_VEC_BOUND) THEN
  SUBGOAL_THEN `norm(vectorize(P0 - M:real^3^3)) * ((v:real^3) dot v) <= d * (v dot v)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RADD; DOT_RSUB; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

let CMW_GD_AREA_CLOSE = prove
 (`!(M:real^3^3) (P0:real^3^3) (x:real^3) d.
        x dot x = &1 /\ transp M = M /\ M ** x = vec 0 /\ norm(vectorize(P0 - M)) < d
        ==> norm(vectorize((mat 1 - cmw_outer x x) ** (P0 + (&2 * d) %% mat 1) **
                           (mat 1 - cmw_outer x x)) - vectorize M) <= &20 * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real^3` CMW_PROJ_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `M:real^3^3`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [MP_TAC(ISPEC `vectorize(P0 - M:real^3^3)` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vectorize((mat 1 - cmw_outer (x:real^3) x) ** (P0 + (&2 * d) %% mat 1) **
              (mat 1 - cmw_outer x x)) - vectorize(M:real^3^3) =
    vectorize((mat 1 - cmw_outer x x) ** ((P0 + (&2 * d) %% mat 1) - M) **
              (mat 1 - cmw_outer x x))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!A B C:real^3^3. A ** B ** A - A ** C ** A = A ** (B - C) ** A`
      (fun th -> REWRITE_TAC[GSYM th]) THENL
     [REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTORIZE_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(vectorize((P0 + (&2 * d) %% mat 1) - M:real^3^3)) <= &5 * d`
  ASSUME_TAC THENL
   [REWRITE_TAC[VECTORIZE_SUB; VECTORIZE_ADD; VECTORIZE_CMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(P0:real^3^3) - vectorize(M:real^3^3)) +
                norm((&2 * d) % vectorize(mat 1:real^3^3))` THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC(NORM_ARITH `!a b c:real^N. norm((a + b) - c) <= norm(a - c) + norm b`);
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(&2 * d) * norm(vectorize(mat 1:real^3^3)) <= (&2 * d) * &2`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> abs(&2 * d) = &2 * d`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[CMW_MAT1_NORM3] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `norm(vectorize(P0 - M:real^3^3)) < d` THEN
      REWRITE_TAC[VECTORIZE_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize(mat 1 - cmw_outer (x:real^3) x)) *
              norm(vectorize(((P0 + (&2 * d) %% mat 1) - M:real^3^3) **
                             (mat 1 - cmw_outer x x)))` THEN
  REWRITE_TAC[NORM_VECTORIZE_MUL_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (norm(vectorize((P0 + (&2 * d) %% mat 1) - M:real^3^3)) * &2)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize((P0 + (&2 * d) %% mat 1) - M:real^3^3)) *
              norm(vectorize(mat 1 - cmw_outer (x:real^3) x))` THEN
  REWRITE_TAC[NORM_VECTORIZE_MUL_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

(* The reparametrized sweepout W1 y t = W (h t y) t: C^1 slices with jointly *)
(* continuous Jacobians, and joint continuity on S^2 x [0,1].                *)

let CMW_SLAB_REPARAM_CONT = prove
 (`!(Q:real^(3,1)finite_sum->real^N) (h:real->real^3->real^3).
        Q continuous_on
          {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
        (\x. h (drop(sndcart x)) (fstcart x)) continuous_on
          {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
        (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
               ==> h t y IN sphere(vec 0,&1))
        ==> (\x. Q(pastecart (h (drop(sndcart x)) (fstcart x)) (sndcart x))) continuous_on
            {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (Q:real^(3,1)finite_sum->real^N)
           (pastecart ((h:real->real^3->real^3) (drop(sndcart x)) (fstcart x)) (sndcart x))) =
    Q o (\x. pastecart (h (drop(sndcart x)) (fstcart x)) (sndcart x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                          drop(sndcart x) IN real_interval[&0,&1]}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[]]);;

let CMW_REPARAM_C1SWEEP = prove
 (`!(W:real^3->real->real^K) (h:real->real^3->real^3).
        cmw_c1sweep W /\
        (!t. t IN real_interval[&0,&1]
             ==> (!y. y IN sphere(vec 0,&1) ==> h t y IN sphere(vec 0,&1)) /\
                 continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (h t))) /\
        (\x. h (drop(sndcart x)) (fstcart x)) continuous_on
          {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(jacobian (wan_rext (h (drop(sndcart x)))) (at (fstcart x))$i$j))
                   continuous_on
                   {x | fstcart x IN sphere(vec 0,&1) /\
                        drop(sndcart x) IN real_interval[&0,&1]})
        ==> cmw_c1sweep (\y t. W (h t y) t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[cmw_c1sweep])
    (CONJUNCTS_THEN2 (LABEL_TAC "H") (CONJUNCTS_THEN2 (LABEL_TAC "HC") (LABEL_TAC "HJ")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "WC") (LABEL_TAC "WJ")) THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (wan_rext (\y. (W:real^3->real->real^K) ((h:real->real^3->real^3) t y) t)) /\
            !y. y IN sphere(vec 0,&1)
                ==> jacobian (wan_rext (\y. W (h t y) t)) (at y) =
                    jacobian (wan_rext (\y. W y t)) (at (h t y)) **
                    jacobian (wan_rext (h t)) (at y)`
  (LABEL_TAC "SL") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\y. (W:real^3->real->real^K) y t`;
                             `(h:real->real^3->real^3) t`] CMW_SLICE_REPARAM)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "H" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    USE_THEN "WC" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cmw_c1sweep] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "SL" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\x. lift((jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                       (at ((h:real->real^3->real^3) (drop(sndcart x)) (fstcart x))) **
              jacobian (wan_rext (h (drop(sndcart x)))) (at (fstcart x)))$i$j)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "SL" (MP_TAC o C MATCH_MP
      (ASSUME `drop(sndcart(x:real^(3,1)finite_sum)) IN real_interval[&0,&1]`)) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP
      (ASSUME `fstcart(x:real^(3,1)finite_sum) IN sphere(vec 0,&1)`) o CONJUNCT2) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                               drop(sndcart x) IN real_interval[&0,&1]}`;
    `\x. jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                  (at ((h:real->real^3->real^3) (drop(sndcart x)) (fstcart x)))`;
    `\x. jacobian (wan_rext ((h:real->real^3->real^3) (drop(sndcart x)))) (at (fstcart x))`]
   CMT_CONT_MATMUL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL [ALL_TAC; USE_THEN "HJ" ACCEPT_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. lift(jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                       (at (fstcart x))$p$q)`;
    `h:real->real^3->real^3`] CMW_SLAB_REPARAM_CONT) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN USE_THEN "H" (fun th -> MESON_TAC[th]));;

(* Essentiality is preserved by the reparametrization (y,t) -> (h t y, t).  *)

let CMW_REPARAM_ESSENTIAL = prove
 (`!top atlas (f:A->real^K) (sigma:real^3->real->A) U (h:real->real^3->real^3).
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f /\
        U SUBSET topspace top /\
        p4_sweepout (top,atlas) sigma /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> sigma y t IN U) /\
        p4_essential (subtopology top U) (p4_susp sigma) /\
        (\x. h (drop(sndcart x)) (fstcart x)) continuous_on
          {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
        (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
               ==> h t y IN sphere(vec 0,&1)) /\
        (!t x. t IN real_interval[&0,&1] /\ x IN sphere(vec 0,&1)
               ==> ?!y. y IN sphere(vec 0,&1) /\ h t y = x)
        ==> p4_essential (subtopology top U)
              (p4_susp (\y t. mfd_emb_inv top f (f(sigma (h t y) t))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `sigma:real^3->real->A`; `U:A->bool`] CMW_EMB_SELF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                 `\y t. mfd_emb_inv top (f:A->real^K)
                          (f((sigma:real^3->real->A) ((h:real->real^3->real^3) t y) t))`;
                 `\y t. (sigma:real^3->real->A) ((h:real->real^3->real^3) t y) t`]
                CMW_ESSENTIAL_SLICES_EQ) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(h:real->real^3->real^3) t y`; `t:real`] o
      check (fun th -> can (find_term (fun u -> is_const u &&
        fst(dest_const u) = "mfd_emb_inv")) (concl th))) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`; `sigma:real^3->real->A`;
                 `h:real->real^3->real^3`] CMW_ESSENTIAL_REPARAM) THEN
  ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `p4_sweepout (top,atlas:((A->bool)#(A->real^N))->bool) sigma` THEN
  REWRITE_TAC[p4_sweepout] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `\y t. (h:real->real^3->real^3) t y` CMW_SLAB_CONTINUOUS_MAP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[]]);;

(* D.7 applied to Gd t y = P0(y,t) + 2 dl I, P0 polynomial and symmetric:   *)
(* a family h of conformal C^1 bijections of S^2, continuous in (y,t) with   *)
(* jointly continuous Jacobians.                                            *)

let CMW_GD_D7 = prove
 (`!(P0:real^(3,1)finite_sum->real^3^3) dl.
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> real_polynomial_function (\x. P0 x$i$j)) /\
        (!x. transp(P0 x) = P0 x) /\ &0 < dl /\
        (!t y v. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ v dot y = &0
                 ==> dl * (v dot v) <=
                     v dot ((P0(pastecart y (lift t)) + (&2 * dl) %% mat 1) ** v))
        ==> ?h:real->real^3->real^3.
              (!t. t IN real_interval[&0,&1]
                   ==> (!y. y IN sphere(vec 0,&1) ==> h t y IN sphere(vec 0,&1)) /\
                       (!x. x IN sphere(vec 0,&1)
                            ==> ?!y. y IN sphere(vec 0,&1) /\ h t y = x) /\
                       continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                         (wan_rext (h t)) /\
                       (!y. y IN sphere(vec 0,&1)
                            ==> ?lam. &0 < lam /\
                                  !v w. v dot y = &0 /\ w dot y = &0
                                        ==> (jacobian (wan_rext (h t)) (at y) ** v) dot
                                            ((P0(pastecart (h t y) (lift t)) +
                                              (&2 * dl) %% mat 1) **
                                             (jacobian (wan_rext (h t)) (at y) ** w)) =
                                            lam * (v dot w))) /\
              (\x. h (drop(sndcart x)) (fstcart x)) continuous_on
                {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
              (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                     ==> (\x. lift(jacobian (wan_rext (h (drop(sndcart x))))
                                            (at (fstcart x))$i$j))
                         continuous_on
                         {x | fstcart x IN sphere(vec 0,&1) /\
                              drop(sndcart x) IN real_interval[&0,&1]})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^(3,1)finite_sum.
                  (P0:real^(3,1)finite_sum->real^3^3) x + (&2 * dl) %% mat 1`
               CMW_D7_REG_HYPS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT; DIMINDEX_3] THEN
    MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_ADD THEN
    ASM_SIMP_TAC[real_polynomial_function_RULES];
    STRIP_TAC] THEN
  MP_TAC CM_D7_UNIFORMIZATION THEN REWRITE_TAC[CM_D7_UNIFORMIZATION_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\t y. (P0:real^(3,1)finite_sum->real^3^3) (pastecart y (lift t)) +
           (&2 * dl) %% mat 1`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MAT] THEN
    EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2")
      (CONJUNCTS_THEN2 (LABEL_TAC "H3") (K ALL_TAC))))) THEN
  SUBGOAL_THEN `!t. (\z. (h:real->real^3->real^3) t (inv(norm z) % z)) = wan_rext (h t)`
  (LABEL_TAC "FOLD") THENL [REWRITE_TAC[wan_rext]; ALL_TAC] THEN
  EXISTS_TAC `h:real->real^3->real^3` THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    USE_THEN "FOLD" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[smooth_map_on];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x:real^(3,1)finite_sum.
                  (h:real->real^3->real^3) (drop(sndcart x)) (inv(norm(fstcart x)) % fstcart x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                            drop(sndcart x) IN real_interval[&0,&1]}` THEN
      USE_THEN "H2" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[P4_SPHERE_NONZERO]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                          drop(sndcart x) IN real_interval[&0,&1]}` THEN
    CONJ_TAC THENL
     [USE_THEN "H3" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      USE_THEN "FOLD" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[P4_SPHERE_NONZERO]]]);;

(* CM Prop 1.5 for one sweepout, before footnote 8: for a jointly C^1      *)
(* sweepout W there is a family h of conformal reparametrizations with      *)
(* E(W(h_t ., t)) <= Area(W(., t)) + c for every t.                         *)

let CMW_POLY_GD_CONT = prove
 (`!(P0:real^(3,1)finite_sum->real^3^3) dl t i j.
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> real_polynomial_function (\x. P0 x$i$j)) /\
        1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
        ==> (\y:real^3. lift((P0(pastecart y (lift t)) + (&2 * dl) %% mat 1)$i$j))
            continuous_on sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y:real^3. lift(((P0:real^(3,1)finite_sum->real^3^3) (pastecart y (lift t)) +
                      (&2 * dl) %% mat 1)$i$j)) =
    (lift o (\x. (P0 x + (&2 * dl) %% mat 1)$i$j)) o (\y. pastecart y (lift t))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION THEN
    REWRITE_TAC[VECTOR_POLYNOMIAL_FUNCTION_LIFT] THEN
    ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT; DIMINDEX_3] THEN
    MATCH_MP_TAC REAL_POLYNOMIAL_FUNCTION_ADD THEN
    ASM_SIMP_TAC[real_polynomial_function_RULES]]);;

let CMW_P15_REPARAM = prove
 (`!S (G:real^K->real^K^K) d (W:real^3->real->real^K) c.
        cm_target S G d /\
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
        &0 < c
        ==> ?h:real->real^3->real^3.
              (!t. t IN real_interval[&0,&1]
                   ==> (!y. y IN sphere(vec 0,&1) ==> h t y IN sphere(vec 0,&1)) /\
                       (!x. x IN sphere(vec 0,&1)
                            ==> ?!y. y IN sphere(vec 0,&1) /\ h t y = x) /\
                       continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                         (wan_rext (h t)) /\
                       cm_sen G (\y. W (h t y) t) <= cm_sarea G (\y. W y t) + c) /\
              (\x. h (drop(sndcart x)) (fstcart x)) continuous_on
                {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
              (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                     ==> (\x. lift(jacobian (wan_rext (h (drop(sndcart x))))
                                            (at (fstcart x))$i$j))
                         continuous_on
                         {x | fstcart x IN sphere(vec 0,&1) /\
                              drop(sndcart x) IN real_interval[&0,&1]})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "GS") (K ALL_TAC))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `W:real^3->real->real^K`] CMW_PMET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MC") (CONJUNCTS_THEN2 (LABEL_TAC "MS")
    (CONJUNCTS_THEN2 (LABEL_TAC "MP") (LABEL_TAC "MY")))) THEN
  SUBGOAL_THEN `cmw_c1sweep (W:real^3->real->real^K)` MP_TAC THENL
   [MATCH_MP_TAC CMW_C1_IMP_C1SWEEP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cmw_c1sweep] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "WC") (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `?R0. &0 <= R0 /\
         !x. x IN {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                            drop(sndcart x) IN real_interval[&0,&1]}
             ==> norm(vectorize(cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K)
                                         (drop(sndcart x)) (fstcart x))) <= R0`
  (X_CHOOSE_THEN `R0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RB"))) THENL
   [MP_TAC(ISPECL
     [`\x:real^(3,1)finite_sum. vectorize(cmw_pmet (G:real^K->real^K^K)
                                  (W:real^3->real->real^K) (drop(sndcart x)) (fstcart x))`;
      `{x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                 drop(sndcart x) IN real_interval[&0,&1]}`]
     COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[CMW_SLAB_COMPACT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < c / (&3 * measure(ball(vec 0:real^3,&1)) + &1) /\
    &3 * measure(ball(vec 0:real^3,&1)) * c / (&3 * measure(ball(vec 0:real^3,&1)) + &1)
    <= c`
  MP_TAC THENL
   [MP_TAC(ISPEC `ball(vec 0:real^3,&1)` MEASURE_POS_LE) THEN
    REWRITE_TAC[MEASURABLE_BALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &3 * measure(ball(vec 0:real^3,&1)) + &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ABBREV_TAC `ep = c / (&3 * measure(ball(vec 0:real^3,&1)) + &1)` THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`R0 + &1`; `ep:real`] CMW_SQRT_E2_UNIF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UNIF"))) THEN
  ABBREV_TAC `dl = min (r / &40) (&1 / &40)` THEN
  SUBGOAL_THEN `&0 < dl /\ &20 * dl < r /\ &20 * dl <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^(3,1)finite_sum. cmw_pmet (G:real^K->real^K^K)
                     (W:real^3->real->real^K) (drop(sndcart x)) (fstcart x)`;
                 `{x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                            drop(sndcart x) IN real_interval[&0,&1]}`;
                 `dl:real`] CMW_SYM_POLY_APPROX) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMW_SLAB_COMPACT];
    DISCH_THEN(X_CHOOSE_THEN `P0:real^(3,1)finite_sum->real^3^3`
      (CONJUNCTS_THEN2 (LABEL_TAC "PP") (CONJUNCTS_THEN2 (LABEL_TAC "PS")
        (LABEL_TAC "PA"))))] THEN
  SUBGOAL_THEN
   `!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
          ==> norm(vectorize((P0:real^(3,1)finite_sum->real^3^3) (pastecart y (lift t)) -
                             cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t y)) < dl /\
              norm(vectorize(cmw_pmet G W t y)) <= R0`
  (LABEL_TAC "PT") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `pastecart (y:real^3) (lift t) IN
                  {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                            drop(sndcart x) IN real_interval[&0,&1]}`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    USE_THEN "PA" (fun pa -> USE_THEN "RB" (fun rb -> FIRST_ASSUM(fun m ->
      MP_TAC(CONJ (MATCH_MP pa m) (MATCH_MP rb m))))) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P0:real^(3,1)finite_sum->real^3^3`; `dl:real`] CMW_GD_D7) THEN
  ANTS_TAC THENL
   [USE_THEN "PP" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "PS" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t y`;
                   `(P0:real^(3,1)finite_sum->real^3^3) (pastecart y (lift t))`;
                   `dl:real`; `v:real^3`] CMW_GD_FORM) THEN
    USE_THEN "PT" (MP_TAC o REWRITE_RULE[ASSUME `t IN real_interval[&0,&1]`;
                                         ASSUME `y IN sphere(vec 0:real^3,&1)`] o
                   SPECL [`t:real`; `y:real^3`]) THEN
    USE_THEN "MP" (MP_TAC o SPECL [`t:real`; `y:real^3`; `v:real^3`]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3")))) THEN
  EXISTS_TAC `h:real->real^3->real^3` THEN
  USE_THEN "H2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "H3" (fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "HS") (CONJUNCTS_THEN2 (LABEL_TAC "HB")
    (CONJUNCTS_THEN2 (LABEL_TAC "HC") (LABEL_TAC "HK")))) THEN
  USE_THEN "HS" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "HB" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cm_sarea (G:real^K->real^K^K) (\y. (W:real^3->real->real^K) y t) +
              &3 * measure(ball(vec 0:real^3,&1)) * ep` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`G:real^K->real^K^K`; `\y. (W:real^3->real->real^K) y t`;
     `(h:real->real^3->real^3) t`;
     `\y. (P0:real^(3,1)finite_sum->real^3^3) (pastecart y (lift t)) + (&2 * dl) %% mat 1`;
     `ep:real`] CMW_SLICE_ENERGY_REPARAM)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  USE_THEN "GS" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "WC" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`)]) THEN
  USE_THEN "HS" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "HB" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "HK" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MAT] THEN
  USE_THEN "PS" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM cmw_pmet] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t x`;
                   `(P0:real^(3,1)finite_sum->real^3^3) (pastecart x (lift t))`;
                   `dl:real`; `v:real^3`] CMW_GD_FORM) THEN
    USE_THEN "PT" (MP_TAC o REWRITE_RULE[ASSUME `t IN real_interval[&0,&1]`;
                                         ASSUME `x IN sphere(vec 0:real^3,&1)`] o
                   SPECL [`t:real`; `x:real^3`]) THEN
    MP_TAC(ISPEC `v:real^3` DOT_POS_LE) THEN
    SUBGOAL_THEN `&0 <= dl * ((v:real^3) dot v)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; DOT_POS_LE]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_POLY_GD_CONT THEN
    USE_THEN "PP" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "PT" (MP_TAC o REWRITE_RULE[ASSUME `t IN real_interval[&0,&1]`;
                                         ASSUME `x IN sphere(vec 0:real^3,&1)`] o
                   SPECL [`t:real`; `x:real^3`]) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t x`;
                   `(P0:real^(3,1)finite_sum->real^3^3) (pastecart x (lift t))`;
                   `x:real^3`; `dl:real`] CMW_GD_AREA_CLOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `x IN sphere(vec 0:real^3,&1)` THEN
        REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1];
        USE_THEN "MS" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "MY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(a - b) < e ==> a <= b + e`) THEN
    USE_THEN "UNIF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b:real^N e R. norm(a - b) <= e /\ norm b <= R /\ e <= &1 ==> norm a <= R + &1`) THEN
    MAP_EVERY EXISTS_TAC
     [`vectorize(cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t x)`;
      `&20 * dl`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* CM footnote 8.  Collapse a small cap around the north pole N              *)
(* to N: Phi(y) = normalize(N + rho m((y - N)/rho)) with m(w) = (1 - bump) w *)
(* (m = 0 for |w| <= 1, m = id for |w| >= 2), so D Phi is bounded            *)
(* independently of rho.  Slices of W o Phi have zero Jacobian on the cap    *)
(* (hence are not harmonic by CM_CRITICAL_ISOLATED), are uniformly close to  *)
(* those of W, and have at most O(int of the cap) more energy.               *)
(* ========================================================================= *)

let cmw_capm = new_definition
 `cmw_capm (w:real^3) = (&1 - smooth_bump (&1) (&2) w) % w`;;

let cmw_capq = new_definition
 `cmw_capq rho (z:real^3) = basis 3 + rho % cmw_capm(inv rho % (z - basis 3))`;;

let cmw_cap = new_definition
 `cmw_cap rho (y:real^3) = inv(norm(cmw_capq rho y)) % cmw_capq rho y`;;

let CMW_CAPM_FACTS = prove
 (`(!w. norm w <= &1 ==> cmw_capm w = vec 0) /\
   (!w. &2 <= norm w ==> cmw_capm w = w) /\
   (!w. norm(cmw_capm w) <= norm w) /\
   smooth_map_on (:real^3) cmw_capm`,
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_capm] THEN
    MP_TAC(ISPECL [`&1`; `&2`; `w:real^3`] SMOOTH_BUMP_1) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO];
    REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_capm] THEN
    MP_TAC(ISPECL [`&1`; `&2`; `w:real^3`] SMOOTH_BUMP_0) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID];
    GEN_TAC THEN REWRITE_TAC[cmw_capm; NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MP_TAC(ISPECL [`&1`; `&2`; `w:real^3`] SMOOTH_BUMP_BOUNDS) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `cmw_capm = \w:real^3. drop(lift(&1 - smooth_bump (&1) (&2) w)) % w`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cmw_capm; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC]);;

let CMW_JACOBIAN_ID = prove
 (`!x:real^N. jacobian (\z. z) (at x) = mat 1`,
  GEN_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `frechet_derivative (\z:real^N. z) (at x) = (\h. h)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    REWRITE_TAC[MATRIX_ID]]);;

let CMW_CAPM_JAC_BOUND = prove
 (`?C. &2 <= C /\ !w. norm(vectorize(jacobian cmw_capm (at w))) <= C`,
  SUBGOAL_THEN `(\w. vectorize(jacobian cmw_capm (at w))) continuous_on (:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
    MATCH_MP_TAC CMW_C1_JAC_ENTRY_CONT THEN REWRITE_TAC[OPEN_UNIV] THEN
    MP_TAC CMW_CAPM_FACTS THEN SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. vectorize(jacobian cmw_capm (at w))`; `cball(vec 0:real^3,&3)`]
    COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max (&2) B` THEN REWRITE_TAC[REAL_MAX_MAX] THEN
  X_GEN_TAC `w:real^3` THEN ASM_CASES_TAC `norm(w:real^3) <= &3` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max (&2) B`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> x <= max (&2) B`) THEN
  SUBGOAL_THEN `jacobian cmw_capm (at (w:real^3)) = mat 1` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\w:real^3. w`; `cmw_capm`; `{w:real^3 | &2 < norm w}`; `w:real^3`]
      CMW_JACOBIAN_LOCAL_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; DIFFERENTIABLE_ID] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE; GSYM IN_CBALL_0;
                    SET_RULE `{x | ~(x IN s)} = (:real^3) DIFF s`] THEN
        SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL];
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
        MP_TAC CMW_CAPM_FACTS THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[CMW_JACOBIAN_ID]];
    REWRITE_TAC[CMW_MAT1_NORM3]]);;

(* The rescaled collapse q(z) = N + rho m((z - N)/rho): its derivative is   *)
(* Dm at the rescaled point (bounded independently of rho), it is the       *)
(* identity outside the cap of radius 2 rho and N on the cap of radius rho. *)

let CMW_CAPQ_DERIV = prove
 (`!rho z:real^3.
        &0 < rho
        ==> (cmw_capq rho has_derivative
             (\h. jacobian cmw_capm (at (inv rho % (z - basis 3))) ** h)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cmw_capq rho =
                (\v. basis 3 + rho % v) o cmw_capm o (\z:real^3. inv rho % (z - basis 3))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; cmw_capq]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^3. jacobian cmw_capm (at (inv rho % (z - basis 3))) ** h) =
    (\v. rho % v) o (\h. jacobian cmw_capm (at (inv rho % (z - basis 3))) ** h) o
    (\h. inv rho % h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `((\z:real^3. z - basis 3) has_derivative (\h. h - vec 0)) (at z)`
      MP_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
        REWRITE_TAC[VECTOR_SUB_RZERO] THEN
        DISCH_THEN(ACCEPT_TAC o BETA_RULE o SPEC `inv rho` o MATCH_MP HAS_DERIVATIVE_CMUL)];
      REWRITE_TAC[GSYM JACOBIAN_WORKS] THEN
      MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      MP_TAC CMW_CAPM_FACTS THEN SIMP_TAC[smooth_map_on]];
    MP_TAC(ISPECL [`\v:real^3. basis 3:real^3`; `\v:real^3. vec 0:real^3`;
                   `\v:real^3. rho % v`; `\v:real^3. rho % v`;
                   `at ((cmw_capm o (\z:real^3. inv rho % (z - basis 3))) z)`]
                  HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC]);;

let CMW_CAPQ_FACTS = prove
 (`!rho z:real^3.
        &0 < rho
        ==> (&2 * rho <= norm(z - basis 3) ==> cmw_capq rho z = z) /\
            (norm(z - basis 3) <= rho ==> cmw_capq rho z = basis 3) /\
            norm(cmw_capq rho z - basis 3) <= norm(z - basis 3) /\
            jacobian (cmw_capq rho) (at z) =
            jacobian cmw_capm (at (inv rho % (z - basis 3)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(inv rho % (z - basis 3):real^3) = norm(z - basis 3) / rho`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[cmw_capq] THEN
    SUBGOAL_THEN `cmw_capm(inv rho % (z - basis 3)) = inv rho % (z - basis 3)`
    SUBST1_TAC THENL
     [MP_TAC CMW_CAPM_FACTS THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC];
    DISCH_TAC THEN REWRITE_TAC[cmw_capq] THEN
    SUBGOAL_THEN `cmw_capm(inv rho % (z - basis 3)) = vec 0` SUBST1_TAC THENL
     [MP_TAC CMW_CAPM_FACTS THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    REWRITE_TAC[cmw_capq; VECTOR_ARITH `(a + b) - a:real^N = b`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `rho * norm(inv rho % (z - basis 3):real^3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MP_TAC(SPEC `inv rho % (z - basis 3):real^3`
          (CONJUNCT1(CONJUNCT2(CONJUNCT2 CMW_CAPM_FACTS)))) THEN REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    MP_TAC(ISPECL [`rho:real`; `z:real^3`] CMW_CAPQ_DERIV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[jacobian] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]]);;

(* The collapse Phi = cmw_cap rho on S^2 (0 < rho <= 1/4): a map of S^2 into *)
(* S^2, the identity outside the cap of radius 2 rho, N on the cap of radius *)
(* rho, within 6 rho of the identity; its radial extension is smooth with   *)
(* Jacobian at most 8 C on S^2.                                             *)

let CMW_NORMALIZE_UNIT = prove
 (`!v:real^N. ~(v = vec 0) ==> norm(inv(norm v) % v) = &1`,
  SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0]);;

let CMW_NORMALIZE_DIST = prove
 (`!q:real^N. ~(q = vec 0) ==> norm(inv(norm q) % q - q) = abs(&1 - norm q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(q:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `inv(n) % q - q:real^N = (inv n - &1) % q`; NORM_MUL] THEN
  SUBGOAL_THEN `abs(inv(norm(q:real^N)) - &1) * norm q =
                abs((inv(norm q) - &1) * norm q)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM]; ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC);;

let CMW_CAP_FACTS = prove
 (`!rho y:real^3.
        &0 < rho /\ rho <= &1 / &4 /\ y IN sphere(vec 0,&1)
        ==> &1 / &2 <= norm(cmw_capq rho y) /\
            cmw_cap rho y IN sphere(vec 0,&1) /\
            (&2 * rho <= norm(y - basis 3) ==> cmw_cap rho y = y) /\
            (norm(y - basis 3) <= rho ==> cmw_cap rho y = basis 3) /\
            norm(cmw_cap rho y - y) <= &6 * rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `y:real^3`] CMW_CAPQ_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Q1") (CONJUNCTS_THEN2 (LABEL_TAC "Q2")
    (CONJUNCTS_THEN2 (LABEL_TAC "Q3") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `norm(y:real^3) = &1 /\ norm(basis 3:real^3) = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= norm(cmw_capq rho (y:real^3))` ASSUME_TAC THENL
   [ASM_CASES_TAC `&2 * rho <= norm(y - basis 3:real^3)` THENL
     [USE_THEN "Q1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `&2 * rho <= norm(y - basis 3:real^3)`)]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `norm(cmw_capq rho y - basis 3:real^3) <= norm(y - basis 3)` THEN
      UNDISCH_TAC `~(&2 * rho <= norm(y - basis 3:real^3))` THEN
      UNDISCH_TAC `rho <= &1 / &4` THEN UNDISCH_TAC `norm(basis 3:real^3) = &1` THEN
      CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cmw_capq rho (y:real^3) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 / &2 <= norm(cmw_capq rho (y:real^3))` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cmw_cap; IN_SPHERE_0] THEN ASM_SIMP_TAC[CMW_NORMALIZE_UNIT];
    DISCH_TAC THEN REWRITE_TAC[cmw_cap] THEN
    USE_THEN "Q1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `&2 * rho <= norm(y - basis 3:real^3)`)]) THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID];
    DISCH_TAC THEN REWRITE_TAC[cmw_cap] THEN
    USE_THEN "Q2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `norm(y - basis 3:real^3) <= rho`)]) THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 * rho <= norm(y - basis 3:real^3)` THENL
   [REWRITE_TAC[cmw_cap] THEN
    USE_THEN "Q1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `&2 * rho <= norm(y - basis 3:real^3)`)]) THEN
    ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; VECTOR_SUB_REFL; NORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[cmw_cap] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(inv(norm(cmw_capq rho y)) % cmw_capq rho y - cmw_capq rho (y:real^3)) +
              norm(cmw_capq rho y - basis 3:real^3) + norm(y - basis 3:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC(NORM_ARITH
     `!c q n y:real^3. norm(c - y) <= norm(c - q) + norm(q - n) + norm(y - n)`);
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMW_NORMALIZE_DIST] THEN
  UNDISCH_TAC `norm(cmw_capq rho y - basis 3:real^3) <= norm(y - basis 3)` THEN
  UNDISCH_TAC `~(&2 * rho <= norm(y - basis 3:real^3))` THEN
  UNDISCH_TAC `norm(basis 3:real^3) = &1` THEN
  CONV_TAC NORM_ARITH);;

let CMW_NORMALIZE_JAC = prove
 (`!v:real^3. ~(v = vec 0)
        ==> jacobian (\z. inv(norm z) % z) (at v) =
            inv(norm v) %% (mat 1 - cmw_outer (inv(norm v) % v) (inv(norm v) % v))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP BEL_NORMALIZE_HAS_DERIVATIVE) THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN
   `(\h:real^3. inv(norm v) % h - ((v dot h) / norm v pow 3) % v) =
    (\h. (inv(norm v) %% (mat 1 - cmw_outer (inv(norm v) % v) (inv(norm v) % v))) ** h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                MATRIX_VECTOR_MUL_LID; CMW_OUTER_MV; DOT_LMUL] THEN
    X_GEN_TAC `h:real^3` THEN
    SUBGOAL_THEN `(v dot h) / norm(v:real^3) pow 3 =
                  inv(norm v) * (inv(norm v) * (v dot h)) * inv(norm v)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD
       `!x n. ~(n = &0) ==> x / n pow 3 = inv(n) * (inv(n) * x) * inv(n)`) THEN
      ASM_REWRITE_TAC[NORM_EQ_0];
      SPEC_TAC(`(v:real^3) dot h`,`c:real`) THEN SPEC_TAC(`inv(norm(v:real^3))`,`a:real`) THEN
      REPEAT GEN_TAC THEN VECTOR_ARITH_TAC];
    REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]]);;

let CMW_NORMALIZE_JAC_BOUND = prove
 (`!v:real^3. ~(v = vec 0)
        ==> norm(vectorize(jacobian (\z. inv(norm z) % z) (at v))) <= &2 * inv(norm v)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMW_NORMALIZE_JAC; VECTORIZE_CMUL; NORM_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; NORM_POS_LE] THEN
  MP_TAC(SPEC `inv(norm v) % v:real^3` CMW_PROJ_FACTS) THEN
  ASM_SIMP_TAC[GSYM NORM_EQ_1; CMW_NORMALIZE_UNIT]);;

let CMW_CAPQ_SMOOTH = prove
 (`!rho. smooth_map_on (:real^3) (cmw_capq rho)`,
  GEN_TAC THEN
  SUBGOAL_THEN `cmw_capq rho =
                \z:real^3. basis 3 + rho % (cmw_capm o (\z. inv rho % (z - basis 3))) z`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cmw_capq; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; CMW_CAPM_FACTS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let CMW_CAP_REXT = prove
 (`!rho C. &0 < rho /\ rho <= &1 / &4 /\
           (!w. norm(vectorize(jacobian cmw_capm (at w))) <= C)
           ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (cmw_cap rho)) /\
               (!y. y IN sphere(vec 0,&1)
                    ==> norm(vectorize(jacobian (wan_rext (cmw_cap rho)) (at y))) <= &8 * C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_rext (cmw_cap rho) =
                (\v:real^3. inv(norm v) % v) o cmw_capq rho o (\z:real^3. inv(norm z) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_rext; cmw_cap; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0)
                           ==> &1 / &2 <= norm(cmw_capq rho (inv(norm z) % z))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`rho:real`; `inv(norm z) % z:real^3`]
      CMW_CAP_FACTS) THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{v:real^3 | ~(v = vec 0)}` THEN
    REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[NORM_0] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[CMT_OPEN_NONZERO; OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_NORMALIZE;
                  CMW_CAPQ_SMOOTH]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ norm(y:real^3) = &1 /\ inv(norm y) % y = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= norm(cmw_capq rho (y:real^3))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(cmw_capq rho (y:real^3) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 / &2 <= norm(cmw_capq rho (y:real^3))` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^3. inv(norm z) % z) differentiable at y /\
                (\z:real^3. inv(norm z) % z) differentiable at (cmw_capq rho y) /\
                cmw_capq rho differentiable at y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[BEL_NORMALIZE_HAS_DERIVATIVE];
      ASM_MESON_TAC[BEL_NORMALIZE_HAS_DERIVATIVE];
      ASM_MESON_TAC[CMW_CAPQ_DERIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `jacobian ((\v:real^3. inv(norm v) % v) o cmw_capq rho o (\z:real^3. inv(norm z) % z))
             (at y) =
    jacobian (\v:real^3. inv(norm v) % v) (at (cmw_capq rho y)) **
    jacobian (cmw_capq rho) (at y) **
    jacobian (\z:real^3. inv(norm z) % z) (at y)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`cmw_capq rho o (\z:real^3. inv(norm z) % z)`;
                   `\v:real^3. inv(norm v) % v`; `y:real^3`] CMW_JACOBIAN_CHAIN) THEN
    MP_TAC(ISPECL [`\z:real^3. inv(norm z) % z`; `cmw_capq rho`; `y:real^3`]
      CMW_JACOBIAN_CHAIN) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * &2) * C * (&2 * inv(norm(y:real^3)))` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_INV_1] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize(jacobian (\v:real^3. inv(norm v) % v) (at (cmw_capq rho y)))) *
              norm(vectorize(jacobian (cmw_capq rho) (at y) **
                             jacobian (\z:real^3. inv(norm z) % z) (at y)))` THEN
  REWRITE_TAC[NORM_VECTORIZE_MUL_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * inv(norm(cmw_capq rho (y:real^3)))` THEN
    ASM_SIMP_TAC[CMW_NORMALIZE_JAC_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> &2 * x <= &2 * &2`) THEN
    SUBGOAL_THEN `inv(norm(cmw_capq rho (y:real^3))) <= inv(&1 / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize(jacobian (cmw_capq rho) (at (y:real^3)))) *
              norm(vectorize(jacobian (\z:real^3. inv(norm z) % z) (at y)))` THEN
  REWRITE_TAC[NORM_VECTORIZE_MUL_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[CMW_NORMALIZE_JAC_BOUND] THEN
  MP_TAC(ISPECL [`rho:real`; `y:real^3`] CMW_CAPQ_FACTS) THEN ASM_SIMP_TAC[]);;

(* Slices u o Phi: zero Jacobian on the cap of radius rho, the same energy  *)
(* density as u outside the cap of radius 2 rho, and a density bounded by    *)
(* 32 C^2 B (B bounding the pullback metric of u) everywhere.               *)

let cmw_capcut = new_definition
 `cmw_capcut s = min (&1) (max (&0) (&3 - s))`;;

let CMW_CAPCUT_FACTS = prove
 (`(!s. &0 <= cmw_capcut s /\ cmw_capcut s <= &1) /\
   (!s. s <= &2 ==> cmw_capcut s = &1) /\
   (!s. &3 <= s ==> cmw_capcut s = &0) /\
   (!f:real^3->real s. (\x. lift(f x)) continuous_on s
                       ==> (\x. lift(cmw_capcut(f x))) continuous_on s)`,
  REWRITE_TAC[cmw_capcut] THEN REPEAT CONJ_TAC THEN
  TRY(GEN_TAC THEN REAL_ARITH_TAC) THEN
  TRY(GEN_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(min (&1) (max (&0) (&3 - (f:real^3->real) x)))) =
    (\x. &1 / &2 % (lift(&1) + lift(max (&0) (&3 - f x))) -
         &1 / &2 % lift(abs(&1 - max (&0) (&3 - f x))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD; GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(max (&0) (&3 - (f:real^3->real) x))) continuous_on s`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(max (&0) (&3 - (f:real^3->real) x))) =
      (\x. &1 / &2 % lift(&3 - f x) + &1 / &2 % lift(abs(&3 - f x)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS) THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]]);;

let CMW_TRACE_GRAM_VEC_BOUND = prove
 (`!(A:real^3^3) (M:real^3^3).
        trace(transp A ** M ** A) <= norm(vectorize A) pow 2 * norm(vectorize M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DOT_VECTORIZE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize(A:real^3^3)) * norm(vectorize((M:real^3^3) ** A))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize(A:real^3^3)) *
              (norm(vectorize(M:real^3^3)) * norm(vectorize(A:real^3^3)))` THEN
  SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE; NORM_VECTORIZE_MUL_LE] THEN
  REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

let CMW_TRACE_GRAM_NONNEG = prove
 (`!(J:real^3^K) (G:real^K^K).
        (!v. &0 <= v dot (G ** v)) ==> &0 <= trace(transp J ** G ** J)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CMT_TRACE_GRAM] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]);;

let CMW_CAP_ZERO_JAC = prove
 (`!rho (u:real^3->real^K) y.
        &0 < rho /\ rho <= &1 / &4 /\ y IN sphere(vec 0,&1) /\ norm(y - basis 3) < rho
        ==> jacobian (wan_rext (\y. u(cmw_cap rho y))) (at y) = mat 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. (u:real^3->real^K)(basis 3)`;
                 `wan_rext (\y. (u:real^3->real^K)(cmw_cap rho y))`;
                 `{z:real^3 | z IN {z | ~(z = vec 0)} /\
                              inv(norm z) % z IN ball(basis 3,rho)}`;
                 `y:real^3`] CMW_JACOBIAN_LOCAL_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIFFERENTIABLE_CONST] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      REWRITE_TAC[CMT_NORMALIZE_CONTINUOUS; CMT_OPEN_NONZERO; OPEN_BALL];
      REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN
      UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; GSYM NORM_EQ_0] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL; wan_rext] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`rho:real`; `inv(norm z) % z:real^3`] CMW_CAP_FACTS) THEN
      ASM_SIMP_TAC[P4_RADIAL_SPHERE] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `dist(basis 3:real^3,inv(norm z) % z) < rho` THEN
      REWRITE_TAC[dist] THEN SPEC_TAC(`inv(norm z) % z:real^3`,`w:real^3`) THEN
      GEN_TAC THEN CONV_TAC NORM_ARITH];
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[jacobian; FRECHET_DERIVATIVE_CONST_AT; MATRIX_0]]);;

let CMW_CAP_SAME_JAC = prove
 (`!rho (u:real^3->real^K) y.
        &0 < rho /\ rho <= &1 / &4 /\ y IN sphere(vec 0,&1) /\
        &2 * rho < norm(y - basis 3) /\
        wan_rext u differentiable at y
        ==> jacobian (wan_rext (\y. u(cmw_cap rho y))) (at y) =
            jacobian (wan_rext u) (at y) /\
            u(cmw_cap rho y) = u y`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`wan_rext (u:real^3->real^K)`;
                   `wan_rext (\y. (u:real^3->real^K)(cmw_cap rho y))`;
                   `{z:real^3 | z IN {z | ~(z = vec 0)} /\
                                inv(norm z) % z IN
                                ((:real^3) DIFF cball(basis 3,&2 * rho))}`;
                   `y:real^3`] CMW_JACOBIAN_LOCAL_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
        SIMP_TAC[CMT_NORMALIZE_CONTINUOUS; CMT_OPEN_NONZERO; OPEN_DIFF; OPEN_UNIV;
                 CLOSED_CBALL];
        REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL] THEN
        UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID; GSYM NORM_EQ_0] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `z:real^3` THEN
        REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL; wan_rext] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
        MP_TAC(ISPECL [`rho:real`; `inv(norm z) % z:real^3`] CMW_CAP_FACTS) THEN
        ASM_SIMP_TAC[P4_RADIAL_SPHERE] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        UNDISCH_TAC `~(dist(basis 3:real^3,inv(norm z) % z) <= &2 * rho)` THEN
        REWRITE_TAC[dist] THEN SPEC_TAC(`inv(norm z) % z:real^3`,`w:real^3`) THEN
        GEN_TAC THEN CONV_TAC NORM_ARITH];
      SIMP_TAC[]];
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`rho:real`; `y:real^3`] CMW_CAP_FACTS) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* The energy of u o Phi exceeds that of u by at most 32 C^2 B times the     *)
(* integral of the cutoff of the cap of radius 3 rho.                         *)

let CMW_CAP_ENERGY = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) rho C B.
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
        (!z v. &0 <= v dot (G z ** v)) /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        &0 < rho /\ rho <= &1 / &4 /\
        (!w. norm(vectorize(jacobian cmw_capm (at w))) <= C) /\
        (!x. x IN sphere(vec 0,&1)
             ==> norm(vectorize(transp(jacobian (wan_rext u) (at x)) ** G(u x) **
                                jacobian (wan_rext u) (at x))) <= B)
        ==> cm_sen G (\y. u(cmw_cap rho y)) <=
            cm_sen G u +
            (&32 * C pow 2 * B) *
            p4_s2_integral (\y. cmw_capcut(norm(y - basis 3) / rho))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["GS";"GP";"UC";"R0";"R1";"CB";"BB"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`rho:real`; `C:real`] CMW_CAP_REXT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PS") (LABEL_TAC "PJ")) THEN
  SUBGOAL_THEN `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                  (wan_rext (cmw_cap rho))` (LABEL_TAC "PC") THENL
   [USE_THEN "PS" (MP_TAC o REWRITE_RULE[smooth_map_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> cmw_cap rho y IN sphere(vec 0,&1)`
  (LABEL_TAC "PM") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`rho:real`; `y:real^3`] CMW_CAP_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `cmw_cap rho`] CMW_SLICE_REPARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "VC") (LABEL_TAC "VJ")) THEN
  MP_TAC(BETA_RULE(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`;
                           `\y:real^3. (u:real^3->real^K)(cmw_cap rho y)`] CM_CLASSICAL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `G:real^K->real^K^K`; `u:real^3->real^K`]
    CM_CLASSICAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
  MP_TAC(BETA_RULE(ISPECL [`G:real^K->real^K^K`; `\y:real^3. (u:real^3->real^K)(cmw_cap rho y)`]
    CMW_DENS_CONT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "E2C") (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`] CMW_DENS_CONT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "E1C") (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `(\y. lift(cmw_capcut(norm(y - basis 3:real^3) / rho))) continuous_on sphere(vec 0,&1)`
  (LABEL_TAC "CC") THENL
   [MP_TAC CMW_CAPCUT_FACTS THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = &32 * C pow 2 * B` THEN
  SUBGOAL_THEN `&0 <= C /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "CB" (MP_TAC o SPEC `vec 0:real^3`) THEN
      MP_TAC(ISPEC `vectorize(jacobian cmw_capm (at (vec 0:real^3)))` NORM_POS_LE) THEN
      REAL_ARITH_TAC;
      USE_THEN "BB" (MP_TAC o SPEC `basis 3:real^3`) THEN
      SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= b ==> &0 <= b`) THEN
      REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K0` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `p4_s2_integral
     (\y. trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at y)) **
                (G:real^K->real^K^K)(u y) ** jacobian (wan_rext u) (at y)) / &2 +
          K0 * cmw_capcut(norm(y - basis 3:real^3) / rho))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_S2_INTEGRAL_MONO THEN REWRITE_TAC[] THEN
    USE_THEN "E2C" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      USE_THEN "E1C" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN USE_THEN "CC" ACCEPT_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ wan_rext (u:real^3->real^K) differentiable at y`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[P4_SPHERE_NONZERO] THEN MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_SIMP_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM; P4_SPHERE_NONZERO];
      ALL_TAC] THEN
    ASM_CASES_TAC `&2 * rho < norm(y - basis 3:real^3)` THENL
     [MP_TAC(ISPECL [`rho:real`; `u:real^3->real^K`; `y:real^3`] CMW_CAP_SAME_JAC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC CMW_CAPCUT_FACTS THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `cmw_capcut(norm(y - basis 3:real^3) / rho) = &1` SUBST1_TAC THENL
     [MP_TAC CMW_CAPCUT_FACTS THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ b <= k ==> b <= a + k * &1`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x / &2`) THEN
      MATCH_MP_TAC CMW_TRACE_GRAM_NONNEG THEN USE_THEN "GP" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "VJ" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `y IN sphere(vec 0:real^3,&1)`)]) THEN
    REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &2 * k ==> x / &2 <= k`) THEN
    EXPAND_TAC "K0" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(jacobian (wan_rext (cmw_cap rho)) (at (y:real^3)))) pow 2 *
                norm(vectorize(transp(jacobian (wan_rext (u:real^3->real^K))
                                       (at (cmw_cap rho y))) **
                               (G:real^K->real^K^K)(u(cmw_cap rho y)) **
                               jacobian (wan_rext u) (at (cmw_cap rho y))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_ASSOC] THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
      MP_TAC(ISPECL [`jacobian (wan_rext (cmw_cap rho)) (at (y:real^3))`;
                     `transp(jacobian (wan_rext (u:real^3->real^K)) (at (cmw_cap rho y))) **
                      (G:real^K->real^K^K)(u(cmw_cap rho y)) **
                      jacobian (wan_rext u) (at (cmw_cap rho y))`]
        CMW_TRACE_GRAM_VEC_BOUND) THEN
      REWRITE_TAC[MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&8 * C) pow 2 * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        USE_THEN "PJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "BB" MATCH_MP_TAC THEN USE_THEN "PM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y. trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at y)) **
               (G:real^K->real^K^K)(u y) ** jacobian (wan_rext u) (at y)) / &2`;
    `\y. K0 * cmw_capcut(norm(y - basis 3:real^3) / rho)`] P4_S2_INTEGRAL_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [USE_THEN "E1C" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN USE_THEN "CC" ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\y. cmw_capcut(norm(y - basis 3:real^3) / rho)`; `K0:real`]
    P4_S2_INTEGRAL_CMUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [USE_THEN "CC" ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

(* The integral of the cap cutoff tends to 0 with rho (dominated convergence *)
(* along rho_n = r0 / (n + 1); the exceptional set is the hyperplane x1 = 0). *)

let CMW_EVENTUAL_ARITH = prove
 (`!dd r0 N n. &0 < dd /\ &0 < r0 /\ &3 * r0 / dd <= &N /\ N <= n
               ==> &3 <= dd / (r0 / &(n + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(n + 1) /\ &0 < r0 / &(n + 1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `&3 * r0 / m = (&3 * r0) / m`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dd * &N` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&3 * r0 / dd <= &N` THEN
    REWRITE_TAC[REAL_ARITH `&3 * r0 / m = (&3 * r0) / m`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;

let CMW_CAP_INTEGRAL_SMALL = prove
 (`!r0 e. &0 < r0 /\ &0 < e
          ==> ?rho. &0 < rho /\ rho <= r0 /\
                    p4_s2_integral (\y. cmw_capcut(norm(y - basis 3:real^3) / rho)) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\y. lift(cmw_capcut(norm(y - basis 3:real^3) / (r0 / &(n + 1)))))
        continuous_on sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC CMW_CAPCUT_FACTS THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n z:real^3. lift(cmw_capcut(norm(inv(norm z) % z - basis 3) / (r0 / &(n + 1))))`;
    `\z:real^3. vec 0:real^1`; `\z:real^3. lift(&1)`; `ball(vec 0:real^3,&1)`;
    `{x:real^3 | x$1 = &0}`] DOMINATED_CONVERGENCE_AE) THEN
  REWRITE_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPEC `\y. cmw_capcut(norm(y - basis 3:real^3) / (r0 / &(k + 1)))`
        P4_S2_INTEGRABLE) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      MP_TAC CMW_CAPCUT_FACTS THEN
      DISCH_THEN(MP_TAC o SPEC `norm(inv(norm x) % x - basis 3:real^3) / (r0 / &(k + 1))` o
        CONJUNCT1) THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      SUBGOAL_THEN `&0 < norm(inv(norm z) % z - basis 3:real^3)` ASSUME_TAC THENL
       [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((z:real^3)$1 = &0)` THEN
        SUBGOAL_THEN `(inv(norm z) % z:real^3)$1 = &0` MP_TAC THENL
         [ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH]; ALL_TAC] THEN
        REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ENTIRE; REAL_INV_EQ_0; NORM_EQ_0] THEN
        ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_REWRITE_TAC[VEC_COMPONENT];
        ALL_TAC] THEN
      MP_TAC(SPEC `&3 * r0 / norm(inv(norm z) % z - basis 3:real^3)` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      MP_TAC CMW_CAPCUT_FACTS THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
        CONJUNCT2) THEN
      MATCH_MP_TAC CMW_EVENTUAL_ARITH THEN EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[INTEGRAL_0; LIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL; DIST_0; NORM_1] THEN DISCH_TAC THEN
  EXISTS_TAC `r0 / &(N + 1)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MP_TAC(SPEC `N:num` REAL_POS) THEN
    SUBGOAL_THEN `&0 <= r0 * &N` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[p4_s2_integral] THEN ASM_REAL_ARITH_TAC]);;

(* The pullback metric of a cmw_c1sweep with jointly continuous values is    *)
(* jointly continuous on S^2 x [0,1].                                        *)

let CMW_C1SWEEP_PMET_CONT = prove
 (`!S (G:real^K->real^K^K) d (W:real^3->real->real^K).
        cm_target S G d /\ cmw_c1sweep W /\
        (\x. W (fstcart x) (drop(sndcart x))) continuous_on
          {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]}
        ==> (\x. vectorize(cmw_pmet G W (drop(sndcart x)) (fstcart x))) continuous_on
            {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP CMW_TARGET_FACTS)
    (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[cmw_c1sweep]) (LABEL_TAC "WCT"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "WJ")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "GC") (K ALL_TAC)))))) THEN
  ABBREV_TAC `KK = {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  REWRITE_TAC[cmw_pmet; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:K) /\ 1 <= q /\ q <= dimindex(:K)
          ==> (\x. lift((G:real^K->real^K^K)
                         ((W:real^3->real->real^K) (fstcart x) (drop(sndcart x)))$p$q))
              continuous_on KK`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. lift((G:real^K->real^K^K)
                 ((W:real^3->real->real^K) (fstcart x) (drop(sndcart x)))$p$q)) =
      (\z. lift(G z$p$q)) o (\x. W (fstcart x) (drop(sndcart x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN USE_THEN "WCT" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    USE_THEN "GC" (MP_TAC o REWRITE_RULE[o_DEF; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:K) /\ 1 <= q /\ q <= 3
          ==> (\x. lift(((G:real^K->real^K^K)
                          ((W:real^3->real->real^K) (fstcart x) (drop(sndcart x))) **
                         jacobian (wan_rext (\y. W y (drop(sndcart x)))) (at (fstcart x)))$p$q))
              continuous_on KK`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`KK:real^(3,1)finite_sum->bool`;
      `\x. (G:real^K->real^K^K) ((W:real^3->real->real^K) (fstcart x) (drop(sndcart x)))`;
      `\x. jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                    (at (fstcart x))`] CMT_CONT_MATMUL) THEN
    REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "WJ" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`KK:real^(3,1)finite_sum->bool`;
    `\x. transp(jacobian (wan_rext (\y. (W:real^3->real->real^K) y (drop(sndcart x))))
                          (at (fstcart x)))`;
    `\x. (G:real^K->real^K^K) ((W:real^3->real->real^K) (fstcart x) (drop(sndcart x))) **
         jacobian (wan_rext (\y. W y (drop(sndcart x)))) (at (fstcart x))`] CMT_CONT_MATMUL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[TRANSP_COMPONENT] THEN
  USE_THEN "WJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CMW_FSTCART_COMPOSE_CONT = prove
 (`!(f:real^3->real^N) s.
        f continuous_on s /\ sphere(vec 0,&1) SUBSET s
        ==> (\x. f(fstcart x)) continuous_on
            {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                      drop(sndcart x) IN real_interval[&0,&1]}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^(3,1)finite_sum. (f:real^3->real^N)(fstcart x)) = f o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[]);;

(* CM footnote 8: composing with a small cap collapse gives a sweepout with  *)
(* the same properties, energy at most e more, every slice with zero         *)
(* Jacobian on a cap, and homotopic to the given one.                        *)

let CMW_FOOTNOTE8 = prove
 (`!S (G:real^K->real^K^K) d (W:real^3->real->real^K) V A e.
        cm_target S G d /\ cmw_c1sweep W /\
        (\x. W (fstcart x) (drop(sndcart x))) continuous_on
          {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
        V SUBSET S /\
        (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> W y t IN V) /\
        (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                ==> W y (&0) = W y' (&0) /\ W y (&1) = W y' (&1)) /\
        (!t. t IN real_interval[&0,&1] ==> cm_sen G (\y. W y t) <= A) /\ &0 < e
        ==> ?W':real^3->real->real^K.
              cmw_c1sweep W' /\
              (\x. W' (fstcart x) (drop(sndcart x))) continuous_on
                {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
              (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] ==> W' y t IN V) /\
              (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                      ==> W' y (&0) = W' y' (&0) /\ W' y (&1) = W' y' (&1)) /\
              (!t. t IN real_interval[&0,&1]
                   ==> cm_sen G (\y. W' y t) < A + e /\
                       ?O. open_in (subtopology euclidean (sphere(vec 0,&1))) O /\
                           ~(O = {}) /\
                           !y. y IN O ==> jacobian (wan_rext (\y. W' y t)) (at y) = mat 0) /\
              cm_shomotopic S W W'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GS")
      (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real`
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
          (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
            (LABEL_TAC "GP")))))))))))) THEN
  ABBREV_TAC `KK = {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN `compact(KK:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN REWRITE_TAC[CMW_SLAB_COMPACT]; ALL_TAC] THEN
  (* the bound B of the pullback metric *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `W:real^3->real->real^K`] CMW_C1SWEEP_PMET_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?B. !t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
              ==> norm(vectorize(cmw_pmet (G:real^K->real^K^K) (W:real^3->real->real^K) t y))
                  <= B`
  (X_CHOOSE_THEN `B:real` (LABEL_TAC "BB")) THENL
   [MP_TAC(ISPECL
     [`\x:real^(3,1)finite_sum. vectorize(cmw_pmet (G:real^K->real^K^K)
                                  (W:real^3->real->real^K) (drop(sndcart x)) (fstcart x))`;
      `KK:real^(3,1)finite_sum->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y:real^3) (lift t)`) THEN
    EXPAND_TAC "KK" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  (* the constant C of m and the uniform continuity of W *)
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CB")) CMW_CAPM_JAC_BOUND THEN
  MP_TAC(ISPECL [`\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (fstcart x)
                                                (drop(sndcart x))`;
                 `KK:real^(3,1)finite_sum->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC"))) THEN
  (* the choice of rho *)
  MP_TAC(ISPECL [`min (&1 / &4) (r / &7)`;
                 `e / (&32 * C pow 2 * abs B + &1)`] CMW_CAP_INTEGRAL_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rho <= &1 / &4 /\ &6 * rho < r` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real`; `C:real`] CMW_CAP_REXT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PS") (LABEL_TAC "PJ")) THEN
  SUBGOAL_THEN `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                  (wan_rext (cmw_cap rho))` (LABEL_TAC "PC") THENL
   [USE_THEN "PS" (MP_TAC o REWRITE_RULE[smooth_map_on]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> cmw_cap rho y IN sphere(vec 0,&1)`
  (LABEL_TAC "PM") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`rho:real`; `y:real^3`] CMW_CAP_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cmw_cap rho) continuous_on sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_SPHERE_MAP_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (W:real^3->real->real^K) (cmw_cap rho (fstcart x)) (drop(sndcart x)))
    continuous_on KK`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (fstcart x)
                                                  (drop(sndcart x))`;
                   `\t:real. cmw_cap rho`] CMW_SLAB_REPARAM_CONT) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN EXPAND_TAC "KK" THEN
    MATCH_MP_TAC CMW_FSTCART_COMPOSE_CONT THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[SUBSET_REFL; ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `\y t. (W:real^3->real->real^K) (cmw_cap rho y) t` THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the C^1 sweep *)
    MP_TAC(ISPECL [`W:real^3->real->real^K`; `\t:real. cmw_cap rho`]
      CMW_REPARAM_C1SWEEP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "KK" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMW_FSTCART_COMPOSE_CONT THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[SUBSET_REFL; ETA_AX];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`\z:real^3. lift(jacobian (wan_rext (cmw_cap rho)) (at z)$i$j)`;
                     `{z:real^3 | ~(z = vec 0)}`] CMW_FSTCART_COMPOSE_CONT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; P4_SPHERE_NONZERO] THEN
      MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (cmw_cap rho)`]
        CMW_C1_JAC_ENTRY_CONT) THEN
      ASM_REWRITE_TAC[CMT_OPEN_NONZERO; DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    (* values *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    (* ends *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    (* energy and the cap *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL [`G:real^K->real^K^K`; `\y. (W:real^3->real->real^K) y t`;
                              `rho:real`; `C:real`; `B:real`] CMW_CAP_ENERGY)) THEN
      ANTS_TAC THENL
       [USE_THEN "GS" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "GP" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "CB" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `cmw_c1sweep (W:real^3->real->real^K)` THEN
          REWRITE_TAC[cmw_c1sweep] THEN ASM_SIMP_TAC[];
          REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM cmw_pmet] THEN
          USE_THEN "BB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= A /\ k < e ==> x <= a + k ==> x < A + e`) THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= p4_s2_integral (\y. cmw_capcut(norm(y - basis 3:real^3) / rho))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC P4_S2_INTEGRAL_POS THEN REWRITE_TAC[] THEN CONJ_TAC THENL
         [MP_TAC CMW_CAPCUT_FACTS THEN
          DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
          REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
          REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
          MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
          REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
          MP_TAC CMW_CAPCUT_FACTS THEN SIMP_TAC[]];
        ALL_TAC] THEN
      ABBREV_TAC `I0 = p4_s2_integral (\y. cmw_capcut(norm(y - basis 3:real^3) / rho))` THEN
      ABBREV_TAC `K1 = &32 * C pow 2 * abs B` THEN
      SUBGOAL_THEN `&0 <= K1 /\ &32 * C pow 2 * B <= K1` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "K1" THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_ABS_POS];
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC[REAL_ARITH `B <= abs B`] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          REWRITE_TAC[REAL_LE_POW_2]];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `K1 * I0` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `K1 * e / (K1 + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < K1 + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      SUBGOAL_THEN `&0 <= K1 * e` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `sphere(vec 0:real^3,&1) INTER ball(basis 3,rho)` THEN
      SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `basis 3:real^3` THEN
        ASM_SIMP_TAC[IN_INTER; IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH; CENTRE_IN_BALL];
        X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN STRIP_TAC THEN
        MP_TAC(BETA_RULE(ISPECL [`rho:real`; `\y. (W:real^3->real->real^K) y t`;
                                 `y:real^3`] CMW_CAP_ZERO_JAC)) THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `dist(basis 3:real^3,y) < rho` THEN REWRITE_TAC[dist] THEN
        CONV_TAC NORM_ARITH]];
    (* the homotopy *)
    MATCH_MP_TAC CMW_CLOSE_SHOMOTOPIC THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMW_SLAB_CONTINUOUS_MAP THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `\y t. (W:real^3->real->real^K) (cmw_cap rho y) t`
        CMW_SLAB_CONTINUOUS_MAP) THEN
      ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `cmw_cap rho (y:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(V:real^K->bool) SUBSET S` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(V:real^K->bool) SUBSET S` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "UC" (MP_TAC o SPECL [`pastecart (y:real^3) (lift t)`;
                                     `pastecart (cmw_cap rho (y:real^3)) (lift t)`]) THEN
      EXPAND_TAC "KK" THEN
      REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      ASM_REWRITE_TAC[dist; PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`rho:real`; `y:real^3`] CMW_CAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[NORM_SUB]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* CM Prop 1.5 with footnote 8 (CMW_P15_STATEMENT) from                      *)
(* CM_CRITICAL_ISOLATED, the embedded image W0 = f o sigma, the conformal    *)
(* reparametrization W1 = W0(h_t ., t) of D.7 and the cap collapse           *)
(* W2 = W1 o Phi, all constructed above.                                     *)
(* ========================================================================= *)

let CMW_P15 = prove
 (`CM_CRITICAL_ISOLATED_STATEMENT (:K) ==> CMW_P15_STATEMENT (:A) (:K)`,
  REWRITE_TAC[CMW_P15_STATEMENT; CM_CRITICAL_ISOLATED_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "CRIT") THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                       `U:A->bool`; `sigma:real^3->real->A`; `e:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                 `U:A->bool`; `sigma:real^3->real->A`] CMW_P15_W0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0C") (CONJUNCTS_THEN2 (LABEL_TAC "W0V")
    (CONJUNCTS_THEN2 (LABEL_TAC "W0E") (CONJUNCTS_THEN2 (LABEL_TAC "W0A") (K ALL_TAC))))) THEN
  UNDISCH_TAC `p4_sweepout_in (top,atlas:((A->bool)#(A->real^3))->bool) U sigma` THEN
  REWRITE_TAC[p4_sweepout_in] THEN STRIP_TAC THEN
  UNDISCH_TAC `cm_emb (top,atlas:((A->bool)#(A->real^3))->bool) g (f:A->real^K) G d` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[cm_emb] th)) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (f:A->real^K) (topspace top)` THEN
  SUBGOAL_THEN `IMAGE (f:A->real^K) U SUBSET S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `KK = {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  (* W0 on the slab *)
  SUBGOAL_THEN `cmw_c1sweep (\y t. (f:A->real^K)((sigma:real^3->real->A) y t))`
  (LABEL_TAC "W0S") THENL
   [MATCH_MP_TAC CMW_C1_IMP_C1SWEEP THEN REWRITE_TAC[] THEN USE_THEN "W0C" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (f:A->real^K)((sigma:real^3->real->A) (fstcart x) (drop(sndcart x))))
    continuous_on KK`
  (LABEL_TAC "W0K") THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. (f:A->real^K)((sigma:real^3->real->A)
                       (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "KK" THEN REWRITE_TAC[IN_ELIM_THM; IN_SPHERE_0] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                            drop(sndcart x) IN real_interval[&0,&1]}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        EXISTS_TAC `1` THEN USE_THEN "W0C" ACCEPT_TAC;
        EXPAND_TAC "KK" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[P4_SPHERE_NONZERO]]];
    ALL_TAC] THEN
  (* the reparametrization W1 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\y t. (f:A->real^K)((sigma:real^3->real->A) y t)`; `e / &4`]
                CMW_P15_REPARAM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [USE_THEN "W0C" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3")))) THEN
  SUBGOAL_THEN
   `!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
          ==> (h:real->real^3->real^3) t y IN sphere(vec 0,&1)`
  (LABEL_TAC "HS") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmw_c1sweep (\y t. (f:A->real^K)((sigma:real^3->real->A) ((h:real->real^3->real^3) t y) t))`
  (LABEL_TAC "W1S") THENL
   [MP_TAC(ISPECL [`\y t. (f:A->real^K)((sigma:real^3->real->A) y t)`;
                   `h:real->real^3->real^3`] CMW_REPARAM_C1SWEEP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "W0S" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (f:A->real^K)((sigma:real^3->real->A)
           ((h:real->real^3->real^3) (drop(sndcart x)) (fstcart x)) (drop(sndcart x))))
    continuous_on KK`
  (LABEL_TAC "W1K") THENL
   [MP_TAC(ISPECL [`\x. (f:A->real^K)((sigma:real^3->real->A) (fstcart x) (drop(sndcart x)))`;
                   `h:real->real^3->real^3`] CMW_SLAB_REPARAM_CONT) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "HS" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the area bound *)
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> cm_sen (G:real^K->real^K^K)
              (\y. (f:A->real^K)((sigma:real^3->real->A) ((h:real->real^3->real^3) t y) t))
            <= p4_sweep_area atlas (g:A->real^3^3) sigma + e / &4`
  (LABEL_TAC "E1") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm_sarea (G:real^K->real^K^K)
                  (\y. (f:A->real^K)((sigma:real^3->real->A) y t)) + e / &4` THEN
    CONJ_TAC THENL
     [USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "W0A" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`)]) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
    REWRITE_TAC[p4_sweep_area] THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `sigma:real^3->real->A`] P4_SWEEP_AREA_BOUND) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* footnote 8 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\y t. (f:A->real^K)((sigma:real^3->real->A) ((h:real->real^3->real^3) t y) t)`;
                 `IMAGE (f:A->real^K) U`; `p4_sweep_area atlas (g:A->real^3^3) sigma + e / &4`;
                 `e / &4`] CMW_FOOTNOTE8) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "W0V" MATCH_MP_TAC THEN
      USE_THEN "HS" (fun th -> ASM_SIMP_TAC[th]);
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "W0E" (MP_TAC o SPECL [`(h:real->real^3->real^3) (&0) y`;
                                        `(h:real->real^3->real^3) (&0) y'`]);
        USE_THEN "W0E" (MP_TAC o SPECL [`(h:real->real^3->real^3) (&1) y`;
                                        `(h:real->real^3->real^3) (&1) y'`])] THEN
      (ANTS_TAC THENL
        [CONJ_TAC THEN USE_THEN "HS" MATCH_MP_TAC THEN
         ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
         SIMP_TAC[]]);
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:real^3->real->real^K`
    (CONJUNCTS_THEN2 (LABEL_TAC "W2S") (CONJUNCTS_THEN2 (LABEL_TAC "W2K")
      (CONJUNCTS_THEN2 (LABEL_TAC "W2V") (CONJUNCTS_THEN2 (LABEL_TAC "W2E")
        (CONJUNCTS_THEN2 (LABEL_TAC "W2N") (LABEL_TAC "W2H"))))))) THEN
  EXISTS_TAC `W2:real^3->real->real^K` THEN
  USE_THEN "W2S" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "W2V" (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [(* cm_sweep *)
    MATCH_MP_TAC CMW_C1SWEEP_CM_SWEEP THEN
    USE_THEN "W2S" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "W2E" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMW_SLAB_CONTINUOUS_MAP THEN EXPAND_TAC "KK" THEN
      USE_THEN "W2K" ACCEPT_TAC;
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (f:A->real^K) U SUBSET S` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN USE_THEN "W2V" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* energy and non-harmonicity *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "W2N" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    USE_THEN "CRIT" (fun crit -> MP_TAC(SPECL
      [`\y. (W2:real^3->real->real^K) y t`; `O:real^3->bool`]
      (MATCH_MP (SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] crit)
                (ASSUME `cm_target (S:real^K->bool) G d`)))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(jacobian (wan_rext (\y. (W2:real^3->real->real^K) y t)) (at y) = mat 0)` THEN
    ASM_SIMP_TAC[];
    (* essentiality *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `U:A->bool`;
                   `\y t. (f:A->real^K)((sigma:real^3->real->A) ((h:real->real^3->real^3) t y) t)`;
                   `W2:real^3->real->real^K`] CMW_EMB_ESSENTIAL_HOMOTOPIC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "W0V" MATCH_MP_TAC THEN
      USE_THEN "HS" (fun th -> ASM_SIMP_TAC[th]);
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] CMW_REPARAM_ESSENTIAL) THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "H1" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    ASM_SIMP_TAC[]]);;

