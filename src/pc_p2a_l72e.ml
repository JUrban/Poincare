(* ========================================================================= *)
(* pc_p2a_l72e: O10 part 5, the minimizing case (c) of Lemma 7.2 for a       *)
(* single box (the route to FL2).  On a chart piece the limit curve is the   *)
(* BVP solution between its end points: the broken curve through a midpoint  *)
(* is no longer than the BVP solution in the limit (BVP comparison for the   *)
(* approximating curves, which are almost minimizing on the piece), hence    *)
(* equal to it (uniqueness clause of P2A_LOC_BVP_PW); the energy of the      *)
(* broken curve is bounded by the energies of BVP solutions (minimality      *)
(* against segments and domination).                                         *)
(* The first part: restrictions of the local families to open subsets,       *)
(* energy of C^1 curves and of BVP solutions, broken curves (p2ak_join).     *)
(* ========================================================================= *)

needs "src/pc_p2a_l72d.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AK_LSMOOTH_SUBSET = prove
 (`!U U' ta tb (Gt:real->real^N->real^N^N).
     p2a_lsmooth U ta tb Gt /\ open U' /\ U' SUBSET U ==> p2a_lsmooth U' ta tb Gt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[]]);;

let P2AK_LRICCI_SUBSET = prove
 (`!U U' a b (G:real->real^N->real^N^N).
     lricci_flow U a b G /\ open U' /\ U' SUBSET U ==> lricci_flow U' a b G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let P2AK_C1_ENERGY = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (z:real^1->real^N) s1 s2 C lam Rm.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 <= s2 /\ s2 < sb /\
     &0 <= s1 /\ &0 < lam /\
     (!s. s1 <= s /\ s <= s2
          ==> z(lift s) IN U /\ z(lift s) IN C /\ z differentiable (at (lift s)) /\
              (\v. vector_derivative z (at v)) continuous (at (lift s))) /\
     (!s y u. s1 <= s /\ s <= s2 /\ y IN C
              ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) y ** u) /\
                  abs(lscalar (Gt(tt - s pow 2)) y) <= Rm)
     ==> (\s. p2a_llag Gt tt s (z(lift s)) (vector_derivative z (at (lift s))))
           real_integrable_on real_interval[s1,s2] /\
         p2a_cE Gt tt z s1 s2 <=
         &2 / lam * (p2a_cL Gt tt z s1 s2 + &2 * s2 pow 2 * Rm * (s2 - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^1->real^N) continuous_on interval[lift s1,lift s2] /\
                (\v. vector_derivative z (at v)) continuous_on interval[lift s1,lift s2]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                  (vector_derivative z (at (lift s))))
    real_integrable_on real_interval[s1,s2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `z:real^1->real^N`; `\v. vector_derivative (z:real^1->real^N) (at v)`;
                   `s1:real`; `s2:real`] P2A_LLAG_CURVE_CONTINUOUS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `z:real^1->real^N`; `s1:real`; `s2:real`;
                 `{}:real->bool`; `C:real^N->bool`; `lam:real`; `Rm:real`] P2AK_ENERGY_DOM) THEN
  ASM_SIMP_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REWRITE_TAC[p2a_cE; p2a_cL; GSYM NORM_POW_2] THEN SIMP_TAC[]]);;

let P2AK_SEG_CL_BOUND = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y1:real^N) y2 s1 s2 C Gm Rm.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 < s2 /\ s2 < sb /\
     &0 <= s1 /\ segment[y1,y2] SUBSET U /\ segment[y1,y2] SUBSET C /\ &0 <= Rm /\
     (!s y u. s1 <= s /\ s <= s2 /\ y IN C
              ==> u dot (Gt(tt - s pow 2) y ** u) <= Gm * norm u pow 2 /\
                  abs(lscalar (Gt(tt - s pow 2)) y) <= Rm)
     ==> p2a_cL Gt tt (\x. y1 + (drop x - s1) % (inv(s2 - s1) % (y2 - y1))) s1 s2
         <= Gm / &2 * norm(y2 - y1) pow 2 / (s2 - s1) + &2 * s2 pow 2 * Rm * (s2 - s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w = inv(s2 - s1) % ((y2:real^N) - y1)` THEN
  SUBGOAL_THEN `!s. vector_derivative (\x. (y1:real^N) + (drop x - s1) % w) (at (lift s)) = w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN REWRITE_TAC[P2AK_AFFINE_VD]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (y1:real^N) + (s - s1) % w IN segment[y1,y2]`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `(s - s1) / (s2 - s1)` THEN
    SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_cL; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[s1,s2])
                (\s:real. Gm / &2 * norm(w:real^N) pow 2 + &2 * s2 pow 2 * Rm)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `\x:real^1. (y1:real^N) + (drop x - s1) % w`;
                     `\x:real^1. (w:real^N)`; `s1:real`; `s2:real`] P2A_LLAG_CURVE_CONTINUOUS) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[p2a_llag] THEN
    SUBGOAL_THEN `(y1:real^N) + (s - s1) % w IN C` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(y1:real^N) + (s - s1) % w`; `w:real^N`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Gm:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 * lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                                    ((y1:real^N) + (s - s1) % w) <= s2 pow 2 * Rm`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2 * Rm` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `norm(w:real^N) pow 2 = norm((y2:real^N) - y1) pow 2 / (s2 - s1) pow 2`
  SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `s1 < s2 ==> abs(s2 - s1) = s2 - s1`; REAL_POW_INV] THEN
    REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN `~(s2 - s1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let P2AK_SOL_ENERGY = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (sol:real^1->real^N) y1 y2 s1 s2 E lam Gm Rm.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 < s2 /\ s2 < sb /\
     &0 <= s1 /\ convex U /\ y1 IN U /\ y2 IN U /\ &0 < lam /\ &0 <= Rm /\
     (!s y u. s1 <= s /\ s <= s2 /\ y IN U
              ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) y ** u) /\
                  u dot (Gt(tt - s pow 2) y ** u) <= Gm * norm u pow 2 /\
                  abs(lscalar (Gt(tt - s pow 2)) y) <= Rm) /\
     sol(lift s1) = y1 /\ sol(lift s2) = y2 /\
     (!s. s1 <= s /\ s <= s2
          ==> sol(lift s) IN U /\ sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s))) /\
     (!sig' K M. sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                 (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                 FINITE K /\ sig' continuous_on interval[lift s1,lift s2] /\
                 (!s. s1 < s /\ s < s2 /\ ~(s IN K)
                      ==> sig' differentiable (at (lift s)) /\
                          norm(vector_derivative sig' (at (lift s))) <= M) /\
                 p2a_cE Gt tt sig' s1 s2 <= E
                 ==> p2a_cL Gt tt sol s1 s2 <= p2a_cL Gt tt sig' s1 s2) /\
     norm(y2 - y1) pow 2 / (s2 - s1) <= E
     ==> p2a_cE Gt tt sol s1 s2 <=
         &2 / lam * (Gm / &2 * norm(y2 - y1) pow 2 / (s2 - s1) +
                     &4 * s2 pow 2 * Rm * (s2 - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sol:real^1->real^N`; `s1:real`; `s2:real`; `U:real^N->bool`; `lam:real`;
                 `Rm:real`] P2AK_C1_ENERGY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  ABBREV_TAC `w = inv(s2 - s1) % ((y2:real^N) - y1)` THEN
  SUBGOAL_THEN `segment[y1:real^N,y2] SUBSET U` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. vector_derivative (\x. (y1:real^N) + (drop x - s1) % w) (at (lift s)) = w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN REWRITE_TAC[P2AK_AFFINE_VD]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (y1:real^N) + (s - s1) % w IN segment[y1,y2]`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `(s - s1) / (s2 - s1)` THEN
    SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt sol s1 s2 <=
    p2a_cL Gt tt (\x. (y1:real^N) + (drop x - s1) % w) s1 s2`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`{}:real->bool`; `norm(w:real^N)`] THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; LIFT_DROP; REAL_SUB_REFL; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "w" THEN MATCH_MP_TAC P2AK_CHORD_END THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^1. drop h % (w:real^N)` THEN
      REWRITE_TAC[GSYM has_vector_derivative; P2AK_AFFINE_VD];
      REWRITE_TAC[p2a_cE] THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE; DOT_SQUARE_NORM] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((y2:real^N) - y1) pow 2 / (s2 - s1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `s1 < s2 ==> abs(s2 - s1) = s2 - s1`; REAL_POW_INV] THEN
      SUBGOAL_THEN `~(s2 - s1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `y2:real^N`; `s1:real`; `s2:real`; `U:real^N->bool`;
                 `Gm:real`; `Rm:real`] P2AK_SEG_CL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 / lam * (p2a_cL (Gt:real->real^N->real^N^N) tt sol s1 s2 +
                         &2 * s2 pow 2 * Rm * (s2 - s1))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

let P2AK_INT_JOIN = prove
 (`!f fa fb s1 sm s2.
     s1 <= sm /\ sm <= s2 /\
     fa real_integrable_on real_interval[s1,sm] /\ fb real_integrable_on real_interval[sm,s2] /\
     (!s. s1 < s /\ s < sm ==> f s = fa s) /\ (!s. sm < s /\ s < s2 ==> f s = fb s)
     ==> f real_integrable_on real_interval[s1,s2] /\
         real_integral (real_interval[s1,s2]) f =
         real_integral (real_interval[s1,sm]) fa + real_integral (real_interval[sm,s2]) fb`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `fa:real->real`; `s1:real`; `sm:real`]
                P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  MP_TAC(ISPECL [`f:real->real`; `fb:real->real`; `sm:real`; `s2:real`]
                P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ASM_SIMP_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real->real`; `real_integral (real_interval[s1,sm]) fa`;
                 `real_integral (real_interval[sm,s2]) fb`; `s1:real`; `s2:real`; `sm:real`]
                HAS_REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (find_term ((=) `fa:real->real`)) (concl th) &&
        is_eq (concl th))) THEN
      MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (find_term ((=) `fb:real->real`)) (concl th) &&
        is_eq (concl th))) THEN
      MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MESON_TAC[REAL_INTEGRAL_UNIQUE; real_integrable_on]);;

let P2AK_INT_JOIN_EQ = prove
 (`!f fa fb s1 sm s2.
     s1 <= sm /\ sm <= s2 /\
     fa real_integrable_on real_interval[s1,sm] /\ fb real_integrable_on real_interval[sm,s2] /\
     (!s. s1 < s /\ s < sm ==> f s = fa s) /\ (!s. sm < s /\ s < s2 ==> f s = fb s)
     ==> real_integral (real_interval[s1,s2]) f =
         real_integral (real_interval[s1,sm]) fa + real_integral (real_interval[sm,s2]) fb`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2AK_INT_JOIN) THEN SIMP_TAC[]);;

let p2ak_join = new_definition
 `p2ak_join (soa:real^1->real^N) (sob:real^1->real^N) (sm:real) =
    \v. if drop v <= sm then soa v else sob v`;;

let P2AK_JOIN_FACTS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (soa:real^1->real^N) sob s1 sm s2.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 < sm /\ sm < s2 /\ s2 < sb /\
     soa(lift sm) = sob(lift sm) /\
     (!s. s1 <= s /\ s <= sm
          ==> soa(lift s) IN U /\ soa differentiable (at (lift s)) /\
              (\v. vector_derivative soa (at v)) continuous (at (lift s))) /\
     (!s. sm <= s /\ s <= s2
          ==> sob(lift s) IN U /\ sob differentiable (at (lift s)) /\
              (\v. vector_derivative sob (at v)) continuous (at (lift s)))
     ==> ?M. p2ak_join soa sob sm (lift s1) = soa(lift s1) /\
             p2ak_join soa sob sm (lift s2) = sob(lift s2) /\
             (!s. s1 <= s /\ s <= s2 ==> p2ak_join soa sob sm (lift s) IN U) /\
             p2ak_join soa sob sm continuous_on interval[lift s1,lift s2] /\
             (!s. s1 < s /\ s < s2 /\ ~(s IN {sm})
                  ==> p2ak_join soa sob sm differentiable (at (lift s)) /\
                      norm(vector_derivative (p2ak_join soa sob sm) (at (lift s))) <= M) /\
             p2a_cL Gt tt (p2ak_join soa sob sm) s1 s2 =
             p2a_cL Gt tt soa s1 sm + p2a_cL Gt tt sob sm s2 /\
             p2a_cE Gt tt (p2ak_join soa sob sm) s1 s2 =
             p2a_cE Gt tt soa s1 sm + p2a_cE Gt tt sob sm s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `j = p2ak_join (soa:real^1->real^N) sob sm` THEN
  SUBGOAL_THEN `!v. (j:real^1->real^N) v = if drop v <= sm then soa v else sob v` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN REWRITE_TAC[p2ak_join]; ALL_TAC] THEN
  (* derivatives off sm *)
  SUBGOAL_THEN
   `!s. s1 < s /\ s < sm
        ==> ((j:real^1->real^N) has_vector_derivative vector_derivative soa (at (lift s)))
              (at (lift s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`soa:real^1->real^N`; `sm - s`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `soa:real^1->real^N`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. sm < s /\ s < s2
        ==> ((j:real^1->real^N) has_vector_derivative vector_derivative sob (at (lift s)))
              (at (lift s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`sob:real^1->real^N`; `s - sm`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `sob:real^1->real^N`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* bounds for the derivatives on the closed pieces *)
  SUBGOAL_THEN
   `?M. (!s. s1 <= s /\ s <= sm ==> norm(vector_derivative (soa:real^1->real^N) (at (lift s))) <= M) /\
        (!s. sm <= s /\ s <= s2 ==> norm(vector_derivative (sob:real^1->real^N) (at (lift s))) <= M)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\v. vector_derivative (soa:real^1->real^N) (at v)`;
                   `interval[lift s1,lift sm]`] COMPACT_CONTINUOUS_IMAGE) THEN
    MP_TAC(ISPECL [`\v. vector_derivative (sob:real^1->real^N) (at v)`;
                   `interval[lift sm,lift s2]`] COMPACT_CONTINUOUS_IMAGE) THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC(TAUT `(p1 /\ p2) /\ (q1 ==> q2 ==> r) ==> (p1 ==> q1) ==> (p2 ==> q2) ==> r`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED)) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `M1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `M2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `max M1 M2` THEN ASM_MESON_TAC[REAL_LE_MAX];
    ALL_TAC] THEN
  EXISTS_TAC `M:real` THEN
  SUBGOAL_THEN `(soa:real^1->real^N) continuous_on interval[lift s1,lift sm] /\
                (\v. vector_derivative soa (at v)) continuous_on interval[lift s1,lift sm] /\
                (sob:real^1->real^N) continuous_on interval[lift sm,lift s2] /\
                (\v. vector_derivative sob (at v)) continuous_on interval[lift sm,lift s2]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `sm < s2 ==> ~(s2 <= sm)`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sob:real^1->real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    SUBGOAL_THEN `(j:real^1->real^N) = (\v. if drop v <= sm then soa v else sob v)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `interval[lift s1,lift s2] =
                  interval[lift s1,lift sm] UNION interval[lift sm,lift s2]` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `v:real^1` THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `v = lift sm` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_SING] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < sm` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `soa:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[differentiable; has_vector_derivative]; ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sob:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[differentiable; has_vector_derivative]; ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[p2a_cL] THEN
    MATCH_MP_TAC P2AK_INT_JOIN_EQ THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `soa:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT)] THEN
      REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `sm < s ==> ~(s <= sm)`; LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sob:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT)] THEN
      REWRITE_TAC[]];
    REWRITE_TAC[p2a_cE] THEN
    MATCH_MP_TAC P2AK_INT_JOIN_EQ THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[DOT_SQUARE_NORM] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[DOT_SQUARE_NORM] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `soa:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT)] THEN
      REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `sob:real^1->real^N`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT)] THEN
      REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The BVP data of P2A_LOC_BVP_PW as a predicate (p2ak_bvpd), limits of     *)
(* almost nonpositive sequences, the BVP comparison for p2ak_sq curves      *)
(* (P2AK_BVPD_LE), and the chart-level uniqueness argument: a limit of      *)
(* almost minimizing curves lies on the BVP solution (P2AK_UNIQ_CHART).     *)
(* ------------------------------------------------------------------------- *)

let p2ak_bvpd = new_definition
 `p2ak_bvpd (U:real^N->bool) (Gt:real->real^N->real^N^N) (tt:real) (Kc:real^N->bool) (E:real)
            (sa:real) (sb:real) (delta:real) (rho:real)
            (sol:real->real->real^N->real^N->real^1->real^N) <=>
    &0 < delta /\ &0 < rho /\
    (!s1 s2 y1 y2.
        sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
        y1 IN Kc /\ norm(y2 - y1) <= rho
        ==> sol s1 s2 y1 y2 (lift s1) = y1 /\ sol s1 s2 y1 y2 (lift s2) = y2 /\
            (!s. s1 <= s /\ s <= s2 ==> sol s1 s2 y1 y2 (lift s) IN U) /\
            (!s. s1 <= s /\ s <= s2
                 ==> (sol s1 s2 y1 y2 has_vector_derivative
                      vector_derivative (sol s1 s2 y1 y2) (at (lift s))) (at (lift s)) /\
                     ((\v. vector_derivative (sol s1 s2 y1 y2) (at v))
                      has_vector_derivative
                      p2a_lacc Gt tt s (sol s1 s2 y1 y2 (lift s))
                               (vector_derivative (sol s1 s2 y1 y2) (at (lift s))))
                     (at (lift s))) /\
            !sig' K M.
                   sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                   (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                   FINITE K /\ sig' continuous_on interval[lift s1,lift s2] /\
                   (!s. s1 < s /\ s < s2 /\ ~(s IN K)
                        ==> sig' differentiable (at (lift s)) /\
                            norm(vector_derivative sig' (at (lift s))) <= M) /\
                   p2a_cE Gt tt sig' s1 s2 <= E
                   ==> p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 <= p2a_cL Gt tt sig' s1 s2 /\
                       (p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 = p2a_cL Gt tt sig' s1 s2
                        ==> !s. s1 <= s /\ s <= s2
                                ==> sig'(lift s) = sol s1 s2 y1 y2 (lift s))) /\
    (!s1 s2 y1 y2 s1n s2n y1n y2n.
        sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
        y1 IN Kc /\ norm(y2 - y1) <= rho /\
        (!n:num. sa <= s1n n /\ s1n n < s2n n /\ s2n n <= sb /\
                 s2n n - s1n n <= delta /\ y1n n IN Kc /\
                 norm(y2n n - y1n n) <= rho) /\
        ((\n. lift(s1n n)) --> lift s1) sequentially /\
        ((\n. lift(s2n n)) --> lift s2) sequentially /\
        (y1n --> y1) sequentially /\ (y2n --> y2) sequentially
        ==> ((\n. lift(p2a_cL Gt tt (sol (s1n n) (s2n n) (y1n n) (y2n n))
                             (s1n n) (s2n n)))
             --> lift(p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2)) sequentially)`;;

let P2AK_BVPD_EXISTS = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt Kc E sa sb.
       p2a_lsmooth U ta tb Gt /\ lricci_flow U ta tb Gt /\
       compact Kc /\ Kc SUBSET U /\ &0 <= sa /\ sa < sb /\
       ta < tt - sb pow 2 /\ tt - sa pow 2 < tb /\ &0 < E
       ==> ?delta rho sol. p2ak_bvpd U Gt tt Kc E sa sb delta rho sol`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2ak_bvpd] THEN
  MATCH_MP_TAC P2A_LOC_BVP_PW THEN MAP_EVERY EXISTS_TAC [`ta:real`; `tb:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2AK_LIM_LE_EPS = prove
 (`!(x:num->real) l.
     ((\n. lift(x n)) --> lift l) sequentially /\
     (!e. &0 < e ==> ?N. !n. N <= n ==> x n <= e)
     ==> l <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `l <= l / &2` MP_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN EXISTS_TAC `x:num->real` THEN
    ASM_REWRITE_TAC[TENDSTO_REAL; o_DEF; TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The BVP solution between two points of a p2ak_sq curve with bounded     *)
(* energy is no longer than the curve (P2AK_BVP_SQ with the bvpd data).     *)

let P2AK_BVPD_LE = prove
 (`!U (Gt:real->real^N->real^N^N) tt Kc E sa sb delta rho sol sa' sb' s1 s2
    (z:real^1->real^N) z' K B.
     p2ak_bvpd U Gt tt Kc E sa sb delta rho sol /\
     p2a_lsmooth U sa' sb' (\s. Gt(tt - s pow 2)) /\ sa' < sa /\ sb < sb' /\
     sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
     z(lift s1) IN Kc /\ norm(z(lift s2) - z(lift s1)) <= rho /\
     p2ak_sq U s1 s2 z z' K B /\
     real_integral (real_interval[s1,s2]) (\s. norm(z'(lift s)) pow 2) <= E /\
     (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) real_integrable_on real_interval[s1,s2]
     ==> p2a_cL Gt tt (sol s1 s2 (z(lift s1)) (z(lift s2))) s1 s2 <=
         real_integral (real_interval[s1,s2]) (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2AK_BVP_SQ THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa':real`; `sb':real`; `E:real`;
                        `K:real->bool`; `B:real->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`sig':real^1->real^N`; `K1:real->bool`; `M:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_bvpd] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bvpd")) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`s1:real`; `s2:real`; `(z:real^1->real^N)(lift s1)`;
                             `(z:real^1->real^N)(lift s2)`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`sig':real^1->real^N`; `K1:real->bool`; `M:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]);;

let P2AK_UNIQ_CHART = prove
 (`!U (Gt:real->real^N->real^N^N) tt Kc E sa sb delta rho sol sa' sb' lam Gm Rm Eh
    (Y:real^1->real^N) (Yn:num->real^1->real^N) p sm q.
     p2ak_bvpd U Gt tt Kc E sa sb delta rho sol /\
     p2a_lsmooth U sa' sb' (\s. Gt(tt - s pow 2)) /\ sa' < sa /\ sb < sb' /\ &0 <= sa /\
     convex U /\ Kc SUBSET U /\ &0 < lam /\ &0 <= Rm /\ &0 <= Gm /\
     (!s y u. sa <= s /\ s <= sb /\ y IN U
              ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) y ** u) /\
                  u dot (Gt(tt - s pow 2) y ** u) <= Gm * norm u pow 2 /\
                  abs(lscalar (Gt(tt - s pow 2)) y) <= Rm) /\
     sa <= p /\ p < sm /\ sm < q /\ q <= sb /\ q - p <= delta /\
     &0 <= Eh /\ Eh <= E /\
     &2 * (&2 / lam * (Gm / &2 * Eh + &4 * sb pow 2 * Rm * (sb - sa))) <= E /\
     Y(lift p) IN Kc /\ Y(lift sm) IN Kc /\ Y(lift q) IN Kc /\
     norm(Y(lift q) - Y(lift p)) <= rho /\ norm(Y(lift sm) - Y(lift p)) <= rho /\
     norm(Y(lift q) - Y(lift sm)) <= rho /\
     norm(Y(lift sm) - Y(lift p)) pow 2 <= Eh * (sm - p) /\
     norm(Y(lift q) - Y(lift sm)) pow 2 <= Eh * (q - sm) /\
     (!n. Yn n (lift p) IN Kc /\ Yn n (lift sm) IN Kc /\
          norm(Yn n (lift q) - Yn n (lift p)) <= rho /\
          norm(Yn n (lift sm) - Yn n (lift p)) <= rho /\
          norm(Yn n (lift q) - Yn n (lift sm)) <= rho) /\
     (!n. (?K B. p2ak_sq U p sm (Yn n) (\v. vector_derivative (Yn n) (at v)) K B) /\
          (?K B. p2ak_sq U sm q (Yn n) (\v. vector_derivative (Yn n) (at v)) K B) /\
          real_integral (real_interval[p,sm])
            (\s. norm(vector_derivative (Yn n) (at (lift s))) pow 2) <= E /\
          real_integral (real_interval[sm,q])
            (\s. norm(vector_derivative (Yn n) (at (lift s))) pow 2) <= E /\
          (\s. p2a_llag Gt tt s (Yn n (lift s)) (vector_derivative (Yn n) (at (lift s))))
            real_integrable_on real_interval[p,q]) /\
     ((\n. Yn n (lift p)) --> Y(lift p)) sequentially /\
     ((\n. Yn n (lift sm)) --> Y(lift sm)) sequentially /\
     ((\n. Yn n (lift q)) --> Y(lift q)) sequentially /\
     (!e. &0 < e
          ==> ?N. !n. N <= n
                      ==> real_integral (real_interval[p,q])
                            (\s. p2a_llag Gt tt s (Yn n (lift s))
                                          (vector_derivative (Yn n) (at (lift s))))
                          <= p2a_cL Gt tt (sol p q (Yn n (lift p)) (Yn n (lift q))) p q + e)
     ==> Y(lift sm) = sol p q (Y(lift p)) (Y(lift q)) (lift sm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bvpd]) THEN
  FIRST_X_ASSUM(LABEL_TAC "C" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
    can (find_term ((=) `s1n:num->real`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "B" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
  ABBREV_TAC `ya = (Y:real^1->real^N)(lift p)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `ym = (Y:real^1->real^N)(lift sm)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `yb = (Y:real^1->real^N)(lift q)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  (* the three limit BVP solutions *)
  USE_THEN "B" (MP_TAC o SPECL [`p:real`; `q:real`; `ya:real^N`; `yb:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "B" (MP_TAC o SPECL [`p:real`; `sm:real`; `ya:real^N`; `ym:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "B" (MP_TAC o SPECL [`sm:real`; `q:real`; `ym:real^N`; `yb:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* the broken BVP curves of the sequence are no longer than the curves *)
  SUBGOAL_THEN
   `!n. p2a_cL (Gt:real->real^N->real^N^N) tt
          ((sol:real->real->real^N->real^N->real^1->real^N) p sm
             ((Yn:num->real^1->real^N) n (lift p)) (Yn n (lift sm))) p sm +
        p2a_cL Gt tt (sol sm q (Yn n (lift sm)) (Yn n (lift q))) sm q
        <= real_integral (real_interval[p,q])
             (\s. p2a_llag Gt tt s (Yn n (lift s)) (vector_derivative (Yn n) (at (lift s))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_sq")) (concl th))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `K1:real->bool` (X_CHOOSE_TAC `B1:real->bool`))
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `K2:real->bool` (X_CHOOSE_TAC `B2:real->bool`))
        STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kc:real^N->bool`)) (concl th) &&
      can (find_term ((=) `Yn:num->real^1->real^N`)) (concl th))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `real_integral (real_interval[p,q])
        (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((Yn:num->real^1->real^N) n (lift s))
                      (vector_derivative (Yn n) (at (lift s)))) =
      real_integral (real_interval[p,sm])
        (\s. p2a_llag Gt tt s (Yn n (lift s)) (vector_derivative (Yn n) (at (lift s)))) +
      real_integral (real_interval[sm,q])
        (\s. p2a_llag Gt tt s (Yn n (lift s)) (vector_derivative (Yn n) (at (lift s))))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `E:real`; `p:real`; `sm:real`;
                     `(sol:real->real->real^N->real^N->real^1->real^N) p sm
                        ((Yn:num->real^1->real^N) n (lift p)) (Yn n (lift sm))`;
                     `(Yn:num->real^1->real^N) n`;
                     `\v. vector_derivative ((Yn:num->real^1->real^N) n) (at v)`;
                     `K1:real->bool`; `B1:real->bool`] P2AK_BVP_SQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        USE_THEN "B" (MP_TAC o SPECL [`p:real`; `sm:real`; `(Yn:num->real^1->real^N) n (lift p)`;
                                      `(Yn:num->real^1->real^N) n (lift sm)`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
        DISCH_THEN(MP_TAC o SPECL [`sig':real^1->real^N`; `K:real->bool`; `M:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `E:real`; `sm:real`; `q:real`;
                     `(sol:real->real->real^N->real^N->real^1->real^N) sm q
                        ((Yn:num->real^1->real^N) n (lift sm)) (Yn n (lift q))`;
                     `(Yn:num->real^1->real^N) n`;
                     `\v. vector_derivative ((Yn:num->real^1->real^N) n) (at v)`;
                     `K2:real->bool`; `B2:real->bool`] P2AK_BVP_SQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN
        USE_THEN "B" (MP_TAC o SPECL [`sm:real`; `q:real`; `(Yn:num->real^1->real^N) n (lift sm)`;
                                      `(Yn:num->real^1->real^N) n (lift q)`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
        DISCH_THEN(MP_TAC o SPECL [`sig':real^1->real^N`; `K:real->bool`; `M:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* in the limit the broken BVP curve is no longer than the BVP solution *)
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt ((sol:real->real->real^N->real^N->real^1->real^N) p sm ya ym) p sm +
    p2a_cL Gt tt ((sol:real->real->real^N->real^N->real^1->real^N) sm q ym yb) sm q - p2a_cL Gt tt ((sol:real->real->real^N->real^N->real^1->real^N) p q ya yb) p q <= &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_LIM_LE_EPS THEN
    EXISTS_TAC
     `\n. p2a_cL (Gt:real->real^N->real^N^N) tt
            ((sol:real->real->real^N->real^N->real^1->real^N) p sm ((Yn:num->real^1->real^N) n (lift p)) (Yn n (lift sm))) p sm +
          p2a_cL Gt tt ((sol:real->real->real^N->real^N->real^1->real^N) sm q (Yn n (lift sm)) (Yn n (lift q))) sm q -
          p2a_cL Gt tt ((sol:real->real->real^N->real^N->real^1->real^N) p q (Yn n (lift p)) (Yn n (lift q))) p q` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LIM_SUB THEN CONJ_TAC] THENL
       [USE_THEN "C" (MP_TAC o SPECL [`p:real`; `sm:real`; `ya:real^N`; `ym:real^N`;
                                     `\n:num. (p:real)`; `\n:num. (sm:real)`;
                                     `\n. (Yn:num->real^1->real^N) n (lift p)`;
                                     `\n. (Yn:num->real^1->real^N) n (lift sm)`]);
        USE_THEN "C" (MP_TAC o SPECL [`sm:real`; `q:real`; `ym:real^N`; `yb:real^N`;
                                     `\n:num. (sm:real)`; `\n:num. (q:real)`;
                                     `\n. (Yn:num->real^1->real^N) n (lift sm)`;
                                     `\n. (Yn:num->real^1->real^N) n (lift q)`]);
        USE_THEN "C" (MP_TAC o SPECL [`p:real`; `q:real`; `ya:real^N`; `yb:real^N`;
                                     `\n:num. (p:real)`; `\n:num. (q:real)`;
                                     `\n. (Yn:num->real^1->real^N) n (lift p)`;
                                     `\n. (Yn:num->real^1->real^N) n (lift q)`])] THEN
      REWRITE_TAC[LIM_CONST; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_integral")) (concl th) &&
      not(can (find_term ((=) `lam:real`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_cL")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N:num`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_integral")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_cL")) (concl th) &&
      not(can (find_term ((=) `e:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the broken curve through ym *)
  SUBGOAL_THEN
   `!s1 s2 y1 y2. sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                  y1 IN Kc /\ norm(y2 - y1) <= rho
                  ==> !s. s1 <= s /\ s <= s2
                          ==> (sol:real->real->real^N->real^N->real^1->real^N) s1 s2 y1 y2 (lift s) IN U /\
                              (sol:real->real->real^N->real^N->real^1->real^N) s1 s2 y1 y2 differentiable (at (lift s)) /\
                              (\v. vector_derivative ((sol:real->real->real^N->real^N->real^1->real^N) s1 s2 y1 y2) (at v))
                                continuous (at (lift s))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "B" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[differentiable; has_vector_derivative; DIFFERENTIABLE_IMP_CONTINUOUS_AT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `(sol:real->real->real^N->real^N->real^1->real^N) p sm ya ym`; `(sol:real->real->real^N->real^N->real^1->real^N) sm q ym yb`; `p:real`; `sm:real`; `q:real`] P2AK_JOIN_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`p:real`; `sm:real`; `ya:real^N`; `ym:real^N`] o check
        (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "differentiable")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPECL [`sm:real`; `q:real`; `ym:real^N`; `yb:real^N`] o check
        (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
          fst(dest_const t) = "differentiable")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  (* energies of the two BVP pieces *)
  SUBGOAL_THEN
   `p2a_cE (Gt:real->real^N->real^N^N) tt ((sol:real->real->real^N->real^N->real^1->real^N) p sm ya ym) p sm
    <= &2 / lam * (Gm / &2 * Eh + &4 * sb pow 2 * Rm * (sb - sa)) /\
    p2a_cE Gt tt ((sol:real->real->real^N->real^N->real^1->real^N) sm q ym yb) sm q
    <= &2 / lam * (Gm / &2 * Eh + &4 * sb pow 2 * Rm * (sb - sa))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 / lam * (Gm / &2 * norm((ym:real^N) - ya) pow 2 / (sm - p) +
                             &4 * sm pow 2 * Rm * (sm - p))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2AK_SOL_ENERGY THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa':real`; `sb':real`; `E:real`] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]; ASM SET_TAC[];
          REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MP_TAC o SPECL [`p:real`; `sm:real`; `ya:real^N`; `ym:real^N`] o check
            (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
              fst(dest_const t) = "differentiable")) (concl th))) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          MAP_EVERY X_GEN_TAC [`sig':real^1->real^N`; `K1:real->bool`; `M1:real`] THEN
          DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`sig':real^1->real^N`; `K1:real->bool`; `M1:real`] o check
            (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sig':real^1->real^N`)) (concl th) &&
          can (find_term ((=) `ya:real^N`)) (concl th) &&
          can (find_term ((=) `ym:real^N`)) (concl th) &&
          not(can (find_term ((=) `yb:real^N`)) (concl th)))) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
          SUBGOAL_THEN `&0 < sm - p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `Eh * (sm - p)` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `&0 < sm - p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
          MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 / lam * (Gm / &2 * norm((yb:real^N) - ym) pow 2 / (q - sm) +
                             &4 * q pow 2 * Rm * (q - sm))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2AK_SOL_ENERGY THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa':real`; `sb':real`; `E:real`] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
          ASM SET_TAC[]; ASM SET_TAC[];
          REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MP_TAC o SPECL [`sm:real`; `q:real`; `ym:real^N`; `yb:real^N`] o check
            (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
              fst(dest_const t) = "differentiable")) (concl th))) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          MAP_EVERY X_GEN_TAC [`sig':real^1->real^N`; `K1:real->bool`; `M1:real`] THEN
          DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`sig':real^1->real^N`; `K1:real->bool`; `M1:real`] o check
            (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sig':real^1->real^N`)) (concl th) &&
          can (find_term ((=) `ym:real^N`)) (concl th) &&
          can (find_term ((=) `yb:real^N`)) (concl th) &&
          not(can (find_term ((=) `ya:real^N`)) (concl th)))) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
          SUBGOAL_THEN `&0 < q - sm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `Eh * (q - sm)` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `&0 < q - sm` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
          MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
          REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]]];
    ALL_TAC] THEN
  (* the BVP solution from ya to yb is not longer than the broken curve, so equal *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`p2ak_join ((sol:real->real->real^N->real^N->real^1->real^N) p sm ya ym) ((sol:real->real->real^N->real^N->real^1->real^N) sm q ym yb) sm`;
                                `{sm:real}`; `M:real`] o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `sig':real^1->real^N`)) (concl th) &&
          can (find_term ((=) `ya:real^N`)) (concl th) &&
          can (find_term ((=) `yb:real^N`)) (concl th) &&
          not(can (find_term ((=) `ym:real^N`)) (concl th)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_SING] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sm:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2ak_join; LIFT_DROP; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Box-level pieces.  The chart piece of an admissible curve in a box chart  *)
(* is a p2ak_sq curve with bounded energy (P2AK_BXD_PIECE); convergence in   *)
(* the slice topology gives chart convergence; replacing a piece by a C^1    *)
(* chart curve (P2AK_REPLACE_PIECE); BVP data for the box charts             *)
(* (P2AK_BOX_BVP).                                                           *)
(* ------------------------------------------------------------------------- *)

let P2AK_BXD_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b (gamma:real->A) Lb k s1 s2.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
     p2a_admx V tt x b gamma /\ b <= T1 /\
     (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN C) /\
     p2a_L_length V tt gamma b <= Lb /\
     k IN Fs /\ &0 < s1 /\ s1 < s2 /\ s2 pow 2 <= b /\
     (!s. s1 <= s /\ s <= s2
          ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
              SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)) IN
              cball(SND(chart_at (p2a_vatlas V tt) k) k,&6 * R k))
     ==> ?K. p2ak_sq (IMAGE (SND(chart_at (p2a_vatlas V tt) k)) (FST(chart_at (p2a_vatlas V tt) k) INTER W)) s1 s2
                     (\v. SND(chart_at (p2a_vatlas V tt) k) (gamma(drop v pow 2)))
                     (\v. vector_derivative (\v. SND(chart_at (p2a_vatlas V tt) k) (gamma(drop v pow 2))) (at v))
                     K (K INTER real_interval[s1,s2]) /\
             (\s. p2a_llag (p2a_rlocal V W tt (FST(chart_at (p2a_vatlas V tt) k) INTER W,SND(chart_at (p2a_vatlas V tt) k))) tt s
                    (SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)))
                    (vector_derivative (\v. SND(chart_at (p2a_vatlas V tt) k) (gamma(drop v pow 2))) (at (lift s))))
             real_integrable_on real_interval[s1,s2] /\
             real_integral (real_interval[s1,s2])
               (\s. p2a_llag (p2a_rlocal V W tt (FST(chart_at (p2a_vatlas V tt) k) INTER W,SND(chart_at (p2a_vatlas V tt) k))) tt s
                      (SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)))
                      (vector_derivative (\v. SND(chart_at (p2a_vatlas V tt) k) (gamma(drop v pow 2))) (at (lift s)))) =
             real_integral (real_interval[s1 pow 2,s2 pow 2]) (p2a_L_integrand V tt gamma b) /\
             real_integral (real_interval[s1,s2])
               (\s. norm(vector_derivative (\v. SND(chart_at (p2a_vatlas V tt) k) (gamma(drop v pow 2))) (at (lift s))) pow 2)
             <= &2 / lam * (Lb + &4 * b * sqrt b * Rm)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt /\
                cball((phi:A->real^N) k,&6 * (R:A->real) k) SUBSET IMAGE phi (U INTER W) /\
                !t z u. tt - T1 <= t /\ t <= tt /\ z IN cball(phi k,&6 * R k)
                        ==> lam * norm u pow 2 <=
                            u dot (p2a_rlocal V W tt (U INTER W,phi) t z ** u) /\
                            u dot (p2a_rlocal V W tt (U INTER W,phi) t z ** u)
                            <= Gm * norm u pow 2 /\
                            abs(lscalar (p2a_rlocal V W tt (U INTER W,phi) t) z) <= Rm`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b /\ s2 <= sqrt b /\ sqrt b < sqrt(tt - a')` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `s2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LT THEN
      MP_TAC(SPEC `s2:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `s2:real`; `&0`; `sqrt(tt - a')`;
                 `cball((phi:A->real^N) k,&6 * (R:A->real) k)`; `lam:real`; `Rm:real`]
                P2AK_PIECE_SQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(tt - a') pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(tt - a') pow 2 = tt - a'` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `u:real^N`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`tt - s pow 2`; `y:real^N`; `u:real^N`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s pow 2 <= s2 pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:real->bool` THEN ASM_REWRITE_TAC[] THEN
  (* the L-length of the piece *)
  SUBGOAL_THEN `real_integral (real_interval[s1 pow 2,s2 pow 2])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) tt (gamma:real->A) b)
                <= Lb + &2 * (sqrt b * Rm) * (b - &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_INT_PIECE_UPPER THEN
    UNDISCH_TAC `p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_admx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM p2a_L_length] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC P2AK_BXD_LINT_LOWER THEN
        MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `tt:real`; `C:A->bool`; `T1:real`;
                              `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s2 pow 2 * Rm * (s2 - s1) <= b * Rm * sqrt b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1,s2])
      (\s. norm(vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                  (at (lift s))) pow 2)
    <= &2 / lam * (Lb + &4 * b * sqrt b * Rm)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / lam * (real_integral (real_interval[s1 pow 2,s2 pow 2])
                             (p2a_L_integrand (V:(real->A topology)#
                                (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                                tt (gamma:real->A) b) +
                           &2 * s2 pow 2 * Rm * (s2 - s1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let P2AK_SQ_MONO = prove
 (`!U U' a b (z:real^1->real^N) z' K B.
     p2ak_sq U a b z z' K B /\ (!s. a <= s /\ s <= b ==> z(lift s) IN U')
     ==> p2ak_sq U' a b z z' K B`,
  REWRITE_TAC[p2ak_sq] THEN MESON_TAC[]);;

let P2AK_CHART_CONV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b' U (phi:A->real^N) t (y:A) (z:num->A).
     p2a_region V W a' b' /\ (U,phi) IN p2a_vatlas V b' /\ a' < t /\ t <= b' /\
     y IN U INTER W /\
     (!O. open_in (p2a_vtop V t) O /\ y IN O ==> ?N. !n. N <= n ==> z n IN O)
     ==> !e. &0 < e
             ==> ?N. !n. N <= n ==> z n IN U INTER W /\ dist(phi(z n),phi y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b':real`; `U:A->bool`;
                 `phi:A->real^N`; `t:real`; `y:A`; `e:real`] P2A_CHART_PREIMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `O:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `O:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

(* Integrals over [a,c] of functions agreeing on (a,c) are equal.          *)

let P2AK_RINT_OPEN_EQ = prove
 (`!f g a c. (!t. a < t /\ t < c ==> f t = g t)
             ==> real_integral (real_interval[a,c]) f = real_integral (real_interval[a,c]) g`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  SIMP_TAC[]);;

let P2AK_REPLACE_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (x:A) b (gamma:real->A) W a' U (phi:A->real^N) (sol:real^1->real^N) p q.
     p2a_svs V /\ p2a_adm V tt x b gamma /\ p2a_region V W a' tt /\
     (U,phi) IN p2a_vatlas V tt /\
     &0 < p /\ p < q /\ q pow 2 <= b /\ b < tt - a' /\
     gamma(p pow 2) IN U INTER W /\ gamma(q pow 2) IN U INTER W /\
     sol(lift p) = phi(gamma(p pow 2)) /\ sol(lift q) = phi(gamma(q pow 2)) /\
     (!s. p <= s /\ s <= q
          ==> sol(lift s) IN IMAGE phi (U INTER W) /\ sol differentiable (at (lift s)) /\
              (\v. vector_derivative sol (at v)) continuous (at (lift s)))
     ==> ?c. p2a_adm V tt x b c /\ c b = gamma b /\
             p2a_L_length V tt c b =
             p2a_L_length V tt gamma b -
             real_integral (real_interval[p pow 2,q pow 2]) (p2a_L_integrand V tt gamma b) +
             p2a_cL (p2a_rlocal V W tt (U INTER W,phi)) tt sol p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q /\ q < sqrt(tt - a') /\ &0 < p pow 2 /\ p pow 2 < q pow 2 /\ &0 < b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `&0 < p pow 2 /\ p pow 2 < q pow 2` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
                        MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
                        ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `tt:real`;
                 `U:A->bool`; `phi:A->real^N`; `sol:real^1->real^N`; `p:real`; `q:real`;
                 `p / &2`; `sqrt(tt - a')`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `s pow 2 < sqrt(tt - a') pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `sqrt(tt - a') pow 2 = tt - a'` SUBST1_TAC THENL
         [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  ABBREV_TAC `sig = \tau. chart_inv (U INTER W,phi:A->real^N) ((sol:real^1->real^N)(lift(sqrt tau)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(sig:real->A) (p pow 2) = (gamma:real->A)(p pow 2) /\ sig (q pow 2) = gamma(q pow 2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; LIFT_DROP] THEN
    CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `tt:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN DISCH_TAC THEN
  ASM_CASES_TAC `q pow 2 < b` THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `sig:real->A`;
                   `b:real`; `p pow 2`; `q pow 2`] P2A_REPLACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `\tau. if tau <= p pow 2 then (gamma:real->A) tau
                      else if tau <= q pow 2 then (sig:real->A) tau else gamma tau` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `q2 < b ==> ~(b <= q2)`; COND_ID] THEN
    SUBGOAL_THEN `real_integral (real_interval[p pow 2,q pow 2]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (sig:real->A) b) =
                  real_integral (real_interval[p pow 2,q pow 2]) (p2a_L_integrand V tt sig (q pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P2AK_RINT_OPEN_EQ THEN
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`p pow 2`; `q pow 2`] THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 = b` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `sig:real->A`; `gamma:real->A`;
                 `\tau. if tau <= p pow 2 then (gamma:real->A) tau else sig tau`;
                 `b:real`; `p pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      CONJ_TAC THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      (SUBGOAL_THEN `tau = p pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]])];
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\tau. if tau <= p pow 2 then (gamma:real->A) tau else sig tau` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `p2 < b ==> ~(b <= p2)`] THEN
  SUBGOAL_THEN `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) (p pow 2) =
                real_integral (real_interval[&0,p pow 2]) (p2a_L_integrand V tt gamma b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2a_L_length] THEN
    MATCH_MP_TAC P2AK_RINT_OPEN_EQ THEN
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `p pow 2`] THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[&0,p pow 2]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b) +
                real_integral (real_interval[p pow 2,b]) (p2a_L_integrand V tt gamma b) =
                p2a_L_length V tt gamma b` MP_TAC THENL
   [REWRITE_TAC[p2a_L_length] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
    UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A)` THEN REWRITE_TAC[p2a_adm] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2AK_BOX_BVP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt k eps S0 E.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ k IN Fs /\
     &0 < eps /\ eps < S0 /\ S0 pow 2 <= T1 /\ &0 < E
     ==> ?delta rho sol.
           p2ak_bvpd (ball(SND(chart_at (p2a_vatlas V tt) k) k,&6 * R k))
                     (p2a_rlocal V W tt (FST(chart_at (p2a_vatlas V tt) k) INTER W,
                                         SND(chart_at (p2a_vatlas V tt) k)))
                     tt (cball(SND(chart_at (p2a_vatlas V tt) k) k,&3 * R k)) E eps S0
                     delta rho sol`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`;
                 `phi:A->real^N`] P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball((phi:A->real^N) k,&6 * (R:A->real) k) SUBSET IMAGE phi (U INTER W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AK_BVPD_EXISTS THEN MAP_EVERY EXISTS_TAC [`a':real`; `tt:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2AK_LSMOOTH_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC P2AK_LRICCI_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[COMPACT_CBALL];
    REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `eps:real` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `&0 < eps pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The limit datum p2ak_lim (a minimizing sequence in one box with a        *)
(* pointwise limit in the slice topologies), the chart of a short piece     *)
(* (P2AK_SB_PIECE_LIMIT), almost minimality on pieces, and the good pieces: *)
(* the limit curve is the BVP solution between its end points and its chart *)
(* length is at most the liminf (P2AK_SB_GOOD_PIECE).                       *)
(* ------------------------------------------------------------------------- *)

let p2ak_lim = new_definition
 `p2ak_lim (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
           (W:A->bool) (a':real) (C:A->bool) (T1:real) (Fs:A->bool) (R:A->real) (r:real)
           (lam:real) (Gm:real) (Rm:real) (tt:real) (x:A) (b:real) (gs:num->real->A)
           (Lb:real) (q:A) (sub:num->num) (gamma:real->A) (Lam:real) <=>
    p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ p2a_atlas_lc V /\
    &0 < b /\ b <= T1 /\ &0 <= Lb /\
    (!n. p2a_adm V tt x b (gs n) /\ p2a_L_length V tt (gs n) b <= Lb /\
         (!tau. &0 <= tau /\ tau <= b ==> gs n tau IN C) /\ gs n b = q) /\
    p3_subseq sub /\
    (!tau. &0 <= tau /\ tau <= b
           ==> gamma tau IN C /\
               !O. open_in (p2a_vtop V (tt - tau)) O /\ gamma tau IN O
                   ==> ?N. !n. N <= n ==> gs (sub n) tau IN O) /\
    (!n. Lam <= p2a_L_length V tt (gs (sub n)) b) /\
    (!eta. &0 < eta ==> ?N. !n. N <= n ==> p2a_L_length V tt (gs (sub n)) b <= Lam + eta) /\
    (!gamma'. p2a_adm V tt x b gamma' /\ gamma' b = q ==> Lam <= p2a_L_length V tt gamma' b)`;;

let P2AK_SB_PIECE_LIMIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam p p'.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam /\
     &0 <= p /\ p < p' /\ p' pow 2 <= b /\
     (p' - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm)) <= r pow 2
     ==> ?k N0.
           k IN Fs /\
           (!n s. N0 <= n /\ p <= s /\ s <= p'
                  ==> gs (sub n) (s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
                      dist(SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2)),
                           SND(chart_at (p2a_vatlas V tt) k) k) <= &2 * R k) /\
           (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
                     ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s' pow 2)),
                              SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2))) pow 2
                         <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm))) /\
           (!s. p <= s /\ s <= p'
                ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
                    dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)),
                         SND(chart_at (p2a_vatlas V tt) k) k) <= &2 * R k /\
                    ((\n. SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2))) -->
                     SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2))) sequentially) /\
           (!s s'. p <= s /\ s <= s' /\ s' <= p'
                   ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s' pow 2)),
                            SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2))) pow 2
                       <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ak_lim] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. p <= s /\ s <= p' ==> &0 <= s pow 2 /\ s pow 2 <= b /\
                                         tt - T1 <= tt - s pow 2 /\ a' < tt - s pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `s pow 2 <= p' pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the chart at gamma(p^2) *)
  FIRST_ASSUM(MP_TAC o SPEC `p pow 2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `gamma:real->A`)) (concl th) &&
    can (find_term ((=) `C:A->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIMp")) THEN
  FIRST_ASSUM(MP_TAC o SPEC `(gamma:real->A)(p pow 2)` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `R:A->real`)) (concl th) &&
    can (find_term ((=) `C:A->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `k:A` THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* eventually the curves start in the radius R k ball of the chart *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                 `tt - p pow 2`; `(gamma:real->A)(p pow 2)`;
                 `\n. (gs:num->real->A) ((sub:num->num) n) (p pow 2)`] P2AK_CHART_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `T1:real`)) (concl th) && can (find_term ((=) `p':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(R:A->real) k - dist((phi:A->real^N)((gamma:real->A)(p pow 2)),phi k)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:num` (LABEL_TAC "N0" o BETA_RULE)) THEN EXISTS_TAC `N0:num` THEN
  SUBGOAL_THEN
   `!n. N0 <= n ==> (gs:num->real->A) ((sub:num->num) n) (p pow 2) IN U INTER W /\
                    dist((phi:A->real^N)(gs (sub n) (p pow 2)),phi k) < (R:A->real) k`
  (LABEL_TAC "START") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N0" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`;
                   `(phi:A->real^N)((gamma:real->A)(p pow 2))`; `(phi:A->real^N) k`]
                  DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. p2a_admx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b ((gs:num->real->A) ((sub:num->num) n)) /\
        p2a_L_length V tt (gs (sub n)) b <= Lb /\
        (!tau. &0 <= tau /\ tau <= b ==> gs (sub n) tau IN C)`
  (LABEL_TAC "GS") THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
      can (find_term ((=) `q:A`)) (concl th))) THEN
    SIMP_TAC[P2AX_ADM_IMP];
    ALL_TAC] THEN
  (* stay in the chart *)
  SUBGOAL_THEN
   `!n s. N0 <= n /\ p <= s /\ s <= p'
          ==> (gs:num->real->A) ((sub:num->num) n) (s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(gs (sub n) (s pow 2)),phi(gs (sub n) (p pow 2))) <= r`
  (LABEL_TAC "STAY") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "GS" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "START" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                   `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`;
                   `b:real`; `(gs:num->real->A) ((sub:num->num) n)`; `Lb:real`; `k:A`;
                   `p:real`; `p':real`] P2AK_BXD_STAY) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s. N0 <= n /\ p <= s /\ s <= p'
          ==> (gs:num->real->A) ((sub:num->num) n) (s pow 2) IN U INTER W /\
              dist((phi:A->real^N)(gs (sub n) (s pow 2)),phi k) <= &2 * (R:A->real) k`
  (LABEL_TAC "IN2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "STAY" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "START" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s pow 2))`;
                   `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`;
                   `(phi:A->real^N) k`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the displacement bound for the curves *)
  SUBGOAL_THEN
   `!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
             ==> dist((phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s' pow 2)),
                      phi(gs (sub n) (s pow 2))) pow 2 <= (s' - s) * E`
  (LABEL_TAC "FE") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "GS" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                   `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`;
                   `b:real`; `(gs:num->real->A) ((sub:num->num) n)`; `Lb:real`; `k:A`;
                   `s:real`; `s':real`] P2AK_BXD_FE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `s':real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `T1:real`)) (concl th) && can (find_term ((=) `p':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      USE_THEN "IN2" (MP_TAC o SPECL [`n:num`; `u:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`;
                     `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (u pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the limit curve on [p,p'] *)
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p'
        ==> (gamma:real->A)(s pow 2) IN U INTER W /\
            dist((phi:A->real^N)(gamma(s pow 2)),phi k) <= &2 * (R:A->real) k /\
            ((\n. phi((gs:num->real->A) ((sub:num->num) n) (s pow 2))) --> phi(gamma(s pow 2)))
            sequentially`
  (LABEL_TAC "LIM") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `T1:real`)) (concl th) && can (find_term ((=) `p':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s pow 2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term ((=) `C:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIMs"))] THEN
    (* membership in the closed chart ball *)
    SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN {y | y IN U INTER W /\
                    (phi:A->real^N) y IN cball(phi k,&2 * (R:A->real) k)}` MP_TAC THENL
     [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                     `(phi:A->real^N) k`; `&2 * (R:A->real) k`; `tt - s pow 2`]
                    P2AK_CHART_CBALL_CLOSED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[closed_in] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      USE_THEN "LIMs" (MP_TAC o SPEC
        `topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)) DIFF
         {y | y IN U INTER W /\ (phi:A->real^N) y IN cball(phi k,&2 * (R:A->real) k)}`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `tt - s pow 2`]
                      P2A_REGION_SLICE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
          concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2)) W`)) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `N + N0:num`) THEN
      REWRITE_TAC[ARITH_RULE `N <= N + N0:num`; IN_DIFF; IN_ELIM_THM; IN_CBALL] THEN
      USE_THEN "IN2" (MP_TAC o SPECL [`N + N0:num`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `N0 <= N + N0:num`]; ALL_TAC] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`;
                     `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) (N + N0)) (s pow 2))`]
                    DIST_SYM) THEN
      MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_CBALL] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                   `tt - s pow 2`; `(gamma:real->A)(s pow 2)`;
                   `\n. (gs:num->real->A) ((sub:num->num) n) (s pow 2)`] P2AK_CHART_CONV) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the displacement bound for the limit *)
  MAP_EVERY X_GEN_TAC [`s:real`; `s':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (s' - s) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dist((phi:A->real^N)((gamma:real->A)(s' pow 2)),phi(gamma(s pow 2))) <=
                sqrt((s' - s) * E)` MP_TAC THENL
   [REWRITE_TAC[dist] THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (s' pow 2)) -
                    phi(gs (sub n) (s pow 2))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
       [USE_THEN "LIM" (MP_TAC o SPEC `s':real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        USE_THEN "LIM" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      EXISTS_TAC `N0:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM dist] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN USE_THEN "FE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((s' - s) * E) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[DIST_POS_LE];
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]);;

let P2AK_SB_ALMOST_MIN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam U (phi:A->real^N)
    (soln:num->real^1->real^N) p p' N0.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam /\
     (U,phi) IN p2a_vatlas V tt /\ &0 < p /\ p < p' /\ p' pow 2 <= b /\
     (!n. N0 <= n
          ==> gs (sub n) (p pow 2) IN U INTER W /\ gs (sub n) (p' pow 2) IN U INTER W /\
              soln n (lift p) = phi(gs (sub n) (p pow 2)) /\
              soln n (lift p') = phi(gs (sub n) (p' pow 2)) /\
              (!s. p <= s /\ s <= p'
                   ==> soln n (lift s) IN IMAGE phi (U INTER W) /\
                       soln n differentiable (at (lift s)) /\
                       (\v. vector_derivative (soln n) (at v)) continuous (at (lift s))))
     ==> !e. &0 < e
             ==> ?N. !n. N <= n
                         ==> real_integral (real_interval[p pow 2,p' pow 2])
                               (p2a_L_integrand V tt (gs (sub n)) b)
                             <= p2a_cL (p2a_rlocal V W tt (U INTER W,phi)) tt (soln n) p p' + e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ak_lim] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lam:real`)) (concl th) &&
    can (find_term ((=) `sub:num->num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N0 + N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `soln:num->real^1->real^N`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
    can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`;
                 `(gs:num->real->A) ((sub:num->num) n)`; `W:A->bool`; `a':real`; `U:A->bool`;
                 `phi:A->real^N`; `(soln:num->real^1->real^N) n`; `p:real`; `p':real`]
                P2AK_REPLACE_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real->A` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lam:real`)) (concl th) &&
    can (find_term ((=) `q:A`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Real arithmetic after removing num side conditions m <= n + m.          *)

let P2AK_ARITH_TAC = ASM_REWRITE_TAC[ARITH_RULE `!m n:num. m <= n + m`] THEN ASM_REAL_ARITH_TAC;;

let P2AK_SB_GOOD_PIECE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam eps p p' k N0 Eb delta rho
    (sol:real->real->real^N->real^N->real^1->real^N).
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam /\
     &0 < eps /\ eps <= p /\ p < p' /\ p' pow 2 <= b /\ k IN Fs /\
     (!n s. N0 <= n /\ p <= s /\ s <= p'
            ==> gs (sub n) (s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
                dist(SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2)),SND(chart_at (p2a_vatlas V tt) k) k) <= &2 * R k) /\
     (!n s s'. N0 <= n /\ p <= s /\ s <= s' /\ s' <= p'
               ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s' pow 2)),SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2))) pow 2
                   <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm))) /\
     (!s. p <= s /\ s <= p'
          ==> gamma(s pow 2) IN FST(chart_at (p2a_vatlas V tt) k) INTER W /\
              dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2)),SND(chart_at (p2a_vatlas V tt) k) k) <= &2 * R k /\
              ((\n. SND(chart_at (p2a_vatlas V tt) k) (gs (sub n) (s pow 2))) --> SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2))) sequentially) /\
     (!s s'. p <= s /\ s <= s' /\ s' <= p'
             ==> dist(SND(chart_at (p2a_vatlas V tt) k) (gamma(s' pow 2)),SND(chart_at (p2a_vatlas V tt) k) (gamma(s pow 2))) pow 2 <= (s' - s) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm))) /\
     p2ak_bvpd (ball(SND(chart_at (p2a_vatlas V tt) k) k,&6 * R k)) (p2a_rlocal V W tt (FST(chart_at (p2a_vatlas V tt) k) INTER W,SND(chart_at (p2a_vatlas V tt) k))) tt (cball(SND(chart_at (p2a_vatlas V tt) k) k,&3 * R k)) Eb eps (sqrt b)
               delta rho sol /\
     p' - p <= delta /\ (p' - p) * (&2 / lam * (Lb + &4 * b * sqrt b * Rm)) <= (rho / &2) pow 2 /\
     (&2 / lam * (Lb + &4 * b * sqrt b * Rm)) <= Eb /\
     &2 * (&2 / lam * (Gm / &2 * (&2 / lam * (Lb + &4 * b * sqrt b * Rm)) + &4 * sqrt b pow 2 * Rm * (sqrt b - eps))) <= Eb
     ==> (!s. p <= s /\ s <= p'
              ==> sol p p' (SND(chart_at (p2a_vatlas V tt) k) (gamma(p pow 2))) (SND(chart_at (p2a_vatlas V tt) k) (gamma(p' pow 2))) (lift s) IN
                  IMAGE (SND(chart_at (p2a_vatlas V tt) k)) (FST(chart_at (p2a_vatlas V tt) k) INTER W) /\
                  sol p p' (SND(chart_at (p2a_vatlas V tt) k) (gamma(p pow 2))) (SND(chart_at (p2a_vatlas V tt) k) (gamma(p' pow 2))) differentiable (at (lift s)) /\
                  (\v. vector_derivative (sol p p' (SND(chart_at (p2a_vatlas V tt) k) (gamma(p pow 2))) (SND(chart_at (p2a_vatlas V tt) k) (gamma(p' pow 2)))) (at v))
                    continuous (at (lift s)) /\
                  gamma(s pow 2) =
                  chart_inv (FST(chart_at (p2a_vatlas V tt) k) INTER W,SND(chart_at (p2a_vatlas V tt) k)) (sol p p' (SND(chart_at (p2a_vatlas V tt) k) (gamma(p pow 2))) (SND(chart_at (p2a_vatlas V tt) k) (gamma(p' pow 2))) (lift s))) /\
         (!e. &0 < e
              ==> ?N. !n. N <= n
                          ==> p2a_cL (p2a_rlocal V W tt (FST(chart_at (p2a_vatlas V tt) k) INTER W,SND(chart_at (p2a_vatlas V tt) k))) tt (sol p p' (SND(chart_at (p2a_vatlas V tt) k) (gamma(p pow 2))) (SND(chart_at (p2a_vatlas V tt) k) (gamma(p' pow 2)))) p p'
                              <= real_integral (real_interval[p pow 2,p' pow 2])
                                   (p2a_L_integrand V tt (gs (sub n)) b) + e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b /\ p' <= sqrt b /\ &0 < p /\ &0 <= E /\
                sqrt b < sqrt(tt - a') /\ &0 < (R:A->real) k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bvpd]) THEN
  FIRST_X_ASSUM(LABEL_TAC "C" o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `s1n:num->real`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "B" o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th))) THEN
  ABBREV_TAC `ya = (phi:A->real^N)((gamma:real->A)(p pow 2))` THEN
  ABBREV_TAC `yb = (phi:A->real^N)((gamma:real->A)(p' pow 2))` THEN
  (* the limit end points and the main BVP solution *)
  SUBGOAL_THEN `ya IN cball((phi:A->real^N) k,&3 * (R:A->real) k) /\
                yb IN cball((phi:A->real^N) k,&3 * (R:A->real) k) /\
                norm((yb:real^N) - ya) <= rho /\ norm(yb - ya) pow 2 <= (p' - p) * E`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p':real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`p:real`; `p':real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      not(can (find_term ((=) `sub:num->num`)) (concl th)) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_CBALL] THEN EXPAND_TAC "ya" THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(p pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_CBALL] THEN EXPAND_TAC "yb" THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(p' pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "B" (MP_TAC o SPECL [`p:real`; `p':real`; `ya:real^N`; `yb:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* the s-form family on the ball and the bounds there *)
  SUBGOAL_THEN
   `p2a_lsmooth (ball((phi:A->real^N) k,&6 * (R:A->real) k)) (--sqrt(tt - a')) (sqrt(tt - a'))
      (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AK_LSMOOTH_SUBSET THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REGION_LSMOOTH THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(tt - a') pow 2` MP_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
        REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(tt - a') pow 2 = tt - a'` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^N) k,&6 * (R:A->real) k)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y u. eps <= s /\ s <= sqrt b /\ y IN ball((phi:A->real^N) k,&6 * (R:A->real) k)
            ==> lam * norm u pow 2 <=
                u dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi) (tt - s pow 2) y ** u) /\
                u dot (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi) (tt - s pow 2) y ** u)
                <= Gm * norm u pow 2 /\
                abs(lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi) (tt - s pow 2)) y) <= Rm`
  (LABEL_TAC "BD") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL] THEN
    SUBGOAL_THEN `s pow 2 <= sqrt b pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* per-curve facts on sub-pieces *)
  SUBGOAL_THEN
   `!n s1 s2. p <= s1 /\ s1 < s2 /\ s2 <= p'
              ==> (?K. p2ak_sq (ball((phi:A->real^N) k,&6 * (R:A->real) k)) s1 s2
                         (\v. phi((gs:num->real->A) ((sub:num->num) (n + N0)) (drop v pow 2)))
                         (\v. vector_derivative (\v. phi((gs:num->real->A) ((sub:num->num) (n + N0)) (drop v pow 2))) (at v))
                         K (K INTER real_interval[s1,s2])) /\
                  (\s. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi)) tt s (phi((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2)))
                         (vector_derivative (\v. phi((gs:num->real->A) ((sub:num->num) (n + N0)) (drop v pow 2))) (at (lift s))))
                  real_integrable_on real_interval[s1,s2] /\
                  real_integral (real_interval[s1,s2])
                    (\s. p2a_llag (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi)) tt s (phi((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2)))
                           (vector_derivative (\v. phi((gs:num->real->A) ((sub:num->num) (n + N0)) (drop v pow 2))) (at (lift s)))) =
                  real_integral (real_interval[s1 pow 2,s2 pow 2])
                    (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) (n + N0))) b) /\
                  real_integral (real_interval[s1,s2])
                    (\s. norm(vector_derivative (\v. phi((gs:num->real->A) ((sub:num->num) (n + N0)) (drop v pow 2))) (at (lift s))) pow 2)
                  <= E`
  (LABEL_TAC "PC") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                   `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`;
                   `b:real`; `(gs:num->real->A) ((sub:num->num) (n + N0))`; `Lb:real`; `k:A`; `s1:real`; `s2:real`] P2AK_BXD_PIECE) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) (n + N0)` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
      can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[P2AX_ADM_IMP] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p' pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `N0:num`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `K:real->bool` THEN
    MATCH_MP_TAC P2AK_SQ_MONO THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_BALL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* further per-curve facts *)
  SUBGOAL_THEN
   `!n s. p <= s /\ s <= p'
          ==> (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2)) IN cball(phi k,&3 * (R:A->real) k) /\
              (gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2) IN U INTER W`
  (LABEL_TAC "KC") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN
    MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2))`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s s'. p <= s /\ s <= s' /\ s' <= p'
             ==> norm((phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (s' pow 2)) - phi((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2))) <= rho`
  (LABEL_TAC "NR") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + N0:num`; `s:real`; `s':real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s' - s) * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. p <= s /\ s <= p'
        ==> ((\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (s pow 2))) --> phi((gamma:real->A)(s pow 2))) sequentially`
  (LABEL_TAC "CV") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
                         MP_TAC(SPEC `e:real` (CONJUNCT2(CONJUNCT2 th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!d. &0 <= d /\ d pow 2 <= (p' - p) * E ==> d <= rho` (LABEL_TAC "SQR") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* almost-minimality of the sequence on the piece *)
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n. N <= n
                    ==> real_integral (real_interval[p pow 2,p' pow 2])
                          (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) n)) b)
                        <= p2a_cL (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)) tt
                             ((sol:real->real->real^N->real^N->real^1->real^N) p p'
                                (phi((gs:num->real->A) ((sub:num->num) n) (p pow 2))) (phi((gs:num->real->A) ((sub:num->num) n) (p' pow 2)))) p p' + e`
  (LABEL_TAC "AM") THENL
   [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                   `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`;
                   `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                   `gamma:real->A`; `Lam:real`; `U:A->bool`; `phi:A->real^N`;
                   `\n. (sol:real->real->real^N->real^N->real^1->real^N) p p'
                          ((phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))) (phi((gs:num->real->A) ((sub:num->num) n) (p' pow 2)))`;
                   `p:real`; `p':real`; `N0:num`] P2AK_SB_ALMOST_MIN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p':real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`; `p':real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; REWRITE_TAC[dist] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `norm((phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p' pow 2)) - phi((gs:num->real->A) ((sub:num->num) n) (p pow 2))) <= rho`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(rho / &2) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "B" (MP_TAC o SPECL [`p:real`; `p':real`; `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`;
                                  `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p' pow 2))`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      can (find_term ((=) `(gs:num->real->A) ((sub:num->num) n)`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(gs:num->real->A) ((sub:num->num) n)`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                  MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE)];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lacc")) (concl th) &&
      can (find_term ((=) `ya:real^N`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ya:real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ball")) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; DISCH_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
      ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT o
                  MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A)(s pow 2)) = (sol:real->real->real^N->real^N->real^1->real^N) p p' ya yb (lift s)`
    (SUBST1_TAC o SYM) THENL
     [ASM_CASES_TAC `s:real = p` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `s:real = p'` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `p < s /\ s < p'` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`p:real`; `s:real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        not(can (find_term ((=) `sub:num->num`)) (concl th)) &&
        can (find_term ((=) `E:real`)) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[dist] THEN DISCH_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `p':real`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th) &&
        not(can (find_term ((=) `sub:num->num`)) (concl th)) &&
        can (find_term ((=) `E:real`)) (concl th))) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[dist] THEN DISCH_TAC] THEN
      MP_TAC(ISPECL
        [`ball((phi:A->real^N) k,&6 * (R:A->real) k)`;
         `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)`; `tt:real`;
         `cball((phi:A->real^N) k,&3 * (R:A->real) k)`; `Eb:real`; `eps:real`; `sqrt b`;
         `delta:real`; `rho:real`; `sol:real->real->real^N->real^N->real^1->real^N`;
         `--sqrt(tt - a')`; `sqrt(tt - a')`; `lam:real`; `Gm:real`; `Rm:real`; `E:real`;
         `\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
         `\n:num v:real^1. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (drop v pow 2))`;
         `p:real`; `s:real`; `p':real`] P2AK_UNIQ_CHART) THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[CONVEX_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET_BALLS; DIST_REFL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_CBALL] THEN
        MP_TAC(ISPECL [`(phi:A->real^N) k`; `(phi:A->real^N)((gamma:real->A)(s pow 2))`] DIST_SYM) THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "SQR" MATCH_MP_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s - p) * E` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        USE_THEN "SQR" MATCH_MP_TAC THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - s) * E` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= a * b ==> x <= b * a`) THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= a * b ==> x <= b * a`) THEN FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `n:num` THEN REPEAT CONJ_TAC THENL
         [USE_THEN "KC" (MP_TAC o SPECL [`n:num`; `p:real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "KC" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `p:real`; `s:real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
          USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `s:real`; `p':real`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
        X_GEN_TAC `n:num` THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `p:real`; `s:real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K1:real->bool`) STRIP_ASSUME_TAC) THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `s:real`; `p':real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K2:real->bool`) STRIP_ASSUME_TAC) THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K3:real->bool`) STRIP_ASSUME_TAC) THEN
        REPEAT CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`K1:real->bool`; `(K1:real->bool) INTER real_interval[p,s]`] THEN
          ASM_REWRITE_TAC[];
          MAP_EVERY EXISTS_TAC [`K2:real->bool`; `(K2:real->bool) INTER real_interval[s,p']`] THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        USE_THEN "CV" (MP_TAC o SPEC `p:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        USE_THEN "CV" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        USE_THEN "CV" (MP_TAC o SPEC `p':real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        USE_THEN "AM" (MP_TAC o SPEC `e:real`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
        EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        USE_THEN "PC" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K3:real->bool`) STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `N:num`)) (concl th))) THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `tt:real`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the BVP length between the limit end points is at most the liminf *)
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (p pow 2)) IN
          cball(phi k,&3 * (R:A->real) k) /\
        norm(phi(gs(sub(n + N0))(p' pow 2)) - phi(gs(sub(n + N0))(p pow 2))) <= rho`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN CONJ_TAC THENL
     [USE_THEN "KC" (MP_TAC o SPECL [`n:num`; `p:real`]) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "NR" (MP_TAC o SPECL [`n:num`; `p:real`; `p':real`]) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (p pow 2))) --> ya)
    sequentially /\
    ((\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (p' pow 2))) --> yb)
    sequentially`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "CV" (MP_TAC o SPEC `p:real`) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "CV" (MP_TAC o SPEC `p':real`) THEN
      ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "C" (MP_TAC o SPECL [`p:real`; `p':real`; `ya:real^N`; `yb:real^N`;
     `\n:num. (p:real)`; `\n:num. (p':real)`;
     `\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (p pow 2))`;
     `\n. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) (n + N0)) (p' pow 2))`]) THEN
  REWRITE_TAC[LIM_CONST] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + N0:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `N0 <= n:num /\ (n - N0) + N0 = n:num` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `N + N0 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - N0:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N:num`)) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `N + N0 <= n:num` THEN ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  USE_THEN "PC" (MP_TAC o SPECL [`n - N0:num`; `p:real`; `p':real`]) THEN
  ANTS_TAC THENL [P2AK_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `K:real->bool`) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N0:num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th))) THEN
  ANTS_TAC THENL [P2AK_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `p:real`; `p':real`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "distance")) (concl th) &&
    can (find_term ((=) `E:real`)) (concl th))) THEN
  ANTS_TAC THENL [P2AK_ARITH_TAC; REWRITE_TAC[dist] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`ball((phi:A->real^N) k,&6 * (R:A->real) k)`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W tt (U INTER W,phi:A->real^N)`; `tt:real`;
                 `cball((phi:A->real^N) k,&3 * (R:A->real) k)`; `Eb:real`; `eps:real`; `sqrt b`;
                 `delta:real`; `rho:real`; `sol:real->real->real^N->real^N->real^1->real^N`;
                 `--sqrt(tt - a')`; `sqrt(tt - a')`; `p:real`; `p':real`;
                 `\v:real^1. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (drop v pow 2))`;
                 `\v. vector_derivative
                        (\v:real^1. (phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (drop v pow 2)))
                        (at v)`;
                 `K:real->bool`; `(K:real->bool) INTER real_interval[p,p']`] P2AK_BVPD_LE) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`(phi:A->real^N) k`;
                     `(phi:A->real^N)((gs:num->real->A) ((sub:num->num) n) (p pow 2))`] DIST_SYM) THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "SQR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E:real` THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* A uniform mesh of good pieces (P2AK_SB_GOOD), the L-length of the limit  *)
(* curve on good pieces, the partition induction, the bound on [eps^2,b]    *)
(* and, by monotone convergence, integrability on [0,b] with L-length at    *)
(* most Lam (P2AK_SB_INT).                                                  *)
(* ------------------------------------------------------------------------- *)

(* A positive lower bound for finitely many positive numbers.              *)

let P2AK_FINITE_POS_LB = prove
 (`!(f:A->real) s. FINITE s /\ (!k. k IN s ==> &0 < f k)
                   ==> ?d. &0 < d /\ !k. k IN s ==> d <= f k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(&1) INSERT IMAGE (f:A->real) s` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE; IN_INSERT; IN_IMAGE] THEN
  STRIP_TAC THEN EXISTS_TAC `inf((&1) INSERT IMAGE (f:A->real) s)` THEN
  ASM_MESON_TAC[REAL_LT_01]);;

(* Single box, case (c): a uniform mesh h on [eps, sqrt b] such that on     *)
(* every piece of length at most h the limit curve is a C^1 chart curve     *)
(* (the BVP solution between its end points) whose length is at most the   *)
(* liminf of the lengths of the sequence on the piece.                      *)

let P2AK_SB_GOOD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam eps.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam /\
     &0 < eps /\ eps < sqrt b
     ==> ?h. &0 < h /\
             !p p'. eps <= p /\ p < p' /\ p' <= sqrt b /\ p' - p <= h
                    ==> ?U phi (Y:real^1->real^N).
                          (U,phi) IN p2a_vatlas V tt /\
                          (!s. p <= s /\ s <= p'
                               ==> Y(lift s) IN IMAGE phi (U INTER W) /\
                                   Y differentiable (at (lift s)) /\
                                   (\v. vector_derivative Y (at v)) continuous (at (lift s)) /\
                                   gamma(s pow 2) = chart_inv (U INTER W,phi) (Y(lift s))) /\
                          (!e. &0 < e
                               ==> ?N. !n. N <= n
                                   ==> p2a_cL (p2a_rlocal V W tt (U INTER W,phi)) tt Y p p'
                                       <= real_integral (real_interval[p pow 2,p' pow 2])
                                            (p2a_L_integrand V tt (gs (sub n)) b) + e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  SUBGOAL_THEN `sqrt b pow 2 <= T1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Eb. &0 < Eb /\ E <= Eb /\
         &2 * (&2 / lam * (Gm / &2 * E + &4 * sqrt b pow 2 * Rm * (sqrt b - eps))) <= Eb`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `E + abs(&2 * (&2 / lam * (Gm / &2 * E + &4 * sqrt b pow 2 * Rm * (sqrt b - eps)))) + &1` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* BVP data for every chart of the box *)
  SUBGOAL_THEN
   `!k. k IN Fs
        ==> ?delta rho (sol:real->real->real^N->real^N->real^1->real^N).
              p2ak_bvpd (ball(SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k) k,&6 * R k))
                        (p2a_rlocal V W tt (FST(chart_at (p2a_vatlas V tt) k) INTER W,
                                            SND(chart_at (p2a_vatlas V tt) k)))
                        tt (cball(SND(chart_at (p2a_vatlas V tt) k) k,&3 * R k)) Eb eps (sqrt b)
                        delta rho sol`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AK_BOX_BVP THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `r:real`;
                          `lam:real`; `Gm:real`; `Rm:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:A->real` (X_CHOOSE_THEN `rho:A->real`
    (X_CHOOSE_THEN `sol:A->real->real->real^N->real^N->real^1->real^N` (LABEL_TAC "BV")))) THEN
  SUBGOAL_THEN `!k. k IN Fs ==> &0 < (delta:A->real) k /\ &0 < (rho:A->real) k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    USE_THEN "BV" (MP_TAC o SPEC `k:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p2ak_bvpd] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:A. min ((delta:A->real) k) (((rho:A->real) k / &2) pow 2 / (E + &1))`;
                 `Fs:A->bool`] P2AK_FINITE_POS_LB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `delta:A->real`)) (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_bvpd")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min h0 (r pow 2 / (E + &1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 <= E ==> &0 < E + &1`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `p':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p' pow 2 <= b /\ &0 <= p /\ (p' - p) * E <= r pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * (E + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= E ==> &0 < E + &1`] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the chart of the piece and the convergence there *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                 `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`;
                 `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                 `gamma:real->A`; `Lam:real`; `p:real`; `p':real`] P2AK_SB_PIECE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `h0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "BV" (MP_TAC o SPEC `k:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `p' - p <= (delta:A->real) k /\ (p' - p) * E <= ((rho:A->real) k / &2) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(p' - p) * (E + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= E ==> &0 < E + &1`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                 `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`;
                 `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`;
                 `gamma:real->A`; `Lam:real`; `eps:real`; `p:real`; `p':real`; `k:A`; `N0:num`;
                 `Eb:real`; `(delta:A->real) k`; `(rho:A->real) k`;
                 `(sol:A->real->real->real^N->real^N->real^1->real^N) k`]
                P2AK_SB_GOOD_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A))`; `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A))`;
    `(sol:A->real->real->real^N->real^N->real^1->real^N) k p p'
       (SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k) ((gamma:real->A)(p pow 2)))
       (SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) k) (gamma(p' pow 2)))`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* The L-length of the limit curve over a good piece is the length of its  *)
(* chart curve (P2A_CHART_SEG_LINT and the locality of the integrand).      *)

let P2AK_GOOD_LINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' tt (gamma:real->A) b U (phi:A->real^N) (Y:real^1->real^N) p p'.
     p2a_svs V /\ p2a_region V W a' tt /\ (U,phi) IN p2a_vatlas V tt /\
     &0 < p /\ p < p' /\ p' pow 2 <= b /\ p' pow 2 < tt - a' /\
     (!s. p <= s /\ s <= p'
          ==> Y(lift s) IN IMAGE phi (U INTER W) /\
              Y differentiable (at (lift s)) /\
              (\v. vector_derivative Y (at v)) continuous (at (lift s)) /\
              gamma(s pow 2) = chart_inv (U INTER W,phi) (Y(lift s)))
     ==> (p2a_L_integrand V tt gamma b has_real_integral
          p2a_cL (p2a_rlocal V W tt (U INTER W,phi)) tt Y p p')
         (real_interval[p pow 2,p' pow 2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(tt - a') /\ p' < sqrt(tt - a')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC(SPEC `p':real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`;
                 `phi:A->real^N`; `Y:real^1->real^N`; `p:real`; `p':real`;
                 `--sqrt(tt - a')`; `sqrt(tt - a')`] P2A_CHART_SEG_LINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 < sqrt(tt - a') pow 2` MP_TAC THENL
       [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
        REWRITE_TAC[ARITH_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(tt - a') pow 2 = tt - a'` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN MP_TAC(SPEC `p':real` REAL_LE_POW_2) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    DISCH_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_FINITE THEN
  MAP_EVERY EXISTS_TAC
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt
       (\tau. chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau))))
       (p' pow 2)`;
    `{p pow 2,p' pow 2}`] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_REAL_INTERVAL; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC P2A_LINT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`p pow 2`; `p' pow 2`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL
     [MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt s` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
    ASM_SIMP_TAC[SQRT_POW_2] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
      SIMP_TAC[]]]);;

(* Curvature bound at the points of C for the box times.                   *)

let P2AK_BXD_SCALAR = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' tt C T1 Fs R r lam Gm Rm (y:A) t.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ y IN C /\ tt - T1 <= t /\ t <= tt
     ==> abs(mfd_scalar (p2a_vatlas V t) (p2a_vmetric V t) y) <= Rm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `R:A->real`)) (concl th) &&
    can (find_term ((=) `C:A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`;
                 `FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A))`;
                 `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A))`; `t:real`; `y:A`] P2AK_SCALAR_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A)) (y:A)`;
                                `vec 0:real^N`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL] THEN
    MP_TAC(ISPECL [`SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A)) k`;
                   `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A)) (y:A)`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* The L-integrand at points of C is at least -sqrt(tau) Rm.                *)

let P2AK_LINT_LOWER = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' tt C T1 Fs R r lam Gm Rm (gamma:real->A) b tau.
     p2ak_bxd V W a' tt C T1 Fs R r lam Gm Rm /\ &0 <= tau /\ tau <= T1 /\ gamma tau IN C
     ==> --(sqrt tau * Rm) <= p2a_L_integrand V tt gamma b tau`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `C:A->bool`; `T1:real`;
                 `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`;
                 `(gamma:real->A) tau`; `tt - tau`] P2AK_BXD_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[p2a_L_integrand; REAL_ARITH `--(x * y) = x * --y`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MP_TAC(SPEC `mfd_speed (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) (p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau))
                         (gamma:real->A) (&0) b tau` REAL_LE_POW_2) THEN
  ASM_REAL_ARITH_TAC);;

(* Partition induction: if f is integrable on short pieces [p^2,p'^2] with  *)
(* integral at most the liminf of those of fn, the same holds on [a^2,c^2]. *)

let P2AK_PARTITION_LIM = prove
 (`!(f:real->real) (fn:num->real->real) a c h.
     &0 <= a /\ a <= c /\ &0 < h /\
     (!n. fn n real_integrable_on real_interval[a pow 2,c pow 2]) /\
     (!p p'. a <= p /\ p < p' /\ p' <= c /\ p' - p <= h
             ==> f real_integrable_on real_interval[p pow 2,p' pow 2] /\
                 !e. &0 < e
                     ==> ?N. !n. N <= n
                             ==> real_integral (real_interval[p pow 2,p' pow 2]) f
                                 <= real_integral (real_interval[p pow 2,p' pow 2]) (fn n) + e)
     ==> f real_integrable_on real_interval[a pow 2,c pow 2] /\
         !e. &0 < e
             ==> ?N. !n. N <= n
                     ==> real_integral (real_interval[a pow 2,c pow 2]) f
                         <= real_integral (real_interval[a pow 2,c pow 2]) (fn n) + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `a:real = c` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `(c - a) / h` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M0:num`) THEN
  ABBREV_TAC `M = M0 + 1` THEN
  SUBGOAL_THEN `&0 < &M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c - a) / &M <= h` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `(c - a) / h <= &M0` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&M0 <= &M` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`&M0`; `&M`; `h:real`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c - a <= &M0 * h` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `hh = (c - a) / &M` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `&0 < hh` ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a + &M * hh = c` ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN UNDISCH_TAC `&0 < &M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. m <= M
        ==> (f:real->real) real_integrable_on real_interval[a pow 2,(a + &m * hh) pow 2] /\
            !e. &0 < e
                ==> ?N. !n. N <= n:num
                        ==> real_integral (real_interval[a pow 2,(a + &m * hh) pow 2]) f
                            <= real_integral (real_interval[a pow 2,(a + &m * hh) pow 2])
                                 ((fn:num->real->real) n) + e`
  (MP_TAC o SPEC `M:num`) THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH")) THEN
    SUBGOAL_THEN `&m + &1 <= &M` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_ADD_ASSOC] THEN
    ABBREV_TAC `u = a + &m * hh` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `a <= u /\ u + hh <= c` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE];
        MP_TAC(ISPECL [`&m + &1`; `&M`; `hh:real`] REAL_LE_RMUL) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `a + &M * hh = c` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `u + hh`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PIECE")) THEN
    SUBGOAL_THEN `a pow 2 <= u pow 2 /\ u pow 2 <= (u + hh) pow 2 /\ (u + hh) pow 2 <= c pow 2`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `u pow 2` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "IH" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    USE_THEN "PIECE" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N2:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N1:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`f:real->real`; `a pow 2`; `(u + hh) pow 2`; `u pow 2`]
                  REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN
      EXISTS_TAC `u pow 2` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`(fn:num->real->real) n`; `a pow 2`; `(u + hh) pow 2`; `u pow 2`]
                  REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`a pow 2`; `c pow 2`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[LE_REFL]]);;

(* x <= y from x <= y + e for all e > 0.                                    *)

let P2AK_LE_ADD_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN ASM_REAL_ARITH_TAC);;

(* Single box, case (c): for 0 < eps < sqrt b the limit curve has integrable *)
(* L-integrand on [eps^2,b], with integral at most Lam + sqrt b Rm eps^2.    *)

let P2AK_SB_EPS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam eps.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam /\
     &0 < eps /\ eps < sqrt b
     ==> p2a_L_integrand V tt gamma b real_integrable_on real_interval[eps pow 2,b] /\
         real_integral (real_interval[eps pow 2,b]) (p2a_L_integrand V tt gamma b)
         <= Lam + sqrt b * Rm * eps pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`; `eps:real`] P2AK_SB_GOOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eps pow 2 /\ eps pow 2 <= b` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b`;
                 `\n. p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt ((gs:num->real->A) ((sub:num->num) n)) b`;
                 `eps:real`; `sqrt b`; `h:real`] P2AK_PARTITION_LIM) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN
      FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
        can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
      REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_LE_REFL];
      MAP_EVERY X_GEN_TAC [`p:real`; `p':real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:real`; `p':real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `h:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (X_CHOOSE_THEN `Y:real^1->real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `p' pow 2 <= b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `gamma:real->A`; `b:real`;
                   `U:A->bool`; `phi:A->real^N`; `Y:real^1->real^N`; `p:real`; `p':real`]
                  P2AK_GOOD_LINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[real_integrable_on]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIM")) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2AK_LE_ADD_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "LIM" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Lam:real`)) (concl th) &&
    can (find_term ((=) `sub:num->num`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "real_lt")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N1:num`)) (concl th))) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `N2:num`)) (concl th))) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) (N1 + N2)` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
    can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
  ABBREV_TAC `g = (gs:num->real->A) ((sub:num->num) (N1 + N2))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (g:real->A) b`; `&0`; `b:real`; `eps pow 2`]
                REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `--(sqrt b * Rm) * (eps pow 2 - &0)
    <= real_integral (real_interval[&0,eps pow 2]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (g:real->A) b)`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_CONST o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC P2AK_LINT_LOWER THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                          `R:A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `g:real->A`)) (concl th) &&
      can (find_term ((=) `C:A->bool`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (g:real->A) b <= Lam + e / &2` THEN
  REWRITE_TAC[p2a_L_length] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  UNDISCH_TAC
   `real_integral (real_interval[eps pow 2,b]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b)
    <= real_integral (real_interval[eps pow 2,b]) (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (g:real->A) b) + e / &2` THEN
  REAL_ARITH_TAC);;

(* Single box, case (c): the L-integrand of the limit curve is integrable  *)
(* on [0,b] and its L-length is at most Lam (monotone convergence of the    *)
(* integrals over [b/(k+2),b] of the integrand shifted by sqrt b Rm).       *)

let P2AK_SB_INT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam
     ==> p2a_L_integrand V tt gamma b real_integrable_on real_interval[&0,b] /\
         p2a_L_length V tt gamma b <= Lam`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  REWRITE_TAC[p2a_L_length] THEN
  ABBREV_TAC `f = p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt (gamma:real->A) b` THEN
  ABBREV_TAC `K = sqrt b * Rm` THEN
  SUBGOAL_THEN `&0 < sqrt b /\ &0 <= K` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the lower bound of the integrand *)
  SUBGOAL_THEN `!tau. &0 <= tau /\ tau <= b ==> --K <= (f:real->real) tau` (LABEL_TAC "LOW") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `--(sqrt tau * Rm)` THEN CONJ_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[SQRT_MONO_LE];
      MATCH_MP_TAC P2AK_LINT_LOWER THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`;
                            `R:A->real`; `r:real`; `lam:real`; `Gm:real`] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the eps-bounds, with eps^2 = t *)
  SUBGOAL_THEN
   `!t. &0 < t /\ t < b
        ==> (f:real->real) real_integrable_on real_interval[t,b] /\
            real_integral (real_interval[t,b]) f <= Lam + K * t`
  (LABEL_TAC "EPS") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`; `sqrt t`] P2AK_SB_EPS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MAP_EVERY EXPAND_TAC ["f"; "K"] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the increasing sequence of truncations *)
  ABBREV_TAC `tk = \k. b / &(k + 2)` THEN
  SUBGOAL_THEN
   `!k. &0 < (tk:num->real) k /\ tk k < b /\ tk (SUC k) <= tk k`
  (LABEL_TAC "TK") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "tk" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &(k + 2) /\ &1 < &(k + 2) /\ &(k + 2) <= &(SUC k + 2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
      MP_TAC(ISPECL [`&1`; `&(k + 2)`; `b:real`] REAL_LT_RMUL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t ==> ?N. !k. N <= k ==> (tk:num->real) k <= t` (LABEL_TAC "TK0") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPEC `b / t` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "tk" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &(k + 2) /\ &N <= &(k + 2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `b / t <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`&N`; `&(k + 2)`; `t:real`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `b <= &N * t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `fk = \k tau. if tau IN real_interval[(tk:num->real) k,b] then (f:real->real) tau + K
                 else &0` THEN
  SUBGOAL_THEN
   `!k. (fk:num->real->real) k real_integrable_on real_interval[&0,b] /\
        real_integral (real_interval[&0,b]) (fk k) =
        real_integral (real_interval[(tk:num->real) k,b]) f + K * (b - tk k)`
  (LABEL_TAC "FK") THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "EPS" (MP_TAC o SPEC `(tk:num->real) k`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `real_interval[(tk:num->real) k,b] INTER real_interval[&0,b] =
                  real_interval[tk k,b]` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(fk:num->real->real) k =
                  (\tau. if tau IN real_interval[(tk:num->real) k,b]
                         then (\tau. (f:real->real) tau + K) tau else &0)` SUBST1_TAC THENL
     [EXPAND_TAC "fk" THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INTEGRABLE_RESTRICT_INTER; REAL_INTEGRAL_RESTRICT_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\tau. (f:real->real) tau + K) real_integrable_on real_interval[(tk:num->real) k,b]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real->real`; `\tau:real. (K:real)`; `real_interval[(tk:num->real) k,b]`]
                  REAL_INTEGRAL_ADD) THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* monotone convergence *)
  MP_TAC(ISPECL [`fk:num->real->real`; `\tau. (f:real->real) tau + K`; `real_interval[&0,b]`]
                REAL_MONOTONE_CONVERGENCE_INCREASING_AE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `tau:real`] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN EXPAND_TAC "fk" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      USE_THEN "LOW" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_SING] THEN
      STRIP_TAC THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      USE_THEN "TK0" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "fk" THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `abs Lam + K * b` THEN X_GEN_TAC `k:num` THEN
      USE_THEN "FK" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      USE_THEN "EPS" (MP_TAC o SPEC `(tk:num->real) k`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `--K * (b - (tk:num->real) k) <= real_integral (real_interval[tk k,b]) f`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`(tk:num->real) k`; `b:real`; `--K`] REAL_INTEGRAL_CONST) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
        X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        USE_THEN "LOW" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MC")) THEN
  SUBGOAL_THEN `(f:real->real) real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\tau. (f:real->real) tau + K`; `\tau:real. (K:real)`; `real_interval[&0,b]`]
                  REAL_INTEGRABLE_SUB) THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - b:real = a`; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\k. real_integral (real_interval[&0,b]) ((fk:num->real->real) k)`;
                 `real_integral (real_interval[&0,b]) (\tau. (f:real->real) tau + K)`;
                 `Lam + K * b`] REALLIM_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN
    USE_THEN "FK" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TK" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    USE_THEN "EPS" (MP_TAC o SPEC `(tk:num->real) k`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `\tau:real. (K:real)`; `real_interval[&0,b]`] REAL_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The limit curve is continuous in the slice topologies and C^1 in every   *)
(* slice chart (no corners), hence admissible, and a minimizer with the     *)
(* right end point: MT Lemma 7.2(c) for one box (P2AK_SB_7_2_C).            *)
(* ------------------------------------------------------------------------- *)

(* Single box, case (c): the limit curve is continuous in the slice        *)
(* topologies (Hoelder bound in the chart of a short piece around the time, *)
(* P2AK_SB_PIECE_LIMIT, and P2A_CHART_INV_NBHD).                             *)

let P2AK_SB_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam tau0 O.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam /\
     &0 <= tau0 /\ tau0 <= b /\ open_in (p2a_vtop V (tt - tau0)) O /\ gamma tau0 IN O
     ==> ?d. &0 < d /\
             !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau0) < d ==> gamma tau IN O`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  ABBREV_TAC `E = &2 / lam * (Lb + &4 * b * sqrt b * Rm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = sqrt tau0` THEN
  SUBGOAL_THEN `&0 <= s0 /\ s0 <= sqrt b /\ s0 pow 2 = tau0 /\ &0 < sqrt b /\ sqrt b pow 2 = b`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; SQRT_POW_2; SQRT_POS_LT;
                                      REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `dl = r pow 2 / (E + &1)` THEN
  SUBGOAL_THEN `&0 < dl /\ dl * E <= r pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN
    SUBGOAL_THEN `&0 < E + &1 /\ &0 < r pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r pow 2 / (E + &1) * (E + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `p = max (&0) (s0 - dl / &2)` THEN
  ABBREV_TAC `p' = min (sqrt b) (s0 + dl / &2)` THEN
  SUBGOAL_THEN `&0 <= p /\ p <= s0 /\ s0 <= p' /\ p < p' /\ p' <= sqrt b /\ p' - p <= dl`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p' pow 2 <= b /\ (p' - p) * E <= r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`; `p:real`; `p':real`] P2AK_SB_PIECE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:A` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:A` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `U = FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `phi = SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt) (k:A))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(U:A->bool,phi:A->real^N) IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "phi"] THEN REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < tt - tau0 /\ tt - tau0 <= tt` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the chart neighbourhood of gamma(tau0) *)
  FIRST_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`; `phi:A->real^N`;
                 `tt - tau0`; `O:A->bool`; `(phi:A->real^N)((gamma:real->A) tau0)`]
                P2A_CHART_INV_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) (phi((gamma:real->A) tau0)) = gamma tau0`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `tt:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `m = min (dl / &2) (r1 pow 2 / (E + &1))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= dl / &2 /\ m * E < r1 pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < E + &1 /\ &0 < r1 pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r1 pow 2 / (E + &1) /\ r1 pow 2 / (E + &1) * (E + &1) = r1 pow 2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `m * (E + &1) <= r1 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r1 pow 2 / (E + &1) * (E + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(sqrt tau - s0) < m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(abs(tau - tau0))` THEN CONJ_TAC THENL
     [EXPAND_TAC "s0" THEN MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt tau /\ sqrt tau <= sqrt b /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; SQRT_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `p <= sqrt tau /\ sqrt tau <= p'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `sqrt tau` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `dist((phi:A->real^N)((gamma:real->A) tau),phi(gamma tau0)) < r1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(sqrt tau - s0) * E` THEN CONJ_TAC THENL
     [DISJ_CASES_TAC(REAL_ARITH `s0 <= sqrt tau \/ sqrt tau <= s0`) THENL
       [FIRST_ASSUM(MP_TAC o SPECL [`s0:real`; `sqrt tau`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      not(can (find_term ((=) `sub:num->num`)) (concl th)) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
        MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(MP_TAC o SPECL [`sqrt tau`; `s0:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      not(can (find_term ((=) `sub:num->num`)) (concl th)) &&
      can (find_term ((=) `E:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
        SUBST1_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A) tau)`;
                           `(phi:A->real^N)((gamma:real->A) tau0)`] DIST_SYM) THEN
        MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN AP_THM_TAC THEN
        AP_TERM_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `m * E` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^N)((gamma:real->A) tau)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `r1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (U INTER W,phi:A->real^N) (phi((gamma:real->A) tau)) = gamma tau`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC P2A_REGION_CHART_INV THEN
  MAP_EVERY EXISTS_TAC [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `a':real`; `tt:real`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Single box, case (c): the limit curve is C^1 in every chart of the slice *)
(* atlases at every time in (0,b] (p2a_pc1 with no corners): around each    *)
(* time it is chart_inv of the BVP solution of a good piece, composed with *)
(* the square root (P2A_CHART_CURVE_PC1, P2A_SQRT_CURVE_DERIV).             *)

let P2AK_SB_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam
     ==> p2a_pc1 V tt gamma (&0) b {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  REWRITE_TAC[p2a_pc1; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b /\ &0 < sqrt s0 /\ sqrt s0 <= sqrt b /\
                sqrt s0 pow 2 = s0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; SQRT_MONO_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `sg = sqrt s0` THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`; `sg / &2`] P2AK_SB_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GD"))) THEN
  ABBREV_TAC `p = max (sg / &2) (sg - h / &2)` THEN
  ABBREV_TAC `p' = min (sqrt b) (sg + h / &2)` THEN
  SUBGOAL_THEN `&0 < p /\ p < sg /\ sg <= p' /\ p < p' /\ p' <= sqrt b /\ p' - p <= h /\
                sg / &2 <= p`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "GD" (MP_TAC o SPECL [`p:real`; `p':real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (X_CHOOSE_THEN `Y:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Y") ASSUME_TAC))))) THEN
  ABBREV_TAC `m = min (h / &2) (sg / &2)` THEN
  SUBGOAL_THEN `&0 < m /\ &0 < m pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b /\ abs(tau - s0) <= m pow 2 / &2
          ==> p <= sqrt tau /\ sqrt tau <= p' /\ sqrt tau pow 2 = tau`
  (LABEL_TAC "IN") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(sqrt tau - sg) < m` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(abs(tau - s0))` THEN CONJ_TAC THENL
       [EXPAND_TAC "sg" THEN MATCH_MP_TAC REAL_ABS_LE_SQRT_POS THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt tau <= sqrt b /\ sqrt tau pow 2 = tau` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_POW_2]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b /\ abs(tau - s0) <= m pow 2 / &2
          ==> (gamma:real->A) tau =
              chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt tau)))`
  (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    USE_THEN "IN" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "Y" (MP_TAC o SPEC `sqrt tau`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* the chart curve in tau is C^1 in every chart *)
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `tt:real`; `W:A->bool`; `a':real`; `tt:real`; `U:A->bool`;
                 `phi:A->real^N`; `\t:real^1. (Y:real^1->real^N)(lift(sqrt(drop t)))`;
                 `\t:real^1. inv(&2 * sqrt(drop t)) %
                             vector_derivative (Y:real^1->real^N) (at (lift(sqrt(drop t))))`;
                 `p pow 2`; `p' pow 2`] P2A_CHART_CURVE_PC1) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `p' pow 2 <= b` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
        ALL_TAC] THEN
      MP_TAC(SPEC `p:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < tau /\ p <= sqrt tau /\ sqrt tau <= p'` STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `p pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      USE_THEN "Y" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2A_SQRT_CURVE_DERIV THEN
      ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "CC") THEN
  SUBGOAL_THEN
   `!S. S SUBSET {s | s0 - m pow 2 / &2 <= drop s /\ drop s <= s0 + m pow 2 / &2 /\
                      &0 < drop s /\ drop s <= b /\
                      p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - drop s) = p2a_vatlas V (tt - s0) /\
                      (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}
        ==> continuously_differentiable 1 S (\s. SND c (gamma(drop s)))`
  (LABEL_TAC "CD") THENL
   [X_GEN_TAC `S:real^1->bool` THEN DISCH_THEN(LABEL_TAC "SS") THEN
    SUBGOAL_THEN
     `!s. s IN S ==> &0 <= drop s /\ drop s <= b /\ abs(drop s - s0) <= m pow 2 / &2 /\
                     p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - drop s) = p2a_vatlas V (tt - s0) /\
                     (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))`
    (LABEL_TAC "SS2") THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      USE_THEN "SS" (MP_TAC o SPEC `s:real^1` o REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
    EXISTS_TAC `\s:real^1. SND (c:(A->bool)#(A->real^N))
                  (chart_inv (U INTER W,phi:A->real^N) ((Y:real^1->real^N)(lift(sqrt(drop s)))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "EQ" MATCH_MP_TAC THEN
      USE_THEN "SS2" (MP_TAC o SPEC `s:real^1`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "CC" (MP_TAC o SPECL [`S:real^1->bool`; `c:(A->bool)#(A->real^N)`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    USE_THEN "SS2" (MP_TAC o SPEC `s:real^1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "IN" (MP_TAC o SPEC `drop s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "EQ" (MP_TAC o SPEC `drop s`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(drop s) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(drop s) pow 2` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `m pow 2 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN USE_THEN "CD" MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Single box, case (c) (MT Lemma 7.2(c) in one box): the limit curve of a  *)
(* minimizing sequence is a minimizer with the right end point.             *)

let P2AK_SB_7_2_C = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W a' C T1 Fs R r lam Gm Rm tt (x:A) b gs Lb q sub gamma Lam.
     p2ak_lim V W a' C T1 Fs R r lam Gm Rm tt x b gs Lb q sub gamma Lam
     ==> p2a_min V tt x b gamma /\ gamma b = q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_lim]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2ak_bxd]) THEN
  SUBGOAL_THEN `!t. hausdorff_space(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))` THEN SIMP_TAC[p2a_svs]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b
          ==> (gamma:real->A) tau IN W /\ gamma tau IN topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau))`
  (LABEL_TAC "TS") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `tt:real`; `tt - tau`] P2A_REGION_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term ((=) `C:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A) tau IN W` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `(C:A->bool) SUBSET W`)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) (W:A->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the end points *)
  SUBGOAL_THEN `(gamma:real->A)(&0) = x /\ gamma b = q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2AK_LIM_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - &0)`;
                            `\n. (gs:num->real->A) ((sub:num->num) n) (&0)`] THEN
      FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) 0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
      can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
      REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term ((=) `C:A->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "TS" (MP_TAC o SPEC `&0`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
          can (find_term ((=) `(gs:num->real->A) ((sub:num->num) 0)`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
      can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
        REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC P2AK_LIM_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - b)`;
                            `\n. (gs:num->real->A) ((sub:num->num) n) b`] THEN
      FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) 0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
      can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
      REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `b:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `gamma:real->A`)) (concl th) &&
      can (find_term ((=) `C:A->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "TS" (MP_TAC o SPEC `b:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `b:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "topspace")) (concl th) &&
          can (find_term ((=) `(gs:num->real->A) ((sub:num->num) 0)`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `(sub:num->num) n` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_adm")) (concl th) &&
      can (find_term ((=) `q:A`)) (concl th) && not(can (find_term ((=) `Lam:real`)) (concl th)))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* admissibility *)
  SUBGOAL_THEN `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) tt x b (gamma:real->A)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_adm] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      USE_THEN "TS" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`; `tau0:real`; `O:A->bool`] P2AK_SB_CONT) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `{}:real->bool` THEN
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`] P2AK_SB_PC1) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_smooth] THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `tt:real`] THEN
      USE_THEN "TS" (MP_TAC o SPEC `tau:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`] P2AK_SB_INT) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_min] THEN X_GEN_TAC `gamma':real->A` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lam:real` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))`; `W:A->bool`; `a':real`; `C:A->bool`; `T1:real`; `Fs:A->bool`; `R:A->real`; `r:real`; `lam:real`; `Gm:real`; `Rm:real`; `tt:real`; `x:A`; `b:real`; `gs:num->real->A`; `Lb:real`; `q:A`; `sub:num->num`; `gamma:real->A`; `Lam:real`] P2AK_SB_INT) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `q:A`)) (concl th) && can (find_term ((=) `Lam:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;


