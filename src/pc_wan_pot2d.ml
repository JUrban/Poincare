(* ========================================================================= *)
(* pc_wan_pot2d: second-order regularity from jets and the k = 0 case of     *)
(* WAN_SCHAUDER_2D:                                                          *)
(*   - comparison of quadratic jets (slope and quadratic coefficient),       *)
(*     derivatives of w and of the slope a1;                                 *)
(*   - C^2, the iterated partials of length <= 2, Lap w = 4 q;               *)
(*   - mollified second-order jets (WANL_PT_EXPAND with N = 2) and their     *)
(*     limit (WANL_PT_SCH_LIMIT);                                            *)
(*   - the wan_ckal bounds for k = 2 and the constants;                      *)
(*   - WANL_PT_SCH0 (theta form, very weak equation) and                     *)
(*     WANL_PT_SCHAUDER_K0 (the k = 0 instance of WAN_SCHAUDER_2D_STATEMENT, *)
(*     with Lap w = f in addition).                                          *)
(* ========================================================================= *)

needs "src/pc_wan_pot2c.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Quadratic jets J(x) = w0 + Re(b1 z) + Re(b2 z^2) + q |z|^2, z = x - x0:   *)
(* first and second symmetric differences, and the comparison of the jets  *)
(* at two nearby points.                                                     *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_QJET_SYM = prove
 (`!(w0:real) (b1:complex) (b2:complex) q (x0:complex) x1 d e.
     let J = \x. w0 + Re(b1 * (x - x0)) + (Re(b2 * (x - x0) pow 2) + q * norm(x - x0) pow 2) in
     J(x1 + d % e) - J(x1 - d % e) =
     &2 * d * Re((b1 + Cx(&2) * b2 * (x1 - x0) + Cx(&2 * q) * cnj(x1 - x0)) * e) /\
     J(x1 + d % e) + J(x1 - d % e) - &2 * J x1 =
     &2 * d pow 2 * (Re(b2 * e pow 2) + q * norm e pow 2)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN
  REWRITE_TAC[NORM_POW_2; DOT_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[COMPLEX_POW_2; RE_ADD; RE_SUB; RE_MUL_CX; IM_ADD; IM_SUB; IM_MUL_CX;
              complex_mul; RE; IM; RE_CX; IM_CX; RE_CNJ; IM_CNJ; cnj] THEN
  REAL_ARITH_TAC);;

let WANL_PT_JET_GRAD2 = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 sg x0 x1.
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                     (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
                 <= K * norm(x - x0) rpow sg) /\
     x0 IN s /\ x1 IN s /\ &0 <= K /\ &1 < sg /\ &2 * norm(x1 - x0) <= rho0 /\
     (!e. norm e = &1 ==> x1 + norm(x1 - x0) % e IN s /\ x1 - norm(x1 - x0) % e IN s)
     ==> norm(a1 x1 - (a1 x0 + Cx(&2) * a2 x0 * (x1 - x0) + Cx(&2 * q x0) * cnj(x1 - x0)))
         <= &2 * K * (&2 rpow sg + &1) * norm(x1 - x0) rpow (sg - &1)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = norm(x1 - x0:real^2)` THEN
  ASM_CASES_TAC `d = &0` THENL
   [UNDISCH_TAC `norm(x1 - x0:real^2) = d` THEN ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COMPLEX_VEC_0; CNJ_CX; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID;
                COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS; REAL_LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[NORM_POS_LT] THEN
    UNDISCH_TAC `~(d = &0)` THEN EXPAND_TAC "d" THEN REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `R = d rpow (sg - &1)` THEN ABBREV_TAC `S2 = &2 rpow sg` THEN
  SUBGOAL_THEN `d rpow sg = d * R /\ (&2 * d) rpow sg = S2 * (d * R)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &1 + (sg - &1)`] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
      DISCH_TAC THEN EXPAND_TAC "S2" THEN ASM_REWRITE_TAC[RPOW_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R /\ &0 <= S2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "S2"] THEN CONJ_TAC THEN MATCH_MP_TAC RPOW_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A0 = a1 x0 + Cx(&2) * (a2:real^2->complex) x0 * (x1 - x0) +
                   Cx(&2 * (q:real^2->real) x0) * cnj(x1 - x0)` THEN
  SUBGOAL_THEN
   `!e. norm(e:complex) = &1
        ==> abs(Re(((a1:real^2->complex) x1 - A0) * e)) <= K * (S2 + &1) * R`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:complex` o check (fun th ->
      can (find_term (fun t -> t = `(%):real->real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(d % e:real^2) = d` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((x1 + d % e) - x1:real^2) = d /\ norm((x1 - d % e) - x1:real^2) = d`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(x1 + d % e) - x1:real^N = d % e`;
                  VECTOR_ARITH `(x1 - d % e) - x1:real^N = --(d % e)`; NORM_NEG] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((x1 + d % e) - x0:real^2) <= &2 * d /\ norm((x1 - d % e) - x0:real^2) <= &2 * d`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(x1 + d % e) - x0:real^N = (x1 - x0) + d % e`;
                  VECTOR_ARITH `(x1 - d % e) - x0:real^N = (x1 - x0) + --(d % e)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `norm(x1 - x0:real^2) + norm(d % e:real^2)`;
        EXISTS_TAC `norm(x1 - x0:real^2) + norm(--(d % e):real^2)`] THEN
      REWRITE_TAC[NORM_TRIANGLE; NORM_NEG] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)) -
                  (Re((a2:real^2->complex) x0 * (x - x0) pow 2) +
                   (q:real^2->real) x0 * norm(x - x0) pow 2))
              <= K * (S2 * (d * R))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K * norm(x - x0:real^2) rpow sg` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          can (find_term (fun t -> t = `S2:real`)) (concl th) && is_eq(concl th))) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)) -
                  (Re((a2:real^2->complex) x1 * (x - x1) pow 2) +
                   (q:real^2->real) x1 * norm(x - x1) pow 2))
              <= K * (d * R)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x1:real^2`; `x:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `rho0:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPEC `x1 + d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)) -
                  (Re((a2:real^2->complex) x0 * (x - x0) pow 2) +
                   (q:real^2->real) x0 * norm(x - x0) pow 2))
              <= K * (S2 * (d * R))`)) THEN
    MP_TAC(SPEC `x1 - d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)) -
                  (Re((a2:real^2->complex) x0 * (x - x0) pow 2) +
                   (q:real^2->real) x0 * norm(x - x0) pow 2))
              <= K * (S2 * (d * R))`)) THEN
    MP_TAC(SPEC `x1 + d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)) -
                  (Re((a2:real^2->complex) x1 * (x - x1) pow 2) +
                   (q:real^2->real) x1 * norm(x - x1) pow 2))
              <= K * (d * R)`)) THEN
    MP_TAC(SPEC `x1 - d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)) -
                  (Re((a2:real^2->complex) x1 * (x - x1) pow 2) +
                   (q:real^2->real) x1 * norm(x - x1) pow 2))
              <= K * (d * R)`)) THEN
    REPEAT(ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
    MP_TAC(CONJUNCT1(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (SPECL [`(w:real^2->real) x0`; `(a1:real^2->complex) x0`; `(a2:real^2->complex) x0`;
              `(q:real^2->real) x0`; `x0:real^2`; `x1:real^2`; `d:real`; `e:complex`]
             WANL_PT_QJET_SYM))) THEN
    MP_TAC(CONJUNCT1(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (SPECL [`(w:real^2->real) x1`; `(a1:real^2->complex) x1`; `(a2:real^2->complex) x1`;
              `(q:real^2->real) x1`; `x1:real^2`; `x1:real^2`; `d:real`; `e:complex`]
             WANL_PT_QJET_SYM))) THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COMPLEX_VEC_0; CNJ_CX; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB; RE_SUB] THEN
    ABBREV_TAC `P1 = Re((a1:real^2->complex) x1 * e)` THEN
    ABBREV_TAC `PA = Re(A0 * e)` THEN
    REPEAT DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `norm((x1 + d % e) - x1:real^2) = d`;
                                ASSUME `norm((x1 - d % e) - x1:real^2) = d`]) THEN
    SUBGOAL_THEN `abs(d * P1 - d * PA) <= d * (K * (S2 + &1) * R)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_LMUL_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(Re((a1:real^2->complex) x1 - A0)) + abs(Im(a1 x1 - A0))` THEN
  REWRITE_TAC[COMPLEX_NORM_LE_RE_IM] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `Cx(&1)` th) THEN MP_TAC(SPEC `ii` th)) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_II; REAL_ABS_NUM; COMPLEX_MUL_RID; RE_MUL_II;
              REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

let WANL_PT_JET_HESS2 = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 sg x0 x1.
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                     (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
                 <= K * norm(x - x0) rpow sg) /\
     x0 IN s /\ x1 IN s /\ &0 <= K /\ &2 < sg /\ &2 * norm(x1 - x0) <= rho0 /\
     (!e. norm e = &1 ==> x1 + norm(x1 - x0) % e IN s /\ x1 - norm(x1 - x0) % e IN s)
     ==> norm(a2 x1 - a2 x0)
         <= &2 * K * (&2 rpow sg + &2) * norm(x1 - x0) rpow (sg - &2) + &2 * abs(q x1 - q x0)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = norm(x1 - x0:real^2)` THEN
  ASM_CASES_TAC `d = &0` THENL
   [UNDISCH_TAC `norm(x1 - x0:real^2) = d` THEN ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_POS; REAL_LE_REFL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &2`) THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[NORM_POS_LT] THEN
    UNDISCH_TAC `~(d = &0)` THEN EXPAND_TAC "d" THEN REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `R = d rpow (sg - &2)` THEN ABBREV_TAC `S2 = &2 rpow sg` THEN
  SUBGOAL_THEN `d rpow sg = d pow 2 * R /\ (&2 * d) rpow sg = S2 * (d pow 2 * R)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &2 + (sg - &2)`] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW];
      DISCH_TAC THEN EXPAND_TAC "S2" THEN ASM_REWRITE_TAC[RPOW_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= R /\ &0 <= S2 /\ &0 < d pow 2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "S2"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC RPOW_POS_LE) THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. norm(e:complex) = &1
        ==> abs((Re((a2:real^2->complex) x1 * e pow 2) + (q:real^2->real) x1) -
                (Re(a2 x0 * e pow 2) + q x0)) <= K * (S2 + &2) * R`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:complex` o check (fun th ->
      can (find_term (fun t -> t = `(%):real->real^2->real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(d % e:real^2) = d` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((x1 + d % e) - x1:real^2) = d /\ norm((x1 - d % e) - x1:real^2) = d`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(x1 + d % e) - x1:real^N = d % e`;
                  VECTOR_ARITH `(x1 - d % e) - x1:real^N = --(d % e)`; NORM_NEG] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `norm((x1 + d % e) - x0:real^2) <= &2 * d /\ norm((x1 - d % e) - x0:real^2) <= &2 * d`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(x1 + d % e) - x0:real^N = (x1 - x0) + d % e`;
                  VECTOR_ARITH `(x1 - d % e) - x0:real^N = (x1 - x0) + --(d % e)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `norm(x1 - x0:real^2) + norm(d % e:real^2)`;
        EXISTS_TAC `norm(x1 - x0:real^2) + norm(--(d % e):real^2)`] THEN
      REWRITE_TAC[NORM_TRIANGLE; NORM_NEG] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)) -
                  (Re((a2:real^2->complex) x0 * (x - x0) pow 2) +
                   (q:real^2->real) x0 * norm(x - x0) pow 2))
              <= K * (S2 * (d pow 2 * R))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K * norm(x - x0:real^2) rpow sg` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          can (find_term (fun t -> t = `S2:real`)) (concl th) && is_eq(concl th))) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)) -
                  (Re((a2:real^2->complex) x1 * (x - x1) pow 2) +
                   (q:real^2->real) x1 * norm(x - x1) pow 2))
              <= K * (d pow 2 * R)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x1:real^2`; `x:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `rho0:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs((w:real^2->real) x1 - w x0 - Re((a1:real^2->complex) x0 * (x1 - x0)) -
          (Re((a2:real^2->complex) x0 * (x1 - x0) pow 2) +
           (q:real^2->real) x0 * norm(x1 - x0) pow 2)) <= K * (d pow 2 * R)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * norm(x1 - x0:real^2) rpow sg` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `rho0:real`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      ALL_TAC] THEN
    MP_TAC(SPEC `x1 + d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)) -
                  (Re((a2:real^2->complex) x0 * (x - x0) pow 2) +
                   (q:real^2->real) x0 * norm(x - x0) pow 2))
              <= K * (S2 * (d pow 2 * R))`)) THEN
    MP_TAC(SPEC `x1 - d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x0:real^2) <= &2 * d
          ==> abs((w:real^2->real) x - w x0 - Re((a1:real^2->complex) x0 * (x - x0)) -
                  (Re((a2:real^2->complex) x0 * (x - x0) pow 2) +
                   (q:real^2->real) x0 * norm(x - x0) pow 2))
              <= K * (S2 * (d pow 2 * R))`)) THEN
    MP_TAC(SPEC `x1 + d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)) -
                  (Re((a2:real^2->complex) x1 * (x - x1) pow 2) +
                   (q:real^2->real) x1 * norm(x - x1) pow 2))
              <= K * (d pow 2 * R)`)) THEN
    MP_TAC(SPEC `x1 - d % e:real^2`
     (ASSUME `!x. x IN s /\ norm(x - x1:real^2) = d
          ==> abs((w:real^2->real) x - w x1 - Re((a1:real^2->complex) x1 * (x - x1)) -
                  (Re((a2:real^2->complex) x1 * (x - x1) pow 2) +
                   (q:real^2->real) x1 * norm(x - x1) pow 2))
              <= K * (d pow 2 * R)`)) THEN
    REPEAT(ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
    MP_TAC(CONJUNCT2(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (SPECL [`(w:real^2->real) x0`; `(a1:real^2->complex) x0`; `(a2:real^2->complex) x0`;
              `(q:real^2->real) x0`; `x0:real^2`; `x1:real^2`; `d:real`; `e:complex`]
             WANL_PT_QJET_SYM))) THEN
    MP_TAC(CONJUNCT2(CONV_RULE(TOP_DEPTH_CONV let_CONV)
      (SPECL [`(w:real^2->real) x1`; `(a1:real^2->complex) x1`; `(a2:real^2->complex) x1`;
              `(q:real^2->real) x1`; `x1:real^2`; `x1:real^2`; `d:real`; `e:complex`]
             WANL_PT_QJET_SYM))) THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COMPLEX_VEC_0; COMPLEX_MUL_RZERO; RE_CX; REAL_ADD_RID;
                NORM_0; REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; COMPLEX_POW_ZERO;
                COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; NORM_0; REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO;
                REAL_ADD_RID] THEN
    ABBREV_TAC `B1 = Re((a2:real^2->complex) x1 * e pow 2)` THEN
    ABBREV_TAC `B0 = Re((a2:real^2->complex) x0 * e pow 2)` THEN
    REPEAT DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `norm((x1 + d % e) - x1:real^2) = d`;
                                ASSUME `norm((x1 - d % e) - x1:real^2) = d`;
                                ASSUME `norm(x1 - x0:real^2) = d`]) THEN
    SUBGOAL_THEN
     `abs(d pow 2 * (B1 + (q:real^2->real) x1) - d pow 2 * (B0 + q x0)) <=
      d pow 2 * (K * (S2 + &2) * R)`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_LE_LMUL_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(Re((a2:real^2->complex) x1 - a2 x0)) + abs(Im(a2 x1 - a2 x0))` THEN
  REWRITE_TAC[COMPLEX_NORM_LE_RE_IM] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `Cx(&1)` th) THEN
                          MP_TAC(SPEC `cexp(ii * Cx(pi / &4))` th)) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; WANL_PT_OMEGA; COMPLEX_POW_ONE;
              COMPLEX_MUL_RID; RE_MUL_II; RE_SUB; IM_SUB] THEN
  REAL_ARITH_TAC);;

let WANL_PT_JET2_DERIV_W = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 sg x0.
     open s /\ x0 IN s /\ &0 < rho0 /\ &0 <= K /\ &2 < sg /\
     (!x. x IN s /\ norm(x - x0) <= rho0
          ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                  (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
              <= K * norm(x - x0) rpow sg)
     ==> ((\x. lift(w x)) has_derivative (\h. lift(Re(a1 x0 * h)))) (at x0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_JET_DERIV1 THEN
  MAP_EVERY EXISTS_TAC [`s:real^2->bool`;
    `K * rho0 rpow (sg - &2) + norm((a2:real^2->complex) x0) + abs((q:real^2->real) x0)`;
    `rho0:real`; `&2`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_LT_IMP_LE; NORM_POS_LE; REAL_ABS_POS];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `dd = norm(x - x0:real^2)` THEN
  SUBGOAL_THEN `&0 <= dd` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `dd rpow sg <= dd pow 2 * rho0 rpow (sg - &2)` ASSUME_TAC THENL
   [ASM_CASES_TAC `dd = &0` THENL
     [ASM_SIMP_TAC[RPOW_ZERO; REAL_ARITH `&2 < sg ==> ~(sg = &0)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; RPOW_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `dd rpow sg = dd pow 2 * dd rpow (sg - &2)` SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &2 + (sg - &2)`] THEN
      SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(Re((a2:real^2->complex) x0 * (x - x0) pow 2)) <= norm(a2 x0) * dd pow 2 /\
    abs((q:real^2->real) x0 * dd pow 2) <= abs(q x0) * dd pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((a2:real^2->complex) x0 * (x - x0) pow 2)` THEN
      REWRITE_TAC[COMPLEX_NORM_GE_RE_IM; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `K * dd rpow sg <= K * (dd pow 2 * rho0 rpow (sg - &2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RPOW_POW] THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_HAS_DERIV_RPOW = prove
 (`!(f:real^M->real^N) L x0 d K sg.
     linear L /\ &0 < d /\ &0 <= K /\ &1 < sg /\
     (!y. norm(y - x0) < d ==> norm(f y - f x0 - L(y - x0)) <= K * norm(y - x0) rpow sg)
     ==> (f has_derivative L) (at x0)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[has_derivative_at] THEN
  REWRITE_TAC[LIM_AT; DIST_0] THEN X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
  ABBREV_TAC `eta = ep / (K + &1)` THEN
  SUBGOAL_THEN `&0 < eta /\ K * eta < ep` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `K * ep / (K + &1) = (K * ep) / (K + &1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= K ==> &0 < K + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min d (eta rpow inv(sg - &1))` THEN
  SUBGOAL_THEN `&0 < eta rpow inv(sg - &1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `y:real^M` THEN REWRITE_TAC[REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ABBREV_TAC `dy = norm(y - x0:real^M)` THEN
  SUBGOAL_THEN `dy rpow sg = dy * dy rpow (sg - &1)` SUBST_ALL_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `sg = &1 + (sg - &1)`] THEN
    SUBGOAL_THEN `&0 <= dy` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_ADD_ALT; RPOW_POW; REAL_POW_1;
                 REAL_ARITH `&1 < sg ==> ~(&1 + (sg - &1) = &0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `dy rpow (sg - &1) < eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `(eta rpow inv(sg - &1)) rpow (sg - &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LT2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `inv(sg - &1) * (sg - &1) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) y - (f x0 + L(y - x0)) = f y - f x0 - L(y - x0)`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `E = norm((f:real^M->real^N) y - f x0 - L(y - x0))` THEN
  SUBGOAL_THEN `E <= dy * (K * eta)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * dy * dy rpow (sg - &1)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `K * d * r = d * (K * r)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dy` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dy * (K * eta)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dy * (K * eta) < dy * ep` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let WANL_PT_JET2_DERIV_A1 = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 sg x0.
     open s /\ x0 IN s /\ &0 < rho0 /\ &0 <= K /\ &2 < sg /\
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                     (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
                 <= K * norm(x - x0) rpow sg)
     ==> (a1 has_derivative (\h. Cx(&2) * a2 x0 * h + Cx(&2 * q x0) * cnj h)) (at x0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC WANL_PT_HAS_DERIV_RPOW THEN
  MAP_EVERY EXISTS_TAC [`min (d1 / &3) (rho0 / &2)`; `&2 * K * (&2 rpow sg + &1)`;
                        `sg - &1`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; COMPLEX_CMUL; CNJ_ADD; CNJ_MUL; CNJ_CX] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC COMPLEX_RING;
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(a1:real^2->complex) y - a1 x0 -
    (Cx(&2) * a2 x0 * (y - x0) + Cx(&2 * q x0) * cnj(y - x0)) =
    a1 y - (a1 x0 + Cx(&2) * (a2:real^2->complex) x0 * (y - x0) +
            Cx(&2 * (q:real^2->real) x0) * cnj(y - x0))`
  SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC WANL_PT_JET_GRAD2 THEN
  MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `w:real^2->real`; `rho0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z:real^2. norm(z - x0) < d1 ==> z IN s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real^2` THEN DISCH_TAC THEN
  ABBREV_TAC `dd = norm(y - x0:real^2)` THEN
  SUBGOAL_THEN `norm(dd % e:real^2) = dd` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN EXPAND_TAC "dd" THEN
    REWRITE_TAC[REAL_ABS_NORM];
    ALL_TAC] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [SUBGOAL_THEN `(y + dd % e) - x0:real^2 = (y - x0) + dd % e` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`y - x0:real^2`; `dd % e:real^2`] NORM_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(y - dd % e) - x0:real^2 = (y - x0) - dd % e` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`y - x0:real^2`; `--(dd % e):real^2`] NORM_TRIANGLE) THEN
    REWRITE_TAC[NORM_NEG; GSYM VECTOR_SUB] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Regularity from second-order jets: C^2, the iterated partials of length  *)
(* at most 2 in terms of the jet coefficients, and the Laplacian 4 q.        *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_LINEAR_RE_MUL = prove
 (`!h. linear (\z. lift(Re(z * h)))`,
  GEN_TAC THEN REWRITE_TAC[linear; COMPLEX_ADD_RDISTRIB; RE_ADD; LIFT_ADD; COMPLEX_CMUL] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; LIFT_CMUL]);;

let WANL_PT_C2_FROM_DERIVS = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real).
     open s /\
     (!x. x IN s ==> ((\x. lift(w x)) has_derivative (\h. lift(Re(a1 x * h)))) (at x)) /\
     (!x. x IN s ==> (a1 has_derivative (\h. Cx(&2) * a2 x * h + Cx(&2 * q x) * cnj h)) (at x)) /\
     a2 continuous_on s /\ (\x. lift(q x)) continuous_on s
     ==> continuously_differentiable 2 s (\x. lift(w x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[num_CONV `2`] THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\(x:real^2) h. lift(Re((a1:real^2->complex) x * h))` THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `h:complex` THEN
  REWRITE_TAC[num_CONV `1`] THEN ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\(x:real^2) k. lift(Re((Cx(&2) * (a2:real^2->complex) x * k +
                                      Cx(&2 * (q:real^2->real) x) * cnj k) * h))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a1:real^2->complex`; `\z:complex. lift(Re(z * h))`;
                   `\k. Cx(&2) * (a2:real^2->complex) x * k + Cx(&2 * (q:real^2->real) x) * cnj k`;
                   `\z:complex. lift(Re(z * h))`; `x:real^2`] DIFF_CHAIN_AT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[WANL_PT_LINEAR_RE_MUL];
      REWRITE_TAC[o_DEF]];
    X_GEN_TAC `k:complex` THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    ONCE_REWRITE_TAC[GSYM CONTINUOUS_ON_CX_LIFT] THEN
    SUBGOAL_THEN
     `(\x:real^2. Cx(Re((Cx(&2) * (a2:real^2->complex) x * k +
                         Cx(&2 * (q:real^2->real) x) * cnj k) * h))) =
      (Cx o Re) o (\x. (Cx(&2) * a2 x * k + Cx(&2 * q x) * cnj k) * h)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CX_RE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_RMUL THEN REWRITE_TAC[CX_MUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CX_LIFT]]]);;

let WANL_PT_ITP2 = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (D:complex->complex) x i j.
     open s /\ x IN s /\
     (!y. y IN s ==> ((\x. lift(w x)) has_derivative (\h. lift(Re(a1 y * h)))) (at y)) /\
     (a1 has_derivative D) (at x)
     ==> iterated_partial [] (\x. lift(w x)) x = lift(w x) /\
         iterated_partial [i] (\x. lift(w x)) x = lift(Re(a1 x * basis i)) /\
         iterated_partial [j; i] (\x. lift(w x)) x = lift(Re(D(basis j) * basis i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[iterated_partial] THENL
   [MP_TAC(ISPECL [`i:num`; `\x:real^2. lift((w:real^2->real) x)`;
                   `\h. lift(Re((a1:real^2->complex) x * h))`; `x:real^2`]
          PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative j (\y. lift(Re((a1:real^2->complex) y * basis i))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`i:num`; `\x:real^2. lift((w:real^2->real) x)`;
                   `\h. lift(Re((a1:real^2->complex) y * h))`; `y:real^2`]
          PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:num`; `\y:real^2. lift(Re((a1:real^2->complex) y * basis i))`;
                 `\k. lift(Re((D:complex->complex) k * basis i))`; `x:real^2`]
        PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MP_TAC(ISPECL [`a1:real^2->complex`; `\z:complex. lift(Re(z * basis i))`;
                 `D:complex->complex`; `\z:complex. lift(Re(z * basis i))`; `x:real^2`]
        DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[WANL_PT_LINEAR_RE_MUL];
    REWRITE_TAC[o_DEF]]);;

let WANL_PT_LIST_LE2 = prove
 (`!l:(num)list. LENGTH l <= 2
       ==> l = [] \/ (?i. l = [i]) \/ (?i j. l = [j; i])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  SPEC_TAC(`t:(num)list`,`t:(num)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[CONS_11; NOT_CONS_NIL] THENL [MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`t':(num)list`,`t':(num)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[CONS_11; NOT_CONS_NIL; LENGTH] THENL [MESON_TAC[]; ARITH_TAC]);;

(* Copy of the proof of LLAP_FLAT (pc_lrg_lap), without the smoothness    *)
(* hypothesis, which that proof does not use.                              *)

let WANL_PT_LLAP_FLAT0 = prove
 (`!f (y:real^N).
        llap (\z. mat 1) f y =
        sum(1..dimindex(:N))
          (\i. drop(partial_derivative i (partial_derivative i (\z. lift(f z))) y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
  REWRITE_TAC[llap; LRG_CHRISTOFFEL_CONST; MATRIX_INV_I; VEC_COMPONENT;
              REAL_MUL_LZERO; SUM_0; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\j. if j = i
          then drop(frechet_derivative
                     (\z. frechet_derivative (\w. lift((f:real^N->real) w))
                                             (at z) (basis i))
                     (at y) (basis i))
          else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[MAT_COMPONENT] THEN
    ASM_CASES_TAC `i:num = j` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LID];
      SUBGOAL_THEN `~(j:num = i)` (fun th -> ASM_REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]);;

let WANL_PT_JET2_A2_CONT = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 sg Hq.
     open s /\ &0 < rho0 /\ &0 <= K /\ &2 < sg /\
     (!x y. x IN s /\ y IN s ==> abs(q x - q y) <= Hq * norm(x - y) rpow (sg - &2)) /\
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                     (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
                 <= K * norm(x - x0) rpow sg)
     ==> a2 continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PT_HOLDER_CONT THEN
  MAP_EVERY EXISTS_TAC [`&2 * K * (&2 rpow sg + &2) + &2 * Hq`; `sg - &2`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:real^2` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d1 / &3) (rho0 / &2)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^2. norm(z - x0) < d1 ==> z IN s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real`; `a1:real^2->complex`;
                 `a2:real^2->complex`; `q:real^2->real`; `K:real`; `rho0:real`; `sg:real`;
                 `x0:real^2`; `y:real^2`] WANL_PT_JET_HESS2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real^2` THEN DISCH_TAC THEN
    ABBREV_TAC `dd = norm(y - x0:real^2)` THEN
    SUBGOAL_THEN `norm(dd % e:real^2) = dd` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN EXPAND_TAC "dd" THEN
      REWRITE_TAC[REAL_ABS_NORM];
      ALL_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
     [SUBGOAL_THEN `(y + dd % e) - x0:real^2 = (y - x0) + dd % e` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`y - x0:real^2`; `dd % e:real^2`] NORM_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(y - dd % e) - x0:real^2 = (y - x0) - dd % e` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`y - x0:real^2`; `--(dd % e):real^2`] NORM_TRIANGLE) THEN
      REWRITE_TAC[NORM_NEG; GSYM VECTOR_SUB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `x0:real^2`] o check (fun th ->
    can (find_term (fun t -> t = `Hq:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= y' ==> x + y <= x + y'`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REWRITE_TAC[]);;

let WANL_PT_JET2_REG = prove
 (`!(s:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 sg Hq.
     open s /\ &0 < rho0 /\ &0 <= K /\ &2 < sg /\
     (!x y. x IN s /\ y IN s ==> abs(q x - q y) <= Hq * norm(x - y) rpow (sg - &2)) /\
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                     (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
                 <= K * norm(x - x0) rpow sg)
     ==> continuously_differentiable 2 s (\x. lift(w x)) /\
         (!x i j. x IN s
                  ==> iterated_partial [] (\x. lift(w x)) x = lift(w x) /\
                      iterated_partial [i] (\x. lift(w x)) x = lift(Re(a1 x * basis i)) /\
                      iterated_partial [j; i] (\x. lift(w x)) x =
                      lift(Re((Cx(&2) * a2 x * basis j + Cx(&2 * q x) * cnj(basis j)) *
                              basis i))) /\
         (!x. x IN s ==> llap (\y. mat 1) w x = &4 * q x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s ==> ((\x. lift((w:real^2->real) x)) has_derivative
                    (\h. lift(Re((a1:real^2->complex) x * h)))) (at x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC WANL_PT_JET2_DERIV_W THEN
    MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `a2:real^2->complex`; `q:real^2->real`;
                          `K:real`; `rho0:real`; `sg:real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> ((a1:real^2->complex) has_derivative
                    (\h. Cx(&2) * (a2:real^2->complex) x * h + Cx(&2 * (q:real^2->real) x) * cnj h))
                   (at x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC WANL_PT_JET2_DERIV_A1 THEN
    MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `w:real^2->real`; `K:real`; `rho0:real`;
                          `sg:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a2:real^2->complex) continuous_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC WANL_PT_JET2_A2_CONT THEN
    MAP_EVERY EXISTS_TAC [`w:real^2->real`; `a1:real^2->complex`; `q:real^2->real`;
                          `K:real`; `rho0:real`; `sg:real`; `Hq:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((q:real^2->real) x)) continuous_on s` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTINUOUS_ON_CX_LIFT] THEN MATCH_MP_TAC WANL_PT_HOLDER_CONT THEN
    MAP_EVERY EXISTS_TAC [`Hq:real`; `sg - &2`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x i j. x IN s
            ==> iterated_partial [] (\x. lift((w:real^2->real) x)) x = lift(w x) /\
                iterated_partial [i] (\x. lift(w x)) x =
                lift(Re((a1:real^2->complex) x * basis i)) /\
                iterated_partial [j; i] (\x. lift(w x)) x =
                lift(Re((Cx(&2) * (a2:real^2->complex) x * basis j +
                         Cx(&2 * (q:real^2->real) x) * cnj(basis j)) * basis i))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real`; `a1:real^2->complex`;
                   `\h. Cx(&2) * (a2:real^2->complex) x * h + Cx(&2 * (q:real^2->real) x) * cnj h`;
                   `x:real^2`; `i:num`; `j:num`] WANL_PT_ITP2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WANL_PT_C2_FROM_DERIVS THEN
    MAP_EVERY EXISTS_TAC [`a1:real^2->complex`; `a2:real^2->complex`; `q:real^2->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[WANL_PT_LLAP_FLAT0; DIMINDEX_2; SUM_2] THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (partial_derivative i (\y. lift((w:real^2->real) y))) x =
        lift(Re((Cx(&2) * (a2:real^2->complex) x * basis i +
                 Cx(&2 * (q:real^2->real) x) * cnj(basis i)) * basis i))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `i:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[iterated_partial] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; COMPLEX_BASIS; CNJ_CX; CNJ_II; COMPLEX_MUL_RID] THEN
  SUBGOAL_THEN
   `(Cx(&2) * (a2:real^2->complex) x * ii + Cx(&2 * (q:real^2->real) x) * --ii) * ii =
    --(Cx(&2) * a2 x) + Cx(&2 * q x)`
  SUBST1_TAC THENL
   [MP_TAC COMPLEX_POW_II_2 THEN REWRITE_TAC[COMPLEX_POW_2] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[RE_ADD; RE_NEG; RE_MUL_CX; RE_CX] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Mollified second-order jets (WANL_PT_EXPAND with N = 2 and c = f_e(x0))  *)
(* and their limit: a function w = u a.e. on ball(a,R1) with uniform        *)
(* quadratic expansions whose |z|^2 coefficient is f(x0)/4.                  *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_SCH_CONST = prove
 (`!al r rho0 U A.
     &0 < al /\ al < &1 /\ &0 < rho0 /\ rho0 <= r /\ &0 <= U /\ &0 <= A
     ==> ((U + A * rho0 pow 2 / &4) / rho0 rpow (&2 + al) + A / r rpow al) *
         rho0 rpow (&2 + al) <= &2 * (U + A * rho0 pow 2) /\
         rho0 rpow (&2 + al - &1) = rho0 rpow (&2 + al) / rho0 /\
         rho0 rpow (&2 + al - &2) = rho0 rpow (&2 + al) / rho0 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rho0 rpow (&2 + al) = rho0 pow 2 * rho0 rpow al` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_ADD; RPOW_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho0 rpow al /\ &0 < r rpow al /\ rho0 rpow al <= r rpow al`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_POS_LT] THEN MATCH_MP_TAC RPOW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho0 pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_ARITH `&2 + al - &1 = &1 + al`] THEN ASM_SIMP_TAC[RPOW_ADD] THEN
    REWRITE_TAC[RPOW_POW] THEN
    UNDISCH_TAC `&0 < rho0` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_ARITH `&2 + al - &2 = al`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < rho0 pow 2` THEN CONV_TAC REAL_FIELD] THEN
  SUBGOAL_THEN `&0 < rho0 rpow (&2 + al)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&2 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al) =
                &2 * ((U + A * rho0 pow 2) / rho0 rpow (&2 + al))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `A / r rpow al <= (A * rho0 pow 2) / (rho0 pow 2 * rho0 rpow al)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(A * rho0 pow 2) / (rho0 pow 2 * rho0 rpow al) = A / rho0 rpow al`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < rho0 rpow al`; `&0 < rho0 pow 2`] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(U + A * rho0 pow 2 / &4) / (rho0 pow 2 * rho0 rpow al) +
              (A * rho0 pow 2) / (rho0 pow 2 * rho0 rpow al)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho0 pow 2 * rho0 rpow al` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ABBREV_TAC `R = inv(rho0 pow 2 * rho0 rpow al)` THEN
  ABBREV_TAC `P = A * rho0 pow 2` THEN
  SUBGOAL_THEN `&0 <= R * (U + &3 / &4 * P)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      SUBGOAL_THEN `&0 <= P` MP_TAC THENL
       [EXPAND_TAC "P" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

let WANL_PT_SCH_JETS = prove
 (`!al. &0 < al /\ al < &1
        ==> ?C1. &0 < C1 /\
             !(a:real^2) r (u:real^2->real) (f:real^2->real) U A e x0 rho0.
                &0 < r /\ &0 < rho0 /\ rho0 <= r /\ &0 < e /\ e <= rho0 /\
                dist(a,x0) + &3 * rho0 <= r /\ &0 <= U /\ &0 <= A /\
                (\x. lift(u x)) measurable_on ball(a,r) /\
                (\x. lift(f x)) measurable_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                (!x. x IN ball(a,r) ==> abs(f x) <= A) /\
                (!x y. x IN ball(a,r) /\ y IN ball(a,r)
                       ==> r rpow al * abs(f x - f y) <= A * norm(x - y) rpow al) /\
                (!phi. wan_test (ball(a,r)) phi
                       ==> integral (ball(a,r)) (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                           integral (ball(a,r)) (\x. lift(f x * phi x)))
                ==> ?c1 c2. norm c1 <= C1 * (U + A * rho0 pow 2) / rho0 /\
                            norm c2 <= C1 * (U + A * rho0 pow 2) / rho0 pow 2 /\
                            !x. norm(x - x0) <= rho0
                                ==> abs(wanl_pt_me e (ball(a,r)) u x -
                                        wanl_pt_me e (ball(a,r)) u x0 - Re(c1 * (x - x0)) -
                                        (Re(c2 * (x - x0) pow 2) +
                                         wanl_pt_me e (ball(a,r)) f x0 / &4 *
                                         norm(x - x0) pow 2))
                                    <= (C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al)) *
                                       norm(x - x0) rpow (&2 + al)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `al:real`] WANL_PT_EXPAND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ex"))) THEN
  EXISTS_TAC `&2 * C0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable(ball(a:real^2,r))` ASSUME_TAC THENL
   [REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. lift(wanl_pt_me e (ball(a:real^2,r)) u x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WANL_PT_ME_SMOOTH THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. abs(wanl_pt_me e (ball(a:real^2,r)) u x) <= U` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. abs(wanl_pt_me e (ball(a:real^2,r)) f x) <= A` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. norm(x - x0) < &2 * rho0 ==> cball(x,e) SUBSET ball(a,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `dist(x0:real^2,x) < &2 * rho0` MP_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist]; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^2`; `x0:real^2`; `x:real^2`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`a:real^2`; `x:real^2`; `y:real^2`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(x0:real^2,e) SUBSET ball(a,r)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r rpow al` ASSUME_TAC THENL [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  (* the Laplacian of the mollified solution and its Hoelder bound *)
  SUBGOAL_THEN
   `!x. norm(x - x0:real^2) < &2 * rho0
        ==> llap (\y:real^2. mat 1) (wanl_pt_me e (ball(a,r)) u) x =
            wanl_pt_me e (ball(a,r)) f x /\
            abs(wanl_pt_me e (ball(a,r)) f x - wanl_pt_me e (ball(a,r)) f x0)
            <= A / r rpow al * norm(x - x0) rpow al`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cball(x:real^2,e) SUBSET ball(a,r)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x:real^2. norm(x - x0) < &2 * rho0 ==> cball(x,e) SUBSET ball(a,r)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WANL_PT_ME_LAP THEN
      MAP_EVERY EXISTS_TAC [`U:real`; `A:real`] THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    MATCH_MP_TAC WANL_PT_ME_HOLDER THEN EXISTS_TAC `A:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x - z:real^2) IN ball(a,r) /\ (x0 - z:real^2) IN ball(a,r)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME `cball(x:real^2,e) SUBSET ball(a,r)`));
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME `cball(x0:real^2,e) SUBSET ball(a,r)`))] THEN
      REWRITE_TAC[IN_CBALL; dist; VECTOR_ARITH `x - (x - z):real^2 = z`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x - z:real^2`; `x0 - z:real^2`] o check (fun th ->
      can (find_term (fun t -> t = `rpow`)) (concl th) &&
      can (find_term (fun t -> t = `f:real^2->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x - z) - (x0 - z):real^2 = x - x0`] THEN
    DISCH_TAC THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `A * i * n = (A * n) * i`] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = wanl_pt_me e (ball(a:real^2,r)) u` THEN
  ABBREV_TAC `fe = wanl_pt_me e (ball(a:real^2,r)) f` THEN
  ABBREV_TAC `Ah = A / r rpow al` THEN
  SUBGOAL_THEN `&0 <= Ah` ASSUME_TAC THENL
   [EXPAND_TAC "Ah" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  USE_THEN "ex" (MP_TAC o SPECL [`ball(x0:real^2,&2 * rho0)`; `v:real^2->real`;
                                 `(fe:real^2->real) x0`; `x0:real^2`; `rho0:real`; `Ah:real`;
                                 `U + A * rho0 pow 2 / &4`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MAP_EVERY X_GEN_TAC [`rho:real`; `x:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `norm(x - x0:real^2) < rho` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^2) IN ball(x0,rho)` THEN REWRITE_TAC[IN_BALL; dist] THEN
        MESON_TAC[NORM_SUB];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "llap")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&2 + al - &2 = al`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ah * norm(x - x0:real^2) rpow al` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(x - x0:real^2) pow 2 <= rho0 pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
        ALL_TAC] THEN
      SUBGOAL_THEN `abs((fe:real^2->real) x0 / &4 * norm(x - x0:real^2) pow 2)
                    <= A * rho0 pow 2 / &4` ASSUME_TAC THENL
       [SUBGOAL_THEN `abs((fe:real^2->real) x0) * norm(x - x0:real^2) pow 2 <= A * rho0 pow 2`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2];
          ALL_TAC] THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NORM; REAL_ABS_NUM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> t = `v:real^2->real`)) (concl th) && is_forall(concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "llap")) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cf:num->complex`
    (CONJUNCTS_THEN2 (LABEL_TAC "cb") (LABEL_TAC "cx"))) THEN
  MP_TAC(SPECL [`al:real`; `r:real`; `rho0:real`; `U:real`; `A:real`] WANL_PT_SCH_CONST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = rho0 rpow (&2 + al)` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `S0 = (U + A * rho0 pow 2 / &4) / R + Ah` THEN
  ABBREV_TAC `W = U + A * rho0 pow 2` THEN
  SUBGOAL_THEN `!z. &0 < z ==> C0 * S0 * (R / z) <= (&2 * C0) * W / z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `C0 * S0 * (R / z) = (C0 * (S0 * R)) / z /\
                  (&2 * C0) * W / z = (C0 * (&2 * W)) / z`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[real_div] THEN CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `(cf:num->complex) 1` THEN EXISTS_TAC `(cf:num->complex) 2` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "cb" (MP_TAC o SPEC `1`) THEN REWRITE_TAC[ARITH_RULE `1 <= 2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "cb" (MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH_RULE `2 <= 2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  USE_THEN "cx" (fun th -> MP_TAC(SPEC `x:real^2` th) THEN MP_TAC(SPEC `x0:real^2` th)) THEN
  REWRITE_TAC[IN_CBALL; DIST_REFL; VECTOR_SUB_REFL; NORM_0] THEN
  ASM_SIMP_TAC[RPOW_ZERO; REAL_ARITH `&0 < al ==> ~(&2 + al = &0)`; REAL_MUL_RZERO;
               REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wanl_pt_hp] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ARITH; VSUM_TRIV_NUMSEG] THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_MUL_RID; VECTOR_SUB_REFL; RE_ADD] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; COMPLEX_MUL_LZERO; RE_CX; REAL_ADD_RID;
              COMPLEX_ADD_RID; COMPLEX_POW_2] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `D = norm(x - x0:real^2) rpow (&2 + al)` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `C0 * S0 * D <= ((&2 * C0) * W / R) * D` MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&2 * C0) * W / R = C0 * (&2 * W) / R` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_RDIV_EQ];
    ASM_REAL_ARITH_TAC]);;

let WANL_PT_EM_NULL = prove
 (`!rho0. ((\m. lift(rho0 / (&m + &1))) --> vec 0) sequentially`,
  GEN_TAC THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\m. abs rho0 * inv(&m)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_DIV; real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(&n + &1) = &n + &1` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
    REWRITE_TAC[SEQ_HARMONIC]]);;

let WANL_PT_ME_HOLDER_LIM = prove
 (`!(s:real^N->bool) g M H al x0 (em:num->real).
     lebesgue_measurable s /\ (\x. lift(g x)) measurable_on s /\
     (!x. x IN s ==> abs(g x) <= M) /\ &0 < al /\ (!m. &0 < em m) /\
     ((\m. lift(em m)) --> vec 0) sequentially /\
     (!m. cball(x0,em m) SUBSET s) /\
     (!y. y IN s ==> abs(g y - g x0) <= H * norm(y - x0) rpow al)
     ==> ((\m. lift(wanl_pt_me (em m) s g x0)) --> lift(g x0)) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIM_NULL] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\m:num. abs H * (em:num->real) m rpow al` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN MATCH_MP_TAC WANL_PT_ME_CLOSE THEN
    EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_CBALL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `H * norm(y - x0:real^N) rpow al` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs H * norm(y - x0:real^N) rpow al` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
      MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC RPOW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      CONJ_TAC THENL [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist];
                      ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_CMUL THEN
    MP_TAC(ISPECL [`sequentially`; `al:real`; `em:num->real`] LIM_NULL_RPOW) THEN
    ASM_REWRITE_TAC[o_DEF]]);;

let WANL_PT_SCH_LIMIT = prove
 (`!al. &0 < al /\ al < &1
        ==> ?C1. &0 < C1 /\
             !(a:real^2) r (u:real^2->real) (f:real^2->real) U A rho0 R1.
                &0 < r /\ &0 < rho0 /\ rho0 <= r /\ &0 < R1 /\ R1 + &3 * rho0 <= r /\
                &0 <= U /\ &0 <= A /\
                (\x. lift(u x)) measurable_on ball(a,r) /\
                (\x. lift(f x)) measurable_on ball(a,r) /\
                (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                (!x. x IN ball(a,r) ==> abs(f x) <= A) /\
                (!x y. x IN ball(a,r) /\ y IN ball(a,r)
                       ==> r rpow al * abs(f x - f y) <= A * norm(x - y) rpow al) /\
                (!phi. wan_test (ball(a,r)) phi
                       ==> integral (ball(a,r)) (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                           integral (ball(a,r)) (\x. lift(f x * phi x)))
                ==> ?w a1 a2 t.
                      negligible t /\
                      (!x. x IN ball(a,R1) /\ ~(x IN t) ==> w x = u x) /\
                      (!x. x IN ball(a,R1) ==> abs(w x) <= U) /\
                      (!x0. x0 IN ball(a,R1)
                            ==> norm(a1 x0) <= C1 * (U + A * rho0 pow 2) / rho0 /\
                                norm(a2 x0) <= C1 * (U + A * rho0 pow 2) / rho0 pow 2) /\
                      (!x0 x. x0 IN ball(a,R1) /\ x IN ball(a,R1) /\ norm(x - x0) <= rho0
                              ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                                      (Re(a2 x0 * (x - x0) pow 2) +
                                       f x0 / &4 * norm(x - x0) pow 2))
                                  <= (C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al)) *
                                     norm(x - x0) rpow (&2 + al))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `al:real` WANL_PT_SCH_JETS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "jets"))) THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `em = \m. rho0 / (&m + &1)` THEN
  SUBGOAL_THEN `!m. &0 < (em:num->real) m /\ em m <= rho0` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "em" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &m + &1`] THEN
      SUBGOAL_THEN `rho0 * &1 <= rho0 * (&m + &1)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= U + A * rho0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al) /\
    &0 <= C1 * (U + A * rho0 pow 2) / rho0 /\
    &0 <= C1 * (U + A * rho0 pow 2) / rho0 pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c1 c2:num->real^2->complex.
      !m x0. x0 IN ball(a,R1)
             ==> norm(c1 m x0) <= C1 * (U + A * rho0 pow 2) / rho0 /\
                 norm(c2 m x0) <= C1 * (U + A * rho0 pow 2) / rho0 pow 2 /\
                 !x. norm(x - x0) <= rho0
                     ==> abs(wanl_pt_me ((em:num->real) m) (ball(a,r)) u x -
                             wanl_pt_me (em m) (ball(a,r)) u x0 - Re(c1 m x0 * (x - x0)) -
                             (Re(c2 m x0 * (x - x0) pow 2) +
                              wanl_pt_me (em m) (ball(a,r)) f x0 / &4 * norm(x - x0) pow 2))
                         <= (C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al)) *
                            norm(x - x0) rpow (&2 + al)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MAP_EVERY X_GEN_TAC [`m:num`; `x0:real^2`] THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "jets" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x0:real^2) IN ball(a,R1)` THEN REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real`; `U:real`] WANL_PT_ME_AE) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(a:real^2,R1) SUBSET ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r rpow al` ASSUME_TAC THENL [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x0. x0 IN ball(a:real^2,R1)
         ==> ((\m. lift(wanl_pt_me ((em:num->real) m) (ball(a,r)) f x0 / &4)) -->
              lift(f x0 / &4)) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!z. lift(z / &4) = inv(&4) % lift z` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_CMUL THEN MATCH_MP_TAC WANL_PT_ME_HOLDER_LIM THEN
    MAP_EVERY EXISTS_TAC [`A:real`; `A / r rpow al`; `al:real`] THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "em" THEN REWRITE_TAC[WANL_PT_EM_NULL];
      X_GEN_TAC `m:num` THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      UNDISCH_TAC `(x0:real^2) IN ball(a,R1)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^2`; `x0:real^2`; `y:real^2`] DIST_TRIANGLE) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
        can (find_term (fun t -> t = `em:num->real`)) (concl th) && is_forall(concl th) &&
        not(can (find_term (fun t -> t = `c1:num->real^2->complex`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x0:real^2) IN ball(a,r)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `x0:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `rpow`)) (concl th) &&
        can (find_term (fun t -> t = `f:real^2->real`)) (concl th) &&
        not(can (find_term (fun t -> t = `c1:num->real^2->complex`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `A * i * n = (A * n) * i`] THEN
      REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al)` THEN
  ABBREV_TAC `G1 = C1 * (U + A * rho0 pow 2) / rho0` THEN
  ABBREV_TAC `G2 = C1 * (U + A * rho0 pow 2) / rho0 pow 2` THEN
  MP_TAC(ISPECL [`ball(a:real^2,R1)`; `t:real^2->bool`;
                 `\m x. wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) u x`;
                 `u:real^2->real`; `c1:num->real^2->complex`; `c2:num->real^2->complex`;
                 `\m x0. wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) f x0 / &4`;
                 `Kc:real`; `G1 + G2 + A`; `rho0:real`; `&2 + al`] WANL_PT_JET_LIMIT_CORE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
      X_GEN_TAC `ep:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `ep:real`] o check (fun th ->
        can (find_term (fun t -> t = `t:real^2->bool`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `rho0 / d` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "em" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      UNDISCH_TAC `rho0 / d <= &N` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
      SUBGOAL_THEN `d * &N <= d * &n` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
        ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`m:num`; `x0:real^2`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `x0:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `c1:num->real^2->complex`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs(wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) f x0) <= A`
      MP_TAC THENL
       [MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_MESON_TAC[LEBESGUE_MEASURABLE_BALL];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`m:num`; `x0:real^2`; `x:real^2`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `x0:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `c1:num->real^2->complex`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC WANL_PT_C2_CAUCHY THEN
      MAP_EVERY EXISTS_TAC [`ball(a:real^2,R1)`;
                            `\m x. wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) u x`;
                            `\m. (c1:num->real^2->complex) m x0`;
                            `\m. wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) f x0 / &4`;
                            `Kc:real`; `rho0:real`; `&2 + al`; `x0:real^2`] THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        EXISTS_TAC `lift((f:real^2->real) x0 / &4)` THEN ASM_SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`m:num`; `x:real^2`] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `x0:real^2`] o check (fun th ->
          can (find_term (fun t -> t = `c1:num->real^2->complex`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
      EXISTS_TAC `lift((f:real^2->real) x0 / &4)` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `a1:real^2->complex`
    (X_CHOOSE_THEN `a2:real^2->complex` (X_CHOOSE_THEN `aq:real^2->real`
      (STRIP_ASSUME_TAC o BETA_RULE))))) THEN
  SUBGOAL_THEN `!x0. x0 IN ball(a:real^2,R1) ==> (aq:real^2->real) x0 = f x0 / &4`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(MESON[LIFT_DROP] `lift a = lift b ==> a = b`) THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\m. lift(wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) f x0 / &4)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`w:real^2->real`; `a1:real^2->complex`; `a2:real^2->complex`;
                        `t:real^2->bool`] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NORM_LIFT] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\m. lift(wanl_pt_me ((em:num->real) m) (ball(a:real^2,r)) u x)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
    MATCH_MP_TAC WANL_PT_ME_BOUND THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
    X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THENL
     [EXISTS_TAC `\m. (c1:num->real^2->complex) m x0`;
      EXISTS_TAC `\m. (c2:num->real^2->complex) m x0`] THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `m:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `x0:real^2`] o check (fun th ->
      can (find_term (fun t -> t = `c1:num->real^2->complex`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wanl_pt_me")) (concl th))) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`x0:real^2`; `x:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^2->real) x0 / &4 = aq x0` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The C^(2,al) bounds (wan_ckal with k = 2) from the jet coefficients, the *)
(* Hoelder bound of the quadratic coefficient on an inner set, and the       *)
(* constant bookkeeping of the theta form.                                   *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_D2_BOUND = prove
 (`!(a:complex) (q:real) (b:complex) (b':complex).
     norm b = &1 /\ norm b' = &1
     ==> abs(Re((Cx(&2) * a * b + Cx(&2 * q) * cnj b) * b')) <= &2 * norm a + &2 * abs q`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((Cx(&2) * a * b + Cx(&2 * q) * cnj b) * b')` THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(Cx(&2) * a * b) + norm(Cx(&2 * q) * cnj b)` THEN
  REWRITE_TAC[NORM_TRIANGLE] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_LE_REFL]);;

let WANL_PT_D2_SUB = prove
 (`!(a:complex) a' (q:real) q' (b:complex) (b':complex).
     lift(Re((Cx(&2) * a * b + Cx(&2 * q) * cnj b) * b')) -
     lift(Re((Cx(&2) * a' * b + Cx(&2 * q') * cnj b) * b')) =
     lift(Re((Cx(&2) * (a - a') * b + Cx(&2 * (q - q')) * cnj b) * b'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LIFT_SUB; GSYM RE_SUB] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CX_MUL; CX_SUB] THEN CONV_TAC COMPLEX_RING);;

let WANL_PT_CKAL2 = prove
 (`!(S:real^2->bool) (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) al r U A G1 G2 H B.
     &0 < r /\
     (!x i j. x IN S
              ==> iterated_partial [] (\x. lift(w x)) x = lift(w x) /\
                  iterated_partial [i] (\x. lift(w x)) x = lift(Re(a1 x * basis i)) /\
                  iterated_partial [j; i] (\x. lift(w x)) x =
                  lift(Re((Cx(&2) * a2 x * basis j + Cx(&2 * q x) * cnj(basis j)) *
                          basis i))) /\
     (!x. x IN S ==> abs(w x) <= U /\ norm(a1 x) <= G1 /\ norm(a2 x) <= G2 /\
                     abs(q x) <= A / &4) /\
     (!x y. x IN S /\ y IN S
            ==> norm(a2 x - a2 y) <= H * norm(x - y) rpow al /\
                r rpow al * abs(q x - q y) <= A / &4 * norm(x - y) rpow al) /\
     U <= B /\ r * G1 <= B /\ r pow 2 * (&2 * G2 + A / &2) <= B /\
     &2 * H * r rpow (&2 + al) + r pow 2 * A / &2 <= B
     ==> wan_ckal S 2 al r (\x. lift(w x)) B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_ckal; DIMINDEX_2] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2 ==> norm(basis i:complex) = &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_BASIS THEN ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r rpow al /\ &0 <= r pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_POW_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^2`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WANL_PT_LIST_LE2) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `1`; `1`] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
            (concl th))) THEN
      ASM_REWRITE_TAC[LENGTH; real_pow; REAL_MUL_LID; NORM_LIFT] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `U:real` THEN ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= 2) [i]` THEN REWRITE_TAC[ALL] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `i:num`; `1`] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
            (concl th))) THEN
      ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NORM_LIFT; REAL_POW_1] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r * G1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((a1:real^2->complex) x * basis i)` THEN
      REWRITE_TAC[COMPLEX_NORM_GE_RE_IM; COMPLEX_NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_RID];
      DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)) THEN
      UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= 2) [j; i]` THEN REWRITE_TAC[ALL] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `i:num`; `j:num`] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
            (concl th))) THEN
      ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `r pow 2 * (&2 * G2 + A / &2)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * norm((a2:real^2->complex) x) + &2 * abs((q:real^2->real) x)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC WANL_PT_D2_BOUND THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> t = `G2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:(num)list`; `x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `l:(num)list` WANL_PT_LIST_LE2) THEN ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `LENGTH([]:(num)list) = 2` THEN
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `LENGTH [i:num] = 2` THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= 2) [j; i]` THEN REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real^2`; `i:num`; `j:num`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
        (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `i:num`; `j:num`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WANL_PT_D2_SUB; NORM_LIFT] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
    can (find_term (fun t -> t = `H:real`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(a2:real^2->complex) x - a2 y`; `(q:real^2->real) x - q y`;
                 `basis j:complex`; `basis i:complex`] WANL_PT_D2_BOUND) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `D = norm(x - y:real^2) rpow al` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (&2 + al) = r pow 2 * r rpow al` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_ADD; RPOW_POW]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `r rpow (&2 + al) * (&2 * norm((a2:real^2->complex) x - a2 y) +
                                  &2 * abs((q:real^2->real) x - q y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * H * r rpow (&2 + al) + r pow 2 * A / &2) * D` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `r rpow (&2 + al) * norm((a2:real^2->complex) x - a2 y) <=
                r rpow (&2 + al) * (H * D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 * (r rpow al * abs((q:real^2->real) x - q y)) <=
                r pow 2 * (A / &4 * D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `r rpow (&2 + al) * norm((a2:real^2->complex) x - a2 y) <=
               r rpow (&2 + al) * (H * D)` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `r pow 2 * (r rpow al * abs((q:real^2->real) x - q y)) <=
                                      r pow 2 * (A / &4 * D)` THEN
  REAL_ARITH_TAC);;

let WANL_PT_A2_HOLDER = prove
 (`!(s:real^2->bool) S (w:real^2->real) (a1:real^2->complex) (a2:real^2->complex)
    (q:real^2->real) K rho0 al Hq G2.
     &0 < rho0 /\ &0 <= K /\ &0 < al /\ al < &1 /\ &0 <= G2 /\ &0 <= Hq /\
     S SUBSET s /\
     (!x y e. x IN S /\ y IN S /\ norm(y - x) <= rho0 / &2 /\ norm e = &1
              ==> y + norm(y - x) % e IN s /\ y - norm(y - x) % e IN s) /\
     (!x. x IN S ==> norm(a2 x) <= G2) /\
     (!x y. x IN s /\ y IN s ==> abs(q x - q y) <= Hq * norm(x - y) rpow al) /\
     (!x0 x. x0 IN s /\ x IN s /\ norm(x - x0) <= rho0
             ==> abs(w x - w x0 - Re(a1 x0 * (x - x0)) -
                     (Re(a2 x0 * (x - x0) pow 2) + q x0 * norm(x - x0) pow 2))
                 <= K * norm(x - x0) rpow (&2 + al))
     ==> !x y. x IN S /\ y IN S
               ==> norm(a2 x - a2 y) <=
                   (&20 * K + &2 * Hq + &4 * G2 / rho0 rpow al) * norm(x - y) rpow al`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
  STRIP_TAC THEN ABBREV_TAC `d = norm(y - x:real^2)` THEN
  SUBGOAL_THEN `norm(x - y:real^2) = d` SUBST1_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[NORM_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [EXPAND_TAC "d" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d rpow al /\ &0 < rho0 rpow al` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LE; RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= G2 / rho0 rpow al` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN s /\ (y:real^2) IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `d <= rho0 / &2` THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `w:real^2->real`; `a1:real^2->complex`;
                   `a2:real^2->complex`; `q:real^2->real`; `K:real`; `rho0:real`; `&2 + al`;
                   `x:real^2`; `y:real^2`] WANL_PT_JET_HESS2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        X_GEN_TAC `e:real^2` THEN DISCH_TAC THEN EXPAND_TAC "d" THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(&2 + al) - &2 = al`] THEN
    SUBGOAL_THEN `&2 rpow (&2 + al) <= &8` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow &3` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[RPOW_POW] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((q:real^2->real) y - q x) <= Hq * d rpow al` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `x:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `Hq:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * K * (&2 rpow (&2 + al) + &2) * d rpow al <= (&20 * K) * d rpow al`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(&2 * K) * x = K * (&2 * x)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&20 * K = K * &20`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&4 * G2 / rho0 rpow al) * d rpow al` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    SUBGOAL_THEN `(&2 * Hq) * d rpow al = &2 * (Hq * d rpow al)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((a2:real^2->complex) x - a2 y) <= &2 * G2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((a2:real^2->complex) x) + norm((a2:real^2->complex) y)` THEN
    REWRITE_TAC[NORM_ARITH `!x y:real^2. norm(x - y) <= norm x + norm y`] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= g /\ b <= g ==> a + b <= &2 * g`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho0 rpow al <= &2 * d rpow al` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * d) rpow al` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_MUL; REAL_POS] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * G2 <= (&4 * G2 / rho0 rpow al) * d rpow al` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&4 * G2 / rho0 rpow al) * d rpow al =
                  (&2 * G2) * ((&2 * d rpow al) / rho0 rpow al)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&20 * K) * d rpow al /\ &0 <= (&2 * Hq) * d rpow al`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let WANL_PT_SCH0_CONST = prove
 (`!al C1 r U A rho0 Tt.
     &0 < al /\ al < &1 /\ &0 < C1 /\ &0 < rho0 /\ &0 <= U /\ &0 <= A /\ &1 <= Tt /\
     r = Tt * rho0
     ==> U <= (&2 + &50 * C1 * Tt pow 3) * (r pow 2 * A + U) /\
         r * (C1 * (U + A * rho0 pow 2) / rho0)
         <= (&2 + &50 * C1 * Tt pow 3) * (r pow 2 * A + U) /\
         r pow 2 * (&2 * (C1 * (U + A * rho0 pow 2) / rho0 pow 2) + A / &2)
         <= (&2 + &50 * C1 * Tt pow 3) * (r pow 2 * A + U) /\
         &2 * (&20 * (C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al)) +
               &2 * (A / (&4 * r rpow al)) +
               &4 * (C1 * (U + A * rho0 pow 2) / rho0 pow 2) / rho0 rpow al) *
         r rpow (&2 + al) + r pow 2 * A / &2
         <= (&2 + &50 * C1 * Tt pow 3) * (r pow 2 * A + U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Tt` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ rho0 <= r` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `r = Tt * rho0`)) THEN
  SUBGOAL_THEN `&0 < rho0 rpow al /\ &0 < r rpow al /\ &0 < rho0 pow 2 /\
                &0 <= Tt rpow (&2 + al)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; REAL_POW_LT; RPOW_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (&2 + al) = Tt rpow (&2 + al) * rho0 pow 2 * rho0 rpow al /\
                r rpow (&2 + al) = r pow 2 * r rpow al`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(Tt * rho0) rpow (&2 + al)` THEN CONJ_TAC THENL
       [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[RPOW_MUL; REAL_LT_IMP_LE] THEN ASM_SIMP_TAC[RPOW_ADD; RPOW_POW];
      ASM_SIMP_TAC[RPOW_ADD; RPOW_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho0 rpow (&2 + al) = rho0 pow 2 * rho0 rpow al` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_ADD; RPOW_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `Tt rpow (&2 + al) <= Tt pow 3 /\ Tt <= Tt pow 3 /\ Tt pow 2 <= Tt pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM RPOW_POW] THEN MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN MATCH_MP_TAC REAL_POW_MONO THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `W = r pow 2 * A + U` THEN
  ABBREV_TAC `W0 = U + A * rho0 pow 2` THEN
  SUBGOAL_THEN `&0 <= W0 /\ W0 <= W /\ &0 <= r pow 2 * A` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "W0"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
      SUBGOAL_THEN `A * rho0 pow 2 <= A * r pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  ABBREV_TAC `P = C1 * W * Tt pow 3` THEN
  SUBGOAL_THEN `C1 * W0 * Tt <= P /\ C1 * W0 * Tt pow 2 <= P /\
                C1 * W0 * Tt rpow (&2 + al) <= P /\ &0 <= P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN
        NO_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 + &50 * C1 * Tt pow 3) * W = &2 * W + &50 * P` SUBST1_TAC THENL
   [EXPAND_TAC "P" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(rho0 = &0) /\ ~(rho0 rpow al = &0) /\ ~(r rpow al = &0) /\
                ~(rho0 pow 2 = &0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * (C1 * W0 / rho0) = C1 * W0 * Tt` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(Tt * rho0) * (C1 * W0 / rho0)` THEN
    CONJ_TAC THENL [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(rho0 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 * (&2 * (C1 * W0 / rho0 pow 2) + A / &2) =
                &2 * (C1 * W0 * Tt pow 2) + r pow 2 * A / &2` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `&2 * (C1 * W0 * (r pow 2 / rho0 pow 2)) + r pow 2 * A / &2` THEN
    CONJ_TAC THENL [UNDISCH_TAC `~(rho0 pow 2 = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 = Tt pow 2 * rho0 pow 2` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(Tt * rho0) pow 2` THEN CONJ_TAC THENL
       [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_POW_MUL]];
      ALL_TAC] THEN
    UNDISCH_TAC `~(rho0 pow 2 = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (&20 * (C1 * W0 / rho0 rpow (&2 + al)) + &2 * (A / (&4 * r rpow al)) +
          &4 * (C1 * W0 / rho0 pow 2) / rho0 rpow al) * r rpow (&2 + al) =
    &48 * (C1 * W0 * (r rpow (&2 + al) / (rho0 pow 2 * rho0 rpow al))) +
    A * (r rpow (&2 + al) / r rpow al)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`~(rho0 pow 2 = &0)`; `~(rho0 rpow al = &0)`; `~(r rpow al = &0)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (&2 + al) / (rho0 pow 2 * rho0 rpow al) = Tt rpow (&2 + al) /\
                r rpow (&2 + al) / r rpow al = r pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `r rpow (&2 + al) = Tt rpow (&2 + al) * rho0 pow 2 * rho0 rpow al` THEN
      DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY UNDISCH_TAC [`~(rho0 pow 2 = &0)`; `~(rho0 rpow al = &0)`] THEN
      CONV_TAC REAL_FIELD;
      UNDISCH_TAC `r rpow (&2 + al) = r pow 2 * r rpow al` THEN
      DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `~(r rpow al = &0)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The k = 0 Schauder estimate in theta form: for 0 < th < 1, a very weak   *)
(* solution of Lap u = f on ball(a,r) with |u| <= U, |f| <= A and           *)
(* r^al [f]_al <= A agrees a.e. on ball(a, th r) with a C^2 function w with *)
(* Lap w = f and the C^(2,al) bound wan_ckal 2 al r (C (r^2 A + U)).        *)
(* ------------------------------------------------------------------------- *)

let WANL_PT_SCH0 = prove
 (`!al th. &0 < al /\ al < &1 /\ &0 < th /\ th < &1
     ==> ?C. &0 < C /\
         !(a:real^2) r (u:real^2->real) (f:real^2->real) U A.
            &0 < r /\ &0 <= U /\ &0 <= A /\
            (\x. lift(u x)) measurable_on ball(a,r) /\
            (\x. lift(f x)) measurable_on ball(a,r) /\
            (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
            (!x. x IN ball(a,r) ==> abs(f x) <= A) /\
            (!x y. x IN ball(a,r) /\ y IN ball(a,r)
                   ==> r rpow al * abs(f x - f y) <= A * norm(x - y) rpow al) /\
            (!phi. wan_test (ball(a,r)) phi
                   ==> integral (ball(a,r)) (\x. lift(u x * llap (\y:real^2. mat 1) phi x)) =
                       integral (ball(a,r)) (\x. lift(f x * phi x)))
            ==> ?w. continuously_differentiable 2 (ball(a,th * r)) (\x. lift(w x)) /\
                    negligible {x | x IN ball(a,th * r) /\ ~(u x = w x)} /\
                    wan_ckal (ball(a,th * r)) 2 al r (\x. lift(w x)) (C * (r pow 2 * A + U)) /\
                    (!x. x IN ball(a,th * r) ==> llap (\y. mat 1) w x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `al:real` WANL_PT_SCH_LIMIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lim"))) THEN
  ABBREV_TAC `Tt = &6 / (&1 - th)` THEN
  SUBGOAL_THEN `&1 <= Tt` ASSUME_TAC THENL
   [EXPAND_TAC "Tt" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&2 + &50 * C1 * Tt pow 3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 + x`) THEN
    SUBGOAL_THEN `&0 <= Tt` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE; REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho0 = (&1 - th) * r / &6` THEN
  ABBREV_TAC `R1 = (&1 + th) / &2 * r` THEN
  SUBGOAL_THEN
   `&0 < rho0 /\ rho0 <= r /\ &0 < R1 /\ R1 + &3 * rho0 <= r /\ th * r <= R1 /\
    th * r + rho0 / &2 <= R1 /\ Tt * rho0 = r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho0"; "R1"; "Tt"] THEN
    SUBGOAL_THEN `&0 < &1 - th` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `th * r <= r` ASSUME_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= th * r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < &1 - th` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  USE_THEN "lim" (MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                                  `U:real`; `A:real`; `rho0:real`; `R1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->real` (X_CHOOSE_THEN `a1:real^2->complex`
    (X_CHOOSE_THEN `a2:real^2->complex` (X_CHOOSE_THEN `t:real^2->bool`
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `Kc = C1 * (U + A * rho0 pow 2) / rho0 rpow (&2 + al)` THEN
  ABBREV_TAC `G1 = C1 * (U + A * rho0 pow 2) / rho0` THEN
  ABBREV_TAC `G2 = C1 * (U + A * rho0 pow 2) / rho0 pow 2` THEN
  ABBREV_TAC `Hq = A / (&4 * r rpow al)` THEN
  SUBGOAL_THEN `&0 < r rpow al /\ &0 <= U + A * rho0 pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kc /\ &0 <= G2 /\ &0 <= Hq` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Kc"; "G2"; "Hq"] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE; REAL_POW_LE; REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,R1) SUBSET ball(a,r) /\ ball(a:real^2,th * r) SUBSET ball(a,R1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN ball(a:real^2,r) /\ y IN ball(a,r)
          ==> abs((f:real^2->real) x / &4 - f y / &4) <= Hq * norm(x - y) rpow al /\
              r rpow al * abs(f x / &4 - f y / &4) <= A / &4 * norm(x - y) rpow al`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
      can (find_term (fun t -> t = `r rpow al`)) (concl th) &&
      can (find_term (fun t -> t = `f:real^2->real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((f:real^2->real) x / &4 - f y / &4) = abs(f x - f y) / &4`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Hq" THEN
      SUBGOAL_THEN `~(r rpow al = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `abs((f:real^2->real) x - f y) / &4 =
        (r rpow al * abs(f x - f y)) / (&4 * r rpow al) /\
        A / (&4 * r rpow al) * norm(x - y:real^2) rpow al =
        (A * norm(x - y) rpow al) / (&4 * r rpow al)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN UNDISCH_TAC `~(r rpow al = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &4 * r rpow al` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      UNDISCH_TAC `r rpow al * abs((f:real^2->real) x - f y) <= A * norm(x - y) rpow al` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,R1)`; `w:real^2->real`; `a1:real^2->complex`;
                 `a2:real^2->complex`; `\x:real^2. (f:real^2->real) x / &4`; `Kc:real`;
                 `rho0:real`; `&2 + al`; `Hq:real`] WANL_PT_JET2_REG) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL; REAL_ARITH `(&2 + al) - &2 = al`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check
      (fun th -> can (find_term (fun t -> t = `Hq:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE) THEN
  MP_TAC(ISPECL [`ball(a:real^2,R1)`; `ball(a:real^2,th * r)`; `w:real^2->real`;
                 `a1:real^2->complex`; `a2:real^2->complex`; `\x:real^2. (f:real^2->real) x / &4`;
                 `Kc:real`; `rho0:real`; `al:real`; `Hq:real`; `G2:real`] WANL_PT_A2_HOLDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`; `e:real^2`] THEN
      REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
      ABBREV_TAC `dd = norm(y - x:real^2)` THEN
      SUBGOAL_THEN `norm(dd % e:real^2) = dd` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN EXPAND_TAC "dd" THEN
        REWRITE_TAC[REAL_ABS_NORM];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`a:real^2`; `y:real^2`; `y + dd % e:real^2`] DIST_TRIANGLE) THEN
        REWRITE_TAC[dist; VECTOR_ARITH `y - (y + d % e):real^2 = --(d % e)`; NORM_NEG];
        MP_TAC(ISPECL [`a:real^2`; `y:real^2`; `y - dd % e:real^2`] DIST_TRIANGLE) THEN
        REWRITE_TAC[dist; VECTOR_ARITH `y - (y - d % e):real^2 = d % e`]] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `dist(a:real^2,y) < th * r` THEN
      REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> t = `G2:real`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `Hq:real`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; SIMP_TAC[]]];
    DISCH_TAC] THEN
  EXISTS_TAC `w:real^2->real` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `ball(a:real^2,R1)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:real^2) IN t` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((u:real^2->real) x = w x)` THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC;
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN ball(a,R1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`al:real`; `C1:real`; `r:real`; `U:real`; `A:real`; `rho0:real`; `Tt:real`]
         WANL_PT_SCH0_CONST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC WANL_PT_CKAL2 THEN
  MAP_EVERY EXISTS_TAC [`a1:real^2->complex`; `a2:real^2->complex`;
                        `\x:real^2. (f:real^2->real) x / &4`; `U:real`; `A:real`;
                        `G1:real`; `G2:real`; `&20 * Kc + &2 * Hq + &4 * G2 / rho0 rpow al`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term (fun t ->
      is_const t && fst(dest_const t) = "iterated_partial")) (concl th))) THEN
    ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN ball(a,R1) /\ x IN ball(a,r)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> t = `G1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        can (find_term (fun t -> t = `G1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
        concl th = `!x. x IN ball(a:real^2,r) ==> abs((f:real^2->real) x) <= A`)) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `Hq:real`)) (concl th) &&
        can (find_term (fun t -> t = `r rpow al`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; SIMP_TAC[]]]]);;

let WANL_PT_SCHAUDER_K0 = prove
 (`!al. &0 < al /\ al < &1
        ==> ?C. &0 < C /\
                !(a:real^2) r (u:real^2->real) (f:real^2->real) A U.
                   &0 < r /\ wan_w12 (ball(a,r)) (\x. lift(u x)) /\
                   continuously_differentiable 0 (ball(a,r)) (\x. lift(f x)) /\
                   wan_ckal (ball(a,r)) 0 al r (\x. lift(f x)) A /\
                   (!x. x IN ball(a,r) ==> abs(u x) <= U) /\
                   (!phi. wan_test (ball(a,r)) phi
                          ==> vsum(1..2)
                                (\i. integral (ball(a,r))
                                       (\x. wan_dpart i phi x %
                                            wan_wd (ball(a,r)) i (\y. lift(u y)) x)) =
                              --(integral (ball(a,r)) (\x. lift(f x * phi x))))
                   ==> ?w. continuously_differentiable 2 (ball(a,r / &2)) (\x. lift(w x)) /\
                           negligible {x | x IN ball(a,r / &2) /\ ~(u x = w x)} /\
                           wan_ckal (ball(a,r / &2)) 2 al r (\x. lift(w x))
                                    (C * (r pow 2 * A + U)) /\
                           (!x. x IN ball(a,r / &2) ==> llap (\y. mat 1) w x = f x)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`al:real`; `&1 / &2`] WANL_PT_SCH0) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sch"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real`; `f:real^2->real`;
                       `A:real`; `U:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `r / &2 = &1 / &2 * r` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_ckal] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_ckal")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `[]:(num)list`)
                             (ASSUME_TAC o SPEC `[]:(num)list`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ALL; iterated_partial; real_pow; REAL_MUL_LID;
                              NORM_LIFT; REAL_ADD_LID; GSYM LIFT_SUB; LE_REFL]) THEN
  SUBGOAL_THEN `&0 <= U /\ &0 <= A` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `abs((u:real^2->real) a)`; EXISTS_TAC `abs((f:real^2->real) a)`] THEN
    REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((u:real^2->real) x)) measurable_on ball(a,r) /\
                (\x. lift((f:real^2->real) x)) measurable_on ball(a,r)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x:real^2. lift(u x)`] WAN_W12_IMP_LSPACE) THEN
      ASM_REWRITE_TAC[lspace; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
      ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_0]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real`; `f:real^2->real`] WANL_PT_VERY_WEAK) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  USE_THEN "sch" MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

