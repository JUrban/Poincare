(* ========================================================================= *)
(* Unit pc_p3_c172c: MT Lemma 17.2, part C (strong necks at                 *)
(* a first bad time whose neck region persists slightly beyond its initial  *)
(* time).  Repair of MT p. 397: the neck is first                            *)
(* compressed axially by the radial power map z -> |z|^(p-1) z (p < 1 close  *)
(* to 1), which costs exactly (1 - p^2)^2 in closeness (the difference is   *)
(* the parallel tensor 2 (p^2 - 1) ds^2), so the compressed neck has compact *)
(* closure inside the original neck region; it is then extended slightly    *)
(* backward in time and re-centred by the linear maps z -> r Q z.            *)
(*                                                                         *)
(* The radial power map pulls the evolving cylinder back to a               *)
(* rescaled evolving cylinder: pw^* cyl(t) = p^2 cyl(1 - (1 - t) / p^2)     *)
(* with p = 2 e + 1 for the map z -> (|z|^2)^e z of pc_rf_basic.             *)
(* ========================================================================= *)

needs "src/pc_p3_c172b.ml";;
needs "src/pc_apx_chain.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_PW_CYL = prove
 (`!e t (y:real^3).
     ~(y = vec 0) /\ ~(&2 * e + &1 = &0)
     ==> mpullback (\z. ((norm z pow 2) rpow e) % z) (cylinder_flow t) y =
         ((&2 * e + &1) pow 2) %%
         cylinder_flow (&1 - (&1 - t) / (&2 * e + &1) pow 2) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_FRECHET) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  MP_TAC(ISPECL [`frechet_derivative (\z:real^3. (norm z pow 2) rpow e % z) (at y)`;
                 `cylinder_flow t (((norm(y:real^3) pow 2) rpow e) % y)`;
                 `u:real^3`; `v:real^3`] RFB_CONGRUENCE_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
              MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_NORM2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `N = norm(y:real^3) pow 2` THEN
  SUBGOAL_THEN `N rpow (&2 * e + &1) = (N rpow e) pow 2 * N /\
                N rpow (e - &1) = N rpow e / N` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[RPOW_ADD; RPOW_SUB] THEN REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN
    SUBGOAL_THEN `&2 * e = e + e` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < N rpow e` ASSUME_TAC THENL [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = N rpow e` THEN
  SUBGOAL_THEN `(y:real^3) dot y = N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[DOT_RADD; DOT_LADD; DOT_RMUL; DOT_LMUL; MATRIX_VECTOR_LMUL] THEN
  ASM_REWRITE_TAC[DOT_SYM] THEN
  UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < N` THEN
  UNDISCH_TAC `~(&2 * e + &1 = &0)` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Base change of the C^k distance between a metric G0 and its               *)
(* constant multiple c G0 (same Levi-Civita connection; norms comparable by *)
(* the factor c; zero-order difference (c - 1) G0 of norm |c - 1| sqrt N),   *)
(* in the pattern of P2B9_CYL_BASE2 of pc_p2b_979.                           *)
(* ========================================================================= *)

let P3H_LCK_SCALE_BASE = prove
 (`!k Z0 (G0:real^N->real^N^N) G c y.
     metric_field Z0 G0 /\ metric_field Z0 G /\ y IN Z0 /\ &0 < c
     ==> sqrt(lck_dist2 k G0 G y) <=
         max (&1) c pow (k + 2) * sqrt(lck_dist2 k (\z. c %% G0 z) G y) +
         abs(c - &1) * sqrt(&(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(Z0:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `G1 = \z:real^N. c %% (G0:real^N->real^N^N) z` THEN
  SUBGOAL_THEN `metric_field Z0 (G1:real^N->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "G1" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z a b. z IN Z0
                        ==> christoffel (G0:real^N->real^N^N) z a b = christoffel G1 z a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G1" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CHRISTOFFEL_SCALE THEN EXISTS_TAC `Z0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z u. lmetric2 (G1:real^N->real^N^N) z u = c * lmetric2 G0 z u`
  ASSUME_TAC THENL
   [EXPAND_TAC "G1" THEN REWRITE_TAC[lmetric2; MATRIX_VECTOR_LMUL; DOT_RMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Z0:real^N->bool`; `G1:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Z0:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `Z0:real^N->bool`; `G1:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G1 z u`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "FS") THEN
  (* the split of the covariant derivatives *)
  SUBGOAL_THEN
   `!l z u. z IN Z0
            ==> lnabla_iter 2 l G0
                  (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) z u =
                lnabla_iter 2 l G1 (\z u. lmetric2 G z u - lmetric2 G1 z u) z u +
                (if l = 0 then (c - &1) * lmetric2 G0 z u else &0)`
  (LABEL_TAC "SPLIT") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) =
      (\x u. &1 * (lmetric2 G x u - lmetric2 G1 x u) + (c - &1) * lmetric2 G0 x u)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`2`; `Z0:real^N->bool`; `G0:real^N->real^N^N`;
       `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G1 z u`;
       `lmetric2 (G0:real^N->real^N^N)`; `&1`; `c - &1`] LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    MP_TAC(ISPECL [`2`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
       `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G1 z u`;
       `Z0:real^N->bool`] LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_EQ_ADD_LCANCEL] THEN
    STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
     [REWRITE_TAC[lnabla_iter]; ALL_TAC] THEN
    REWRITE_TAC[NOT_SUC] THEN
    MP_TAC(ISPECL [`Z0:real^N->bool`; `G0:real^N->real^N^N`] LRG_LNABLA_ITER_METRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = max (&1) c` THEN
  SUBGOAL_THEN `&1 <= lam /\ c <= lam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= lam pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = lck_dist2 k (G1:real^N->real^N^N) G y` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[lck_dist2] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `Z0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..k) (\l. ltnorm2 (2 + l) G0
                     (lnabla_iter 2 l G1
                       (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G1 z u)) y) <=
    lam pow (k + 2) * L`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[lck_dist2; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam pow (2 + l) *
                ltnorm2 (2 + l) G1
                  (lnabla_iter 2 l G1
                    (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G1 z u)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `Z0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real^N` THEN EXPAND_TAC "G1" THEN
      REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `x:real^N = vec 0` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `Z0:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(sum(0..k) (\l. ltnorm2 (2 + l) G0
                          (lnabla_iter 2 l G1
                            (\z u. lmetric2 (G:real^N->real^N^N) z u -
                                   lmetric2 G1 z u)) y)) +
    sqrt(sum(0..k) (\l. if l = 0
                        then ltnorm2 2 G0 (\z u. (c - &1) * lmetric2 G0 z u) y
                        else &0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC LRG_SQRT_SUM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `Z0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th]);
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      REWRITE_TAC[LRG_LTNORM2_CMUL] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `Z0:real^N->bool` THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `Z0:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
     [REWRITE_TAC[ADD_CLAUSES; lnabla_iter] THEN
      MATCH_MP_TAC LRG_LTNORM2_TRIANGLE THEN EXISTS_TAC `Z0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `ltensor_field 2 Z0 (lmetric2 (G0:real^N->real^N^N))` THEN
        REWRITE_TAC[ltensor_field] THEN REWRITE_TAC[LIFT_CMUL] THEN
        REPEAT STRIP_TAC THENL
         [AP_TERM_TAC THEN ASM_MESON_TAC[];
          MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_MESON_TAC[]];
        MP_TAC(ISPECL [`Z0:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
               LRG_LMETRIC2_DIFF_FIELD) THEN ASM_SIMP_TAC[];
        GEN_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      REWRITE_TAC[NOT_SUC; SQRT_0; REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
      USE_THEN "SPLIT" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[NOT_SUC; REAL_ADD_RID]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL; LRG_LTNORM2_CMUL] THEN
  SUBGOAL_THEN `ltnorm2 2 G0 (\z u. lmetric2 (G0:real^N->real^N^N) z u) y =
                &(dimindex(:N))` SUBST1_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LRG_LTNORM2_METRIC THEN
    EXISTS_TAC `Z0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(lam pow (k + 2) * L)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(lam pow (k + 2) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN
    SUBGOAL_THEN `lam pow (k + 2) <= lam pow (k + 2) * lam pow (k + 2)` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC]);;

(* Base change from the compressed cylinder pw^* cyl(t) = p^2 cyl(t') back   *)
(* to cyl(t): two steps, P2B9_CYL_BASE2 (t to t') and P3H_LCK_SCALE_BASE.   *)

let P3H_CMP_BASE = prove
 (`!k e t Z0 (G:real^3->real^3^3) y.
     t <= &0 /\ ~(&2 * e + &1 = &0) /\
     abs(t - (&1 - (&1 - t) / (&2 * e + &1) pow 2)) <= &1 / &2 /\
     Z0 SUBSET ((:real^3) DELETE vec 0) /\ metric_field Z0 G /\ y IN Z0
     ==> sqrt(lck_dist2 k (cylinder_flow t) G y) <=
         (&1 + abs(t - (&1 - (&1 - t) / (&2 * e + &1) pow 2))) pow (k + 2) *
         (max (&1) ((&2 * e + &1) pow 2) pow (k + 2) *
          sqrt(lck_dist2 k (mpullback (\z. ((norm z pow 2) rpow e) % z) (cylinder_flow t))
                         G y) +
          abs((&2 * e + &1) pow 2 - &1) * sqrt(&3) +
          &2 * abs(t - (&1 - (&1 - t) / (&2 * e + &1) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p2 = (&2 * e + &1) pow 2` THEN
  ABBREV_TAC `t' = &1 - (&1 - t) / p2` THEN
  SUBGOAL_THEN `&0 < p2` ASSUME_TAC THENL
   [EXPAND_TAC "p2" THEN REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t' < &1` ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN
    SUBGOAL_THEN `&0 < (&1 - t) / p2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(Z0:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Z0 (cylinder_flow t')` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `t:real`; `t':real`; `Z0:real^3->bool`; `G:real^3->real^3^3`;
                 `y:real^3`] P2B9_CYL_BASE2) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b + c ==> a + d <= b + c + d`) THEN
  MP_TAC(ISPECL [`k:num`; `Z0:real^3->bool`; `cylinder_flow t'`; `G:real^3->real^3^3`;
                 `p2:real`; `y:real^3`] P3H_LCK_SCALE_BASE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN
   `lck_dist2 k (\z. p2 %% cylinder_flow t' z) (G:real^3->real^3^3) y =
    lck_dist2 k (mpullback (\z. ((norm z pow 2) rpow e) % z) (cylinder_flow t)) G y`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `Z0:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN EXPAND_TAC "p2" THEN EXPAND_TAC "t'" THEN EXPAND_TAC "p2" THEN
  MATCH_MP_TAC P3H_PW_CYL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Arithmetic for the compression: for p < 1 close to 1 the                 *)
(* base change factors of P3H_CMP_BASE stay below eps on (-a,0], a <= 2.    *)
(* ========================================================================= *)

let P3H_POW_CONVEX = prove
 (`!n c. &0 <= c /\ c <= &1 ==> (&1 + c) pow n <= &1 + (&2 pow n - &1) * c`,
  INDUCT_TAC THEN REWRITE_TAC[real_pow] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &2 pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + c) * (&1 + (&2 pow n - &1) * c)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * c <= c` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 pow n - &1)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = &2 pow n - &1` THEN
  SUBGOAL_THEN `&2 * &2 pow n - &1 = &2 * m + &1` SUBST1_TAC THENL
   [EXPAND_TAC "m" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m * (c * c) <= m * c` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P3H_CMP_ARITH = prove
 (`!k d1 eps a.
     &0 <= d1 /\ d1 < eps pow 2 /\ &0 < eps /\ &0 < a /\ a <= &2
     ==> ?p0 B. &1 / &2 <= p0 /\ p0 < &1 /\ &0 <= B /\ B < eps /\
                !p s. p0 <= p /\ p < &1 /\ --a < s /\ s <= &0
                    ==> abs(s - (&1 - (&1 - s) / p pow 2)) <= &1 / &2 /\
                        (&1 + abs(s - (&1 - (&1 - s) / p pow 2))) pow (k + 2) *
                        (max (&1) (p pow 2) pow (k + 2) * sqrt d1 +
                         abs(p pow 2 - &1) * sqrt(&3) +
                         &2 * abs(s - (&1 - (&1 - s) / p pow 2))) <= B`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M = &3 * (&2 pow (k + 2) - &1)` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    SUBGOAL_THEN `&1 <= &2 pow (k + 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt d1 < eps /\ &0 <= sqrt d1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eta = eps - sqrt d1` THEN
  SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c0 = min (&1 / &9) (eta / (&2 * (&8 + M * (eps + &1))))` THEN
  SUBGOAL_THEN `&0 < c0 /\ c0 <= &1 / &9 /\ c0 * (&8 + M * (eps + &1)) <= eta / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN
    SUBGOAL_THEN `&0 < &2 * (&8 + M * (eps + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&8` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &8 <= &8 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `eta / (&2 * (&8 + M * (eps + &1))) * (&8 + M * (eps + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &8 + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < &2 * (&8 + M * (eps + &1))` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(&1 + c0 / &3)`; `sqrt d1 + eta / &2`] THEN
  SUBGOAL_THEN `&1 < &1 + c0 / &3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&1 / &2 = inv(&2)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&1 + c0 / &3)` THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = inv(p pow 2) - &1` THEN
  SUBGOAL_THEN `&0 <= c /\ c <= c0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x - &1`) THEN
      MATCH_MP_TAC REAL_INV_1_LE THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 + c0 ==> x - &1 <= c0`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + c0 / &3) pow 2` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `c0 * c0 <= c0 / &9` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * &1 / &9` THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(s - (&1 - (&1 - s) / p pow 2)) = (&1 - s) * c /\
                abs(p pow 2 - &1) <= c /\ max (&1) (p pow 2) = &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < p pow 2 /\ p pow 2 < &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_POW_1_LT THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `s - (&1 - (&1 - s) / p pow 2) = (&1 - s) * c` SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < p pow 2` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(&1 - s) = &1 - s /\ abs c = c` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `abs(p pow 2 - &1) = p pow 2 * c` SUBST1_TAC THENL
       [EXPAND_TAC "c" THEN
        SUBGOAL_THEN `p pow 2 * (inv(p pow 2) - &1) = &1 - p pow 2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < p pow 2` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN
  SUBGOAL_THEN `(&1 - s) * c <= &3 * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = (&1 - s) * c` THEN
  SUBGOAL_THEN `&0 <= w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k + 2`; `w:real`] P3H_POW_CONVEX) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 = sqrt(&2 pow 2)` (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(p pow 2 - &1) * sqrt(&3) <= c * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; SQRT_POS_LE; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X = sqrt d1 + abs(p pow 2 - &1) * sqrt(&3) + &2 * w` THEN
  SUBGOAL_THEN `&0 <= X /\ X <= sqrt d1 + &8 * c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + &2 * c`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; SQRT_POS_LE; REAL_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + (&2 pow (k + 2) - &1) * w) * X` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 pow (k + 2) - &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= &2 pow (k + 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 pow (k + 2) - &1) * w <= M * c` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    SUBGOAL_THEN `(&2 pow (k + 2) - &1) * w <= (&2 pow (k + 2) - &1) * (&3 * c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + M * c) * (sqrt d1 + &8 * c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M * c` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(M * c) * sqrt d1 <= (M * c) * eps /\ (M * c) * (&8 * c) <= (M * c) * &1 /\
                c * (&8 + M * (eps + &1)) <= c0 * (&8 + M * (eps + &1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &8 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The power map pw_p (z -> |z|^(p-1) z, 0 < p <= 1) maps the               *)
(* neck domain of eps diffeomorphically onto that of eps / p, fixing the    *)
(* unit sphere; in one slice the compressed chart e o pw_p is close to the  *)
(* cylinder up to the base change factors of P3H_CMP_BASE.                  *)
(* ========================================================================= *)

let P3H_PW_EQ = prove
 (`!p. (\z:real^3. ((norm z pow 2) rpow ((p - &1) / &2)) % z) =
       (\z. norm z rpow (p - &1) % z)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM RPOW_POW] THEN
  SIMP_TAC[RPOW_RPOW; NORM_POS_LE] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P3H_PW_DOM = prove
 (`!eps p. &0 < eps /\ &0 < p /\ p <= &1
           ==> diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom (eps / p))
                 (\z:real^3. ((norm z pow 2) rpow ((p - &1) / &2)) % z)
                 (\z. norm z rpow (inv p - &1) % z) /\
               rfs_neck_dom (eps / p) SUBSET rfs_neck_dom eps /\
               (!z:real^3. z IN sphere(vec 0,&1)
                           ==> ((norm z pow 2) rpow ((p - &1) / &2)) % z = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; RPOW_ONE; VECTOR_MUL_LID]] THEN
  REWRITE_TAC[P3H_PW_EQ; rfs_neck_dom] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps / p) = p * inv(sqrt(&2) * eps)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `&0 < eps` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `L = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `exp(--L)`; `exp L`]
    (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_POWER_ANNULUS)) THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rpow; REAL_EXP_POS_LT; LOG_EXP; REAL_MUL_RNEG]);;

let P3H_CMP_SLICE = prove
 (`!top atlas (g:A->real^3^3) (e:real^3->A) eps p R d1 k s y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas (rfs_neck_dom (eps / p)) e /\
     &0 < eps /\ &0 < p /\ p <= &1 /\ &0 < R /\ s <= &0 /\
     abs(s - (&1 - (&1 - s) / p pow 2)) <= &1 / &2 /\
     (!z. z IN rfs_neck_dom (eps / p)
          ==> lck_dist2 k (cylinder_flow s) (\z. R %% rfs_pullback atlas e g z) z <= d1) /\
     y IN rfs_neck_dom eps
     ==> &0 <= lck_dist2 k (cylinder_flow s)
                (\z. R %% rfs_pullback atlas
                            (e o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) g z) y /\
         sqrt(lck_dist2 k (cylinder_flow s)
                (\z. R %% rfs_pullback atlas
                            (e o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) g z) y) <=
         (&1 + abs(s - (&1 - (&1 - s) / p pow 2))) pow (k + 2) *
         (max (&1) (p pow 2) pow (k + 2) * sqrt d1 + abs(p pow 2 - &1) * sqrt(&3) +
          &2 * abs(s - (&1 - (&1 - s) / p pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `p:real`] P3H_PW_DOM) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `(p - &1) / &2`; `s:real`; `rfs_neck_dom eps`;
                 `\z. R %% rfs_pullback atlas
                         ((e:real^3->A) o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) g z`;
                 `y:real^3`] P3H_CMP_BASE) THEN
  SUBGOAL_THEN `&2 * (p - &1) / &2 + &1 = p` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `pw = \z:real^3. ((norm z pow 2) rpow ((p - &1) / &2)) % z` THEN
  ABBREV_TAC `pw' = \z:real^3. norm z rpow (inv p - &1) % z` THEN
  DISCH_THEN(LABEL_TAC "base") THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (cylinder_flow s) /\
                metric_field (rfs_neck_dom (eps / p)) (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (pw:real^3->real^3) (rfs_neck_dom eps) = rfs_neck_dom (eps / p)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom (eps / p))
                   (pw:real^3->real^3) pw'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pw:real^3->real^3) y IN rfs_neck_dom (eps / p) /\ pw y IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) ((e:real^3->A) o (pw:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`rfs_neck_dom (eps / p)`; `rfs_neck_dom (eps / p)`;
                          `pw':real^3->real^3`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `H = \z. R %% rfs_pullback atlas (e:real^3->A) g z` THEN
  ABBREV_TAC `Gc = \z. R %% rfs_pullback atlas ((e:real^3->A) o (pw:real^3->real^3)) g z` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom (eps / p)) (H:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (Gc:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "Gc"] THEN CONJ_TAC THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN rfs_neck_dom eps ==> (Gc:real^3->real^3^3) z = mpullback pw H z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "Gc" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `rfs_neck_dom (eps / p)`; `e:real^3->A`;
                   `rfs_neck_dom eps`; `pw:real^3->real^3`; `pw':real^3->real^3`; `z:real^3`]
                  APX_RFS_PULLBACK_PRECOMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k (mpullback pw (cylinder_flow s)) (Gc:real^3->real^3^3) y =
                lck_dist2 k (cylinder_flow s) H (pw y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lck_dist2 k (mpullback pw (cylinder_flow s)) (mpullback pw H) (y:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_SIMP_TAC[APX_NECK_DOM_OPEN];
      MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`rfs_neck_dom (eps / p)`; `rfs_neck_dom eps`;
                            `pw':real^3->real^3`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow s) (H:real^3->real^3^3)
                                ((pw:real^3->real^3) y) /\
                lck_dist2 k (cylinder_flow s) H (pw y) <= d1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom (eps / p)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `!z. z IN rfs_neck_dom (eps / p)
                       ==> lck_dist2 k (cylinder_flow s) (H:real^3->real^3^3) z <= d1` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "base" MP_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Compression of an evolving neck.  For p < 1 close to 1 the               *)
(* chart e o pw_p is again an evolving eps-neck of the same length at the   *)
(* same point and time (a <= 2); its image is e(neck_dom(eps / p)), whose    *)
(* closure is compact inside the original neck: this is the room needed to *)
(* recentre (MT p. 397, repaired).                                         *)
(* ========================================================================= *)

let P3H_CMP_EVOLVING = prove
 (`!V eps x t a (e:real^3->A).
     p2c_regular_view V /\ rfs_evolving_neck V eps x t a e /\ a <= &2
     ==> ?p0. &1 / &2 <= p0 /\ p0 < &1 /\
              !p. p0 <= p /\ p < &1
                  ==> rfs_evolving_neck V eps x t a
                        (e o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) /\
                      IMAGE (e o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z))
                            (rfs_neck_dom eps) = IMAGE e (rfs_neck_dom (eps / p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2B9_EVOLVING_NECK_ALT]) THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t (x:A)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "neck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pers")
      (MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [USE_THEN "neck" (MP_TAC o REWRITE_RULE[rfs_neck]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                   `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`rfs_kreg eps`; `max (&0) d1`; `eps:real`; `a:real`] P3H_CMP_ARITH) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `&0 < eps pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar"))))))) THEN
  EXISTS_TAC `p0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `p:real`] P3H_PW_DOM) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `pw = \z:real^3. ((norm z pow 2) rpow ((p - &1) / &2)) % z` THEN
  ABBREV_TAC `pw' = \z:real^3. norm z rpow (inv p - &1) % z` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((e:real^3->A) o pw) (rfs_neck_dom eps) = IMAGE e (rfs_neck_dom (eps / p))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom (eps / p))
                   (pw:real^3->real^3) pw'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  (* the family bound at every s *)
  SUBGOAL_THEN
   `!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom eps
          ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                (\y. R %% rfs_pullback (rfs_vatlas V (t + s / R)) ((e:real^3->A) o pw)
                                       (rfs_vmetric V (t + s / R)) y) y <= B pow 2`
  (LABEL_TAC "fam") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                   `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    ABBREV_TAC `u = t + s / R` THEN
    USE_THEN "ar" (MP_TAC o SPECL [`p:real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) u`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) u`;
                   `e:real^3->A`; `eps:real`; `p:real`; `R:real`; `max (&0) d1`;
                   `rfs_kreg eps`; `s:real`; `y:real^3`] P3H_CMP_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < p /\ p <= &1` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom eps` THEN
        ASM_REWRITE_TAC[APX_NECK_DOM_OPEN];
        ALL_TAC] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= d1 ==> x <= max (&0) d1`) THEN
      EXPAND_TAC "u" THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `L = lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                      (\y. R %% rfs_pullback (rfs_vatlas V u) ((e:real^3->A) o pw)
                                             (rfs_vmetric V u) y) y` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sqrt L <= B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `L = sqrt L pow 2` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2B9_EVOLVING_NECK_ALT] THEN
  CONJ_TAC THENL
   [(* the neck at time t *)
    USE_THEN "neck" (MP_TAC o REWRITE_RULE[rfs_neck]) THEN STRIP_TAC THEN
    REWRITE_TAC[rfs_neck] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `rfs_neck_dom (eps / p)`;
                            `pw':real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `x0:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "pw" THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `B pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "fam" (MP_TAC o SPECL [`&0`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    SUBGOAL_THEN `mfd_scalar (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) t) (rfs_vmetric V t) x = R`
    SUBST1_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2B9_RFS_VSCALAR]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* persistence of the compressed image *)
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    USE_THEN "pers" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `a:real`;
                   `e:real^3->A`; `(u - t) * R`] P2B9_REGULAR_NECK_SLICE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t + ((u - t) * R) / R = u` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `--a = --(a / R) * R` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x * R <= &0 * R ==> x * R <= &0`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) u`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN];
    ALL_TAC] THEN
  (* the family closeness *)
  REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `B pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Linear recentring maps z -> r f z (r > 0, f orthogonal):                 *)
(* they preserve every shrinking cylinder, map annuli diffeomorphically to *)
(* annuli, and the C^k distance to the cylinder of the recentred chart      *)
(* e o (r f) at w is that of e at r f w.                                    *)
(* ========================================================================= *)

let P3H_CYL_ORTH_INV = prove
 (`!r (f:real^3->real^3) s y.
     &0 < r /\ orthogonal_transformation f /\ ~(y = vec 0)
     ==> mpullback (\z. r % f z) (cylinder_flow s) y = cylinder_flow s y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (\z:real^3. r % (f:real^3->real^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\z:real^3. r % (f:real^3->real^3) z) (at y) =
                (\z. r % f z)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  ASM_SIMP_TAC[RFB_CONGRUENCE_DOT] THEN REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL; NORM_MUL] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[CONJUNCT2(REWRITE_RULE[orthogonal_transformation] th)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT2(REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] th)]) THEN
  SUBGOAL_THEN `abs r = r` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD);;

let P3H_ORTH_ANNULUS = prove
 (`!r (f:real^3->real^3) a b.
     &0 < r /\ orthogonal_transformation f
     ==> ?f'. orthogonal_transformation f' /\ (!x. f'(f x) = x) /\ (!y. f(f' y) = y) /\
              diffeomorphism_on (annulus a b) (annulus (r * a) (r * b))
                (\z:real^3. r % f z) (\z. inv r % f' z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^3->real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear (f:real^3->real^3) /\ linear (f':real^3->real^3)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. norm((f:real^3->real^3) v) = norm v` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  SUBGOAL_THEN `annulus a b = {v:real^3 | (\z. r % (f:real^3->real^3) z) v IN
                                          annulus (r * a) (r * b)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[annulus; EXTENSION; IN_ELIM_THM; NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN
    SUBGOAL_THEN `abs r = r` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOF_LINEAR_DIFFEO THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV;
               REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let P3H_LIN_PULL = prove
 (`!top atlas (g:A->real^3^3) (e:real^3->A) S a b r (f:real^3->real^3) R k s w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S e /\ annulus (r * a) (r * b) SUBSET S /\ &0 <= a /\
     &0 < r /\ orthogonal_transformation f /\ &0 < R /\ s < &1 /\ w IN annulus a b
     ==> lck_dist2 k (cylinder_flow s)
           (\z. R %% rfs_pullback atlas (e o (\z. r % f z)) g z) w =
         lck_dist2 k (cylinder_flow s) (\z. R %% rfs_pullback atlas e g z) (r % f w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `f:real^3->real^3`; `a:real`; `b:real`] P3H_ORTH_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = \z:real^3. r % (f:real^3->real^3) z` THEN
  ABBREV_TAC `M' = \z:real^3. inv r % (f':real^3->real^3) z` THEN
  ABBREV_TAC `H = \z. R %% rfs_pullback atlas (e:real^3->A) g z` THEN
  SUBGOAL_THEN `!z:real^3. z IN annulus a b ==> ~(z = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `a < norm(z:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (r * a) (r * b) SUBSET ((:real^3) DELETE vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; SUBSET; IN_ELIM_THM; IN_DELETE; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `r * a < norm(x:real^3)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN
    SUBGOAL_THEN `&0 <= r * a` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (annulus (r * a) (r * b)) (e:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (annulus (r * a) (r * b)) (H:real^3->real^3^3) /\
                metric_field (annulus (r * a) (r * b)) (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; OPEN_ANNULUS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3->real^3) w = r % f w` (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 k (mpullback M (cylinder_flow s)) (mpullback M H) (w:real^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `annulus a b:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN EXPAND_TAC "M" THEN MATCH_MP_TAC P3H_CYL_ORTH_INV THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `annulus (r * a) (r * b):real^3->bool`; `e:real^3->A`;
                   `annulus a b:real^3->bool`; `M:real^3->real^3`; `M':real^3->real^3`;
                   `z:real^3`] APX_RFS_PULLBACK_PRECOMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL];
    MATCH_MP_TAC LCK_DIST2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`annulus (r * a) (r * b):real^3->bool`;
                          `annulus a b:real^3->bool`; `M':real^3->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

(* A constant rescaling of the target and a change of cylinder time.       *)

let P3H_RESCALE_TIME = prove
 (`!k s1 s2 (K:real^3->real^3^3) c T0 y.
     s2 <= &0 /\ abs(s2 - s1) <= &1 / &2 /\ open T0 /\
     T0 SUBSET ((:real^3) DELETE vec 0) /\ metric_field T0 K /\ y IN T0 /\ &0 < c
     ==> sqrt(lck_dist2 k (cylinder_flow s2) (\z. c %% K z) y) <=
         c * ((&1 + abs(s2 - s1)) pow (k + 2) *
              (sqrt(lck_dist2 k (cylinder_flow s1) K y) + &2 * abs(s2 - s1))) +
         abs(c - &1) * sqrt(&3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field T0 (cylinder_flow s2)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `T0:real^3->bool`; `cylinder_flow s2`; `K:real^3->real^3^3`;
                 `c:real`; `y:real^3`] LCK_DIST_RESCALE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  MP_TAC(ISPECL [`k:num`; `s2:real`; `s1:real`; `T0:real^3->bool`; `K:real^3->real^3^3`;
                 `y:real^3`] P2B9_CYL_BASE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `c * a <= c * b ==> x <= c * a + e ==> x <= c * b + e`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* One slice of the recentred compressed chart (e o (r f)) o pw_p.         *)

let P3H_RCT_SLICE = prove
 (`!top atlas (g:A->real^3^3) (e:real^3->A) S eps p r (f:real^3->real^3) R d1 k s y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S e /\
     &0 < eps /\ &0 < p /\ p <= &1 /\ &0 < r /\ orthogonal_transformation f /\
     annulus (r * exp(--(inv(sqrt(&2) * eps / p)))) (r * exp(inv(sqrt(&2) * eps / p)))
       SUBSET S /\
     &0 < R /\ s <= &0 /\ abs(s - (&1 - (&1 - s) / p pow 2)) <= &1 / &2 /\
     (!w. w IN annulus (r * exp(--(inv(sqrt(&2) * eps / p))))
                       (r * exp(inv(sqrt(&2) * eps / p)))
          ==> lck_dist2 k (cylinder_flow s) (\z. R %% rfs_pullback atlas e g z) w <= d1) /\
     y IN rfs_neck_dom eps
     ==> &0 <= lck_dist2 k (cylinder_flow s)
                (\z. R %% rfs_pullback atlas
                       ((e o (\z. r % f z)) o
                        (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) g z) y /\
         sqrt(lck_dist2 k (cylinder_flow s)
                (\z. R %% rfs_pullback atlas
                       ((e o (\z. r % f z)) o
                        (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) g z) y) <=
         (&1 + abs(s - (&1 - (&1 - s) / p pow 2))) pow (k + 2) *
         (max (&1) (p pow 2) pow (k + 2) * sqrt d1 + abs(p pow 2 - &1) * sqrt(&3) +
          &2 * abs(s - (&1 - (&1 - s) / p pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P3H_CMP_SLICE THEN MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = exp(--(inv(sqrt(&2) * eps / p)))` THEN
  ABBREV_TAC `b = exp(inv(sqrt(&2) * eps / p))` THEN
  SUBGOAL_THEN `rfs_neck_dom (eps / p) = annulus a b` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `f:real^3->real^3`; `a:real`; `b:real`] P3H_ORTH_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `annulus (r * a) (r * b):real^3->bool`;
                          `\z:real^3. inv r % (f':real^3->real^3) z`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `e:real^3->A`; `S:real^3->bool`; `a:real`; `b:real`; `r:real`;
                 `f:real^3->real^3`; `R:real`; `k:num`; `s:real`; `z:real^3`]
                P3H_LIN_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `diffeomorphism_on (annulus a b) (annulus (r * a) (r * b))
                 (\z:real^3. r % (f:real^3->real^3) z) (\z. inv r % f' z)` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  UNDISCH_TAC `IMAGE (\z:real^3. r % (f:real^3->real^3) z) (annulus a b) =
               annulus (r * a) (r * b)` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `r % (f:real^3->real^3) z`) THEN
  MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Neck coordinates of the transported flow p2c_vfam V W b of               *)
(* a persisting region (the Ricci flow of p2c_regular_view) are those of    *)
(* the slices: rfs_pullback in the restricted atlas of the last time b of   *)
(* the transported metric at u equals rfs_pullback in the slice at u.       *)
(* ========================================================================= *)

let P3H_RFS_PULLBACK_RESTRICT = prove
 (`!top atlas (h:A->real^3^3) W S (e:real^3->A) z.
     smooth_manifold_atlas top atlas /\ open_in top W /\ mfd_param top atlas S e /\
     IMAGE e S SUBSET W /\ z IN S
     ==> rfs_pullback (restrict_atlas atlas W) e (restrict_metric atlas W h) z =
         rfs_pullback atlas e h z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) z IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `(e:real^3->A) z`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `h:A->real^3^3`;
                 `S:real^3->bool`; `e:real^3->A`; `U:A->bool`; `phi:A->real^3`; `z:real^3`]
                APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[rfs_pullback] THEN ASM_REWRITE_TAC[SND] THEN
  REWRITE_TAC[mpullback; o_THM] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`; `W:A->bool`; `h:A->real^3^3`; `(e:real^3->A) z`]
                METRIC_LOCAL_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  REFL_TAC);;

let P3H_VFAM_PULLBACK = prove
 (`!V W a b u (e:real^3->A) S z.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < u /\ u <= b /\
     mfd_param (rfs_vtop V b) (rfs_vatlas V b) S e /\ IMAGE e S SUBSET W /\ z IN S
     ==> rfs_pullback (restrict_atlas (rfs_vatlas V b) W) e (p2c_vfam V W b u) z =
         rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))]) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[p2c_vfam] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `\x:A. if u = b then rfs_vmetric (V:(real->A topology)#
                                       (real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) b x
                        else mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V u) (\y. y)
                                                 (rfs_vmetric V u) x`;
                 `W:A->bool`; `S:real^3->bool`; `e:real^3->A`; `z:real^3`]
                P3H_RFS_PULLBACK_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `u:real = b` THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) u`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) u`;
                 `S:real^3->bool`; `e:real^3->A`; `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) u`; `z:real^3`] P2B9_PULLBACK_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* ========================================================================= *)
(* Neck coordinates along one Ricci flow: the tube lemma, the               *)
(* closeness at an end time of a family of necks (limit), and its          *)
(* extension a little past that time on a compact set (MT p. 397; the       *)
(* pattern of P2BL_NECK_ENDPOINT and P2B_KSOL_NECK_EXTEND_Q, for general    *)
(* flows and affine time parametrizations c0 + s / R).                      *)
(* ========================================================================= *)

let P3H_NECK_LCK_CHART = prove
 (`!top atlas (Gf:real->A->real^3^3) a b R s1 s2 k (e:real^3->A) S y.
     ricci_flow_on (top,atlas) a b Gf /\ &0 < R /\ a < s1 /\ s1 < b /\ a < s2 /\ s2 < b /\
     mfd_param top atlas S e /\ y IN S
     ==> metric_field S (\z. R %% rfs_pullback atlas e (Gf s1) z) /\
         lck_dist2 k (\z. R %% rfs_pullback atlas e (Gf s1) z)
                     (\z. R %% rfs_pullback atlas e (Gf s2) z) y =
         lck_dist2 k (metric_local atlas (chart_at atlas (e y)) (\w. R %% Gf s1 w))
                     (metric_local atlas (chart_at atlas (e y)) (\w. R %% Gf s2 w))
                     (SND(chart_at atlas (e y)) (e y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((Gf:real->A->real^3^3) s1) /\
                riemannian_metric atlas ((Gf:real->A->real^3^3) s2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P2B9_RFS_PULLBACK_CMUL] THEN
  MATCH_MP_TAC P2B9_LCK_PARAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `S:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let P3H_NECK_TUBE = prove
 (`!top atlas (Gf:real->A->real^3^3) a b R s0 k (e:real^3->A) S K0 th.
     ricci_flow_on (top,atlas) a b Gf /\ &0 < R /\ a < s0 /\ s0 < b /\
     mfd_param top atlas S e /\ compact K0 /\ K0 SUBSET S /\ &0 < th
     ==> ?eta. &0 < eta /\
               !s y. abs(s - s0) < eta /\ a < s /\ s < b /\ y IN K0
                     ==> lck_dist2 k (\z. R %% rfs_pullback atlas e (Gf s0) z)
                                     (\z. R %% rfs_pullback atlas e (Gf s) z) y < th`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `s0:real`; `k:num`;
                 `IMAGE (e:real^3->A) K0`; `th:real`] P2BL_SLICES_TUBE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `s0:real`; `s:real`;
                 `k:num`; `e:real^3->A`; `S:real^3->bool`; `y:real^3`] P3H_NECK_LCK_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The end time of a family of necks: closeness at s0 from closeness on    *)
(* (s0, s0 + w), by continuity of the flow at c0 + s0 / R.                 *)

let P3H_NECK_ENDPOINT_GEN = prove
 (`!top atlas (Gf:real->A->real^3^3) a b R c0 s0 w k (e:real^3->A) S d1 y.
     ricci_flow_on (top,atlas) a b Gf /\ &0 < R /\
     a < c0 + s0 / R /\ c0 + (s0 + w) / R < b /\ &0 < w /\ w <= &1 / &2 /\ s0 + w <= &0 /\
     mfd_param top atlas S e /\ S SUBSET ((:real^3) DELETE vec 0) /\ y IN S /\
     &0 <= d1 /\ d1 <= &1 / &4 /\
     (!s. s0 < s /\ s < s0 + w
          ==> lck_dist2 k (cylinder_flow s)
                (\z. R %% rfs_pullback atlas e (Gf(c0 + s / R)) z) y <= d1)
     ==> lck_dist2 k (cylinder_flow s0)
           (\z. R %% rfs_pullback atlas e (Gf(c0 + s0 / R)) z) y <= d1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))))))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  ABBREV_TAC `t0 = c0 + s0 / R` THEN
  SUBGOAL_THEN `!s. s0 <= s /\ s < s0 + w ==> a < c0 + s / R /\ c0 + s / R < b`
  (LABEL_TAC "rng") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s0 / R <= s / R /\ s / R < (s0 + w) / R` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_DIV2_EQ]; ALL_TAC] THEN
    UNDISCH_TAC `c0 + s0 / R = t0` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `G = \s z. R %% rfs_pullback atlas (e:real^3->A) ((Gf:real->A->real^3^3)
                                                              (c0 + s / R)) z` THEN
  SUBGOAL_THEN `!s. s0 <= s /\ s < s0 + w ==> metric_field S ((G:real->real^3->real^3^3) s)`
  (LABEL_TAC "mf") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    USE_THEN "rng" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `c0 + s / R`;
                   `c0 + s / R`; `k:num`; `e:real^3->A`; `S:real^3->bool`; `y:real^3`]
                  P3H_NECK_LCK_CHART) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `S:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!th. &0 < th
         ==> sqrt(lck_dist2 k (cylinder_flow s0) ((G:real->real^3->real^3^3) s0) y)
             <= sqrt d1 + th`
  (LABEL_TAC "epsb") THENL
   [X_GEN_TAC `th:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k + 2`; `sqrt d1`; `sqrt d1 + th`; `M:real`] P2BL_EXT_ARITH) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar")))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `t0:real`;
                   `k:num`; `(e:real^3->A) y`; `h pow 2`] P2BL_SLICE_PT_CONT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN
      USE_THEN "rng" (MP_TAC o SPEC `s0:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pc"))) THEN
    ABBREV_TAC `m = min h (min (eta * R) w)` THEN
    SUBGOAL_THEN `&0 < m /\ m <= h /\ m <= eta * R /\ m <= w` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN
      ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_MUL; REAL_MIN_LE; REAL_LE_REFL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `s = s0 + m / &2` THEN
    SUBGOAL_THEN `s0 < s /\ s < s0 + w /\ s <= &0 /\ abs(s0 - s) <= h /\
                  abs(s0 - s) <= &1 / &2 /\ abs((c0 + s / R) - t0) < eta`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "t0" THEN
        SUBGOAL_THEN `(c0 + (s0 + m / &2) / R) - (c0 + s0 / R) = (m / &2) / R`
        SUBST1_TAC THENL [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < (m / &2) / R` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_LDIV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "rng" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ABBREV_TAC `L = lck_dist2 k ((G:real->real^3->real^3^3) s) (G s0) y` THEN
    SUBGOAL_THEN `&0 <= L /\ L <= h pow 2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "mf" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "G" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `c0 + s / R`;
                     `t0:real`; `k:num`; `e:real^3->A`; `S:real^3->bool`; `y:real^3`]
                    P3H_NECK_LCK_CHART) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "rng" (MP_TAC o SPEC `s0:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "pc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `metric_field S ((G:real->real^3->real^3^3) s) /\
                  metric_field S ((G:real->real^3->real^3^3) s0) /\
                  lck_dist2 k (cylinder_flow s) ((G:real->real^3->real^3^3) s) y <= d1`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "G" THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `M:real`; `S:real^3->bool`;
                   `(G:real->real^3->real^3^3) s`; `(G:real->real^3->real^3^3) s0`;
                   `s:real`; `s0:real`; `y:real^3`; `d1:real`; `L:real`]
                  P2BL_CYL_TRANSFER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs(s0 - s)) pow (k + 2) *
                (sqrt d1 + sqrt(M * L) + &2 * abs(s0 - s))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ar" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow s0) ((G:real->real^3->real^3^3) s0) y)
                <= sqrt d1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "epsb" (MP_TAC o SPEC
      `(sqrt(lck_dist2 k (cylinder_flow s0) ((G:real->real^3->real^3^3) s0) y) -
        sqrt d1) / &2`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow s0) ((G:real->real^3->real^3^3) s0) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[GRGD_PARAM_FACTS]];
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MONO_LE_EQ] THEN EXPAND_TAC "G" THEN ASM_REWRITE_TAC[]);;

(* Closeness at s0 on a compact set extends to flow times c0 + s / R and    *)
(* cylinder times s' with |s - s0|, |s' - s0| <= h, s' <= 0, with any larger *)
(* bound d2 (tube lemma plus the base change of P2BL_CYL_TRANSFER).          *)

let P3H_NECK_SHIFT_GEN = prove
 (`!top atlas (Gf:real->A->real^3^3) a b R c0 s0 k (e:real^3->A) S K0 d1 d2.
     ricci_flow_on (top,atlas) a b Gf /\ &0 < R /\ a < c0 + s0 / R /\ c0 + s0 / R < b /\
     s0 <= &0 /\ mfd_param top atlas S e /\ S SUBSET ((:real^3) DELETE vec 0) /\
     compact K0 /\ K0 SUBSET S /\ &0 <= d1 /\ d1 < d2 /\ d1 <= &1 / &4 /\
     (!y. y IN K0 ==> lck_dist2 k (cylinder_flow s0)
                        (\z. R %% rfs_pullback atlas e (Gf(c0 + s0 / R)) z) y <= d1)
     ==> ?h. &0 < h /\
             !s s' y. abs(s - s0) <= h /\ abs(s' - s0) <= h /\ s' <= &0 /\ y IN K0
                      ==> a < c0 + s / R /\ c0 + s / R < b /\
                          lck_dist2 k (cylinder_flow s')
                            (\z. R %% rfs_pullback atlas e (Gf(c0 + s / R)) z) y <= d2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))))))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(SPEC `k:num` (REWRITE_RULE[P2B_REQ_LRG_BASE_STATEMENT] P2B_REQ_LRG_BASE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "base"))) THEN
  MP_TAC(SPECL [`k + 2`; `sqrt d1`; `sqrt d2`; `M:real`] P2BL_EXT_ARITH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LT_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `c0 + s0 / R`;
                 `k:num`; `e:real^3->A`; `S:real^3->bool`; `K0:real^3->bool`; `h1 pow 2`]
                P3H_NECK_TUBE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tb"))) THEN
  EXISTS_TAC `min h1 (min (eta * R / &2)
                       (min ((c0 + s0 / R - a) * R / &2) ((b - (c0 + s0 / R)) * R / &2)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `s':real`; `y:real^3`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((c0 + s / R) - (c0 + s0 / R)) = abs(s - s0) / R` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c0 + s / R) - (c0 + s0 / R) = (s - s0) / R` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < R ==> abs R = R`];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(s - s0) / R <= eta / &2 /\
                abs(s - s0) / R <= (c0 + s0 / R - a) / &2 /\
                abs(s - s0) / R <= (b - (c0 + s0 / R)) / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `eta * R / &2`; EXISTS_TAC `(c0 + s0 / R - a) * R / &2`;
      EXISTS_TAC `(b - (c0 + s0 / R)) * R / &2`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < c0 + s / R /\ c0 + s / R < b /\
                abs((c0 + s / R) - (c0 + s0 / R)) < eta` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= abs(s - s0) / R` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs((c0 + s / R) - (c0 + s0 / R)) = abs(s - s0) / R` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G0 = \z. R %% rfs_pullback atlas (e:real^3->A)
                                ((Gf:real->A->real^3^3) (c0 + s0 / R)) z` THEN
  ABBREV_TAC `G1 = \z. R %% rfs_pullback atlas (e:real^3->A)
                                ((Gf:real->A->real^3^3) (c0 + s / R)) z` THEN
  SUBGOAL_THEN `y IN (S:real^3->bool)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (G0:real^3->real^3^3) /\ metric_field S (G1:real^3->real^3^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G0"; "G1"] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `c0 + s0 / R`;
                     `c0 + s0 / R`; `k:num`; `e:real^3->A`; `S:real^3->bool`; `y:real^3`]
                    P3H_NECK_LCK_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `Gf:real->A->real^3^3`; `a:real`; `b:real`; `R:real`; `c0 + s / R`;
                     `c0 + s / R`; `k:num`; `e:real^3->A`; `S:real^3->bool`; `y:real^3`]
                    P3H_NECK_LCK_CHART)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = lck_dist2 k (G0:real^3->real^3^3) G1 y` THEN
  SUBGOAL_THEN `&0 <= L /\ L <= h1 pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN EXPAND_TAC "G1" THEN
      USE_THEN "tb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 k (cylinder_flow s0) (G0:real^3->real^3^3) y <= d1` ASSUME_TAC THENL
   [USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `M:real`; `S:real^3->bool`; `G0:real^3->real^3^3`;
                 `G1:real^3->real^3^3`; `s0:real`; `s':real`; `y:real^3`; `d1:real`; `L:real`]
                P2BL_CYL_TRANSFER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow s') (G1:real^3->real^3^3) y) <= sqrt d2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + abs(s' - s0)) pow (k + 2) *
                (sqrt d1 + sqrt(M * L) + &2 * abs(s' - s0))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ar" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow s') (G1:real^3->real^3^3) y` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[GRGD_PARAM_FACTS]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MONO_LE_EQ] THEN EXPAND_TAC "G1" THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The Ricci flow of a persisting region carrying a neck chart:              *)
(* the transported flow is a Ricci flow on the open interval, the chart is a *)
(* parametrization of the restricted last slice and of every slice, and the *)
(* neck coordinates agree (P3H_VFAM_PULLBACK).                              *)
(* ========================================================================= *)

let P3H_VFLOW_NECK = prove
 (`!V W A0 B0 (e:real^3->A) S.
     p2c_regular_view V /\ A0 < B0 /\ rfs_persists V W A0 B0 /\
     mfd_param (rfs_vtop V B0) (rfs_vatlas V B0) S e /\ IMAGE e S SUBSET W
     ==> ricci_flow_on (subtopology (rfs_vtop V B0) W, restrict_atlas (rfs_vatlas V B0) W)
                       A0 B0 (p2c_vfam V W B0) /\
         mfd_param (subtopology (rfs_vtop V B0) W) (restrict_atlas (rfs_vatlas V B0) W) S e /\
         (!u. A0 < u /\ u <= B0
              ==> smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
                  mfd_param (rfs_vtop V u) (rfs_vatlas V u) S e /\
                  !z. z IN S
                      ==> riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
                          rfs_pullback (restrict_atlas (rfs_vatlas V B0) W) e
                                       (p2c_vfam V W B0 u) z =
                          rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))]) THEN
  DISCH_THEN(LABEL_TAC "pers") THEN
  USE_THEN "pers" (MP_TAC o SPEC `B0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `A0:real`; `B0:real`]
                P2C_REGULAR_VFLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2c_vflow; rfs_flow_upto] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) B0`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) B0`;
                   `W:A->bool`; `S:real^3->bool`; `e:real^3->A`] APX_PARAM_RESTRICT_EQ) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  USE_THEN "pers" (MP_TAC o SPEC `u:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) u)
                          (rfs_vatlas V u) S (e:real^3->A)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->A) = (\y. y) o e` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) B0`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) B0`;
      `W:A->bool`; `W:A->bool`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `u:real`; `(e:real^3->A) z`]
                  P2C_REGULAR_SLICE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) u) W` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC P3H_VFAM_PULLBACK THEN EXISTS_TAC `A0:real` THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_persists")) (concl th)))]);;

(* Closed sub-annuli of neck domains: compact, between neck_dom(eps / q) and *)
(* neck_dom(eps / p) for 0 < q < p.                                         *)

let P3H_NECK_DOM_SCALE = prove
 (`!eps p. &0 < eps /\ &0 < p
           ==> rfs_neck_dom (eps / p) =
               annulus (exp(--(p * inv(sqrt(&2) * eps)))) (exp(p * inv(sqrt(&2) * eps)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps / p) = p * inv(sqrt(&2) * eps)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
    REFL_TAC]);;

let P3H_NECK_DOM_CLOSED = prove
 (`!eps p q. &0 < eps /\ &0 < q /\ q < p
             ==> compact (cball(vec 0:real^3,exp(q * inv(sqrt(&2) * eps))) DIFF
                          ball(vec 0,exp(--(q * inv(sqrt(&2) * eps))))) /\
                 rfs_neck_dom (eps / q) SUBSET
                 (cball(vec 0,exp(q * inv(sqrt(&2) * eps))) DIFF
                  ball(vec 0,exp(--(q * inv(sqrt(&2) * eps))))) /\
                 (cball(vec 0,exp(q * inv(sqrt(&2) * eps))) DIFF
                  ball(vec 0,exp(--(q * inv(sqrt(&2) * eps))))) SUBSET
                 rfs_neck_dom (eps / p)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    ASM_SIMP_TAC[P3H_NECK_DOM_SCALE] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P3H_NECK_DOM_SCALE] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(p * inv(sqrt(&2) * eps))) < exp(--(q * inv(sqrt(&2) * eps))) /\
                  exp(q * inv(sqrt(&2) * eps)) < exp(p * inv(sqrt(&2) * eps))`
    MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LT; REAL_LT_NEG2] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Subcase (i) of MT p. 397, the closeness part.  A strong                  *)
(* eps-neck (margin d1) whose sub-neck e(neck_dom(eps / p1)) persists a     *)
(* little before t - 1/Q and after t is, on the smaller closed sub-neck     *)
(* neck_dom(eps / p2), p2 < p1, an evolving neck of some length a > 1 with  *)
(* any larger margin d2, and stays d2-close to the cylinder at time 0 for   *)
(* a short time after t.                                                    *)
(* ========================================================================= *)

let P3H_NECK_EXT_VIEW = prove
 (`!V eps x t (e:real^3->A) p1 p2 eta0 d1 d2.
     p2c_regular_view V /\ rfs_strong_neck V eps x t e /\
     &0 < p2 /\ p2 < p1 /\ p1 < &1 /\ &0 < eta0 /\
     rfs_persists V (IMAGE e (rfs_neck_dom (eps / p1)))
                  (t - &1 / rfs_vscalar V t x - eta0) (t + eta0) /\
     &0 <= d1 /\ d1 < d2 /\ d1 <= &1 / &4 /\
     (!s y. --(&1) < s /\ s <= &0 /\ y IN rfs_neck_dom eps
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                  (\z. rfs_vscalar V t x %%
                       rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                    (rfs_vmetric V (t + s / rfs_vscalar V t x)) z) y <= d1)
     ==> ?a eta. &1 < a /\ &0 < eta /\
           (!u. t - a / rfs_vscalar V t x < u /\ u < t + eta
                ==> smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
                    riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
                    mfd_param (rfs_vtop V u) (rfs_vatlas V u) (rfs_neck_dom (eps / p1)) e) /\
           (!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom (eps / p2)
                  ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                        (\z. rfs_vscalar V t x %%
                             rfs_pullback (rfs_vatlas V (t + s / rfs_vscalar V t x)) e
                                          (rfs_vmetric V (t + s / rfs_vscalar V t x)) z) y
                      <= d2) /\
           (!u y. t <= u /\ u < t + eta /\ y IN rfs_neck_dom (eps / p2)
                  ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                        (\z. rfs_vscalar V t x %%
                             rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) z) y <= d2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pers1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))))))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[real_div; REAL_MUL_LZERO; REAL_ADD_RID])] THEN
  SUBGOAL_THEN `rfs_neck (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t,rfs_vatlas V t)
                         (rfs_vmetric V t) eps x (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) eps x t (e:real^3->A)` THEN
    SIMP_TAC[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x` THEN
  ABBREV_TAC `S = rfs_neck_dom (eps / p1)` THEN
  ABBREV_TAC `W1 = IMAGE (e:real^3->A) S` THEN
  ABBREV_TAC `A0 = t - &1 / Q - eta0` THEN ABBREV_TAC `B0 = t + eta0` THEN
  SUBGOAL_THEN `&0 < p1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `S SUBSET rfs_neck_dom eps /\ open (S:real^3->bool) /\
                S SUBSET ((:real^3) DELETE vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[APX_NECK_DOM_OPEN; P2BL_NECK_DOM_NZ] THEN
    MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) t)
                          (rfs_vatlas V t) S (e:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 < t /\ t <= B0 /\ A0 < B0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A0"; "B0"] THEN
    SUBGOAL_THEN `&0 < &1 / Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) B0)
                          (rfs_vatlas V B0) S (e:real^3->A)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->A) = (\y. y) o e` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) t`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) t`;
      `W1:A->bool`; `W1:A->bool`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "pers1" (MP_TAC o SPEC `B0:real` o
        GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "W1" THEN REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W1:A->bool`; `A0:real`; `B0:real`;
                 `e:real^3->A`; `S:real^3->bool`] P3H_VFLOW_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "W1" THEN REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  ABBREV_TAC `TOP = subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) B0) W1` THEN
  ABBREV_TAC `ATL = restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) B0) W1` THEN
  ABBREV_TAC `Fl = p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W1 B0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  SUBGOAL_THEN `!y:real^3. y IN S ==> y IN rfs_neck_dom eps` (LABEL_TAC "Sdom") THENL
   [UNDISCH_TAC `S SUBSET rfs_neck_dom eps` THEN REWRITE_TAC[SUBSET] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u (C:real^3->real^3^3) y.
       A0 < u /\ u <= B0 /\ y IN S
       ==> lck_dist2 (rfs_kreg eps) C
             (\z. Q %% rfs_pullback ATL (e:real^3->A) (Fl u) z) y =
           lck_dist2 (rfs_kreg eps) C
             (\z. Q %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) e
                     (rfs_vmetric V u) z) y`
  (LABEL_TAC "tr") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "uc" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. --(&1) < s /\ s <= &0 ==> A0 < t + s / Q /\ t + s / Q <= B0`
  (LABEL_TAC "rng") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `--(&1) / Q < s / Q /\ s / Q <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A0"; "B0"] THEN REWRITE_TAC[real_div] THEN
    UNDISCH_TAC `&0 < eta0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. --(&1) < s /\ s <= &0 /\ y IN S
          ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                (\z. Q %% rfs_pullback ATL (e:real^3->A) (Fl (t + s / Q)) z) y <= d1`
  (LABEL_TAC "cl1") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "rng" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "tr" (MP_TAC o SPECL [`t + s / Q`; `cylinder_flow s`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "Sdom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `p1:real`; `p2:real`] P3H_NECK_DOM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K0 = cball(vec 0:real^3,exp(p2 * inv(sqrt(&2) * eps))) DIFF
                   ball(vec 0,exp(--(p2 * inv(sqrt(&2) * eps))))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN K0 ==> y IN S` (LABEL_TAC "KS") THENL
   [UNDISCH_TAC `(K0:real^3->bool) SUBSET S` THEN REWRITE_TAC[SUBSET] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom (eps / p2) ==> y IN K0` (LABEL_TAC "dK") THENL
   [UNDISCH_TAC `rfs_neck_dom (eps / p2) SUBSET (K0:real^3->bool)` THEN
    REWRITE_TAC[SUBSET] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A0 < t + --(&1) / Q /\ t + (--(&1) + &1 / &2) / Q < B0 /\
                t + --(&1) / Q < B0 /\ A0 < t + &0 / Q /\ t + &0 / Q < B0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv Q` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A0"; "B0"] THEN REWRITE_TAC[real_div] THEN
    UNDISCH_TAC `&0 < inv Q` THEN UNDISCH_TAC `&0 < eta0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN K0
        ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (--(&1)))
              (\z. Q %% rfs_pullback ATL (e:real^3->A) (Fl (t + --(&1) / Q)) z) y <= d1`
  (LABEL_TAC "ep") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`TOP:A topology`; `ATL:((A->bool)#(A->real^3))->bool`;
                   `Fl:real->A->real^3^3`; `A0:real`; `B0:real`; `Q:real`; `t:real`;
                   `--(&1)`; `&1 / &2`; `rfs_kreg eps`; `e:real^3->A`; `S:real^3->bool`;
                   `d1:real`; `y:real^3`] P3H_NECK_ENDPOINT_GEN) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 / &2 /\ --(&1) + &1 / &2 <= &0`; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "KS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "cl1" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; USE_THEN "KS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`TOP:A topology`; `ATL:((A->bool)#(A->real^3))->bool`;
                 `Fl:real->A->real^3^3`; `A0:real`; `B0:real`; `Q:real`; `t:real`;
                 `--(&1)`; `rfs_kreg eps`; `e:real^3->A`; `S:real^3->bool`; `K0:real^3->bool`;
                 `d1:real`; `d2:real`] P3H_NECK_SHIFT_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `--(&1) <= &0`] THEN USE_THEN "ep" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bk"))) THEN
  MP_TAC(ISPECL [`TOP:A topology`; `ATL:((A->bool)#(A->real^3))->bool`;
                 `Fl:real->A->real^3^3`; `A0:real`; `B0:real`; `Q:real`; `t:real`;
                 `&0`; `rfs_kreg eps`; `e:real^3->A`; `S:real^3->bool`; `K0:real^3->bool`;
                 `d1:real`; `d2:real`] P3H_NECK_SHIFT_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "cl1" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; USE_THEN "KS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fw"))) THEN
  SUBGOAL_THEN `(basis 1:real^3) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MP_TAC(SPEC `eps / p1` APX_UNIT_SPHERE_NECK_DOM) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `m = min h1 (Q * eta0)` THEN
  SUBGOAL_THEN `&0 < m /\ m <= h1 /\ m <= Q * eta0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min (h2 / Q) eta0 /\ Q * min (h2 / Q) eta0 <= h2 /\
                min (h2 / Q) eta0 <= eta0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_DIV];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * (h2 / Q)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `n = min (h2 / Q) eta0` THEN
  EXISTS_TAC `&1 + m / &2` THEN EXISTS_TAC `n / &2` THEN
  SUBGOAL_THEN `&0 < inv Q /\ (m / &2) / Q <= eta0 / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `A0 < u /\ u <= B0` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(&1 + m / &2) / Q = &1 / Q + (m / &2) / Q` ASSUME_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["A0"; "B0"] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "uc" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `basis 1:real^3`))) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN K0 /\ y IN S` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN K0` ASSUME_TAC THENL
       [USE_THEN "dK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "KS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `--(&1) < s` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d1:real` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "Sdom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "bk" (MP_TAC o SPECL [`s:real`; `s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    USE_THEN "tr" (MP_TAC o SPECL [`t + s / Q`; `cylinder_flow s`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN K0 /\ y IN S` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN K0` ASSUME_TAC THENL
       [USE_THEN "dK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "KS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t + (Q * (u - t)) / Q = u` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Q * (u - t) /\ Q * (u - t) <= h2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "fw" (MP_TAC o SPECL [`Q * (u - t)`; `&0`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "tr" (MP_TAC o SPECL [`u:real`; `cylinder_flow (&0)`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Arithmetic for the recentred necks: for p close to 1, the                 *)
(* scale ratio c close to 1 and the cylinder time shift u small, the bound  *)
(* of P3H_RCT_SLICE after P3H_RESCALE_TIME stays below some B < eps.        *)
(* ========================================================================= *)

let P3H_RCT_INNER = prove
 (`!k sd K w c u.
     &0 <= sd /\ &0 < K /\ &4 + (&2 * (&2 pow (k + 2) - &1) + &1) * (sd + &2) <= K /\
     &0 < w /\ w <= &1 / &4 /\ abs(c - &1) <= w /\ &0 <= u /\ u <= w
     ==> c * ((&1 + u) pow (k + 2) * (sd + &2 * u)) + abs(c - &1) * sqrt(&3) <= sd + K * w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M1 = &2 pow (k + 2) - &1` THEN
  SUBGOAL_THEN `&0 <= M1` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN
    SUBGOAL_THEN `&1 <= &2 pow (k + 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k + 2`; `u:real`] P3H_POW_CONVEX) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `&1 <= (&1 + u) pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 = sqrt(&2 pow 2)` (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) * sqrt(&3) <= w * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; SQRT_POS_LE; REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `P = (&1 + u) pow (k + 2)` THEN
  SUBGOAL_THEN `c * (P * (sd + &2 * u)) <= (&1 + w) * ((&1 + M1 * w) * (sd + &2 * w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + M1 * u` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> &1 + a <= &1 + b`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `M1 * w * w <= M1 * w /\ w * w <= w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + w) * (&1 + M1 * w) <= &1 + (&2 * M1 + &1) * w` ASSUME_TAC THENL
   [UNDISCH_TAC `M1 * w * w <= M1 * w` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + w) * ((&1 + M1 * w) * (sd + &2 * w)) <=
                (&1 + (&2 * M1 + &1) * w) * (sd + &2 * w)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((&2 * M1 + &1) * w) * sd <= ((&2 * M1 + &1) * sd) * w /\
                ((&2 * M1 + &1) * w) * (&2 * w) <= (&2 * (&2 * M1 + &1)) * w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `((&2 * M1 + &1) * w) * (&2 * w) = (&2 * (&2 * M1 + &1)) * (w * w)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&4 + (&2 * M1 + &1) * (sd + &2)) * w <= K * w` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_RCT_ARITH = prove
 (`!k d2 eps.
     &0 <= d2 /\ d2 < eps pow 2 /\ &0 < eps
     ==> ?p0 w0 B. &1 / &2 <= p0 /\ p0 < &1 /\ &0 < w0 /\ w0 <= &1 / &4 /\
                   &0 <= B /\ B < eps /\
           !p c u s. p0 <= p /\ p < &1 /\ abs(c - &1) <= w0 /\ &0 <= u /\ u <= w0 /\
                     --(&1) < s /\ s <= &0
                     ==> abs(s - (&1 - (&1 - s) / p pow 2)) <= &1 / &2 /\
                         (&1 + abs(s - (&1 - (&1 - s) / p pow 2))) pow (k + 2) *
                         (max (&1) (p pow 2) pow (k + 2) *
                          (c * ((&1 + u) pow (k + 2) * (sqrt d2 + &2 * u)) +
                           abs(c - &1) * sqrt(&3)) +
                          abs(p pow 2 - &1) * sqrt(&3) +
                          &2 * abs(s - (&1 - (&1 - s) / p pow 2))) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt d2 < eps /\ &0 <= sqrt d2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S1 = (sqrt d2 + eps) / &2` THEN
  SUBGOAL_THEN `sqrt d2 < S1 /\ S1 < eps /\ &0 <= S1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `S1 pow 2`; `eps:real`; `&1`] P3H_CMP_ARITH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE] THEN REWRITE_TAC[REAL_LE_REFL; REAL_LT_01] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ar"))))))) THEN
  ABBREV_TAC `K = &4 + (&2 * (&2 pow (k + 2) - &1) + &1) * (sqrt d2 + &2)` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN `&1 <= &2 pow (k + 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &4 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min (&1 / &4) ((S1 - sqrt d2) / K) /\
                min (&1 / &4) ((S1 - sqrt d2) / K) <= &1 / &4 /\
                K * min (&1 / &4) ((S1 - sqrt d2) / K) <= S1 - sqrt d2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * (S1 - sqrt d2) / K` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < K` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  ABBREV_TAC `w = min (&1 / &4) ((S1 - sqrt d2) / K)` THEN
  MAP_EVERY EXISTS_TAC [`p0:real`; `w:real`; `B:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `c:real`; `u:real`; `s:real`] THEN STRIP_TAC THEN
  USE_THEN "ar" (MP_TAC o SPECL [`p:real`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`k:num`; `sqrt d2`; `K:real`; `w:real`; `c:real`; `u:real`] P3H_RCT_INNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  ABBREV_TAC `X = c * ((&1 + u) pow (k + 2) * (sqrt d2 + &2 * u)) + abs(c - &1) * sqrt(&3)` THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= B ==> a <= B`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* One slice of the recentred neck: from closeness of Q e^* g to the        *)
(* cylinder at time sg on S, closeness of R ((e o r f) o pw_p)^* g to the     *)
(* cylinder at time s, |s - sg| <= u.                                        *)

let P3H_RCT_FULL = prove
 (`!top atlas (g:A->real^3^3) (e:real^3->A) S eps p r (f:real^3->real^3) Q R d2 k s sg u y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas S e /\ open S /\ S SUBSET ((:real^3) DELETE vec 0) /\
     &0 < eps /\ &0 < p /\ p <= &1 /\ &0 < r /\ orthogonal_transformation f /\
     annulus (r * exp(--(inv(sqrt(&2) * eps / p)))) (r * exp(inv(sqrt(&2) * eps / p)))
       SUBSET S /\
     &0 < Q /\ &0 < R /\ s <= &0 /\ abs(s - (&1 - (&1 - s) / p pow 2)) <= &1 / &2 /\
     abs(s - sg) <= u /\ u <= &1 / &2 /\ &0 <= d2 /\
     (!w. w IN S
          ==> lck_dist2 k (cylinder_flow sg) (\z. Q %% rfs_pullback atlas e g z) w <= d2) /\
     y IN rfs_neck_dom eps
     ==> sqrt(lck_dist2 k (cylinder_flow s)
                (\z. R %% rfs_pullback atlas
                       ((e o (\z. r % f z)) o
                        (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z)) g z) y) <=
         (&1 + abs(s - (&1 - (&1 - s) / p pow 2))) pow (k + 2) *
         (max (&1) (p pow 2) pow (k + 2) *
          (R / Q * ((&1 + u) pow (k + 2) * (sqrt d2 + &2 * u)) + abs(R / Q - &1) * sqrt(&3)) +
          abs(p pow 2 - &1) * sqrt(&3) + &2 * abs(s - (&1 - (&1 - s) / p pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R / Q /\ R / Q * Q = R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV] THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `c = R / Q` THEN
  ABBREV_TAC `X = c * ((&1 + u) pow (k + 2) * (sqrt d2 + &2 * u)) + abs(c - &1) * sqrt(&3)` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS; SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `e:real^3->A`; `S:real^3->bool`; `eps:real`; `p:real`; `r:real`;
                 `f:real^3->real^3`; `R:real`; `X pow 2`; `k:num`; `s:real`; `y:real^3`]
                P3H_RCT_SLICE) THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `H = \z. Q %% rfs_pullback atlas (e:real^3->A) g z` THEN
  SUBGOAL_THEN `metric_field S (H:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. R %% rfs_pullback atlas (e:real^3->A) g z) = (\z. c %% H z)`
  SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_CMUL_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `sg:real`; `s:real`; `H:real^3->real^3^3`; `c:real`;
                 `S:real^3->bool`; `w:real^3`] P3H_RESCALE_TIME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow s) (\z. c %% (H:real^3->real^3^3) z) w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow s) (\z. c %% (H:real^3->real^3^3) z) w) <= X`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * ((&1 + abs(s - sg)) pow (k + 2) *
                     (sqrt(lck_dist2 k (cylinder_flow sg) (H:real^3->real^3^3) w) +
                      &2 * abs(s - sg))) + abs(c - &1) * sqrt(&3)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "X" THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + e <= b + e`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
        EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `a <= b /\ x <= y ==> a + &2 * x <= b + &2 * y`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `lck_dist2 k (cylinder_flow s) (\z. c %% (H:real^3->real^3^3) z) w =
                sqrt(lck_dist2 k (cylinder_flow s) (\z. c %% H z) w) pow 2` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]);;

(* ========================================================================= *)
(* The recentred strong neck at one point (y, s).  From the                 *)
(* extended closeness of the neck chart e at (x, t) (P3H_NECK_EXT_VIEW), a *)
(* linear recentring z -> r f z and the compression pw_p, the chart        *)
(* (e o r f) o pw_p is a strong eps-neck at (y, s), provided R(y, s) / Q is *)
(* close to 1 and the cylinder times of the two parametrizations differ by *)
(* at most w0 (MT p. 397, repaired).                                       *)
(* ========================================================================= *)

let P3H_RCT_NECK = prove
 (`!V eps t Q (e:real^3->A) p p2 p1 a eta d2 w0 B y s r (f:real^3->real^3).
     p2c_regular_view V /\
     &0 < eps /\ &0 < Q /\ &0 < p /\ p < p2 /\ p2 < p1 /\ p1 < &1 /\ &1 < a /\ &0 < eta /\
     &0 <= d2 /\ B < eps /\ &0 <= B /\ w0 <= &1 / &4 /\
     (!c u s'. abs(c - &1) <= w0 /\ &0 <= u /\ u <= w0 /\ --(&1) < s' /\ s' <= &0
               ==> abs(s' - (&1 - (&1 - s') / p pow 2)) <= &1 / &2 /\
                   (&1 + abs(s' - (&1 - (&1 - s') / p pow 2))) pow (rfs_kreg eps + 2) *
                   (max (&1) (p pow 2) pow (rfs_kreg eps + 2) *
                    (c * ((&1 + u) pow (rfs_kreg eps + 2) * (sqrt d2 + &2 * u)) +
                     abs(c - &1) * sqrt(&3)) +
                    abs(p pow 2 - &1) * sqrt(&3) +
                    &2 * abs(s' - (&1 - (&1 - s') / p pow 2))) <= B) /\
     (!u. t - a / Q < u /\ u < t + eta
          ==> smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
              riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
              mfd_param (rfs_vtop V u) (rfs_vatlas V u) (rfs_neck_dom (eps / p1)) e) /\
     (!s y. --a < s /\ s <= &0 /\ y IN rfs_neck_dom (eps / p2)
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s)
                  (\z. Q %% rfs_pullback (rfs_vatlas V (t + s / Q)) e
                                         (rfs_vmetric V (t + s / Q)) z) y <= d2) /\
     (!u y. t <= u /\ u < t + eta /\ y IN rfs_neck_dom (eps / p2)
            ==> lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                  (\z. Q %% rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) z) y <= d2) /\
     &0 < r /\ orthogonal_transformation f /\
     annulus (r * exp(--(inv(sqrt(&2) * eps / p)))) (r * exp(inv(sqrt(&2) * eps / p)))
       SUBSET rfs_neck_dom (eps / p2) /\
     t <= s /\ s < t + eta /\
     &0 < rfs_vscalar V s y /\ abs(rfs_vscalar V s y / Q - &1) <= w0 /\
     t - a / Q <= s - &1 / rfs_vscalar V s y /\
     (!s'. --(&1) < s' /\ s' <= &0 /\ s + s' / rfs_vscalar V s y <= t
           ==> abs(s' - Q * ((s + s' / rfs_vscalar V s y) - t)) <= w0) /\
     (!s'. --(&1) < s' /\ s' <= &0 /\ t < s + s' / rfs_vscalar V s y ==> abs s' <= w0) /\
     y IN IMAGE ((e o (\z. r % f z)) o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z))
                (sphere(vec 0,&1))
     ==> rfs_strong_neck V eps y s
           ((e o (\z. r % f z)) o (\z. ((norm z pow 2) rpow ((p - &1) / &2)) % z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ar")
    (CONJUNCTS_THEN2 (LABEL_TAC "par") (CONJUNCTS_THEN2 (LABEL_TAC "bk")
    (CONJUNCTS_THEN2 (LABEL_TAC "fw") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sh1")
    (CONJUNCTS_THEN2 (LABEL_TAC "sh2") ASSUME_TAC))))))))))))))))))))))))))) THEN
  ABBREV_TAC `Ry = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s y` THEN
  ABBREV_TAC `ra = exp(--(inv(sqrt(&2) * eps / p)))` THEN
  ABBREV_TAC `rb = exp(inv(sqrt(&2) * eps / p))` THEN
  SUBGOAL_THEN `rfs_neck_dom (eps / p) = annulus ra rb` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ra"; "rb"] THEN REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ra` ASSUME_TAC THENL
   [EXPAND_TAC "ra" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `p:real`] P3H_PW_DOM) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `pw = \z:real^3. ((norm z pow 2) rpow ((p - &1) / &2)) % z` THEN
  ABBREV_TAC `pw' = \z:real^3. norm z rpow (inv p - &1) % z` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `f:real^3->real^3`; `ra:real`; `rb:real`] P3H_ORTH_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = \z:real^3. r % (f:real^3->real^3) z` THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^3->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M' = \z:real^3. inv r % (f':real^3->real^3) z` THEN
  SUBGOAL_THEN `rfs_neck_dom (eps / p2) SUBSET rfs_neck_dom (eps / p1)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN
    SUBGOAL_THEN `&0 < p1 /\ &0 < p2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_DIV2_EQ] THEN
    ASM_SIMP_TAC[real_div; REAL_LE_LMUL_EQ] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. t - a / Q < u /\ u < t + eta
        ==> mfd_param (rfs_vtop V u) (rfs_vatlas V u) (rfs_neck_dom (eps / p2)) (e:real^3->A) /\
            mfd_param (rfs_vtop V u) (rfs_vatlas V u) (rfs_neck_dom eps)
                      (((e:real^3->A) o (M:real^3->real^3)) o (pw:real^3->real^3)) /\
            open_in (rfs_vtop V u) (IMAGE (((e:real^3->A) o (M:real^3->real^3)) o (pw:real^3->real^3)) (rfs_neck_dom eps))`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `u:real` THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                    (rfs_vatlas V u) (rfs_neck_dom (eps / p2)) (e:real^3->A)` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom (eps / p1)` THEN
      ASM_REWRITE_TAC[APX_NECK_DOM_OPEN];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                    (rfs_vatlas V u) (annulus ra rb) ((e:real^3->A) o (M:real^3->real^3))` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`rfs_neck_dom (eps / p2)`; `annulus (r * ra) (r * rb):real^3->bool`;
                            `M':real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                    (rfs_vatlas V u) (rfs_neck_dom eps) (((e:real^3->A) o (M:real^3->real^3)) o (pw:real^3->real^3))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`annulus ra rb:real^3->bool`; `annulus ra rb:real^3->bool`;
                            `pw':real^3->real^3`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      UNDISCH_TAC `diffeomorphism_on (rfs_neck_dom eps) (rfs_neck_dom (eps / p))
                     (pw:real^3->real^3) pw'` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s' z. --(&1) < s' /\ s' <= &0 /\ z IN rfs_neck_dom eps
           ==> lck_dist2 (rfs_kreg eps) (cylinder_flow s')
                 (\w. Ry %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (s + s' / Ry))
                         (((e:real^3->A) o (M:real^3->real^3)) o (pw:real^3->real^3)) (rfs_vmetric V (s + s' / Ry)) w) z
               <= B pow 2`
  (LABEL_TAC "fam") THENL
   [MAP_EVERY X_GEN_TAC [`s':real`; `z:real^3`] THEN STRIP_TAC THEN
    ABBREV_TAC `tau = s + s' / Ry` THEN
    SUBGOAL_THEN `t - a / Q < tau /\ tau <= s` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN
      SUBGOAL_THEN `--(&1) / Ry < s' / Ry /\ s' / Ry <= &0` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
      UNDISCH_TAC `t - a / Q <= s - &1 / Ry` THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "par" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "key" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN
     `?sg. abs(s' - sg) <= w0 /\
           !w. w IN rfs_neck_dom (eps / p2)
               ==> lck_dist2 (rfs_kreg eps) (cylinder_flow sg)
                     (\z. Q %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tau)
                             (e:real^3->A) (rfs_vmetric V tau) z) w <= d2`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `tau <= t` THENL
       [EXISTS_TAC `Q * (tau - t)` THEN CONJ_TAC THENL
         [USE_THEN "sh1" (MP_TAC o SPEC `s':real`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `t + (Q * (tau - t)) / Q = tau` ASSUME_TAC THENL
         [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        USE_THEN "bk" (MP_TAC o SPECL [`Q * (tau - t)`; `w:real^3`]) THEN
        ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `--(a / Q) < tau - t` ASSUME_TAC THENL
           [UNDISCH_TAC `t - a / Q < tau` THEN REAL_ARITH_TAC; ALL_TAC] THEN
          MP_TAC(SPECL [`Q:real`; `--(a / Q)`; `tau - t`] REAL_LT_LMUL) THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `a = b ==> b < c ==> a < c`) THEN
          UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD;
          MATCH_MP_TAC(REAL_ARITH `&0 <= Q * (t - tau) ==> Q * (tau - t) <= &0`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        EXISTS_TAC `&0` THEN CONJ_TAC THENL
         [USE_THEN "sh2" (MP_TAC o SPEC `s':real`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          ALL_TAC] THEN
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN USE_THEN "fw" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "ar" (MP_TAC o SPECL [`Ry / Q`; `abs(s' - sg)`; `s':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_POS]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tau`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tau`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tau`;
                   `e:real^3->A`; `rfs_neck_dom (eps / p2)`; `eps:real`; `p:real`; `r:real`;
                   `f:real^3->real^3`; `Q:real`; `Ry:real`; `d2:real`; `rfs_kreg eps`;
                   `s':real`; `sg:real`; `abs(s' - sg)`; `z:real^3`] P3H_RCT_FULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[APX_NECK_DOM_OPEN; P2BL_NECK_DOM_NZ; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `L = lck_dist2 (rfs_kreg eps) (cylinder_flow s')
                      (\w. Ry %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tau)
                              (((e:real^3->A) o (M:real^3->real^3)) o (pw:real^3->real^3)) (rfs_vmetric V tau) w) z` THEN
    SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
        EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) tau` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt L <= B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `L = sqrt L pow 2` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT; REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rfs_neck] THEN
    USE_THEN "par" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `&0 < a / Q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      STRIP_TAC] THEN
    USE_THEN "key" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `&0 < a / Q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)
                    (rfs_vmetric V s) y = Ry` SUBST1_TAC THENL
     [EXPAND_TAC "Ry" THEN REWRITE_TAC[P2B9_RFS_VSCALAR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `B pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "fam" (MP_TAC o SPECL [`&0`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID];
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t - a / Q < u /\ u < t + eta` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "par" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "key" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `B pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Openness of strong necks, subcase (i) of MT p. 397, view                 *)
(* form.  For a strong eps-neck e at (x, t) there is p1 < 1 such that, if   *)
(* the sub-neck e(neck_dom(eps / p1)) persists a little before t - 1/Q and  *)
(* after t and R is continuous at (x, t) forward in time, every (y, s)      *)
(* close to (x, t) with s >= t is the centre of a strong eps-neck.          *)
(* ========================================================================= *)

(* Time shifts of the recentred parametrization.                          *)

let P3H_SHIFT_ARITH = prove
 (`!Q Ry w1 w0 s t s'.
     &0 < Q /\ &0 < w1 /\ w1 <= &1 / &2 /\ w1 <= w0 / &4 /\ abs(Ry - Q) < Q * w1 /\
     t <= s /\ Q * (s - t) <= w0 / &4 /\ --(&1) < s' /\ s' <= &0
     ==> &0 < Ry /\ abs(s' - Q * ((s + s' / Ry) - t)) <= w0 /\
         (t < s + s' / Ry ==> abs s' <= w0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `Q * w1 <= Q / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `Q * w1 <= Q * (&1 / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q / &2 <= Ry` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Ry` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s' - Q * ((s + s' / Ry) - t) = s' * ((Ry - Q) / Ry) - Q * (s - t)` SUBST1_TAC
  THENL [UNDISCH_TAC `&0 < Ry` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `abs((Ry - Q) / Ry) <= &2 * w1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < Ry ==> abs Ry = Ry`; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * w1` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `w1 * Q <= w1 * (&2 * Ry)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(s' * ((Ry - Q) / Ry)) <= &2 * w1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * abs((Ry - Q) / Ry)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q * (s - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `--s' < Ry * (s - t)` ASSUME_TAC THENL
   [SUBGOAL_THEN `--(s' / Ry) < s - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`Ry:real`; `--(s' / Ry)`; `s - t`] REAL_LT_LMUL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `a = b ==> a < c ==> b < c`) THEN
    UNDISCH_TAC `&0 < Ry` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Ry * (s - t) <= (&2 * Q) * (s - t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_NECK_OPEN_I = prove
 (`!V eps x t (e:real^3->A).
     p2c_regular_view V /\ rfs_strong_neck V eps x t e /\ eps <= &1 / &2
     ==> ?p1. &0 < p1 /\ p1 < &1 /\
           !eta0. &0 < eta0 /\
                  rfs_persists V (IMAGE e (rfs_neck_dom (eps / p1)))
                               (t - &1 / rfs_vscalar V t x - eta0) (t + eta0) /\
                  (!th. &0 < th
                        ==> ?N0 d0. open_in (rfs_vtop V t) N0 /\ x IN N0 /\ &0 < d0 /\
                                    !s y. t <= s /\ s < t + d0 /\ y IN N0
                                          ==> abs(rfs_vscalar V s y - rfs_vscalar V t x) < th)
                  ==> ?N d. open_in (rfs_vtop V t) N /\ x IN N /\ &0 < d /\
                            !s y. t <= s /\ s < t + d /\ y IN N
                                  ==> y IN topspace(rfs_vtop V s) /\
                                      ?e'. rfs_strong_neck V eps y s e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[real_div; REAL_MUL_LZERO; REAL_ADD_RID])] THEN
  MP_TAC(REWRITE_RULE[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT]
    (ASSUME `rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) eps x t (e:real^3->A)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t x` THEN
  ABBREV_TAC `d1' = max (&0) d1` THEN
  SUBGOAL_THEN `eps pow 2 <= &1 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d1' /\ d1' < eps pow 2 /\ d1 <= d1'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d1'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d2 = (d1' + eps pow 2) / &2` THEN
  SUBGOAL_THEN `d1' < d2 /\ d2 < eps pow 2 /\ &0 <= d2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`rfs_kreg eps`; `d2:real`; `eps:real`] P3H_RCT_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `w0:real` (X_CHOOSE_THEN `B:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "ar0")))))))))) THEN
  ABBREV_TAC `p1 = (p + &2) / &3` THEN ABBREV_TAC `p2 = (&2 * p + &1) / &3` THEN
  SUBGOAL_THEN `&0 < p /\ p < p2 /\ p2 < p1 /\ p1 < &1 /\ &0 < p1 /\ &0 < p2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p1"; "p2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `p1:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eta0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rc"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `eps:real`; `x:A`; `t:real`; `e:real^3->A`;
                 `p1:real`; `p2:real`; `eta0:real`; `d1':real`; `d2:real`]
                P3H_NECK_EXT_VIEW) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d1:real` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `eta:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par")
      (CONJUNCTS_THEN2 (LABEL_TAC "bk") (LABEL_TAC "fw"))))))) THEN
  ABBREV_TAC `w1 = min (w0 / &4) ((a - &1) / (&4 * a))` THEN
  SUBGOAL_THEN `&0 < w1 /\ w1 <= w0 / &4 /\ w1 <= &1 / &2 /\ &1 <= a * (&1 - w1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * a /\ &0 < (a - &1) / (&4 * a) /\ (a - &1) / (&4 * a) <= &1 / &4 /\
                  a * (a - &1) / (&4 * a) = (a - &1) / &4`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &4 * a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LE_LDIV_EQ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&1 < a` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "w1" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a * min (w0 / &4) ((a - &1) / (&4 * a)) <= a * (a - &1) / (&4 * a)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 < a` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "rc" (MP_TAC o SPEC `Q * w1`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:A->bool` (X_CHOOSE_THEN `d0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "box")))))) THEN
  ABBREV_TAC `L = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  ABBREV_TAC `dr = (p2 - p) * L / &2` THEN
  SUBGOAL_THEN `&0 < dr /\ dr + p * L <= p2 * L /\ dr < L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dr" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= (p2 - p) * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      SUBGOAL_THEN `(p2 - p) * L <= &1 * L` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (exp(--dr)) (exp dr) SUBSET rfs_neck_dom eps /\
                annulus (exp(--dr)) (exp dr) SUBSET rfs_neck_dom (eps / p1) /\
                sphere(vec 0:real^3,&1) SUBSET annulus (exp(--dr)) (exp dr)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3H_NECK_DOM_SCALE] THEN REWRITE_TAC[rfs_neck_dom] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `exp(--L) <= exp(--dr) /\ exp dr <= exp L /\
                  exp(--(p1 * L)) <= exp(--dr) /\ exp dr <= exp(p1 * L) /\
                  exp(--dr) < &1 /\ &1 < exp dr`
    MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
      SUBGOAL_THEN `dr <= p1 * L` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 <= p * L /\ p2 * L <= p1 * L` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                  (rfs_vatlas V t) (rfs_neck_dom eps) (e:real^3->A) /\
                (x:A) IN IMAGE e (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `dd = min d0 (min (eta / &2) (w0 / (&4 * Q)))` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d0 /\ dd <= eta / &2 /\ Q * dd <= w0 / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < w0 / (&4 * Q) /\ Q * (w0 / (&4 * Q)) = w0 / &4` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &4`] THEN
      UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * (w0 / (&4 * Q))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `N0 INTER IMAGE (e:real^3->A) (annulus (exp(--dr)) (exp dr))` THEN
  EXISTS_TAC `dd:real` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:A) IN IMAGE (e:real^3->A) (annulus (exp(--dr)) (exp dr))` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "box" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `Ry = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s y` THEN
  USE_THEN "par" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `&0 < a / Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s`;
                   `rfs_neck_dom (eps / p1)`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(y0:real^3)` THEN
  SUBGOAL_THEN `exp(--dr) < r /\ r < exp dr /\ &0 < r` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN annulus (exp(--dr)) (exp dr)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `--dr` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x0:real^3`; `inv r % (y0:real^3)`] ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`Q:real`; `Ry:real`; `w1:real`; `w0:real`; `s:real`; `t:real`]
               P3H_SHIFT_ARITH) THEN
  SUBGOAL_THEN `Q * (s - t) <= w0 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * dd` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sha") THEN
  SUBGOAL_THEN `&0 < Ry` ASSUME_TAC THENL
   [USE_THEN "sha" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `((e:real^3->A) o (\z:real^3. r % (f:real^3->real^3) z)) o
              (\z:real^3. ((norm z pow 2) rpow ((p - &1) / &2)) % z)` THEN
  MATCH_MP_TAC P3H_RCT_NECK THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `Q:real`; `p2:real`; `p1:real`; `a:real`; `eta:real`;
                        `d2:real`; `w0:real`; `B:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "ar0" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ASM_SIMP_TAC[P3H_NECK_DOM_SCALE] THEN
    SUBGOAL_THEN `inv(sqrt(&2) * eps / p) = p * L` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--(p2 * L)) <= exp(--dr) * exp(--(p * L)) /\
                  exp dr * exp(p * L) <= exp(p2 * L)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--dr) * exp(--(p * L)) < r * exp(--(p * L)) /\
                  r * exp(p * L) < exp dr * exp(p * L)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `Ry / Q - &1 = (Ry - Q) / Q` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < Q ==> abs Q = Q`; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * w1` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `Q * w1 <= Q * w0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    SUBGOAL_THEN `&1 / Ry <= a / Q` MP_TAC THENL
     [SUBGOAL_THEN `Q <= a * Ry` ASSUME_TAC THENL
       [SUBGOAL_THEN `Q * &1 <= Q * (a * (&1 - w1))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `a * (Q * (&1 - w1)) <= a * Ry` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `a / Q - &1 / Ry = (a * Ry - Q) / (Q * Ry)` ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN UNDISCH_TAC `&0 < Ry` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (a * Ry - Q) / (Q * Ry)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    USE_THEN "sha" (MP_TAC o SPEC `s':real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    USE_THEN "sha" (MP_TAC o SPEC `s':real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; o_THM] THEN EXISTS_TAC `x0:real^3` THEN
    ASM_REWRITE_TAC[REAL_POW_ONE; RPOW_ONE; VECTOR_MUL_LID] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

(* ========================================================================= *)
(* The history form of subcase (i).  Joint continuity of R on               *)
(* a slab gives two-sided boxes; forward persistence inside the slab of ts  *)
(* is automatic; with the backward persistence of the sub-neck (subcase    *)
(* (i)), every nearby point at a time in [ts, ts + d) has a strong neck.    *)
(* ========================================================================= *)

let P3H_SCALAR_BOX2 = prove
 (`!(hs:(A)rfs_history) k ts x c1 c2.
     rfs_history_ok hs /\ k <= hs_count hs /\
     hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\ x IN topspace(hs_top hs k) /\
     c1 < mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x /\
     mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x < c2
     ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
               !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N
                     ==> c1 < mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y /\
                         mfd_scalar (hs_atlas hs k) (hs_metric hs k s) y < c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `top = hs_top (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `atlas = hs_atlas (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `g = hs_metric (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `b = hs_time (hs:(A)rfs_history) (k + 1)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ts:real`;
                 `b:real`; `g:real->A->real^3^3`] RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `hs_time (hs:(A)rfs_history) k`; `b:real`; `g:real->A->real^3^3`;
                     `t:real`] RFA_RICCI_FLOW_FROM_METRIC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC RFA_RICCI_FLOW_FROM_EXT_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `hs_time (hs:(A)rfs_history) k`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_map; SUBTOPOLOGY_TOPSPACE] THEN
  DISCH_THEN(MP_TAC o SPEC `real_interval(c1,c2)` o CONJUNCT2) THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL] THEN
  REWRITE_TAC[OPEN_IN_PROD_TOPOLOGY_ALT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ts:real`; `x:A`]) THEN
  REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; IN_REAL_INTERVAL;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real->bool` (X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_SUBTOPOLOGY] o check (fun th ->
    can (find_term (fun t -> t = `u:real->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in euclideanreal (w:real->bool)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `ts:real`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:A->bool`; `e:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `(u:real->bool) CROSS (v:A->bool)`)) (concl th))) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real->bool) = w INTER {t | ts <= t /\ t < b}` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

let P3H_NECK_OPEN_HIST = prove
 (`!(hs:(A)rfs_history) eps ts x e.
     rfs_history_ok hs /\ p2c_regular_view (rfs_view hs) /\ eps <= &1 / &2 /\
     &0 <= ts /\ ts < rfs_horizon hs /\
     rfs_strong_neck (rfs_view hs) eps x ts e
     ==> ?p1. &0 < p1 /\ p1 < &1 /\
           ((?eta0. &0 < eta0 /\
                    rfs_persists (rfs_view hs) (IMAGE e (rfs_neck_dom (eps / p1)))
                      (ts - &1 / rfs_vscalar (rfs_view hs) ts x - eta0) ts)
            ==> ?N d. open_in (rfs_top_at hs ts) N /\ x IN N /\ &0 < d /\
                      !s y. ts <= s /\ s < ts + d /\ y IN N
                            ==> y IN topspace(rfs_top_at hs s) /\
                                ?e'. rfs_strong_neck (rfs_view hs) eps y s e')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`;
                 `e:real^3->A`] P3H_NECK_OPEN_I) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p1:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "op"))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pb"))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts:real`] RFS_SLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) ts` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`] APX_RFS_SLAB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_scalar (hs_atlas (hs:(A)rfs_history) k) (hs_metric hs k ts) x =
                rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS]; ALL_TAC] THEN
  ABBREV_TAC `Q = rfs_vscalar (rfs_view (hs:(A)rfs_history)) ts x` THEN
  SUBGOAL_THEN `(x:A) IN topspace(hs_top (hs:(A)rfs_history) k)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                   `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; P2C_RFS_VIEW_PARTS] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `eta1 = min eta0 ((hs_time (hs:(A)rfs_history) (k + 1) - ts) / &2)` THEN
  SUBGOAL_THEN `&0 < eta1 /\ eta1 <= eta0 /\ ts + eta1 < hs_time (hs:(A)rfs_history) (k + 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta1" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "op" (MP_TAC o SPEC `eta1:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
      USE_THEN "pb" (MP_TAC o GEN_REWRITE_RULE I
        [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))]) THEN
      DISCH_THEN(LABEL_TAC "pb2") THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM_CASES_TAC `s <= ts` THENL
       [USE_THEN "pb2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "pb2" (MP_TAC o SPEC `ts:real`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LE_REFL] THEN
        SUBGOAL_THEN `&0 <= &1 / Q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
          MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `eps:real`; `x:A`; `ts:real`; `&1`;
                         `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC;
            ASM_SIMP_TAC[REAL_LT_IMP_LE]];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `th:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `ts:real`; `x:A`; `Q - th`; `Q + th`]
                  P3H_SCALAR_BOX2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:A->bool` (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`N0:A->bool`;
                          `min d0 (hs_time (hs:(A)rfs_history) (k + 1) - ts)`] THEN
    ASM_REWRITE_TAC[P2C_RFS_VIEW_PARTS; REAL_LT_MIN] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[P2B9_RFS_VSCALAR; P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`] o check (fun th ->
      can (find_term (fun t -> t = `Q - th`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN SIMP_TAC[]);;

