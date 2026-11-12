(* ========================================================================= *)
(* The reverse base change of lck_dist2.  If G1 is C^k-close to G0 (base     *)
(* G0), the C^k distance from G1 to G2 with base G1 is controlled by the     *)
(* same difference measured with base G0 (LCK_CK_BASE_REV), and reflecting   *)
(* the second metric about the base leaves the distance unchanged            *)
(* (LCK_DIST2_REFLECT).  The proofs are those of SNGL_CK_BASE_REV and        *)
(* SNGL_LCK_DIST2_REFLECT of pc_p2c_sing2; the lemmas are used for MT Thm    *)
(* 11.31 (pc_p2c_horns2) and for the blow-up limits (pc_p2c_blowup).         *)
(* ========================================================================= *)

needs "src/pc_lrg_ckbase.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The two lemmas (proofs as in pc_p2c_sing2).                               *)
(* ------------------------------------------------------------------------- *)

let LCK_CK_BASE_REV = prove
 (`!k. ?M. &0 <= M /\
      !s (G0:real^N->real^N^N) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G1 G2 y <= M * lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`k:num`; `k:num`] GEOB_R_DERIV) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `CR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CR"))) THEN
  EXISTS_TAC `&(k + 1) * CR * &2 pow (2 + k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                       `G2:real^N->real^N^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G0:real^N->real^N^N) z + G2 z - G1 z) z u - lmetric2 G0 z u) =
    geob_hd G1 G2`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; geob_hd; lmetric2] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RADD; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM geob_hd] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
         GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G1 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it0") THEN
  SUBGOAL_THEN
   `sum(0..k) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                    (lnabla_iter 2 i G0 (geob_hd G1 G2)) y) <=
    &2 pow (2 + k) *
    sum(0..k) (\i. ltnorm2 (2 + i) (G0:real^N->real^N^N)
                    (lnabla_iter 2 i G0 (geob_hd G1 G2)) y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow (2 + i) * ltnorm2 (2 + i) (G0:real^N->real^N^N)
                                   (lnabla_iter 2 i G0 (geob_hd G1 G2)) y` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                     `y:real^N`; `2 + i`;
                     `lnabla_iter 2 i G0 (geob_hd G1 (G2:real^N->real^N^N))`]
             GEOB_NORM_COMPARE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "it0" (fun th -> REWRITE_TAC[th]); SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
        MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "it0" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..k) (\b. CR * sum(0..k) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                                                 (lnabla_iter 2 i G0 (geob_hd G1 G2)) y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CR * sum(0..b) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                                      (lnabla_iter 2 i G0 (geob_hd G1 G2)) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "CR" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GEOB_SUM_MONO_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "it0" (fun th -> REWRITE_TAC[th])];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Reflecting the second metric about the base leaves the distance unchanged. *)

let LCK_DIST2_REFLECT = prove
 (`!k s (G0:real^N->real^N^N) G1 y.
     metric_field s G0 /\ metric_field s G1 /\ y IN s
     ==> lck_dist2 k G0 (\z. G0 z + G0 z - G1 z) y = lck_dist2 k G0 G1 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G0:real^N->real^N^N) z + G0 z - G1 z) z u - lmetric2 G0 z u) =
    (\z u. --(&1) * geob_hd G0 G1 z u + &0 * geob_hd G0 G1 z u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; geob_hd; lmetric2] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RADD; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z u. lmetric2 (G1:real^N->real^N^N) z u - lmetric2 G0 z u) = geob_hd G0 G1`
  SUBST1_TAC THENL [REWRITE_TAC[geob_hd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
                GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G0 (G1:real^N->real^N^N)`; `geob_hd G0 (G1:real^N->real^N^N)`;
                 `--(&1)`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`l:num`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[ltnorm2] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(--(&1) * a + &0 * a) * (--(&1) * b + &0 * b) * c = a * b * c`]);;

