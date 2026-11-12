(* ========================================================================= *)
(* pc_p2b_flatfwd: flat forward for Ricci flows of nonnegative sectional     *)
(* curvature, the statement P2B_REQ_FLAT_FORWARD_STATEMENT (defined in       *)
(* pc_p2b_kreq).  On a Hausdorff 3-manifold, a Ricci flow on (a,b) with      *)
(* complete slices, abs Rm <= K and sec >= 0 on [t0,b) and R = 0 at t0 has R *)
(* = 0 on [t0,b).  Main theorem P2B_FLAT_FORWARD_BODY, the body of that      *)
(* statement.                                                                *)
(*                                                                           *)
(* Proof: dR/dt <= Lap R + 12 K R (P2BFF_SCALAR_EVOL_LE, from abs Ric        *)
(* squared <= R squared <= 6 K R); for eta > 0 and L > C + 6 K the function  *)
(* exp(-L(t - t0)) R - eta exp(L(t - t0)) psi, psi the barrier of            *)
(* RFA_HARNACK_BARRIER (pc_rfa_hbar) with constant C, is negative on the     *)
(* component of each point (P2BFF_COMP_NEG): it is negative outside a        *)
(* compact sublevel set of psi, so a first zero exists there (the general    *)
(* first-bad-time lemma P2BFF_FIRST_BAD_TIME and P2BFF_FIRST_ZERO_TIME); at  *)
(* it the smooth upper barrier of psi gives the space step                   *)
(* (P2BFF_SPACE_STEP, RFA_LLAP_LOCAL_MAX), the backward bound of psi gives   *)
(* the time step (P2BFF_TIME_STEP), and the two contradict the evolution     *)
(* inequality (P2BFF_FINAL_ARITH).  Letting eta -> 0 gives R = 0             *)
(* (P2BFF_COMP_ZERO).                                                        *)
(*                                                                           *)
(* Duplication note: P2BFF_TERM_UPPER, P2BFF_LRICCI_SEC_UPPER,               *)
(* P2BFF_MFD_RICCI_SEC_UPPER and P2BFF_MFD_RICCI_ABS are renamed copies of   *)
(* P2AP_TERM_UPPER, P2AP_LRICCI_SEC_UPPER, P2AP_MFD_RICCI_SEC_UPPER and      *)
(* P2AP_MFD_RICCI_ABS of pc_p2a_par.ml, which pulls 39 files into the load   *)
(* closure.  P2BFF_LSCALAR_SEC_BOUNDS has the content of P2BS_LSCALAR_SECT   *)
(* of pc_p2b_slice.ml (proved independently here); pc_p2b_slice pulls 133    *)
(* files.                                                                    *)
(* ========================================================================= *)

needs "src/pc_rfa_hbar.ml";;
needs "src/pc_rfa_lalg.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_lrg_flowsmooth.ml";;
needs "src/pc_p2b_scalpos.ml";;
needs "src/pc_cmp_bg.ml";;

prioritize_real();;
type_invention_error := true;;

(* Cauchy-Schwarz for a nonnegative symmetric bilinear form. *)

let P2BFF_PSD_CS = prove
 (`!B:real^N->real^N->real.
     (!u. &0 <= B u u) /\ (!u v. B u v = B v u) /\ (!v. linear (\u. lift(B u v)))
     ==> !u v. B u v pow 2 <= B u u * B v v`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pos")
    (CONJUNCTS_THEN2 (LABEL_TAC "sym") (LABEL_TAC "lin"))) THEN
  SUBGOAL_THEN `!a b w:real^N t. (B:real^N->real^N->real) (a + t % b) w = B a w + t * B b w`
  (LABEL_TAC "L") THENL
   [REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
    USE_THEN "lin" (fun th -> let th1 = SPEC `w:real^N` th in
                     REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_ADD th1);
                                 BETA_RULE(MATCH_MP LINEAR_CMUL th1)]) THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^N t. (B:real^N->real^N->real) (u + t % v) (u + t % v) =
                          B u u + &2 * t * B u v + t pow 2 * B v v`
  (LABEL_TAC "Q") THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sym" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    USE_THEN "L" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sym" (MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(B:real^N->real^N->real) v v = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_CASES_TAC `(B:real^N->real^N->real) u v = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pos" (MP_TAC o SPEC `u + --((B (u:real^N) u + &1) / (&2 * B u (v:real^N))) % v`) THEN
    USE_THEN "Q" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SUBGOAL_THEN `&2 * --((B (u:real^N) u + &1) / (&2 * B u (v:real^N))) * B u v = --(B u u + &1)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~((B:real^N->real^N->real) u v = &0)` THEN CONV_TAC REAL_FIELD;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (B:real^N->real^N->real) v v` ASSUME_TAC THENL
   [USE_THEN "pos" (MP_TAC o SPEC `v:real^N`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "pos" (MP_TAC o SPEC `u + --(B (u:real^N) (v:real^N) / B v v) % v`) THEN
  USE_THEN "Q" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `B (u:real^N) u + &2 * --(B u (v:real^N) / B v v) * B u v + --(B u v / B v v) pow 2 * B v v =
    B u u - B u v pow 2 / B v v`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < (B:real^N->real^N->real) v v` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `B (u:real^N) (v:real^N) pow 2 / B v v <= B u u` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* |Ric|^2 <= R^2 when the Ricci form is nonnegative (frame expression of  *)
(* RFA_RIC_SCALAR_LE, then Cauchy-Schwarz for the form termwise).           *)

let P2BFF_RIC2_LE_SCALAR2 = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U /\ (!w. &0 <= lricci G y w w)
     ==> ltnorm2 2 G (lric2 G) y <= lscalar G y pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lscalar G y =
    sum(1..dimindex(:N))
      (\r. lricci (G:real^N->real^N^N) y (transp(S:real^N^N) ** basis r)
                  (transp(S:real^N^N) ** basis r))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lric2 (G:real^N->real^N^N)`; `y:real^N`; `S:real^N^N`;
                   `\m:num. vec 0:real^N`] RFA_CONTR_FRAME) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[lric2; lscalar] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lricci (G:real^N->real^N^N) y` P2BFF_PSD_CS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
      (\p. sum(1..dimindex(:N))
             (\q. lricci (G:real^N->real^N^N) y (transp(S:real^N^N) ** basis p)
                         (transp S ** basis p) *
                  lricci G y (transp S ** basis q) (transp S ** basis q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_LMUL; SUM_RMUL; REAL_POW_2; REAL_LE_REFL]]);;

(* The Ricci form is at most (n - 1) kappa |w|^2 when every sectional       *)
(* curvature at y is at most kappa: renamed copies of P2AP_TERM_UPPER and   *)
(* P2AP_LRICCI_SEC_UPPER of pc_p2a_par.ml; pc_p2a_par pulls 39 files, among *)
(* them the pc_p3 units, into the closure, which this light unit avoids.    *)

let P2BFF_TERM_UPPER = prove
 (`!(G:real^N->real^N^N) y kappa (f1:real^N) fi c w.
        (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v <= kappa) /\
        fi dot (G y ** fi) = &1 /\ fi dot (G y ** f1) = &0 /\
        f1 dot (G y ** f1) = &1 /\ &0 < c /\ f1 = inv c % w
        ==> fi dot (G y ** lriemann G y fi w w) <= kappa * (w dot (G y ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f1")))))) THEN
  SUBGOAL_THEN `w = c % (f1:real^N)` SUBST1_TAC THENL
   [REMOVE_THEN "f1" SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    REMOVE_THEN "f1" (K ALL_TAC)] THEN
  SUBGOAL_THEN
   `(fi:real^N) dot ((G:real^N->real^N^N) y ** (c % f1)) = &0 /\
    (c % f1) dot (G y ** (c % f1)) = c pow 2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL; REAL_MUL_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c % f1:real^N) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(c % f1:real^N) dot ((G:real^N->real^N^N) y ** (c % f1)) = c pow 2` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vec 0,fi:real^N,c % f1}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** (c % f1)) = &0` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((c % f1:real^N) = vec 0)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  USE_THEN "sec" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `~collinear {vec 0,fi:real^N,c % f1}`))) THEN
  REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 * x - &0 pow 2 = x`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2BFF_LRICCI_SEC_UPPER = prove
 (`!U (G:real^N->real^N^N) y kappa w.
        metric_field U G /\ y IN U /\
        (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v <= kappa)
        ==> lricci G y w w <= &(dimindex(:N) - 1) * kappa * (w dot (G y ** w))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sec"))) THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
      LRIEMANN_TRILINEAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO; lricci] THEN
    SUBGOAL_THEN `!u. lriemann (G:real^N->real^N^N) y u (vec 0) (vec 0) = vec 0`
      (fun th -> REWRITE_TAC[th; VEC_COMPONENT; SUM_0; REAL_LE_REFL]) THEN
    X_GEN_TAC `u:real^N` THEN
    SUBGOAL_THEN `linear (\z. lriemann (G:real^N->real^N^N) y u (vec 0) z)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`]
    CMPZ_FRAME_FIRST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`;
                 `w:real^N`] P2B_LRICCI_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 2 <= i /\ i <= dimindex(:N)
        ==> (matrix_inv(M:real^N^N) ** basis i) dot
            ((G:real^N->real^N^N) y ** lriemann G y (matrix_inv M ** basis i) w w) <=
            kappa * (w dot (G y ** w))`
  (LABEL_TAC "terms") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= i /\ ~(i = 1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `2 <= i` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(matrix_inv(M:real^N^N) ** basis i) dot
      ((G:real^N->real^N^N) y ** (matrix_inv M ** basis i)) = &1 /\
      (matrix_inv M ** basis i) dot (G y ** (matrix_inv M ** basis 1)) = &0 /\
      (matrix_inv M ** basis 1) dot (G y ** (matrix_inv M ** basis 1)) = &1`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `i:num`]
          P2B_FRAME_ORTHO);
        MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `1`]
          P2B_FRAME_ORTHO);
        MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `1`; `1`]
          P2B_FRAME_ORTHO)] THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BFF_TERM_UPPER THEN
    MAP_EVERY EXISTS_TAC [`matrix_inv(M:real^N^N) ** basis 1`; `c:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
  SUBGOAL_THEN
   `lriemann (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis 1) w w = vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPZ_FIRST_TERM_ZERO THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `c:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_LID]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1 + 1..dimindex(:N))
                (\i. kappa * (w dot ((G:real^N->real^N^N) y ** w)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "terms" MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`1 + 1 <= i`; `i <= dimindex(:N)`] THEN ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    SUBGOAL_THEN `(dimindex(:N) + 1) - (1 + 1) = dimindex(:N) - 1` SUBST1_TAC THENL
     [ARITH_TAC; REWRITE_TAC[REAL_LE_REFL]]]);;


(* 0 <= sec <= K at a point: 0 <= R <= n (n - 1) K. *)

let P2BFF_LSCALAR_SEC_BOUNDS = prove
 (`!U (G:real^N->real^N^N) y K.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G y u v /\ lsectional G y u v <= K)
     ==> &0 <= lscalar G y /\
         lscalar G y <= &(dimindex(:N)) * &(dimindex(:N) - 1) * K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`]
         P2B_LSCALAR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> &0 <= lricci (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis j)
                         (matrix_inv M ** basis j) /\
            lricci G y (matrix_inv M ** basis j) (matrix_inv M ** basis j) <=
            &(dimindex(:N) - 1) * K`
  (LABEL_TAC "T") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `&0`;
                     `matrix_inv(M:real^N^N) ** basis j`] CMPZ_LRICCI_SEC_LOWER) THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `K:real`;
                     `matrix_inv(M:real^N^N) ** basis j`] P2BFF_LRICCI_SEC_UPPER) THEN
      ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `j:num`; `j:num`]
                    P2B_FRAME_ORTHO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\j. &(dimindex(:N) - 1) * K)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]]);;

(* The same at a point of a manifold, from the sectional curvatures and the *)
(* curvature norm; and the evolution inequality of R (from                  *)
(* RFA_MFD_SCALAR_EVOLUTION): d/dt R <= Lap R + 2 n (n - 1) K R.            *)

let P2BFF_MFD_SCALAR_BOUNDS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) g x K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     mfd_rm_norm atlas g x <= K /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> &0 <= mfd_scalar atlas g x /\
         mfd_scalar atlas g x <= &(dimindex(:N)) * &(dimindex(:N) - 1) * K /\
         ltnorm2 2 (metric_local atlas (chart_at atlas x) g)
                   (lric2 (metric_local atlas (chart_at atlas x) g)) (SND(chart_at atlas x) x)
         <= mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^N^N)) /\
    SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> &0 <= lsectional (metric_local atlas (chart_at atlas x) (g:A->real^N^N))
                               (SND(chart_at atlas (x:A)) x) u v /\
              lsectional (metric_local atlas (chart_at atlas x) g)
                         (SND(chart_at atlas x) x) u v <= K`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `u:real^N`; `v:real^N`] MFD_SECTIONAL_LE_RM_NORM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[mfd_sectional] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`; `K:real`]
                P2BFF_LSCALAR_SEC_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BFF_RIC2_LE_SCALAR2 THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`; `&0`;
                 `w:real^N`] CMPZ_LRICCI_SEC_LOWER) THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

let P2BFF_SCALAR_EVOL_LE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t x K.
     ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top /\
     mfd_rm_norm atlas (g t) x <= K /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas (g t) x u v)
     ==> ?D. ((\s. mfd_scalar atlas (g s) x) has_real_derivative D) (atreal t) /\
             D <= rfa_lap atlas (g t) (mfd_scalar atlas (g t)) x +
                  &2 * &(dimindex(:N)) * &(dimindex(:N) - 1) * K * mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `t:real`; `x:A`] RFA_MFD_SCALAR_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `rfa_lap atlas ((g:real->A->real^N^N) t) (mfd_scalar atlas (g t)) x +
              &2 * ltnorm2 2 (metric_local atlas (chart_at atlas x) (g t))
                             (lric2 (metric_local atlas (chart_at atlas x) (g t)))
                             (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) t`; `x:A`; `K:real`] P2BFF_MFD_SCALAR_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!l q m. q <= m ==> l + &2 * q <= l + &2 * m`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_scalar atlas ((g:real->A->real^N^N) t) (x:A) pow 2` THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;

(* A first bad time, general form: a closed bad set in [t1,t2] x K with K  *)
(* compact has a first time.                                                *)

let P2BFF_FIRST_BAD_TIME = prove
 (`!(top:A topology) K t1 t2 (bad:real#A->bool).
     compact_in top K /\
     closed_in (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                              (subtopology top K)) bad /\
     ~(bad = {})
     ==> ?t0 x0. (t0,x0) IN bad /\
                 !t x. (t,x) IN bad ==> t0 <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `compact_in (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                              (subtopology (top:A topology) K)) bad`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
    ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_compact (IMAGE FST (bad:real#A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN
    MATCH_MP_TAC COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT THEN
    EXISTS_TAC `real_interval[t1,t2]` THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                              (subtopology (top:A topology) K)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_FST];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE FST (bad:real#A->bool)` REAL_COMPACT_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
  MESON_TAC[]);;

(* The form used: F continuous on [t1,t2] x K, negative at t1, nonnegative *)
(* somewhere: a first time t0 > t1 with F(t0,x0) = 0, F(t0,.) <= 0 on K,   *)
(* F < 0 before t0.                                                        *)

let P2BFF_FIRST_ZERO_TIME = prove
 (`!(top:A topology) K t1 t2 (Fw:real->A->real).
     compact_in top K /\ t1 <= t2 /\
     continuous_map (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                                   (subtopology top K), euclideanreal)
                    (\z. Fw (FST z) (SND z)) /\
     (!x. x IN K ==> Fw t1 x < &0) /\
     (?t x. t1 <= t /\ t <= t2 /\ x IN K /\ &0 <= Fw t x)
     ==> ?t0 x0. t1 < t0 /\ t0 <= t2 /\ x0 IN K /\ Fw t0 x0 = &0 /\
                 (!x. x IN K ==> Fw t0 x <= &0) /\
                 (!t x. t1 <= t /\ t < t0 /\ x IN K ==> Fw t x < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `K:A->bool`; `t1:real`; `t2:real`;
                 `{(t,x) | t IN real_interval[t1,t2] /\ (x:A) IN K /\ &0 <= (Fw:real->A->real) t x}`]
                P2BFF_FIRST_BAD_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z. (Fw:real->A->real) (FST z) (SND z)`;
                     `prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                                    (subtopology (top:A topology) K)`;
                     `euclideanreal`; `{y:real | y >= &0}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_GE]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; real_ge;
                  IN_CROSS; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                  PAIR_EQ] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN
      UNDISCH_TAC `(K:A->bool) SUBSET topspace top` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `y:A`) THEN MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; EXISTS_PAIR_THM; IN_ELIM_THM; PAIR_EQ;
                  IN_REAL_INTERVAL] THEN
      MAP_EVERY EXISTS_TAC [`t:real`; `x:A`; `t:real`; `x:A`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; IN_REAL_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "min")) THEN
  SUBGOAL_THEN `!s y. t1 <= s /\ s < t0 /\ (y:A) IN K ==> (Fw:real->A->real) s y < &0`
  (LABEL_TAC "before") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < t0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Fw:real->A->real) t1 x0 < &0` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `t1:real = t0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (y:A) IN K ==> (Fw:real->A->real) t0 y <= &0` ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `continuous_map (subtopology euclideanreal (real_interval[t1,t2]), euclideanreal)
                     (\s. (Fw:real->A->real) s y)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[t1,t2])`;
                     `prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                                    (subtopology (top:A topology) K)`;
                     `euclideanreal`; `\s:real. (s,(y:A))`;
                     `\z. (Fw:real->A->real) (FST z) (SND z)`] CONTINUOUS_MAP_COMPOSE) THEN
      ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_ID] THEN
      REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\s. (Fw:real->A->real) s y`;
                   `subtopology euclideanreal (real_interval[t1,t2])`; `euclideanreal`;
                   `{v:real | v > &0}`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_GT]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t0:real) IN V` MP_TAC THENL
     [SUBGOAL_THEN `(t0:real) IN {s | s IN real_interval[t1,t2] /\
                                     (\s. (Fw:real->A->real) s y) s IN {v | v > &0}}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL; real_gt] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    UNDISCH_TAC `open_in euclideanreal (V:real->bool)` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; real_open] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `max t1 (t0 - d / &2) IN {s | s IN real_interval[t1,t2] /\
                                              (\s. (Fw:real->A->real) s y) s IN {v | v > &0}}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; real_gt] THEN STRIP_TAC THEN
    USE_THEN "before" (MP_TAC o SPECL [`max t1 (t0 - d / &2)`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t0:real`; `x0:A`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_SIMP_TAC[]);;

(* Ricci bounds from the norm of Rm: renamed copies of                       *)
(* P2AP_MFD_RICCI_SEC_UPPER and P2AP_MFD_RICCI_ABS of pc_p2a_par.ml;         *)
(* pc_p2a_par pulls 39 files, so the two short proofs are copied, like       *)
(* P2BFF_TERM_UPPER and P2BFF_LRICCI_SEC_UPPER.                              *)

let P2BFF_MFD_RICCI_SEC_UPPER = prove
 (`!top atlas (g:A->real^N^N) y kappa w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        y IN topspace top /\
        (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g y u v <= kappa)
        ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * kappa * (w dot (g y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(g:A->real^N^N) y`)) THEN
  MATCH_MP_TAC P2BFF_LRICCI_SEC_UPPER THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A)))
                    (FST(chart_at atlas y))` THEN
  ASM_REWRITE_TAC[GSYM mfd_sectional]);;

let P2BFF_MFD_RICCI_ABS = prove
 (`!top atlas (g:A->real^N^N) y w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> abs(mfd_ricci atlas g y w w) <=
         &(dimindex(:N) - 1) * mfd_rm_norm atlas g y * (w dot (g y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `--(mfd_rm_norm (atlas:((A->bool)#(A->real^N))->bool) g y)`;
                 `w:real^N`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `mfd_rm_norm (atlas:((A->bool)#(A->real^N))->bool) g y`;
                 `w:real^N`] P2BFF_MFD_RICCI_SEC_UPPER) THEN
  SUBGOAL_THEN
   `!u v. ~collinear {vec 0,u,v}
          ==> abs(mfd_sectional (atlas:((A->bool)#(A->real^N))->bool) g y u v) <=
              mfd_rm_norm atlas g y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Restricting a continuous function on a product of subspaces. *)

let P2BFF_CONT_RESTRICT = prove
 (`!(top:A topology) Is Js U U' (f:real#A->real).
     continuous_map (prod_topology (subtopology euclideanreal Is) (subtopology top U),
                     euclideanreal) f /\
     Js SUBSET Is /\ U' SUBSET U
     ==> continuous_map (prod_topology (subtopology euclideanreal Js) (subtopology top U'),
                         euclideanreal) f`,
  REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
  EXISTS_TAC `(Is:real->bool) CROSS (U:A->bool)` THEN ASM_SIMP_TAC[CROSS_MONO]);;

(* The exponential weights in the time variable are continuous. *)

let P2BFF_CONT_EXP_FST = prove
 (`!(top:A topology) Is L t1.
     continuous_map (prod_topology (subtopology euclideanreal Is) top, euclideanreal)
                    (\z. exp(L * (FST z - t1)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `continuous_map (euclideanreal,euclideanreal) exp` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`exp`; `(:real)`] RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EXP; SUBTOPOLOGY_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real#A. exp(L * (FST z - t1))) = exp o (\z. L * (FST z - t1))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN EXISTS_TAC `Is:real->bool` THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST];
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV]]);;

(* The time step at a first zero time: with w(s) = exp(-L(s - t1)) R(s) -   *)
(* eta exp(L(s - t1)) P(s) negative before ts and zero at ts, and the       *)
(* backward bound of P, the derivative D of R at ts satisfies               *)
(* eta exp(L(ts - t1)) P(ts) (L - C) <= exp(-L(ts - t1)) (D - L R(ts)).      *)

let P2BFF_TIME_STEP = prove
 (`!(Rf:real->real) (P:real->real) D L C eta t1 ts d.
     t1 < ts /\ &0 < d /\ &0 < eta /\
     (Rf has_real_derivative D) (atreal ts) /\
     (!s. t1 <= s /\ ts - d < s /\ s <= ts ==> P s <= P ts + C * (ts - s) * P ts) /\
     (!s. t1 <= s /\ s < ts
          ==> exp(--(L * (s - t1))) * Rf s - eta * exp(L * (s - t1)) * P s < &0) /\
     exp(--(L * (ts - t1))) * Rf ts - eta * exp(L * (ts - t1)) * P ts = &0
     ==> eta * exp(L * (ts - t1)) * P ts * (L - C) <=
         exp(--(L * (ts - t1))) * (D - L * Rf ts)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "back") (CONJUNCTS_THEN2 (LABEL_TAC "neg")
     (LABEL_TAC "zero"))))))) THEN
  SUBGOAL_THEN
   `((\s. exp(--(L * (s - t1)))) has_real_derivative
     (--L * exp(--(L * (ts - t1))))) (atreal ts)`
  ASSUME_TAC THENL [REAL_DIFF_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. exp(L * (s - t1)) * (&1 + C * (ts - s))) has_real_derivative
     (exp(L * (ts - t1)) * (L - C))) (atreal ts)`
  ASSUME_TAC THENL [REAL_DIFF_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. exp(--(L * (s - t1))) * (Rf:real->real) s -
          (eta * (P:real->real) ts) * (exp(L * (s - t1)) * (&1 + C * (ts - s))))
     has_real_derivative
     (exp(--(L * (ts - t1))) * (D - L * Rf ts) -
      eta * exp(L * (ts - t1)) * P ts * (L - C))) (atreal ts)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. exp(--(L * (s - t1)))`; `--L * exp(--(L * (ts - t1)))`;
                   `Rf:real->real`; `D:real`; `ts:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. exp(L * (s - t1)) * (&1 + C * (ts - s))`;
                   `exp(L * (ts - t1)) * (L - C)`; `eta * (P:real->real) ts`; `ts:real`]
                  HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. exp(--(L * (s - t1))) * (Rf:real->real) s`;
                   `exp(--(L * (ts - t1))) * D + (--L * exp(--(L * (ts - t1)))) * Rf ts`;
                   `\s. (eta * (P:real->real) ts) * (exp(L * (s - t1)) * (&1 + C * (ts - s)))`;
                   `(eta * (P:real->real) ts) * (exp(L * (ts - t1)) * (L - C))`;
                   `atreal ts`] HAS_REAL_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `a = b ==> (f has_real_derivative a) net ==> (f has_real_derivative b) net`) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. exp(--(L * (s - t1))) * (Rf:real->real) s -
         (eta * (P:real->real) ts) * (exp(L * (s - t1)) * (&1 + C * (ts - s)))`;
    `exp(--(L * (ts - t1))) * (D - L * (Rf:real->real) ts) -
     eta * exp(L * (ts - t1)) * (P:real->real) ts * (L - C)`;
    `max t1 (ts - d / &2)`; `ts:real`; `&1`] REAL_DERIVATIVE_POS_RIGHT_MAXIMUM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s:real = ts` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `t1 <= s /\ s < ts` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(P:real->real) s <= P ts * (&1 + C * (ts - s))` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `!b. a <= b /\ b = c ==> a <= c`) THEN
      EXISTS_TAC `(P:real->real) ts + C * (ts - s) * P ts` THEN CONJ_TAC THENL
       [USE_THEN "back" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RING];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta * exp(L * (s - t1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(eta * exp(L * (s - t1))) * (P:real->real) s <=
      (eta * exp(L * (s - t1))) * (P ts * (&1 + C * (ts - s)))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    USE_THEN "neg" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "zero" MP_TAC THEN CONV_TAC REAL_ARITH;
    REAL_ARITH_TAC]);;

(* The space step at a maximum point x of A f - E p over an open set U,    *)
(* with a smooth upper barrier q of p at x in the preferred chart:          *)
(* A Lap f(x) <= E C when Lap q(x) <= C and E >= 0.                          *)

let P2BFF_SPACE_STEP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
    (f:A->real) (p:A->real) U x A E C W (q:real^N->real).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top U /\ x IN U /\ &0 <= E /\
     smooth_map_on (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x) INTER topspace top))
                   (\y. lift(f (chart_inv (chart_at atlas x) y))) /\
     (!y. y IN U ==> A * f y - E * p y <= A * f x - E * p x) /\
     open W /\ SND(chart_at atlas x) x IN W /\
     W SUBSET IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x)) /\
     smooth_map_on W (\y. lift(q y)) /\
     (!y. y IN W ==> p (chart_inv (chart_at atlas x) y) <= q y) /\
     q (SND(chart_at atlas x) x) = p x /\
     llap (metric_local atlas (chart_at atlas x) g) q (SND(chart_at atlas x) x) <= C
     ==> A * rfa_lap atlas g f x <= E * C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_lap] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2")) THEN STRIP_TAC THEN
  ABBREV_TAC `O = (W:real^N->bool) INTER
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER U)` THEN
  SUBGOAL_THEN `open (O:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `FST(c:(A->bool)#(A->real^N))`] THEN
    ASM_SIMP_TAC[PAIR; OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) x IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN O ==> chart_inv (c:(A->bool)#(A->real^N)) y IN (U:A->bool) /\
                               chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
                               y IN W`
  (LABEL_TAC "inO") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "inv1" (MP_TAC o SPEC `z:A`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (\y. lift((f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace top)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN
    MATCH_MP_TAC(SET_RULE `(t:real^N->bool) SUBSET u ==> w INTER t SUBSET u`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `open_in top (U:A->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (\y. lift((q:real^N->real) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (\y. lift(A * (f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^N->bool`; `A:real`;
                   `\y. lift((f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y))`]
                  SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (\y. lift(E * (q:real^N->real) y))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^N->bool`; `E:real`; `\y. lift((q:real^N->real) y)`]
                  SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `llap (metric_local atlas c (g:A->real^N^N))
         (\y. A * (f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y) - E * (q:real^N->real) y)
         (SND c (x:A)) <= &0`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL_MAX THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                          `O:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`O:real^N->bool`;
                     `\y. lift(A * (f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y))`;
                     `\y. lift(E * (q:real^N->real) y)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "inO" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(p:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y) <= (q:real^N->real) y` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y. y IN W ==> (p:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y) <= (q:real^N->real) y`)
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` SUBST1_TAC THENL
     [USE_THEN "inv1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `A * (f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y) - E * (p:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y) <=
      A * f x - E * p x`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!y. y IN U ==> A * (f:A->real) y - E * p y <= A * f x - E * p x`)
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `E * (p:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y) <= E * (q:real^N->real) y`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(q:real^N->real) (SND(c:(A->bool)#(A->real^N)) x) = (p:A->real) x` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^N->bool`; `metric_local atlas c (g:A->real^N^N)`;
                 `\y. A * (f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `\y. E * (q:real^N->real) y`; `SND(c:(A->bool)#(A->real^N)) x`]
                RFA_LLAP_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:real^N->bool`; `metric_local atlas c (g:A->real^N^N)`;
                 `\y. (f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y)`; `A:real`;
                 `SND(c:(A->bool)#(A->real^N)) x`] RFA_LLAP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:real^N->bool`; `metric_local atlas c (g:A->real^N^N)`;
                 `q:real^N->real`; `E:real`; `SND(c:(A->bool)#(A->real^N)) x`]
                RFA_LLAP_CMUL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `E * llap (metric_local atlas c (g:A->real^N^N)) q (SND(c:(A->bool)#(A->real^N)) x)
    <= E * C` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* Labelling the conjuncts of an antecedent. *)

let p2bff_labels ns =
  DISCH_THEN(fun th -> EVERY (map2 (fun n t -> LABEL_TAC n t) ns (CONJUNCTS th)));;

(* The weighted function w = exp(-L(t - t1)) R - eta exp(L(t - t1)) psi is  *)
(* continuous on [t1,t2] x K for K inside the set where psi is continuous.  *)

let P2BFF_W_CONT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    t1 t2 J K (psi:real->A->real) L eta.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t2 < b /\
     continuous_map
       (prod_topology (subtopology euclideanreal (real_interval[t1,t2])) (subtopology top J),
        euclideanreal)
       (\z. psi (FST z) (SND z)) /\
     K SUBSET J /\ J SUBSET topspace top
     ==> continuous_map
           (prod_topology (subtopology euclideanreal (real_interval[t1,t2])) (subtopology top K),
            euclideanreal)
           (\z. exp(--(L * (FST z - t1))) * mfd_scalar atlas (g (FST z)) (SND z) -
                eta * exp(L * (FST z - t1)) * psi (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology (top:A topology) K`; `real_interval[t1,t2]`;
                     `--L:real`; `t1:real`] P2BFF_CONT_EXP_FST) THEN
      REWRITE_TAC[REAL_MUL_LNEG];
      MATCH_MP_TAC P2BFF_CONT_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`{t:real | t1 <= t /\ t < b}`; `topspace(top:A topology)`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
          UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                                     a b (g:real->A->real^N^N)` THEN
          REWRITE_TAC[ricci_flow_on] THEN DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC RFA_RICCI_FLOW_ON_EXT THEN
          MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`] THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        UNDISCH_TAC `t2 < b` THEN REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[P2BFF_CONT_EXP_FST];
      MATCH_MP_TAC P2BFF_CONT_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`real_interval[t1,t2]`; `J:A->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL]]]);;

(* Exponential weights. *)

let P2BFF_EXP_WEIGHTS = prove
 (`!L t t1. &0 <= L /\ t1 <= t
            ==> &0 < exp(--(L * (t - t1))) /\ exp(--(L * (t - t1))) <= &1 /\
                &0 < exp(L * (t - t1)) /\ &1 <= exp(L * (t - t1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  SUBGOAL_THEN `&0 <= L * (t - t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  ASM_REAL_ARITH_TAC);;

(* Outside the sublevel set psi <= 6K/eta the weighted function is negative. *)

let P2BFF_W_NEG_FAR = prove
 (`!Rv ps K eta L t t1.
     &0 <= Rv /\ Rv <= &6 * K /\ &1 <= ps /\ &0 < eta /\ &0 <= L /\ t1 <= t /\
     (&6 * K) / eta < ps
     ==> exp(--(L * (t - t1))) * Rv - eta * exp(L * (t - t1)) * ps < &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`L:real`; `t:real`; `t1:real`] P2BFF_EXP_WEIGHTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&6 * K < eta * ps` ASSUME_TAC THENL
   [UNDISCH_TAC `(&6 * K) / eta < ps` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(L * (t - t1))) * Rv <= &1 * Rv` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 * (eta * ps) <= exp(L * (t - t1)) * (eta * ps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eta * exp(L * (t - t1)) * ps = exp(L * (t - t1)) * (eta * ps)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The final arithmetic at a first zero time. *)

let P2BFF_FINAL_ARITH = prove
 (`!Am Bm ps Rs lap D eta L C K.
     &0 < Am /\ &0 < Bm /\ &1 <= ps /\ &0 < eta /\ C + &6 * K < L /\
     Am * Rs - eta * Bm * ps = &0 /\
     Am * lap <= (eta * Bm) * (C * ps) /\
     D <= lap + &12 * K * Rs /\
     eta * Bm * ps * (L - C) <= Am * (D - L * Rs)
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eta * Bm * ps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Am * D <= Am * (lap + &12 * K * Rs)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `Am * Rs = eta * Bm * ps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L * (Am * Rs) = L * (eta * Bm * ps) /\ K * (Am * Rs) = K * (eta * Bm * ps)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (eta * Bm * ps) * (L - C - &6 * K)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The weighted function is negative on [t1,t2] times the component of x0, *)
(* for every eta > 0 and L > C + 6K, L >= 0 (psi the barrier of            *)
(* RFA_HARNACK_BARRIER with constant C): a first zero (ts,xs) would give   *)
(* the space step, the time step and the evolution inequality of R, which  *)
(* contradict each other (P2BFF_FINAL_ARITH).                              *)

let P2BFF_COMP_NEG = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3)
    t1 t2 K x0 C (psi:real->A->real) eta L.
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 < t2 /\ t2 < b /\
     (!t x. t1 <= t /\ t <= t2 /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
     (!t x u v. t1 <= t /\ t <= t2 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g t) x u v) /\
     (!x. x IN topspace top ==> mfd_scalar atlas (g t1) x = &0) /\
     (!t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x ==> &1 <= psi t x) /\
     continuous_map
       (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                      (subtopology top {x | mfd_joinable (top,atlas) x0 x}),
        euclideanreal)
       (\z. psi (FST z) (SND z)) /\
     (!B. ?S. compact_in top S /\
              !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\ psi t x <= B
                    ==> x IN S) /\
     (!t x. t1 < t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
            ==> ?d. &0 < d /\
                    !s. t1 <= s /\ t - d < s /\ s <= t
                        ==> psi s x <= psi t x + C * (t - s) * psi t x) /\
     (!t x c. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
              c IN atlas /\ x IN FST c
              ==> ?W (q:real^3->real).
                    open W /\ SND c x IN W /\ W SUBSET IMAGE (SND c) (FST c) /\
                    smooth_map_on W (\y. lift(q y)) /\
                    (!y. y IN W ==> psi t (chart_inv c y) <= q y) /\
                    q (SND c x) = psi t x /\
                    llap (metric_local atlas c (g t)) q (SND c x) <= C * psi t x /\
                    lgrad2 (metric_local atlas c (g t)) q (SND c x) <= C * psi t x pow 2) /\
     &0 < eta /\ &0 <= L /\ C + &6 * K < L
     ==> !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
               ==> exp(--(L * (t - t1))) * mfd_scalar atlas (g t) x -
                   eta * exp(L * (t - t1)) * psi t x < &0`,
  REPEAT GEN_TAC THEN
  p2bff_labels ["rf";"at1";"t12";"t2b";"rm";"sec";"r0";"psi1";"pcont";"proper";"back";
                "upper";"eta";"L0";"L"] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
    (!t. t1 <= t /\ t <= t2 ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmet")) THENL
   [USE_THEN "rf" (MP_TAC o REWRITE_RULE[ricci_flow_on]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. t1 <= t /\ t <= t2 /\ (x:A) IN topspace top
          ==> &0 <= mfd_scalar atlas ((g:real->A->real^3^3) t) x /\
              mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g t) x <= &6 * K`
  (LABEL_TAC "rb") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`; `K:real`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) x0 y
        ==> y IN topspace top`
  ASSUME_TAC THENL [MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tb:real`; `xb:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  USE_THEN "proper" (MP_TAC o SPEC `(&6 * K) / eta`) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inS"))) THEN
  SUBGOAL_THEN
   `!t y. t1 <= t /\ t <= t2 /\
          mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) x0 y /\
          ~(y IN S)
          ==> exp(--(L * (t - t1))) * mfd_scalar atlas ((g:real->A->real^3^3) t) y -
              eta * exp(L * (t - t1)) * (psi:real->A->real) t y < &0`
  (LABEL_TAC "far") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BFF_W_NEG_FAR THEN EXISTS_TAC `K:real` THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "rb" (MP_TAC o SPECL [`t:real`; `y:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "psi1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:A) IN S)` THEN REWRITE_TAC[] THEN
      USE_THEN "inS" MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xb:A) IN S` ASSUME_TAC THENL
   [ASM_CASES_TAC `(xb:A) IN S` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "far" (MP_TAC o SPECL [`tb:real`; `xb:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed_in (top:A topology)
              {y | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 y}`
  ASSUME_TAC THENL
   [REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC GRGD_JOINABLE_COMPLEMENT_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (top:A topology)
            {y | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x0 y}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`;
    `(S:A->bool) INTER {y | mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                                         x0 y}`;
    `t1:real`; `t2:real`;
    `\t y. exp(--(L * (t - t1))) * mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                              ((g:real->A->real^3^3) t) (y:A) -
           eta * exp(L * (t - t1)) * (psi:real->A->real) t y`] P2BFF_FIRST_ZERO_TIME) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2BFF_W_CONT THEN
      MAP_EVERY EXISTS_TAC
       [`a:real`; `b:real`;
        `{y | mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) x0 y}`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
      SUBGOAL_THEN `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                               ((g:real->A->real^3^3) t1) (y:A) = &0` SUBST1_TAC THENL
       [USE_THEN "r0" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= (psi:real->A->real) t1 y` ASSUME_TAC THENL
       [USE_THEN "psi1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 - x < &0`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`tb:real`; `xb:A`] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` (X_CHOOSE_THEN `xs:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wz")
      (CONJUNCTS_THEN2 (LABEL_TAC "wle") (LABEL_TAC "wlt")))))))) THEN
  SUBGOAL_THEN
   `!y. mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) x0 y
        ==> exp(--(L * (ts - t1))) * mfd_scalar atlas ((g:real->A->real^3^3) ts) y -
            eta * exp(L * (ts - t1)) * (psi:real->A->real) ts y <= &0`
  (LABEL_TAC "wleJ") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN ASM_CASES_TAC `(y:A) IN S` THENL
     [USE_THEN "wle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "far" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xs:A) IN topspace top` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                  ((g:real->A->real^3^3) ts)` ASSUME_TAC THENL
   [USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `xs:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "upper" (MP_TAC o SPECL
    [`ts:real`; `xs:A`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (xs:A)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^3->bool` (X_CHOOSE_THEN `q:real^3->real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 <= eta * exp(L * (ts - t1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on
      (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (xs:A)))
             (FST(chart_at atlas xs) INTER topspace (top:A topology)))
      (\y. lift(mfd_scalar atlas ((g:real->A->real^3^3) ts)
                           (chart_inv (chart_at atlas xs) y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\z:real^(1,3)finite_sum.
         lift(mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                         ((g:real->A->real^3^3) (drop(fstcart z)))
                         (chart_inv (chart_at atlas (xs:A)) (sndcart z)))`;
      `a:real`; `b:real`;
      `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (xs:A)))
             (FST(chart_at atlas xs) INTER topspace (top:A topology))`;
      `ts:real`] RFA_SMOOTH_MAP_ON_SLICE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_SCALAR_CHART_SMOOTH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (xs:A))`] THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (xs:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (xs:A))`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN {y | mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) x0 y}
        ==> exp(--(L * (ts - t1))) * mfd_scalar atlas ((g:real->A->real^3^3) ts) y -
            (eta * exp(L * (ts - t1))) * (psi:real->A->real) ts y <=
            exp(--(L * (ts - t1))) * mfd_scalar atlas (g ts) xs -
            (eta * exp(L * (ts - t1))) * psi ts xs`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; GSYM REAL_MUL_ASSOC] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "wz" SUBST1_TAC THEN USE_THEN "wleJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`;
    `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) ts)`;
    `(psi:real->A->real) ts`;
    `{y | mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool) x0 y}`;
    `xs:A`; `exp(--(L * (ts - t1)))`; `eta * exp(L * (ts - t1))`;
    `C * (psi:real->A->real) ts xs`; `W:real^3->bool`; `q:real^3->real`]
   P2BFF_SPACE_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `ts:real`; `xs:A`; `K:real`] P2BFF_SCALAR_EVOL_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "back" (MP_TAC o SPECL [`ts:real`; `xs:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\s. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) (xs:A)`;
    `\s. (psi:real->A->real) s xs`; `D:real`; `L:real`; `C:real`; `eta:real`; `t1:real`;
    `ts:real`; `d:real`] P2BFF_TIME_STEP) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "wlt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&1 <= (psi:real->A->real) ts xs` ASSUME_TAC THENL
   [USE_THEN "psi1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `D <= rfa_lap atlas ((g:real->A->real^3^3) ts) (mfd_scalar atlas (g ts)) (xs:A) +
         &12 * K * mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g ts) xs`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BFF_FINAL_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`exp(--(L * (ts - t1)))`; `exp(L * (ts - t1))`; `(psi:real->A->real) ts xs`;
    `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) ts) (xs:A)`;
    `rfa_lap (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) ts)
             (mfd_scalar atlas (g ts)) (xs:A)`;
    `D:real`; `eta:real`; `L:real`; `C:real`; `K:real`] THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT]);;

(* R vanishes on [t1,t2] times the component of x0: otherwise take          *)
(* eta = exp(-L(t - t1)) R / (exp(L(t - t1)) psi), for which the weighted    *)
(* function vanishes at (t,x), against P2BFF_COMP_NEG.                      *)

let P2BFF_COMP_ZERO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3)
    t1 t2 K x0 C (psi:real->A->real).
     ricci_flow_on (top,atlas) a b g /\ a < t1 /\ t1 < t2 /\ t2 < b /\
     (!t x. t1 <= t /\ t <= t2 /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
     (!t x u v. t1 <= t /\ t <= t2 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g t) x u v) /\
     (!x. x IN topspace top ==> mfd_scalar atlas (g t1) x = &0) /\
     (!t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x ==> &1 <= psi t x) /\
     continuous_map
       (prod_topology (subtopology euclideanreal (real_interval[t1,t2]))
                      (subtopology top {x | mfd_joinable (top,atlas) x0 x}),
        euclideanreal)
       (\z. psi (FST z) (SND z)) /\
     (!B. ?S. compact_in top S /\
              !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\ psi t x <= B
                    ==> x IN S) /\
     (!t x. t1 < t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
            ==> ?d. &0 < d /\
                    !s. t1 <= s /\ t - d < s /\ s <= t
                        ==> psi s x <= psi t x + C * (t - s) * psi t x) /\
     (!t x c. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x /\
              c IN atlas /\ x IN FST c
              ==> ?W (q:real^3->real).
                    open W /\ SND c x IN W /\ W SUBSET IMAGE (SND c) (FST c) /\
                    smooth_map_on W (\y. lift(q y)) /\
                    (!y. y IN W ==> psi t (chart_inv c y) <= q y) /\
                    q (SND c x) = psi t x /\
                    llap (metric_local atlas c (g t)) q (SND c x) <= C * psi t x /\
                    lgrad2 (metric_local atlas c (g t)) q (SND c x) <= C * psi t x pow 2)
     ==> !t x. t1 <= t /\ t <= t2 /\ mfd_joinable (top,atlas) x0 x
               ==> mfd_scalar atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN
  p2bff_labels ["rf";"at1";"t12";"t2b";"rm";"sec";"r0";"psi1";"pcont";"proper";"back";
                "upper"] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `x:A`; `K:real`] P2BFF_MFD_SCALAR_BOUNDS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "rf" (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ricci_flow_on]);
      USE_THEN "rf" (MP_TAC o el 2 o CONJUNCTS o REWRITE_RULE[ricci_flow_on]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `L = abs C + abs(&6 * K) + &1` THEN
  SUBGOAL_THEN `&0 <= L /\ C + &6 * K < L` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`L:real`; `t:real`; `t1:real`] P2BFF_EXP_WEIGHTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= (psi:real->A->real) t x` ASSUME_TAC THENL
   [USE_THEN "psi1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(L * (t - t1)) * (psi:real->A->real) t x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = (exp(--(L * (t - t1))) *
                     mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x) /
                    (exp(L * (t - t1)) * (psi:real->A->real) t x)` THEN
  SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `t1:real`; `t2:real`; `K:real`; `x0:A`; `C:real`;
                 `psi:real->A->real`; `eta:real`; `L:real`] P2BFF_COMP_NEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `eta * exp(L * (t - t1)) * (psi:real->A->real) t x =
    exp(--(L * (t - t1))) * mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                       ((g:real->A->real^3^3) t) x`
  SUBST1_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The main theorem: the body of P2B_REQ_FLAT_FORWARD_STATEMENT              *)
(* (pc_p2b_kreq).  For t0 < t < b take t2 = (t + b)/2, the barrier of        *)
(* RFA_HARNACK_BARRIER on [t0,t2] at x (|Ric| <= 2K from |Rm| <= K), and     *)
(* P2BFF_COMP_ZERO.                                                          *)

let P2B_FLAT_FORWARD_BODY = prove
 (`!top atlas a b (g:real->A->real^3^3) t0 K.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\ a < t0 /\ t0 < b /\
     (!t. t0 <= t /\ t < b ==> mfd_complete (top,atlas) (g t)) /\
     (!t x. t0 <= t /\ t < b /\ x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
     (!t x v1 v2. t0 <= t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,v1,v2}
                  ==> &0 <= mfd_sectional atlas (g t) x v1 v2) /\
     (!x. x IN topspace top ==> mfd_scalar atlas (g t0) x = &0)
     ==> !t x. t0 <= t /\ t < b /\ x IN topspace top ==> mfd_scalar atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN
  p2bff_labels ["haus";"rf";"at0";"t0b";"comp";"rm";"sec";"r0"] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:real = t0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "r0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t2 = (t + b) / &2` THEN
  SUBGOAL_THEN `t0 < t /\ t < t2 /\ t2 < b /\ t0 < t2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
    (!s. t0 <= s /\ s <= t2 ==> riemannian_metric atlas ((g:real->A->real^3^3) s))`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmet")) THENL
   [USE_THEN "rf" (MP_TAC o REWRITE_RULE[ricci_flow_on]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. t0 <= s /\ s <= t2 /\ (y:A) IN topspace top
          ==> mfd_rm_norm (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) y
              <= K`
  (LABEL_TAC "rm2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y u v. t0 <= s /\ s <= t2 /\ (y:A) IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional (atlas:((A->bool)#(A->real^3))->bool)
                                      ((g:real->A->real^3^3) s) y u v`
  (LABEL_TAC "sec2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `UNIV:A->bool` RFA_HARNACK_BARRIER) THEN
  REWRITE_TAC[RFA_HARNACK_BARRIER_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
    `a:real`; `b:real`; `t0:real`; `t2:real`; `&2 * K`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "comp" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`; `v:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(dimindex(:3) - 1) *
                  mfd_rm_norm (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) y *
                  (v dot (g s y ** v))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BFF_MFD_RICCI_ABS THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `r <= K ==> &2 * r <= &2 * K`) THEN
          USE_THEN "rm2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_CASES_TAC `v:real^3 = vec 0` THEN
          ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
          MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `(g:real->A->real^3^3) s`; `y:A`] RIEMANNIAN_METRIC_POS) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN USE_THEN "rmet" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
            ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `psi:real->A->real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `t0:real`; `t2:real`; `K:real`; `x:A`; `C:real`;
                 `psi:real->A->real`] P2BFF_COMP_ZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

