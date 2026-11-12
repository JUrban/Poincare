(* ========================================================================= *)
(* pc_p2a_smth: smoothing corners of admissible curves (L12 FIX,             *)
(* P2A_SMOOTHING_FIX) and the upper semicontinuity of Lx (L7 FIX).           *)
(*                                                                           *)
(* First: under p2a_atlas_lc only corners at interior times where the slice  *)
(* atlas is constant nearby matter (P2A_PC1_REDUCE): at other times the      *)
(* two-sided condition of p2a_pc1 follows from a one-sided one.              *)
(* ========================================================================= *)

needs "src/pc_p2a_reg.ml";;

prioritize_real();;
type_invention_error := true;;

let p2a_atlas_const = new_definition
 `p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                     (real->A->real^N^N)) (t:real) <=>
    ?d. &0 < d /\ !t'. abs(t' - t) < d ==> p2a_vatlas V t' = p2a_vatlas V t`;;

let P2A_PC1_REDUCE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b P.
     p2a_atlas_lc V /\ p2a_pc1 V tt gamma (&0) b P
     ==> p2a_pc1 V tt gamma (&0) b
           {s | s IN P /\ &0 < s /\ s < b /\ p2a_atlas_const V (tt - s)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1] THEN STRIP_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`] o check (fun th ->
    is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CL") (CONJUNCTS_THEN2 (LABEL_TAC "CR") (LABEL_TAC "CB"))))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `tt - s0` o REWRITE_RULE[p2a_atlas_lc] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_atlas_lc")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "AL") (LABEL_TAC "AR")))) THEN
  EXISTS_TAC `min d dl / &2` THEN
  SUBGOAL_THEN `&0 < min d dl / &2 /\ min d dl / &2 <= d /\ min d dl / &2 < dl`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d' = min d dl / &2` THEN
  SUBGOAL_THEN
   `continuously_differentiable 1
      {s | s0 - d' <= drop s /\ drop s <= s0 /\ &0 < drop s /\
           p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) (tt - drop s) = p2a_vatlas V (tt - s0) /\
           gamma(drop s) IN FST c}
      (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) /\
    continuously_differentiable 1
      {s | s0 <= drop s /\ drop s <= s0 + d' /\ drop s <= b /\
           p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\ gamma(drop s) IN FST c}
      (\s. SND c (gamma(drop s)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THENL
     [EXISTS_TAC `{s | s0 - d <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                       p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - drop s) =
                       p2a_vatlas V (tt - s0) /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
      USE_THEN "CL" (fun th -> REWRITE_TAC[th]);
      EXISTS_TAC `{s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b /\
                       p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - drop s) =
                       p2a_vatlas V (tt - s0) /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
      USE_THEN "CR" (fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(s0:real) IN P` THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{s | s0 - d <= drop s /\ drop s <= s0 + d /\ &0 < drop s /\ drop s <= b /\
                     p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - drop s) =
                     p2a_vatlas V (tt - s0) /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "CB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]] THEN
  (* s0 is a corner of P outside the reduced set *)
  SUBGOAL_THEN
   `(!s. s0 < s /\ s < s0 + dl
         ==> ~(p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) (tt - s) = p2a_vatlas V (tt - s0))) \/
    (!s. s0 - dl < s /\ s < s0
         ==> ~(p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) (tt - s) = p2a_vatlas V (tt - s0))) \/
    s0 = b`
  MP_TAC THENL
   [ASM_CASES_TAC `s0:real = b` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[p2a_atlas_const; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `dl:real`) THEN ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `t1 < tt - s0` THENL
     [DISJ1_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s) = p2a_vatlas V t1`
        SUBST1_TAC THENL
       [USE_THEN "AL" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `t1 = tt - s0` THENL
       [UNDISCH_TAC `~(p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) t1 = p2a_vatlas V (tt - s0))` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISJ2_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s) = p2a_vatlas V t1`
        SUBST1_TAC THENL
       [USE_THEN "AR" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THENL
   [EXISTS_TAC `{s | s0 - d' <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                     p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - drop s) =
                     p2a_vatlas V (tt - s0) /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `~(s0 < x) ==> x <= s0`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop(x:real^1)` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `dl:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "real_le")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `{s | s0 <= drop s /\ drop s <= s0 + d' /\ drop s <= b /\
                     p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - drop s) =
                     p2a_vatlas V (tt - s0) /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `~(x < s0) ==> s0 <= x`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop(x:real^1)` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `dl:real`)) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "real_le")) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `{s | s0 - d' <= drop s /\ drop s <= s0 /\ &0 < drop s /\
                     p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - drop s) =
                     p2a_vatlas V (tt - s0) /\ (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Near a corner tau1 at which the slice atlas is constant, the region chart *)
(* curve has a bounded derivative on the punctured neighbourhood (one-sided  *)
(* C^1 from p2a_pc1 at tau1).                                                *)
(* ========================================================================= *)

let P2A_CD1_COMPACT_BOUND = prove
 (`!(f:real^1->real^N) S Q.
     continuously_differentiable 1 S f /\ compact S /\ open Q /\ Q SUBSET S
     ==> ?M. !y. y IN Q ==> f differentiable (at y) /\
                           norm(vector_derivative f (at y)) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_CONV `1`; continuously_differentiable] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f':real^1->real^1->real^N` STRIP_ASSUME_TAC)
                             STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. y IN Q ==> ((f:real^1->real^N) has_derivative f' y) (at y)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((f:real^1->real^N) has_derivative f' y) (at y within Q)` MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `S:real^1->bool` THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN Q ==> vector_derivative (f:real^1->real^N) (at y) = f' y (lift(&1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^1->real^N) differentiable (at y)` MP_TAC THENL
     [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_DERIVATIVE_WORKS; has_vector_derivative] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x. drop x % vector_derivative (f:real^1->real^N) (at y)) = f' y` MP_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
      MAP_EVERY EXISTS_TAC [`f:real^1->real^N`; `y:real^1`] THEN ASM_SIMP_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; LIFT_DROP; VECTOR_MUL_LID])];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded (IMAGE (\y. (f':real^1->real^1->real^N) y (lift(&1))) S)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* Frechet derivatives of a smooth map are uniformly bounded on compacts.   *)

let P2A_FRECHET_BOUND = prove
 (`!(Tm:real^N->real^M) O K.
     open O /\ smooth_map_on O Tm /\ compact K /\ K SUBSET O
     ==> ?B. &0 <= B /\ !z v. z IN K ==> norm(frechet_derivative Tm (at z) v) <= B * norm v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. (\y. frechet_derivative (Tm:real^N->real^M) (at y) (basis j)) continuous_on O`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`0`; `O:real^N->bool`; `Tm:real^N->real^M`]
                  CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
    REWRITE_TAC[continuously_differentiable] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bounded (IMAGE (\z. lift(sum(1..dimindex(:N))
                     (\j. norm(frechet_derivative (Tm:real^N->real^M) (at z) (basis j))))) K)`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (Tm:real^N->real^M) (at z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^N->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\j. norm(frechet_derivative (Tm:real^N->real^M) (at z) (basis j))) * norm(v:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_LINEAR_BASIS_BOUND THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
  REAL_ARITH_TAC);;

(* The derivative of s |-> Yt(s^2).                                          *)

let P2A_SQ_CURVE_VD = prove
 (`!(Yt:real^1->real^N) s.
     Yt differentiable (at (lift(s pow 2)))
     ==> ((\v. Yt(lift(drop v pow 2))) has_vector_derivative
          (&2 * s) % vector_derivative Yt (at (lift(s pow 2)))) (at (lift s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\v. lift(drop v pow 2)) has_vector_derivative lift(&2 * s)) (at (lift s))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real. x`; `&1`; `s:real`; `2`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN REWRITE_TAC[REAL_POW_1; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (Yt:real^1->real^N)(lift(drop v pow 2))) = Yt o (\v. lift(drop v pow 2))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. lift(drop v pow 2)`; `Yt:real^1->real^N`; `lift(&2 * s)`;
                 `vector_derivative (Yt:real^1->real^N) (at (lift(s pow 2)))`; `lift s`]
                VECTOR_DIFF_CHAIN_AT) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]);;

(* The bound near a constant-atlas corner, in tau.                           *)

let P2A_CORNER_TAU_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) b P tau1 W a' b'' U (phi:A->real^N).
     p2a_pc1 V tt gamma (&0) b P /\ &0 < tau1 /\ tau1 < b /\
     p2a_atlas_const V (tt - tau1) /\
     (!O. open_in (p2a_vtop V (tt - tau1)) O /\ gamma tau1 IN O
          ==> ?d. &0 < d /\
                  !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau1) < d ==> gamma tau IN O) /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     a' < tt - tau1 /\ tt - tau1 <= b'' /\ gamma tau1 IN U INTER W
     ==> ?e M. &0 < e /\
               !tau. abs(tau - tau1) < e /\ ~(tau = tau1)
                     ==> (\t. phi(gamma(drop t))) differentiable (at (lift tau)) /\
                         norm(vector_derivative (\t. phi(gamma(drop t))) (at (lift tau))) <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `tt - tau1`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) tau1 IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - tau1))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) (tt - tau1)) W`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - tau1)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - tau1)`;
                 `(gamma:real->A) tau1`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (p2a_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau1))
                   ((gamma:real->A) tau1)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - tau1)`;
                 `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - tau1)`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - tau1`; `c:(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `Oc = IMAGE (SND (c:(A->bool)#(A->real^N))) ((U INTER W) INTER FST c)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `Tr = chart_trans (c:(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - tau1))
                        ((U INTER W) INTER FST(c:(A->bool)#(A->real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b''`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b''`;
                   `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U INTER W) INTER FST(c:(A->bool)#(A->real^N))` o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p2a_atlas_const] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_atlas_const")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D0"))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`tau1:real`; `c:(A->bool)#(A->real^N)`] o CONJUNCT2 o
    REWRITE_RULE[p2a_pc1] o check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "p2a_pc1")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CL") (CONJUNCTS_THEN2 (LABEL_TAC "CR") (K ALL_TAC))))) THEN
  ABBREV_TAC `e = min (min d1 d2) (min d0 (min tau1 (b - tau1))) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ &2 * e <= d1 /\ &2 * e <= d2 /\ &2 * e <= d0 /\ &2 * e <= tau1 /\
                &2 * e <= b - tau1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^1. abs(drop t - tau1) <= e
               ==> &0 < drop t /\ drop t < b /\
                   (gamma:real->A)(drop t) IN (U INTER W) INTER FST(c:(A->bool)#(A->real^N)) /\
                   p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) (tt - drop t) =
                   p2a_vatlas V (tt - tau1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "D0" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* C^1 on the closed sides *)
  SUBGOAL_THEN
   `continuously_differentiable 1 (interval[lift(tau1 - e),lift tau1])
      (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) /\
    continuously_differentiable 1 (interval[lift tau1,lift(tau1 + e)])
      (\s. SND c (gamma(drop s)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THENL
     [EXISTS_TAC `{s | tau1 - d2 <= drop s /\ drop s <= tau1 /\ &0 < drop s /\
                       p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - drop s) =
                       p2a_vatlas V (tt - tau1) /\
                       (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
      USE_THEN "CL" (fun th -> REWRITE_TAC[th]);
      EXISTS_TAC `{s | tau1 <= drop s /\ drop s <= tau1 + d2 /\ drop s <= b /\
                       p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - drop s) =
                       p2a_vatlas V (tt - tau1) /\
                       (gamma:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}` THEN
      USE_THEN "CR" (fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vatlas")) (concl th))) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN (ASM_REAL_ARITH_TAC ORELSE ASM SET_TAC[]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
                 `interval[lift(tau1 - e),lift tau1]`; `interval(lift(tau1 - e),lift tau1)`]
                P2A_CD1_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (LABEL_TAC "M1")) THEN
  MP_TAC(ISPECL [`\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
                 `interval[lift tau1,lift(tau1 + e)]`; `interval(lift tau1,lift(tau1 + e))`]
                P2A_CD1_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (LABEL_TAC "M2")) THEN
  (* the compact image of the chart curve and the bound of the transition *)
  SUBGOAL_THEN
   `compact (IMAGE (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))
                   (interval[lift(tau1 - e),lift tau1] UNION interval[lift tau1,lift(tau1 + e)])) /\
    IMAGE (\s. SND c (gamma(drop s)))
          (interval[lift(tau1 - e),lift tau1] UNION interval[lift tau1,lift(tau1 + e)])
    SUBSET Oc`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_UNION; COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_UNION THEN
      REWRITE_TAC[CLOSED_INTERVAL] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXPAND_TAC "Oc" THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `e:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vatlas")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Tr:real^N->real^N`; `Oc:real^N->bool`;
                 `IMAGE (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))
                   (interval[lift(tau1 - e),lift tau1] UNION interval[lift tau1,lift(tau1 + e)])`]
                P2A_FRECHET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "B"))) THEN
  EXISTS_TAC `e:real` THEN EXISTS_TAC `B * max M1 M2` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  (* the derivative of the slice-chart curve at lift tau *)
  SUBGOAL_THEN
   `(\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) differentiable (at (lift tau)) /\
    norm(vector_derivative (\s. SND c (gamma(drop s))) (at (lift tau))) <= max M1 M2`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `tau < tau1` THENL
     [USE_THEN "M1" (MP_TAC o SPEC `lift tau`) THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      USE_THEN "M2" (MP_TAC o SPEC `lift tau`) THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) tau) IN
                IMAGE (\s. SND c (gamma(drop s)))
                  (interval[lift(tau1 - e),lift tau1] UNION interval[lift tau1,lift(tau1 + e)])`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `lift tau` THEN
    REWRITE_TAC[LIFT_DROP; IN_UNION; IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the region chart curve agrees with Tr o (slice chart curve) near tau *)
  SUBGOAL_THEN
   `!y:real^1. y IN ball(lift tau1,e)
               ==> ((Tr:real^N->real^N) o (\s. SND (c:(A->bool)#(A->real^N))
                                               ((gamma:real->A)(drop s)))) y =
                   (\t. (phi:A->real^N)(gamma(drop t))) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `e:real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vatlas")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    EXPAND_TAC "Tr" THEN REWRITE_TAC[o_THM; chart_trans; SND] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (phi:A->real^N)((gamma:real->A)(drop t))) has_vector_derivative
     frechet_derivative (Tr:real^N->real^N) (at (SND (c:(A->bool)#(A->real^N)) (gamma tau)))
       (vector_derivative (\s. SND c (gamma(drop s))) (at (lift tau)))) (at (lift tau))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`(Tr:real^N->real^N) o (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))`;
      `ball(lift tau1,e)`] THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN
    REWRITE_TAC[IN_BALL; DIST_LIFT] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`Tr:real^N->real^N`; `Oc:real^N->bool`;
                   `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`; `lift tau`]
                  P2A_CHAIN_SMOOTH_VD) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * norm(vector_derivative (\s. SND (c:(A->bool)#(A->real^N))
                                               ((gamma:real->A)(drop s))) (at (lift tau)))` THEN
  CONJ_TAC THENL
   [USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* The bound near a constant-atlas corner s0^2, in s.                        *)

let P2A_CORNER_S_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P s0 W a' b'' U (phi:A->real^N).
     p2a_atlas_lc V /\ p2a_adm V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b P /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s0 /\ s0 pow 2 < b /\ gamma(s0 pow 2) IN U INTER W /\
     a' < tt - s0 pow 2 /\ tt - s0 pow 2 < b'' /\ p2a_atlas_const V (tt - s0 pow 2)
     ==> ?k M. &0 < k /\ k < s0 /\ (s0 + k) pow 2 < b /\
               (!s. abs(s - s0) < k
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'' /\
                        gamma(s pow 2) IN U INTER W) /\
               (!s. abs(s - s0) < k /\ ~(s = s0)
                    ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
                        (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                          continuous (at (lift s)) /\
                        norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s)))
                          <= M)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `s0:real`]
                P2A_MIN_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HW") (CONJUNCTS_THEN2 (LABEL_TAC "HU") (LABEL_TAC "HC"))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_ADM_SCONT) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `P:real->bool`;
                 `s0 pow 2`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`]
                P2A_CORNER_TAU_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LT] THEN
    X_GEN_TAC `O:A->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s0 pow 2`; `O:A->bool`] o check (fun th ->
      is_forall(concl th) && not (can (find_term ((=) `r:real`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Mt:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "MT")))) THEN
  MP_TAC(SPECL [`s0:real`; `e:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H1"))) THEN
  SUBGOAL_THEN `s0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_POW_2 THEN MP_TAC(SPEC `s0:real` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `k = min (min h h1) (min s0 (sqrt b - s0)) / &2` THEN
  SUBGOAL_THEN `&0 < k /\ &2 * k <= h /\ &2 * k <= h1 /\ &2 * k <= s0 /\
                &2 * k <= sqrt b - s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= s0 + k ==> s pow 2 < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  EXISTS_TAC `k:real` THEN EXISTS_TAC `&4 * s0 * Mt` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "HW" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "HU" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s /\ s pow 2 < b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "HC" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s pow 2 = s0 pow 2) /\ abs(s pow 2 - s0 pow 2) < e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(s:real = s0)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "H1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "MT" (MP_TAC o SPEC `s pow 2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. (phi:A->real^N)((gamma:real->A)(drop t))`; `s:real`]
                P2A_SQ_CURVE_VD) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Mt` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vector_derivative (\t:real^1. (phi:A->real^N)((gamma:real->A)(drop t)))
                      (at (lift(s pow 2))))` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * s) * Mt` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `(&2 * s) * Mt <= &4 * s0 * Mt <=> &0 <= (&4 * s0 - &2 * s) * Mt`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The blend of a chart curve Y with its value at                            *)
(* a corner s0,                                                              *)
(*    B v = Y v + psi((v - s0)/k) (Y(s0) - Y v),                            *)
(* psi a smooth bump (1 near 0, 0 off [-2/3,2/3]): B is C^1 near s0, equals *)
(* Y(s0) near s0 and Y away from s0, and its derivative is bounded by a     *)
(* universal multiple of the bound of Y' (independent of k).                 *)
(* ========================================================================= *)

let P2A_BUMP_FACTS = prove
 (`?C1. &0 <= C1 /\
        (!v:real^1. &0 <= smooth_bump (&1 / &3) (&2 / &3) v /\
                    smooth_bump (&1 / &3) (&2 / &3) v <= &1) /\
        (!v:real^1. norm v <= &1 / &3 ==> smooth_bump (&1 / &3) (&2 / &3) v = &1) /\
        (!v:real^1. &2 / &3 <= norm v ==> smooth_bump (&1 / &3) (&2 / &3) v = &0) /\
        (!v:real^1. (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) differentiable (at v) /\
                    (\v. vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) (at v))
                      continuous (at v)) /\
        (!v:real^1. norm v <= &1
                    ==> norm(vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v))
                                               (at v)) <= C1)`,
  SUBGOAL_THEN `smooth_map_on (:real^1) (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. lift(smooth_bump (&1 / &3) (&2 / &3) v)`; `(:real^1)`; `(:real^1)`]
                P2A_CD1_OPEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV; SUBSET_REFL] THEN ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `bounded (IMAGE (\v. vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) (at v))
                   (cball(vec 0:real^1,&1)))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C1:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[SMOOTH_BUMP_BOUNDS]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `v:real^1` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "continuous_on")) (concl th))) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ASM_SIMP_TAC[]]);;

(* Lipschitz bound through a point where Y may fail to be differentiable.   *)

let P2A_LIPSCHITZ_PUNCT = prove
 (`!(Y:real^1->real^N) s0 k M.
     &0 < k /\ Y continuous_on interval[lift(s0 - k),lift(s0 + k)] /\
     (!s. abs(s - s0) < k /\ ~(s = s0)
          ==> Y differentiable (at (lift s)) /\ norm(vector_derivative Y (at (lift s))) <= M)
     ==> !s. abs(s - s0) <= k ==> norm(Y(lift s) - Y(lift s0)) <= M * abs(s - s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real = s0` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_SUB_REFL; REAL_ABS_0; REAL_MUL_RZERO;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. s0 - k <= a /\ a < b /\ b <= s0 + k /\ (a = s0 \/ b = s0)
                      ==> norm((Y:real^1->real^N)(lift b) - Y(lift a)) <= M * (b - a)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    (MP_TAC(ISPECL [`Y:real^1->real^N`;
                    `\x:real^1 h:real^1. drop h % vector_derivative (Y:real^1->real^N) (at x)`;
                    `lift a`; `lift b`] MVT_GENERAL) THEN
     ANTS_TAC THENL
      [ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
        [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
         EXISTS_TAC `interval[lift(s0 - k),lift(s0 + k)]` THEN
         ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
         REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
         X_GEN_TAC `y:real` THEN STRIP_TAC THEN
         REWRITE_TAC[GSYM has_vector_derivative; GSYM VECTOR_DERIVATIVE_WORKS] THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN
         ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
       ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `y:real^1` (CONJUNCTS_THEN2
       (STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTERVAL_1; LIFT_DROP]) MP_TAC)) THEN
     REWRITE_TAC[GSYM LIFT_SUB; LIFT_DROP; NORM_MUL] THEN
     MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
     SUBGOAL_THEN `abs(b - a) = b - a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `drop(y:real^1)`) THEN REWRITE_TAC[LIFT_DROP] THEN
     ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  ASM_CASES_TAC `s0 < s` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `s0:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `n1 = n2 /\ y = z ==> n1 <= y ==> n2 <= z`) THEN
    CONJ_TAC THENL [MATCH_ACCEPT_TAC NORM_SUB; AP_TERM_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* The bump as a map real^1 -> real^1 is C^1 everywhere.                    *)

let P2A_BUMP_DIFF = prove
 (`!v:real^1. (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) differentiable (at v) /\
              (\v. vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) (at v))
                continuous (at v)`,
  MP_TAC P2A_BUMP_FACTS THEN MESON_TAC[]);;

let P2A_PHK_NORM = prove
 (`!k s s0. &0 < k ==> norm(inv k % (lift s - lift s0)) = abs(s - s0) / k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; GSYM LIFT_SUB; NORM_LIFT; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN REWRITE_TAC[real_div] THEN
  REAL_ARITH_TAC);;

(* The blend of Y with a point P around s0 at scale k.                       *)

let p2a_blend = new_definition
 `p2a_blend (Y:real^1->real^N) (P:real^N) (s0:real) (k:real) =
    \v. Y v + smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0)) % (P - Y v)`;;

let P2A_BLEND_VALUES = prove
 (`!(Y:real^1->real^N) P s0 k.
     &0 < k
     ==> (!s. abs(s - s0) <= k / &3 ==> p2a_blend Y P s0 k (lift s) = P) /\
         (!s. &2 * k / &3 <= abs(s - s0) ==> p2a_blend Y P s0 k (lift s) = Y(lift s)) /\
         (!v. norm(p2a_blend Y P s0 k v - P) <= norm(Y v - P) /\
              norm(p2a_blend Y P s0 k v - Y v) <= norm(Y v - P))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2a_blend] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_bump (&1 / &3) (&2 / &3) (inv k % (lift s - lift s0)) = &1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_SIMP_TAC[P2A_PHK_NORM; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_bump (&1 / &3) (&2 / &3) (inv k % (lift s - lift s0)) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_SIMP_TAC[P2A_PHK_NORM; REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^1` THEN
  MP_TAC(ISPECL [`&1 / &3`; `&2 / &3`; `inv k % (v - lift s0):real^1`] SMOOTH_BUMP_BOUNDS) THEN
  ABBREV_TAC `p = smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0):real^1)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `((Y:real^1->real^N) v + p % (P - Y v)) - P = (&1 - p) % (Y v - P) /\
                (Y v + p % (P - Y v)) - Y v = (--p) % (Y v - P)`
  (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_NEG] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let P2A_BLEND_DERIV = prove
 (`!(Y:real^1->real^N) P s0 k v.
     &0 < k /\ Y differentiable (at v)
     ==> (p2a_blend Y P s0 k has_vector_derivative
          ((&1 - smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0))) %
             vector_derivative Y (at v) +
           (inv k * drop(vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                           (at (inv k % (v - lift s0))))) % (P - Y v)))
         (at v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_blend] THEN
  SUBGOAL_THEN
   `((\v. lift(smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0)))) has_vector_derivative
     (inv k % vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                (at (inv k % (v - lift s0))))) (at v)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\v. lift(smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0)))) =
      (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w)) o (\v. inv k % (v - lift s0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `inv k % vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                (at (inv k % (v - lift s0))) =
      drop(inv k % vec 1) %
      vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                        (at ((\v. inv k % (v - lift s0)) v))`
    SUBST1_TAC THENL [REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `inv k % vec 1:real^1 = inv k % (vec 1 - vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST];
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS; P2A_BUMP_DIFF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1 y:real^N. drop x % y`;
                 `\v. lift(smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0)))`;
                 `\v. (P:real^N) - (Y:real^1->real^N) v`;
                 `inv k % vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                            (at (inv k % (v - lift s0)))`;
                 `vec 0 - vector_derivative (Y:real^1->real^N) (at v)`; `v:real^1`]
                HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BILINEAR_DROP_MUL] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; GSYM VECTOR_DERIVATIVE_WORKS] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP; DROP_CMUL] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 - smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0))) %
      vector_derivative (Y:real^1->real^N) (at v) +
    (inv k * drop(vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                    (at (inv k % (v - lift s0))))) % ((P:real^N) - Y v) =
    vector_derivative Y (at v) +
    (smooth_bump (&1 / &3) (&2 / &3) (inv k % (v - lift s0)) %
       (vec 0 - vector_derivative Y (at v)) +
     (inv k * drop(vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                     (at (inv k % (v - lift s0))))) % (P - Y v))`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]);;

let P2A_BUMP_DBOUND = prove
 (`?C1. &0 <= C1 /\
        !v:real^1. norm v <= &1
                   ==> norm(vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v))
                                              (at v)) <= C1`,
  MP_TAC P2A_BUMP_FACTS THEN MESON_TAC[]);;

let P2A_PHK_CONT = prove
 (`!k s0 x. (\w:real^1. inv k % (w - lift s0)) continuous (at x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
  REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST]);;

let P2A_BUMPK_CONT = prove
 (`!k s0 x. (\w:real^1. lift(smooth_bump (&1 / &3) (&2 / &3) (inv k % (w - lift s0))))
            continuous (at x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\w:real^1. lift(smooth_bump (&1 / &3) (&2 / &3) (inv k % (w - lift s0)))) =
                (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w)) o (\w. inv k % (w - lift s0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN REWRITE_TAC[P2A_PHK_CONT] THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[P2A_BUMP_DIFF]);;

let P2A_DBUMPK_CONT = prove
 (`!k s0 x. (\w:real^1. vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                          (at (inv k % (w - lift s0))))
            continuous (at x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\w:real^1. vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                  (at (inv k % (w - lift s0)))) =
    (\w. vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w)) (at w)) o
    (\w. inv k % (w - lift s0))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN REWRITE_TAC[P2A_PHK_CONT; P2A_BUMP_DIFF]);;

(* The blend is C^1 where Y is (and near s0), with a derivative bound       *)
(* M + C D / k, C a universal constant.                                      *)

let P2A_BLEND_C1 = prove
 (`!C1. &0 <= C1 /\
        (!v:real^1. norm v <= &1
                    ==> norm(vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v))
                                               (at v)) <= C1)
        ==> !(Y:real^1->real^N) P s0 k M D G s.
              &0 < k /\ &0 <= M /\ &0 <= D /\ open G /\
              (!v. v IN G ==> Y differentiable (at v) /\
                              (\w. vector_derivative Y (at w)) continuous (at v) /\
                              norm(vector_derivative Y (at v)) <= M /\
                              norm(Y v - P) <= D) /\
              abs(s - s0) < k /\ (lift s IN G \/ abs(s - s0) < k / &3)
              ==> p2a_blend Y P s0 k differentiable (at (lift s)) /\
                  (\w. vector_derivative (p2a_blend Y P s0 k) (at w)) continuous (at (lift s)) /\
                  norm(vector_derivative (p2a_blend Y P s0 k) (at (lift s))) <= M + C1 * D / k`,
  GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `&0 <= M + C1 * D / k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `abs(s - s0) < k / &3` THENL
   [ABBREV_TAC `d = k / &3 - abs(s - s0)` THEN
    SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!w. dist(w,lift s) < d ==> p2a_blend (Y:real^1->real^N) P s0 k w = P`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`Y:real^1->real^N`; `P:real^N`; `s0:real`; `k:real`] P2A_BLEND_VALUES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `drop w` o CONJUNCT1) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!w. dist(w,lift s) < d
                      ==> (p2a_blend (Y:real^1->real^N) P s0 k has_vector_derivative vec 0) (at w)`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`\w:real^1. (P:real^N)`; `d - dist(w:real^1,lift s)`] THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x':real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`x':real^1`; `w:real^1`; `lift s`] DIST_TRIANGLE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p2a_blend (Y:real^1->real^N) P s0 k has_vector_derivative vec 0) (at (lift s))`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE];
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`\w:real^1. vec 0:real^N`; `d:real`] THEN
      ASM_REWRITE_TAC[CONTINUOUS_CONST] THEN X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[];
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP VECTOR_DERIVATIVE_AT) THEN
      ASM_REWRITE_TAC[NORM_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift s IN G` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !w. dist(w,lift s) < e ==> w IN G` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(G:real^1->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `lift s`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  ABBREV_TAC
   `Bd = \w:real^1. (&1 - smooth_bump (&1 / &3) (&2 / &3) (inv k % (w - lift s0))) %
                    vector_derivative (Y:real^1->real^N) (at w) +
                    (inv k * drop(vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                                    (at (inv k % (w - lift s0))))) % (P - Y w)` THEN
  SUBGOAL_THEN `!w. w IN G ==> (p2a_blend (Y:real^1->real^N) P s0 k has_vector_derivative Bd w)
                                (at w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN EXPAND_TAC "Bd" THEN
    MATCH_MP_TAC P2A_BLEND_DERIV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`Bd:real^1->real^N`; `e:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "Bd" THEN MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
      REWRITE_TAC[CONTINUOUS_CONST; P2A_BUMPK_CONT];
      ASM_MESON_TAC[];
      SUBGOAL_THEN
       `lift o (\w:real^1. inv k * drop(vector_derivative
                   (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w)) (at (inv k % (w - lift s0))))) =
        (\w. inv k % vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                       (at (inv k % (w - lift s0))))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[P2A_DBUMPK_CONT];
      MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `vector_derivative (p2a_blend (Y:real^1->real^N) P s0 k) (at (lift s)) =
                Bd(lift s)` SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "Bd" THEN
  SUBGOAL_THEN
   `&0 <= smooth_bump (&1 / &3) (&2 / &3) (inv k % (lift s - lift s0):real^1) /\
    smooth_bump (&1 / &3) (&2 / &3) (inv k % (lift s - lift s0):real^1) <= &1 /\
    abs(drop(vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                               (at (inv k % (lift s - lift s0))))) <= C1 /\
    norm(vector_derivative (Y:real^1->real^N) (at (lift s))) <= M /\
    norm(Y(lift s) - (P:real^N)) <= D`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SMOOTH_BUMP_BOUNDS; ABS_DROP] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `C1:real`)) (concl th))) THEN
      ASM_SIMP_TAC[P2A_PHK_NORM; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `p = smooth_bump (&1 / &3) (&2 / &3) (inv k % (lift s - lift s0):real^1)` THEN
  ABBREV_TAC `q = drop(vector_derivative (\w. lift(smooth_bump (&1 / &3) (&2 / &3) w))
                                         (at (inv k % (lift s - lift s0))))` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(&1 - p) * norm(vector_derivative (Y:real^1->real^N) (at (lift s))) +
              abs(inv k * q) * norm((P:real^N) - Y(lift s))` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM NORM_MUL; NORM_TRIANGLE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `C1 * D / k = (inv k * C1) * D` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]]]);;

(* A fixed choice of the bump derivative bound.                              *)

let p2a_bc = new_definition
 `p2a_bc = @C1. &0 <= C1 /\
                !v:real^1. norm v <= &1
                           ==> norm(vector_derivative
                                      (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) (at v))
                               <= C1`;;

let P2A_BC = prove
 (`&0 <= p2a_bc /\
   !v:real^1. norm v <= &1
              ==> norm(vector_derivative (\v. lift(smooth_bump (&1 / &3) (&2 / &3) v)) (at v))
                  <= p2a_bc`,
  REWRITE_TAC[p2a_bc] THEN CONV_TAC SELECT_CONV THEN REWRITE_TAC[P2A_BUMP_DBOUND]);;

let P2A_BLEND_C1_BC = prove
 (`!(Y:real^1->real^N) P s0 k M D G s.
     &0 < k /\ &0 <= M /\ &0 <= D /\ open G /\
     (!v. v IN G ==> Y differentiable (at v) /\
                     (\w. vector_derivative Y (at w)) continuous (at v) /\
                     norm(vector_derivative Y (at v)) <= M /\
                     norm(Y v - P) <= D) /\
     abs(s - s0) < k /\ (lift s IN G \/ abs(s - s0) < k / &3)
     ==> p2a_blend Y P s0 k differentiable (at (lift s)) /\
         (\w. vector_derivative (p2a_blend Y P s0 k) (at w)) continuous (at (lift s)) /\
         norm(vector_derivative (p2a_blend Y P s0 k) (at (lift s))) <= M + p2a_bc * D / k`,
  MATCH_MP_TAC P2A_BLEND_C1 THEN REWRITE_TAC[P2A_BC]);;

(* ========================================================================= *)
(* A uniform comparison of the slice distances with the Euclidean distance   *)
(* in a region chart, near a time where the slice atlas is constant          *)
(* (P2A_SLICE_DIST_BOUND).  The slice metric in a slice chart is the         *)
(* pullback of the region metric (inverse form of P2A_RLOCAL_SLICE), which   *)
(* is jointly continuous in time and space.                                  *)
(* ========================================================================= *)

(* Local copy of a one-line fact (the Part 2B copy is not in this closure). *)

let P2A_MPULLBACK_ID = prove
 (`!(G:real^N->real^N^N) z. mpullback (\x. x) G z = G z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^N. x) (at z) = (\x. x)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

(* The slice metric in a slice chart, through the region metric.            *)

let P2A_SLICE_METRIC_RLOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b (U:A->bool) (phi:A->real^N) t (c':(A->bool)#(A->real^N)) y.
     p2a_region V W a b /\ (U,phi) IN p2a_vatlas V b /\ a < t /\ t <= b /\
     c' IN p2a_vatlas V t /\ y IN IMAGE (SND c') ((U INTER W) INTER FST c')
     ==> metric_local (p2a_vatlas V t) c' (p2a_vmetric V t) y =
         mpullback (chart_trans c' (U INTER W,phi)) (p2a_rlocal V W b (U INTER W,phi) t) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^N`; `t:real`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `b:real`; `t:real`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. x IN U /\ x IN W /\ x IN FST(c':(A->bool)#(A->real^N)) /\ y = SND c' x`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N) y = phi x`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) t`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) t`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT1 th]);
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  TRANS_TAC EQ_TRANS
   `mpullback (chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N))
              (mpullback (chart_trans (U INTER W,phi) c')
                         (metric_local (p2a_vatlas (V:(real->A topology)#
                            (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) c'
                                       (p2a_vmetric V t))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2A_RLOCAL_SLICE THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `mpullback (chart_trans (U INTER W,phi:A->real^N) (c':(A->bool)#(A->real^N)) o
               chart_trans c' (U INTER W,phi))
              (metric_local (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t) c'
                            (p2a_vmetric V t)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_COMPOSE THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `IMAGE (phi:A->real^N) ((U INTER W) INTER FST(c':(A->bool)#(A->real^N)))` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `mpullback (\y:real^N. y)
              (metric_local (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) t)
                            (c':(A->bool)#(A->real^N)) (p2a_vmetric V t)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    REWRITE_TAC[P2A_MPULLBACK_ID]]);;

let P2A_QUAD_VECTORIZE_BOUND = prove
 (`!(G:real^N^N) v. v dot (G ** v) <= norm(vectorize G) * norm v pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm((G:real^N^N) ** v)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(v:real^N) * norm(vectorize(G:real^N^N)) * norm v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE];
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* Smooth maps are Lipschitz on small closed balls.                          *)

let P2A_SMOOTH_LIPSCHITZ = prove
 (`!(Tm:real^N->real^M) O z0.
     open O /\ smooth_map_on O Tm /\ z0 IN O
     ==> ?r Lt. &0 < r /\ &0 <= Lt /\ cball(z0,r) SUBSET O /\
                !z1 z2. z1 IN cball(z0,r) /\ z2 IN cball(z0,r)
                        ==> norm(Tm z1 - Tm z2) <= Lt * norm(z1 - z2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z0:real^N` o REWRITE_RULE[OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Tm:real^N->real^M`; `O:real^N->bool`; `cball(z0:real^N,r)`]
                P2A_FRECHET_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Lt:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `Lt:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\z. frechet_derivative (Tm:real^N->real^M) (at z)` THEN
  REWRITE_TAC[CONVEX_CBALL] THEN
  SUBGOAL_THEN `!z. z IN cball(z0:real^N,r) ==> (Tm:real^N->real^M) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPEC `frechet_derivative (Tm:real^N->real^M) (at z)` ONORM) THEN
    ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC[]]);;

(* A bound for the slice metrics in a fixed slice chart, uniform for the    *)
(* times tt - s^2, s in [s1,s2], on a compact set.                          *)

let P2A_SLICE_QUAD_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b'' (U:A->bool) (phi:A->real^N) tt sa sb (c':(A->bool)#(A->real^N)) K s1 s2.
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     sa < s1 /\ s1 <= s2 /\ s2 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'') /\
     (!s. s1 <= s /\ s <= s2 ==> c' IN p2a_vatlas V (tt - s pow 2)) /\
     compact K /\ K SUBSET IMAGE (SND c') ((U INTER W) INTER FST c')
     ==> ?C. !s y v. s1 <= s /\ s <= s2 /\ y IN K
                     ==> &0 * norm v pow 2 <=
                         v dot (metric_local (p2a_vatlas V (tt - s pow 2)) c'
                                             (p2a_vmetric V (tt - s pow 2)) y ** v) /\
                         v dot (metric_local (p2a_vatlas V (tt - s pow 2)) c'
                                             (p2a_vmetric V (tt - s pow 2)) y ** v)
                         <= C * norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - s1 pow 2`; `c':(A->bool)#(A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL] THEN FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `a':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)`;
                 `IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')`;
                 `K:real^N->bool`] P2A_FRECHET_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Bd:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `sa:real`; `sb:real`] P2A_REGION_SFAMILY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?R. &0 <= R /\
        !s y. s1 <= s /\ s <= s2 /\ y IN K
              ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                         (p2a_rlocal V W b'' (U INTER W,phi) (tt - s pow 2)
                            (chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi) y)))
                  <= R`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC
     `IMAGE (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)
                               (tt - drop(fstcart z) pow 2) (sndcart z)))
            (interval[lift s1,lift s2] PCROSS
             IMAGE (chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi)) K)`
     COMPACT_IMP_BOUNDED) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval(lift sa,lift sb) PCROSS IMAGE (phi:A->real^N) (U INTER W)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; PASTECART_IN_PCROSS] THEN
          REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
          MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]];
        MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `R:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `pastecart (lift s) (chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N) y)`) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `R * Bd pow 2` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a' < tt - s pow 2 /\ tt - s pow 2 <= b''` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `a':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - s pow 2`; `c':(A->bool)#(A->real^N)`; `y:real^N`]
                P2A_SLICE_METRIC_RLOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)
                  differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c':(A->bool)#(A->real^N))) ((U INTER W) INTER FST c')` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N)`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)
                             (tt - s pow 2)`; `y:real^N`; `v:real^N`; `v:real^N`]
                LRG_MPULLBACK_DOT) THEN
  ANTS_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
                  DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N) y IN
    IMAGE phi (U INTER W)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^N) (U INTER W))
       (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`;
                   `(U INTER W:A->bool,phi:A->real^N)`; `tt - s pow 2`] P2A_RLOCAL_FIELD) THEN
    ASM_SIMP_TAC[P2A_REGION_RCHART; FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
  ABBREV_TAC `w = frechet_derivative (chart_trans (c':(A->bool)#(A->real^N))
                                                  (U INTER W,phi:A->real^N)) (at y) v` THEN
  ABBREV_TAC `G = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)
                             (tt - s pow 2)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_CASES_TAC `w:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                     ((G:real^N->real^N^N)
                        (chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N) y))) *
              norm(w:real^N) pow 2` THEN
  REWRITE_TAC[P2A_QUAD_VECTORIZE_BOUND] THEN
  SUBGOAL_THEN
   `norm((vectorize:real^N^N->real^(N,N)finite_prod)
           ((G:real^N->real^N^N)
              (chart_trans (c':(A->bool)#(A->real^N)) (U INTER W,phi:A->real^N) y))) <= R /\
    norm(w:real^N) <= Bd * norm(v:real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "G" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "w" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) pow 2 <= (Bd * norm(v:real^N)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(R * Bd pow 2) * norm(v:real^N) pow 2 = R * (Bd * norm v) pow 2`
  SUBST1_TAC THENL [REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; REAL_LE_POW_2]);;

(* The slice distances are uniformly Lipschitz in a region chart near a     *)
(* point, for the times tt - s^2 with s near s0, if the slice atlas is      *)
(* constant there.                                                           *)

let P2A_SLICE_DIST_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a' b'' (U:A->bool) (phi:A->real^N) tt sa sb s0 x0.
     p2a_svs V /\ p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     sa < s0 /\ s0 < sb /\
     (!s. sa < s /\ s < sb ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b'') /\
     (!s. sa < s /\ s < sb ==> p2a_vatlas V (tt - s pow 2) = p2a_vatlas V (tt - s0 pow 2)) /\
     x0 IN U INTER W
     ==> ?r L. &0 < r /\ &0 <= L /\
               !s z1 z2. abs(s - s0) <= r /\ dist(z1,phi x0) < r /\ dist(z2,phi x0) < r
                         ==> z1 IN IMAGE phi (U INTER W) /\ z2 IN IMAGE phi (U INTER W) /\
                             mfd_dist (p2a_vtop V (tt - s pow 2),p2a_vatlas V (tt - s pow 2))
                                      (p2a_vmetric V (tt - s pow 2))
                                      (chart_inv (U INTER W,phi) z1)
                                      (chart_inv (U INTER W,phi) z2)
                             <= L * dist(z1,z2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a' < tt - s0 pow 2 /\ tt - s0 pow 2 <= b''` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `a':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `tt - s0 pow 2`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:A) IN topspace(p2a_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s0 pow 2))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(W:A->bool) SUBSET topspace(p2a_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s0 pow 2))`
    MP_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?U' (phi':A->real^N).
      (U',phi') IN p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s0 pow 2) /\ x0 IN U'`
  (X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `phi':A->real^N` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s0 pow 2)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s0 pow 2)`; `x0:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`FST(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s0 pow 2)) (x0:A))`;
      `SND(chart_at (p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) (tt - s0 pow 2)) (x0:A))`] THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - s0 pow 2`; `(U':A->bool,phi':A->real^N)`]
                P2A_REGION_SLICE_CHART) THEN
  ASM_REWRITE_TAC[diffeomorphism_on; FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. x IN U INTER W ==> chart_inv (U INTER W,phi:A->real^N) (phi x) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN U INTER W
                      ==> chart_trans (U INTER W,phi:A->real^N) (U',phi':A->real^N) (phi x) =
                          phi' x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[chart_trans; SND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`chart_trans (U INTER W,phi:A->real^N) (U':A->bool,phi':A->real^N)`;
                 `IMAGE (phi:A->real^N) ((U INTER W) INTER U')`; `(phi:A->real^N) x0`]
                P2A_SMOOTH_LIPSCHITZ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `Lt:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?r2. &0 < r2 /\
                     cball((phi':A->real^N) x0,r2) SUBSET IMAGE phi' ((U INTER W) INTER U')`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (phi':A->real^N) ((U INTER W) INTER U'))` THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r3. &0 < r3 /\ sa < s0 - r3 /\ s0 + r3 < sb` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (s0 - sa) (sb - s0) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `sa:real`; `sb:real`;
                 `(U':A->bool,phi':A->real^N)`; `cball((phi':A->real^N) x0,r2)`;
                 `s0 - r3`; `s0 + r3`] P2A_SLICE_QUAD_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL; FST; SND] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) (tt - s pow 2) = p2a_vatlas V (tt - s0 pow 2)`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `C:real`)] THEN
  MAP_EVERY EXISTS_TAC [`min (min r1 r3) (r2 / (Lt + &1))`; `sqrt(abs C) * Lt`] THEN
  SUBGOAL_THEN `&0 < r2 / (Lt + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z1:real^N`; `z2:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(s - s0) <= r3 /\ dist(z1,(phi:A->real^N) x0) < r1 /\ dist(z2,phi x0) < r1 /\
                dist(z1,phi x0) < r2 / (Lt + &1) /\ dist(z2,phi x0) < r2 / (Lt + &1)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^N) IN cball((phi:A->real^N) x0,r1) /\ z2 IN cball(phi x0,r1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^N) IN IMAGE (phi:A->real^N) ((U INTER W) INTER U') /\
                z2 IN IMAGE phi ((U INTER W) INTER U')`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* the images in the slice chart stay in the ball *)
  SUBGOAL_THEN
   `!z. z IN cball((phi:A->real^N) x0,r1) /\ dist(z,phi x0) < r2 / (Lt + &1)
        ==> chart_trans (U INTER W,phi) (U',phi') z IN cball((phi':A->real^N) x0,r2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `(phi:A->real^N) x0`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Lt:real`)) (concl th))) THEN
    ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE; IN_INTER] THEN
    SUBGOAL_THEN `norm(z - (phi:A->real^N) x0) * (Lt + &1) < r2` MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN
      SUBGOAL_THEN `&0 < Lt + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    MP_TAC(ISPEC `z - (phi:A->real^N) x0` NORM_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(z1:real^N) IN IMAGE (phi:A->real^N) ((U INTER W) INTER U')` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w1:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(z2:real^N) IN IMAGE (phi:A->real^N) ((U INTER W) INTER U')` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w2:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w1:A) IN U INTER W /\ (w2:A) IN U INTER W /\ w1 IN U' /\ w2 IN U'`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  (* the slice at time tt - s^2 *)
  SUBGOAL_THEN `sa < s /\ s < sb` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a' < tt - s pow 2 /\ tt - s pow 2 <= b''` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `a':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) (tt - s pow 2) = p2a_vatlas V (tt - s0 pow 2)`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `tt - s pow 2`]
                P2A_REGION_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (p2a_vatlas (V:(real->A topology)#
                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2))
                  (p2a_vmetric V (tt - s pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o SPEC `tt - s pow 2`) THEN
    SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2))
                    = {})` (fun th -> SIMP_TAC[th]) THEN
    SUBGOAL_THEN `(W:A->bool) SUBSET topspace(p2a_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2))`
    MP_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U':A->bool,phi':A->real^N) IN
                p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) (tt - s pow 2)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (U':A->bool,phi':A->real^N) (phi' w1) = w1 /\
                chart_inv (U',phi') (phi' w2) = w2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `U':A->bool`; `phi':A->real^N`] CHART_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi':A->real^N) w1 IN cball(phi' x0,r2) /\ phi' w2 IN cball(phi' x0,r2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(phi':A->real^N) w1 =
                    chart_trans (U INTER W,phi:A->real^N) (U',phi') (phi w1)`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `(phi':A->real^N) w2 =
                    chart_trans (U INTER W,phi:A->real^N) (U',phi') (phi w2)`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[(phi':A->real^N) w1,phi' w2] SUBSET cball(phi' x0,r2)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `cball((phi':A->real^N) x0,r2)` CONVEX_CONTAINS_SEGMENT) THEN
    REWRITE_TAC[CONVEX_CBALL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length (p2a_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - s pow 2))
                (p2a_vmetric V (tt - s pow 2))
                (\t. chart_inv (U':A->bool,phi':A->real^N)
                       (phi' w1 + t % (phi' (w2:A) - phi' (w1:A)))) (&0) (&1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `U':A->bool`; `phi':A->real^N`; `(phi':A->real^N) w1`; `(phi':A->real^N) w2`]
                  GRGD_CHART_SEGMENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s pow 2)`;
                   `p2a_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - s pow 2)`;
                   `\t. chart_inv (U':A->bool,phi':A->real^N)
                          (phi' w1 + t % (phi' (w2:A) - phi' (w1:A)))`; `&0`; `&1`]
                  MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                    VECTOR_ARITH `a + (b - a):real^N = b`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(abs C) * dist((phi':A->real^N) w1,phi' w2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_SEGMENT_LENGTH_UPPER THEN
    MAP_EVERY EXISTS_TAC
     [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) (tt - s pow 2)`; `&0`; `cball((phi':A->real^N) x0,r2)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:real^N`; `v:real^N`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `C:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * norm(v:real^N) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS] THEN
  SUBGOAL_THEN `(phi':A->real^N) w1 = chart_trans (U INTER W,phi:A->real^N) (U',phi') (phi w1) /\
                phi' w2 = chart_trans (U INTER W,phi) (U',phi') (phi w2)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `Lt:real`)) (concl th) &&
    can (find_term ((=) `r1:real`)) (concl th))) THEN
  ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Generic tools for the corner rounding: a bound for the s-Lagrangian on    *)
(* compact sets, a small-parameter choice, and the piecewise-C^1 structure   *)
(* of a curve patched on a window.                                           *)
(* ========================================================================= *)

let P2A_LLAG_BOUND = prove
 (`!Uo sa sb (Gt:real->real^N->real^N^N) tt K s1 s2 R.
     p2a_lsmooth Uo sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 <= s2 /\ s2 < sb /\
     compact K /\ K SUBSET Uo
     ==> ?Kb. !s y A. s1 <= s /\ s <= s2 /\ y IN K /\ norm A <= R
                      ==> abs(p2a_llag Gt tt s y A) <= Kb`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN
  MP_TAC(ISPEC
   `IMAGE (\z. lift(p2a_llag (Gt:real->real^N->real^N^N) tt (drop(fstcart z))
                             (fstcart(sndcart z)) (sndcart(sndcart z))))
          (interval[lift s1,lift s2] PCROSS ((K:real^N->bool) PCROSS cball(vec 0:real^N,R)))`
   COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((Uo:real^N->bool) PCROSS (:real^N))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
        REPEAT STRIP_TAC THEN (ASM_REAL_ARITH_TAC ORELSE ASM SET_TAC[])];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_CBALL]];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `Kb:real` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `A:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (pastecart (y:real^N) (A:real^N))`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; NORM_LIFT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_CBALL_0] THEN
  ASM_REWRITE_TAC[]);;

let P2A_SMALL_K = prove
 (`!a b. &0 < a /\ &0 <= b ==> ?k. &0 < k /\ !k'. &0 < k' /\ k' <= k ==> k' * b < a`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `a / (b + &1)` THEN
  SUBGOAL_THEN `&0 < b + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN X_GEN_TAC `k':real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a / (b + &1) * b` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a / (b + &1) * b = a - a / (b + &1)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < b + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> a - x < a`) THEN ASM_SIMP_TAC[REAL_LT_DIV]);;

(* A curve patched on a window [b1,b2] inside (c1,c2), where it agrees with *)
(* a curve sig that is two-sided C^1 in every chart, is piecewise C^1 with  *)
(* any finite corner set containing the old corners outside (c1,c2).        *)

let P2A_PC1_PATCH = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt (gamma:real->A) gamma1 sig b b1 b2 c1 c2 P Q.
     p2a_pc1 V tt gamma (&0) b P /\ FINITE Q /\
     &0 <= c1 /\ c1 < b1 /\ b1 <= b2 /\ b2 < c2 /\
     (!tau. tau < b1 \/ b2 < tau ==> gamma1 tau = gamma tau) /\
     (!tau. c1 < tau /\ tau < c2 ==> gamma1 tau = sig tau) /\
     (!tau0 c. c1 < tau0 /\ tau0 < c2 /\ tau0 <= b /\ c IN p2a_vatlas V (tt - tau0) /\
               sig tau0 IN FST c
               ==> ?d. &0 < d /\
                       continuously_differentiable 1
                         {s | tau0 - d <= drop s /\ drop s <= tau0 + d /\
                              p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - tau0) /\
                              sig(drop s) IN FST c}
                         (\s. SND c (sig(drop s)))) /\
     (!tau. tau IN P /\ ~(c1 < tau /\ tau < c2) ==> tau IN Q)
     ==> p2a_pc1 V tt gamma1 (&0) b Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G")) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "OUT") (CONJUNCTS_THEN2 (LABEL_TAC "IN")
    (CONJUNCTS_THEN2 (LABEL_TAC "SIG") (LABEL_TAC "PQ")))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`tau0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `c1 < tau0 /\ tau0 < c2` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    USE_THEN "SIG" (MP_TAC o SPECL [`tau0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(sig:real->A) tau0 = gamma1 tau0` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "IN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `d' = min d (min (tau0 - c1) (c2 - tau0)) / &2` THEN
    SUBGOAL_THEN `&0 < d' /\ d' <= d /\ c1 < tau0 - d' /\ tau0 + d' < c2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `d':real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(A->bool)#(A->real^N)`; `sig:real->A`;
                   `{s | tau0 - d <= drop s /\ drop s <= tau0 + d /\
                         p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) (tt - drop s) =
                         p2a_vatlas V (tt - tau0) /\
                         (sig:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))}`]
                  P2A_CD_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(gamma1:real->A)(drop s) = sig(drop s)` ASSUME_TAC THENL
      [USE_THEN "IN" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    UNDISCH_TAC `(gamma1:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* outside the window gamma1 = gamma near tau0 *)
  SUBGOAL_THEN `?d1. &0 < d1 /\ !tau. abs(tau - tau0) <= d1 ==> (gamma1:real->A) tau = gamma tau`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `tau0 <= c1` THENL
     [EXISTS_TAC `(b1 - tau0) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN USE_THEN "OUT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `(tau0 - b2) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN USE_THEN "OUT" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma1:real->A) tau0 = gamma tau0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "G" (MP_TAC o SPECL [`tau0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(gamma1:real->A) tau0 IN FST(c:(A->bool)#(A->real^N))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "GL") (CONJUNCTS_THEN2 (LABEL_TAC "GR") (LABEL_TAC "GB"))))) THEN
  EXISTS_TAC `min d d1` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "GL" (MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    USE_THEN "GR" (MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    DISCH_TAC THEN
    SUBGOAL_THEN `~((tau0:real) IN P)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((tau0:real) IN Q)` THEN REWRITE_TAC[] THEN
      USE_THEN "PQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "GB" (fun th -> MP_TAC(MATCH_MP P2A_CD_TRANSFER
      (MP th (ASSUME `~((tau0:real) IN P)`))))] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(gamma1:real->A)(drop s) = gamma(drop s)` ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  UNDISCH_TAC `(gamma1:real->A)(drop s) IN FST(c:(A->bool)#(A->real^N))` THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The corner data at an interior corner s0^2 and the rounded curve          *)
(* p2a_round: in the region chart the s-curve Y is replaced on [s0 - 3k/4,   *)
(* s0 + 3k/4] by its blend with Y(s0).                                       *)
(* ========================================================================= *)

let p2a_cdata = new_definition
 `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
               (real->A->real^N^N)) tt x b (gamma:real->A) W a' b'' (U:A->bool)
            (phi:A->real^N) s0 k0 M <=>
    p2a_svs V /\ p2a_adm V tt x b gamma /\
    p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
    &0 < k0 /\ k0 < s0 /\ (s0 + k0) pow 2 < b /\ &0 <= M /\
    (!s. abs(s - s0) < k0
         ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'' /\ gamma(s pow 2) IN U INTER W) /\
    (!s. abs(s - s0) < k0 /\ ~(s = s0)
         ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift s)) /\
             (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
               continuous (at (lift s)) /\
             norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) <= M)`;;

let P2A_CDATA_YCONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s0 k0 M k.
     p2a_cdata V tt x b gamma W a' b'' U phi s0 k0 M /\ &0 < k /\ k < k0
     ==> (\v. phi(gamma(drop v pow 2))) continuous_on interval[lift(s0 - k),lift(s0 + k)] /\
         !s. abs(s - s0) <= k
             ==> norm(phi(gamma(s pow 2)) - phi(gamma(s0 pow 2))) <= M * abs(s - s0)`,
  REWRITE_TAC[p2a_cdata] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s0 + k) pow 2 <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s0 + k0) pow 2` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(s0 - k),lift(s0 + k)]` ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_ADM_SCONT) THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s0 - k`; `s0 + k`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`; `s0:real`; `k:real`;
                 `M:real`] P2A_LIPSCHITZ_PUNCT) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `M:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let P2A_CDATA_BLEND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s0 k0 M k.
     p2a_cdata V tt x b gamma W a' b'' U phi s0 k0 M /\ &0 < k /\ k < k0
     ==> (!s. abs(s - s0) < k
              ==> p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
                    differentiable (at (lift s)) /\
                  (\w. vector_derivative
                         (p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k)
                         (at w)) continuous (at (lift s)) /\
                  norm(vector_derivative
                         (p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k)
                         (at (lift s))) <= (&1 + p2a_bc) * M) /\
         (!s. &2 * k / &3 <= abs(s - s0)
              ==> p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
                    (lift s) = phi(gamma(s pow 2))) /\
         (!s. abs(s - s0) <= k
              ==> norm(p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
                         (lift s) - phi(gamma(s0 pow 2))) <= M * abs(s - s0) /\
                  norm(p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
                         (lift s) - phi(gamma(s pow 2))) <= M * abs(s - s0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                 `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`; `s0:real`; `k:real`]
                P2A_BLEND_VALUES) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M` THEN
  REWRITE_TAC[p2a_cdata] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s0 pow 2)))` THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_blend")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vector_norm")) (concl th))) THEN
    REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[]] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                 `(phi:A->real^N)((gamma:real->A)(s0 pow 2))`; `s0:real`; `k:real`; `M:real`;
                 `M * k`; `interval(lift(s0 - k),lift(s0 + k)) DIFF {lift s0}`; `s:real`]
                P2A_BLEND_C1_BC) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERVAL; CLOSED_SING]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; IN_DIFF; IN_INTERVAL_1; IN_SING; LIFT_DROP; LIFT_EQ] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `M:real`)) (concl th) &&
        can (find_term ((=) `k0:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[LIFT_DROP]] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * abs(t - s0)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_SING; LIFT_DROP; LIFT_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `M + p2a_bc * (M * k) / k = (&1 + p2a_bc) * M` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD);;

(* The new piece and the rounded curve.                                      *)

let p2a_rsig = new_definition
 `p2a_rsig (gamma:real->A) (U:A->bool) (W:A->bool) (phi:A->real^N) (s0:real) (k:real) =
    \tau. chart_inv (U INTER W,phi)
            (p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
                       (lift(sqrt tau)))`;;

let p2a_round = new_definition
 `p2a_round (gamma:real->A) (U:A->bool) (W:A->bool) (phi:A->real^N) (s0:real) (k:real) =
    \tau. if tau <= (s0 - &3 * k / &4) pow 2 then gamma tau
          else if tau <= (s0 + &3 * k / &4) pow 2 then p2a_rsig gamma U W phi s0 k tau
          else gamma tau`;;

let P2A_ROUND_SEG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s0 k0 M k.
     p2a_cdata V tt x b gamma W a' b'' U phi s0 k0 M /\ &0 < k /\ k < k0 /\
     (!s. abs(s - s0) < k
          ==> p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k (lift s)
              IN IMAGE phi (U INTER W))
     ==> p2a_adm V tt x b (p2a_round gamma U W phi s0 k) /\
         p2a_L_length V tt (p2a_round gamma U W phi s0 k) b =
         p2a_L_length V tt gamma b -
         p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt (\v. phi(gamma(drop v pow 2)))
                (s0 - &3 * k / &4) (s0 + &3 * k / &4) +
         p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt
                (p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k)
                (s0 - &3 * k / &4) (s0 + &3 * k / &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  UNDISCH_TAC `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M` THEN
  REWRITE_TAC[p2a_cdata] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "WIN") (LABEL_TAC "YC1")))))))))) THEN
  SUBGOAL_THEN `&0 < s0 - &3 * k / &4 /\ s0 - &3 * k / &4 < s0 + &3 * k / &4 /\
                s0 - k < s0 - &3 * k / &4 /\ s0 + &3 * k / &4 < s0 + k`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s0 + &3 * k / &4) pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(s0 + k0) pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [USE_THEN "WIN" (MP_TAC o SPEC `s0:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the new piece *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                            (phi(gamma(s0 pow 2))) s0 k`;
                 `s0 - &3 * k / &4`; `s0 + &3 * k / &4`; `s0 - k`; `s0 + k`]
                P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs(s - s0) < k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p2a_rsig] THEN STRIP_TAC THEN
  (* the end values of the new piece *)
  SUBGOAL_THEN
   `!s. abs(s - s0) = &3 * k / &4 /\ &0 <= s
        ==> p2a_rsig gamma U W (phi:A->real^N) s0 k (s pow 2) = (gamma:real->A)(s pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_rsig] THEN
    ASM_SIMP_TAC[POW_2_SQRT] THEN
    SUBGOAL_THEN
     `p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
        (lift s) = phi(gamma(s pow 2))`
    SUBST1_TAC THENL
     [USE_THEN "BEQ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `p2a_rsig (gamma:real->A) U W (phi:A->real^N) s0 k`; `b:real`;
                 `(s0 - &3 * k / &4) pow 2`; `(s0 + &3 * k / &4) pow 2`] P2A_REPLACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM p2a_round] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the old piece *)
  SUBGOAL_THEN `!s. s0 - k < s /\ s < s0 + k ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s0 - &3 * k / &4 <= s /\ s <= s0 + &3 * k / &4
                    ==> (gamma:real->A)(s pow 2) IN U INTER W`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s0 + &3 * k / &4) pow 2 <= b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s O. s0 - &3 * k / &4 < s /\ s < s0 + &3 * k / &4 /\
          open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) (tt - s pow 2)) O /\
          (gamma:real->A)(s pow 2) IN O
          ==> ?e. &0 < e /\
                  !r. &0 <= r /\ r pow 2 <= b /\ abs(r - s) < e ==> gamma(r pow 2) IN O`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `O:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`s:real`; `O:A->bool`] (MATCH_MP P2A_ADM_SCONT (ASSUME
      `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`))) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s0 + &3 * k / &4) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(s0 - &3 * k / &4),lift(s0 + &3 * k / &4)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[lift(s0 - k),lift(s0 + k)]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s0 - &3 * k / &4 < s /\ s < s0 + &3 * k / &4 /\ ~(s IN {s0})
        ==> (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) differentiable (at (lift s)) /\
            (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
              continuous (at (lift s)) /\
            norm(vector_derivative (\v. phi(gamma(drop v pow 2))) (at (lift s))) <= M`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_SING] THEN STRIP_TAC THEN
    USE_THEN "YC1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                 `s0 - &3 * k / &4`; `s0 + &3 * k / &4`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `{s0:real}`; `s0 - k`; `s0 + k`; `M:real`]
                P2A_LINT_PIECE) THEN
  ASM_REWRITE_TAC[FINITE_SING] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_rsig")) (concl th))) THEN
  REFL_TAC);;

(* ========================================================================= *)
(* The rounded curve is longer by at most a multiple of k, it is piecewise   *)
(* C^1 without the corner s0^2, and it is uniformly close to the old curve   *)
(* in the slice distances.                                                   *)
(* ========================================================================= *)

let P2A_CL_ABS_BOUND = prove
 (`!(Gt:real->real^N->real^N^N) tt (sol:real^1->real^N) z' s1 s2 Kb K.
     FINITE K /\ s1 <= s2 /\
     (\s. p2a_llag Gt tt s (sol(lift s)) (z'(lift s))) real_integrable_on real_interval[s1,s2] /\
     (!s. s1 <= s /\ s <= s2 /\ ~(s IN K)
          ==> z'(lift s) = vector_derivative sol (at (lift s))) /\
     (!s. s1 <= s /\ s <= s2 ==> abs(p2a_llag Gt tt s (sol(lift s)) (z'(lift s))) <= Kb)
     ==> abs(p2a_cL Gt tt sol s1 s2) <= Kb * (s2 - s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_cL] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1,s2])
      (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((sol:real^1->real^N)(lift s))
                    (vector_derivative sol (at (lift s)))) =
    real_integral (real_interval[s1,s2])
      (\s. p2a_llag Gt tt s (sol(lift s)) ((z':real^1->real^N)(lift s)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `K:real->bool` THEN
    ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; IN_DIFF; IN_REAL_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_BOUND THEN
  EXISTS_TAC `\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((sol:real^1->real^N)(lift s))
                           ((z':real^1->real^N)(lift s))` THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL; IN_REAL_INTERVAL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s1:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REAL_ARITH_TAC);;

let P2A_ROUND_LENGTH = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s0 k0 M k Kb e.
     p2a_cdata V tt x b gamma W a' b'' U phi s0 k0 M /\ &0 < k /\ k < k0 /\
     (!s. abs(s - s0) < k
          ==> p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k (lift s)
              IN IMAGE phi (U INTER W)) /\
     (!s A. abs(s - s0) <= k /\ norm A <= (&1 + p2a_bc) * M
            ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                             (phi(gamma(s pow 2))) A) <= Kb /\
                abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt s
                             (p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2)))
                                        s0 k (lift s)) A) <= Kb) /\
     &3 * k * Kb < e
     ==> p2a_L_length V tt (p2a_round gamma U W phi s0 k) b <= p2a_L_length V tt gamma b + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_ROUND_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  UNDISCH_TAC `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M` THEN
  REWRITE_TAC[p2a_cdata] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "WIN") (LABEL_TAC "YC1")))))))))) THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (s0 - k) (s0 + k)
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2a_bc` ASSUME_TAC THENL [REWRITE_TAC[P2A_BC]; ALL_TAC] THEN
  SUBGOAL_THEN `M <= (&1 + p2a_bc) * M` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= c * M ==> M <= (&1 + c) * M`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  (* the new piece *)
  SUBGOAL_THEN
   `abs(p2a_cL (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) W b'' (U INTER W,phi)) tt
                (p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                           (phi(gamma(s0 pow 2))) s0 k)
                (s0 - &3 * k / &4) (s0 + &3 * k / &4))
    <= Kb * ((s0 + &3 * k / &4) - (s0 - &3 * k / &4))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_CL_ABS_BOUND THEN
    EXISTS_TAC `\v. vector_derivative
                      (p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                 (phi(gamma(s0 pow 2))) s0 k) (at v)` THEN
    EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2A_LLAG_PW_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - k`; `s0 + k`;
                            `{}:real->bool`; `(&1 + p2a_bc) * M`] THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN REWRITE_TAC[ETA_AX] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        USE_THEN "BC1" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
        USE_THEN "BC1" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        USE_THEN "BC1" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`s:real`; `vector_derivative
                   (p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                              (phi(gamma(s0 pow 2))) s0 k) (at (lift s))`] o check (fun th ->
       is_forall(concl th) && can (find_term ((=) `Kb:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "BC1" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the old piece *)
  SUBGOAL_THEN
   `abs(p2a_cL (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) W b'' (U INTER W,phi)) tt
                (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                (s0 - &3 * k / &4) (s0 + &3 * k / &4))
    <= Kb * ((s0 + &3 * k / &4) - (s0 - &3 * k / &4))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_CL_ABS_BOUND THEN
    EXISTS_TAC `\v. if v = lift s0 then vec 0
                    else vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                           (at v)` THEN
    EXISTS_TAC `{s0:real}` THEN REWRITE_TAC[FINITE_SING; IN_SING; LIFT_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - k`; `s0 + k`;
                     `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                     `tt:real`; `\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`;
                     `\v. if v = lift s0 then vec 0
                          else vector_derivative
                                 (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at v)`;
                     `{s0:real}`; `s0 - &3 * k / &4`; `s0 + &3 * k / &4`; `M:real`]
                    P2A_LLAG_PW_INTEGRABLE) THEN
      REWRITE_TAC[FINITE_SING; IN_SING; LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[lift(s0 - k),lift(s0 + k)]` THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
        USE_THEN "YC1" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[NORM_0] THEN USE_THEN "YC1" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`s:real`; `if lift s = lift s0 then vec 0
                 else vector_derivative (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                        (at (lift s))`] o check (fun th ->
       is_forall(concl th) && can (find_term ((=) `Kb:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; REAL_LE_MUL; REAL_LE_ADD; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "YC1" (MP_TAC o SPEC `s:real`) THEN RULE_ASSUM_TAC(REWRITE_RULE[LIFT_EQ]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      SIMP_TAC[LIFT_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Kb * ((s0 + &3 * k / &4) - (s0 - &3 * k / &4)) = &3 * k * Kb / &2`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_SQRT_BETWEEN = prove
 (`!a c tau. &0 <= a /\ &0 <= c /\ a pow 2 <= tau /\ tau <= c pow 2
             ==> a <= sqrt tau /\ sqrt tau <= c /\ &0 <= tau /\ sqrt tau pow 2 = tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a pow 2` THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(a pow 2)` THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL; SQRT_MONO_LE];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(c pow 2)` THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL; SQRT_MONO_LE]]);;

let P2A_SQRT_BETWEEN_LT = prove
 (`!a c tau. &0 <= a /\ &0 <= c /\ a pow 2 < tau /\ tau < c pow 2
             ==> a < sqrt tau /\ sqrt tau < c /\ &0 < tau /\ sqrt tau pow 2 = tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a pow 2` THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(a pow 2)` THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL; SQRT_MONO_LT];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(c pow 2)` THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL; SQRT_MONO_LT]]);;

(* The rounded curve has no corner at s0^2.                                  *)

let P2A_ROUND_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s0 k0 M k P.
     p2a_cdata V tt x b gamma W a' b'' U phi s0 k0 M /\ &0 < k /\ k < k0 /\
     (!s. abs(s - s0) < k
          ==> p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k (lift s)
              IN IMAGE phi (U INTER W)) /\
     p2a_pc1 V tt gamma (&0) b P
     ==> p2a_pc1 V tt (p2a_round gamma U W phi s0 k) (&0) b (P DELETE (s0 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  UNDISCH_TAC `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M` THEN
  REWRITE_TAC[p2a_cdata] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "WIN") (LABEL_TAC "YC1")))))))))) THEN
  SUBGOAL_THEN `&0 < s0 - &7 * k / &8 /\ s0 - &7 * k / &8 < s0 - &3 * k / &4 /\
                s0 - &3 * k / &4 < s0 + &3 * k / &4 /\ s0 + &3 * k / &4 < s0 + &7 * k / &8`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [USE_THEN "WIN" (MP_TAC o SPEC `s0:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the new piece agrees with gamma on the collars *)
  SUBGOAL_THEN
   `!s. &2 * k / &3 <= abs(s - s0) /\ abs(s - s0) < k /\ &0 <= s
        ==> p2a_rsig gamma U W (phi:A->real^N) s0 k (s pow 2) = (gamma:real->A)(s pow 2)`
  (LABEL_TAC "COLLAR") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_rsig] THEN
    ASM_SIMP_TAC[POW_2_SQRT] THEN
    SUBGOAL_THEN
     `p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k
        (lift s) = phi(gamma(s pow 2))`
    SUBST1_TAC THENL [USE_THEN "BEQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the new piece is two-sided C^1 in every chart on the closed window *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\t:real^1. p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                       (phi(gamma(s0 pow 2))) s0 k (lift(sqrt(drop t)))`;
                 `\t:real^1. inv(&2 * sqrt(drop t)) %
                             vector_derivative
                               (p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                          (phi(gamma(s0 pow 2))) s0 k)
                               (at (lift(sqrt(drop t))))`;
                 `(s0 - &7 * k / &8) pow 2`; `(s0 + &7 * k / &8) pow 2`]
                P2A_CHART_CURVE_PC1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `!tau. (s0 - &7 * k / &8) pow 2 <= tau /\ tau <= (s0 + &7 * k / &8) pow 2
                        ==> abs(sqrt tau - s0) < k /\ &0 < tau /\ sqrt tau pow 2 = tau`
    ASSUME_TAC THENL
     [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`s0 - &7 * k / &8`; `s0 + &7 * k / &8`; `tau:real`] P2A_SQRT_BETWEEN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(s0 - &7 * k / &8) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "WIN" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_LT_IMP_LE]];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "BC1" (MP_TAC o SPEC `sqrt tau`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                (phi(gamma(s0 pow 2))) s0 k`; `tau:real`]
                    P2A_SQRT_CURVE_DERIV) THEN
      ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  MATCH_MP_TAC P2A_PC1_PATCH THEN
  MAP_EVERY EXISTS_TAC
   [`gamma:real->A`; `p2a_rsig (gamma:real->A) U W (phi:A->real^N) s0 k`;
    `(s0 - &3 * k / &4) pow 2`; `(s0 + &3 * k / &4) pow 2`;
    `(s0 - &7 * k / &8) pow 2`; `(s0 + &7 * k / &8) pow 2`; `P:real->bool`] THEN
  ASM_REWRITE_TAC[FINITE_DELETE] THEN
  SUBGOAL_THEN `FINITE(P:real->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_pc1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s0 - &7 * k / &8) pow 2 < (s0 - &3 * k / &4) pow 2 /\
                (s0 - &3 * k / &4) pow 2 < (s0 + &3 * k / &4) pow 2 /\
                (s0 + &3 * k / &4) pow 2 < (s0 + &7 * k / &8) pow 2 /\
                (s0 - &7 * k / &8) pow 2 < s0 pow 2 /\ s0 pow 2 < (s0 + &7 * k / &8) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_round] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN REWRITE_TAC[p2a_round] THEN
    MP_TAC(ISPECL [`s0 - &7 * k / &8`; `s0 + &7 * k / &8`; `tau:real`] P2A_SQRT_BETWEEN_LT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      CONV_TAC SYM_CONV THEN USE_THEN "COLLAR" MATCH_MP_TAC THEN
      SUBGOAL_THEN `sqrt tau <= s0 - &3 * k / &4` MP_TAC THENL
       [MP_TAC(ISPECL [`&0`; `s0 - &3 * k / &4`; `tau:real`] P2A_SQRT_BETWEEN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
                        REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
                        SIMP_TAC[]];
        ASM_REAL_ARITH_TAC];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt tau pow 2 = tau`)) THEN
      CONV_TAC SYM_CONV THEN USE_THEN "COLLAR" MATCH_MP_TAC THEN
      SUBGOAL_THEN `s0 + &3 * k / &4 <= sqrt tau` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((s0 + &3 * k / &4) pow 2)` THEN
        CONJ_TAC THENL
         [SIMP_TAC[POW_2_SQRT; REAL_LE_REFL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE;
            REAL_ARITH `&0 < s0 - &7 * k / &8 /\ &0 < k ==> &0 <= s0 + &3 * k / &4`;
            REAL_LE_REFL];
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`tau0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
    EXISTS_TAC `min (tau0 - (s0 - &7 * k / &8) pow 2) ((s0 + &7 * k / &8) pow 2 - tau0)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[p2a_rsig] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((s0 - &7 * k / &8) pow 2 < tau /\ tau < (s0 + &7 * k / &8) pow 2)` THEN
    ASM_REWRITE_TAC[]]);;

(* The rounded curve is uniformly close to the old one.                      *)

let P2A_ROUND_DIST = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s0 k0 M k r L e.
     p2a_cdata V tt x b gamma W a' b'' U phi s0 k0 M /\ &0 < k /\ k < k0 /\
     k <= r /\ M * k < r /\ L * M * k < e /\ &0 <= L /\ &0 < e /\
     (!s z1 z2. abs(s - s0) <= r /\ dist(z1,phi(gamma(s0 pow 2))) < r /\
                dist(z2,phi(gamma(s0 pow 2))) < r
                ==> z1 IN IMAGE phi (U INTER W) /\ z2 IN IMAGE phi (U INTER W) /\
                    mfd_dist (p2a_vtop V (tt - s pow 2),p2a_vatlas V (tt - s pow 2))
                             (p2a_vmetric V (tt - s pow 2))
                             (chart_inv (U INTER W,phi) z1) (chart_inv (U INTER W,phi) z2)
                    <= L * dist(z1,z2))
     ==> !tau. &0 <= tau /\ tau <= b
               ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                            (p2a_vmetric V (tt - tau))
                            (p2a_round gamma U W phi s0 k tau) (gamma tau) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  UNDISCH_TAC `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M` THEN
  REWRITE_TAC[p2a_cdata] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "WIN") (LABEL_TAC "YC1")))))))))) THEN
  SUBGOAL_THEN `a' < b''` ASSUME_TAC THENL
   [USE_THEN "WIN" (MP_TAC o SPEC `s0:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_dist (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) (tt - tau),p2a_vatlas V (tt - tau))
             (p2a_vmetric V (tt - tau)) ((gamma:real->A) tau) (gamma tau) = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_REFL THEN
    SUBGOAL_THEN `(gamma:real->A) tau IN
                  topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                       (real->A->real^N^N)) (tt - tau))` ASSUME_TAC THENL
     [UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                              (real->A->real^N^N)) tt x b gamma` THEN
      REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N))` THEN
    REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o SPEC `tt - tau`) THEN
    SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) = {})`
    (fun th -> SIMP_TAC[th]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_round] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the replaced part *)
  SUBGOAL_THEN `&0 < s0 - &3 * k / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s0 - &3 * k / &4`; `s0 + &3 * k / &4`; `tau:real`] P2A_SQRT_BETWEEN) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `s = sqrt tau` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `s pow 2 = tau`)) THEN
  SUBGOAL_THEN `abs(s - s0) <= &3 * k / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s pow 2) =
                chart_inv (U INTER W,phi:A->real^N) (phi(gamma(s pow 2)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_rsig] THEN
  SUBGOAL_THEN
   `norm(p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
                   s0 k (lift s) - phi(gamma(s0 pow 2))) <= M * abs(s - s0) /\
    norm(p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
                   s0 k (lift s) - phi(gamma(s pow 2))) <= M * abs(s - s0) /\
    norm((phi:A->real^N)(gamma(s pow 2)) - phi(gamma(s0 pow 2))) <= M * abs(s - s0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "BNEAR" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "BNEAR" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `M * abs(s - s0) <= M * k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s:real`;
    `p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
               s0 k (lift s)`;
    `(phi:A->real^N)((gamma:real->A)(s pow 2))`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `L:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `L * dist(p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                 (phi(gamma(s0 pow 2))) s0 k (lift s),
                       phi(gamma(s pow 2)))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * M * k` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[dist] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Rounding one interior corner at a time where the slice atlas is locally   *)
(* constant (P2A_ROUND1).                                                    *)
(* ========================================================================= *)

let P2A_ROUND1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) P tau1 e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\
     p2a_pc1 V tt gamma (&0) b P /\ &0 < tau1 /\ tau1 < b /\
     p2a_atlas_const V (tt - tau1) /\ &0 < e
     ==> ?gamma1. p2a_adm V tt x b gamma1 /\ p2a_pc1 V tt gamma1 (&0) b (P DELETE tau1) /\
                  gamma1 b = gamma b /\
                  p2a_L_length V tt gamma1 b <= p2a_L_length V tt gamma b + e /\
                  (!tau. ~(abs(tau - tau1) < e) ==> gamma1 tau = gamma tau) /\
                  (!tau. &0 <= tau /\ tau <= b
                         ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                      (p2a_vmetric V (tt - tau)) (gamma1 tau) (gamma tau) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 pow 2 = tau1` (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `sqrt tau1` THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  (* the region chart at the corner *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `s0:real`] P2A_MIN_REGION_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  (* corner bounds *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `P:real->bool`; `s0:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`] P2A_CORNER_S_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s0 + k0 / &2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `M:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[NORM_POS_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_cdata (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)) tt x b gamma W a' b'' U phi s0 k0 M`
  ASSUME_TAC THENL [REWRITE_TAC[p2a_cdata] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the slice atlas is constant near the corner time *)
  UNDISCH_TAC `p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) (tt - s0 pow 2)` THEN
  REWRITE_TAC[p2a_atlas_const] THEN
  DISCH_THEN(X_CHOOSE_THEN `da:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`s0:real`; `da:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?k1. &0 < k1 /\ k1 < k0 /\ k1 <= ha` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (k0 / &2) ha` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* uniform slice distances near the corner *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt:real`; `s0 - k1`; `s0 + k1`; `s0:real`;
                 `(gamma:real->A)(s0 pow 2)`] P2A_SLICE_DIST_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `da:real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vatlas")) (concl th))) THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x - y) < d ==> abs((t - x) - (t - y)) < d`) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `ha:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DIST"))))) THEN
  SUBGOAL_THEN `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),r / &2) SUBSET
                IMAGE phi (U INTER W)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "DIST" (MP_TAC o SPECL [`s0:real`; `z:real^N`; `z:real^N`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* a bound for the s-Lagrangian near the corner *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `s0 - k1`; `s0 + k1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A)(s0 pow 2)),r / &2)`;
                 `s0 - k1 / &2`; `s0 + k1 / &2`; `(&1 + p2a_bc) * M`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th) &&
      can (find_term ((=) `k0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB"))] THEN
  (* the choice of the scale k *)
  MP_TAC(SPECL [`r / &2`; `M:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KC"))) THEN
  MP_TAC(SPECL [`e:real`; `L * M`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KD"))) THEN
  MP_TAC(SPECL [`e:real`; `&3 * abs Kb`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ke:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KE"))) THEN
  MP_TAC(SPECL [`s0:real`; `e:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `he:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HE"))) THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k <= k1 / &2 /\ k <= r / &2 /\ k <= kc /\ k <= kd /\ k <= ke /\ k <= he / &2`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min (k1 / &2) (r / &2)) (min (min kc kd) (min ke (he / &2)))` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * M < r / &2 /\ k * (L * M) < e /\ k * (&3 * abs Kb) < e`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "KC" MATCH_MP_TAC; USE_THEN "KD" MATCH_MP_TAC; USE_THEN "KE" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k < k0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_YCONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_CDATA_BLEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "BC1") (CONJUNCTS_THEN2 (LABEL_TAC "BEQ")
    (LABEL_TAC "BNEAR"))) THEN
  (* the blend and the curve stay in the closed ball of radius r/2 *)
  SUBGOAL_THEN
   `!s. abs(s - s0) <= k
        ==> (phi:A->real^N)((gamma:real->A)(s pow 2)) IN cball(phi(gamma(s0 pow 2)),r / &2) /\
            p2a_blend (\v. phi(gamma(drop v pow 2))) (phi(gamma(s0 pow 2))) s0 k (lift s) IN
            cball(phi(gamma(s0 pow 2)),r / &2)`
  (LABEL_TAC "BALL") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    SUBGOAL_THEN `M * abs(s - s0) <= k * M` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * abs(s - s0)` THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "BNEAR" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < k
        ==> p2a_blend (\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (phi(gamma(s0 pow 2)))
                      s0 k (lift s) IN IMAGE phi (U INTER W)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      not(is_forall(concl th)))) THEN
    USE_THEN "BALL" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `p2a_round (gamma:real->A) U W (phi:A->real^N) s0 k` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s0:real`; `k0:real`; `M:real`; `k:real`] P2A_ROUND_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2A_ROUND_PC1 THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2a_round] THEN
    SUBGOAL_THEN `~(b <= (s0 - &3 * k / &4) pow 2) /\ ~(b <= (s0 + &3 * k / &4) pow 2)`
    (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(s0 + &3 * k / &4) pow 2 < b /\ (s0 - &3 * k / &4) pow 2 <= (s0 + &3 * k / &4) pow 2`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(s0 + k0) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2A_ROUND_LENGTH THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`; `Kb:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "BALL" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THEN USE_THEN "KB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `k * Kb <= k * abs Kb` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_round] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(abs(tau - s0 pow 2) < e)` THEN REWRITE_TAC[] THEN
    USE_THEN "HE" (MP_TAC o SPEC `s0 - &3 * k / &4`) THEN
    USE_THEN "HE" (MP_TAC o SPEC `s0 + &3 * k / &4`) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2A_ROUND_DIST THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `a':real`; `b'':real`; `k0:real`; `M:real`; `r:real`;
                          `L:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The slice distance of a point of the curve to itself is 0.               *)

let P2A_ADM_DIST_REFL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) tau.
     p2a_svs V /\ p2a_adm V tt x b gamma /\ &0 <= tau /\ tau <= b
     ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau)) (p2a_vmetric V (tt - tau))
                  (gamma tau) (gamma tau) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_REFL THEN
  SUBGOAL_THEN `(gamma:real->A) tau IN
                topspace(p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) (tt - tau))` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                            (real->A->real^N^N)) tt x b gamma` THEN
    REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N))` THEN
  REWRITE_TAC[p2a_svs] THEN DISCH_THEN(MP_TAC o SPEC `tt - tau`) THEN
  SUBGOAL_THEN `~(topspace(p2a_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) (tt - tau)) = {})`
  (fun th -> SIMP_TAC[th]) THEN ASM SET_TAC[]);;

(* Rounding all corners, one at a time, with disjoint supports.             *)

let P2A_SMOOTH_INDUCT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt
     ==> !P. FINITE P
             ==> !(gamma:real->A) e.
                   p2a_adm V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b P /\
                   (!s. s IN P ==> &0 < s /\ s < b /\ p2a_atlas_const V (tt - s)) /\ &0 < e
                   ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                                p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                                (!tau. (!s. s IN P ==> ~(abs(tau - s) < e))
                                       ==> gamma' tau = gamma tau) /\
                                (!tau. &0 <= tau /\ tau <= b
                                       ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                                    (p2a_vmetric V (tt - tau))
                                                    (gamma' tau) (gamma tau) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`gamma:real->A`; `e:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[p2a_adm1; REAL_LE_ADDR] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `tau:real`] P2A_ADM_DIST_REFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`tau1:real`; `P:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`gamma:real->A`; `e:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < tau1 /\ tau1 < b /\
                p2a_atlas_const (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) (tt - tau1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau1:real`; `P:real->bool`] P2A_REAL_FINITE_AVOID) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e1 = min (e / &2) (d / &3)` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= e / &2 /\ &3 * e1 <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `(tau1:real) INSERT P`; `tau1:real`; `e1:real`] P2A_ROUND1) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((tau1:real) INSERT P) DELETE tau1 = P` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma1:real->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "D1"))))))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`gamma1:real->A`; `e1:real`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S2") (LABEL_TAC "D2")))))) THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `(gamma1:real->A) tau` THEN CONJ_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "S1" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tau1:real`) THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs(tau - tau1) < e1` THENL
   [SUBGOAL_THEN `(gamma':real->A) tau = gamma1 tau` SUBST1_TAC THENL
     [USE_THEN "S2" MATCH_MP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e1:real` THEN
    CONJ_TAC THENL [USE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(gamma1:real->A) tau = gamma tau` (SUBST1_TAC o SYM) THENL
     [USE_THEN "S1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e1:real` THEN
    CONJ_TAC THENL [USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* L12, generic N.                                                           *)

let P2A_SMOOTHING_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\ &0 < e
     ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                  p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                  !tau. &0 <= tau /\ tau <= b
                        ==> mfd_dist (p2a_vtop V (tt - tau),p2a_vatlas V (tt - tau))
                                     (p2a_vmetric V (tt - tau)) (gamma' tau) (gamma tau) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?P. p2a_pc1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)) tt gamma (&0) b P`
  (X_CHOOSE_TAC `P:real->bool`) THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `P:real->bool`]
                P2A_PC1_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_SMOOTH_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `{s | s IN P /\ &0 < s /\ s < b /\
                                p2a_atlas_const (V:(real->A topology)#
                                  (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
                                  (tt - s)}`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[p2a_pc1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `e:real`]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let P2A_SMOOTHING_FIX = prove
 (`!u:A->bool. P2A_SMOOTHING_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_SMOOTHING_FIX_STATEMENT; GSYM P2A_VIEW_PROJ_3] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_SMOOTHING_GEN THEN ASM_REWRITE_TAC[]);;

