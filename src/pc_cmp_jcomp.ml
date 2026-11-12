(* ========================================================================= *)
(* Unit pc_cmp_jcomp (comparison-geometry layer CMP): comparison theorems   *)
(* for the Jacobi matrix along a unit-speed geodesic, in the coordinates of *)
(* a parallel orthonormal frame E1 = gamma', E2, ..., En.  The matrix data  *)
(* cmp_jsys A B R L: A' = B, B' = -R A on [0,L), A(0) = 0, B(0) = I, R      *)
(* symmetric with R e1 = 0, A e1 = t e1, B e1 = e1, A^T B symmetric.  With  *)
(* S = B A^-1 (the shape operator of the distance spheres):                 *)
(* - sec <= K: |A c| >= sn_K |c| on normal vectors, A invertible before     *)
(*   pi / sqrt K, S >= ct_K on normal vectors, det A >= t sn_K^(n-1);        *)
(* - sec >= k: S <= ct_k on normal vectors (while A is invertible);         *)
(* - Ric >= -(n-1) K: tr S - 1/t <= (n-1) ct_(-K), det A <= t sn_(-K)^(n-1). *)
(* ========================================================================= *)

needs "src/pc_cmp_frame.ml";;
needs "src/pc_cmp_gfacts.ml";;
needs "src/pc_lrg_stab.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The Jacobi matrix data and its block structure.                           *)
(* ========================================================================= *)

let cmp_jsys = new_definition
 `cmp_jsys (A:real->real^N^N) (B:real->real^N^N) (R:real->real^N^N) (L:real) <=>
    &0 < L /\ A(&0) = mat 0 /\ B(&0) = mat 1 /\
    (!t. &0 <= t /\ t < L
         ==> ((\s. vectorize(A(drop s))) has_vector_derivative vectorize(B t))
             (at (lift t)) /\
             ((\s. vectorize(B(drop s))) has_vector_derivative
              vectorize(--(R t ** A t))) (at (lift t)) /\
             transp(R t) = R t /\ R t ** basis 1 = vec 0 /\
             A t ** basis 1 = t % basis 1 /\ B t ** basis 1 = basis 1 /\
             transp(A t) ** B t = transp(B t) ** A t)`;;

let CMPJ_JSYS_INIT = prove
 (`!(A:real->real^N^N) B R L.
        cmp_jsys A B R L ==> &0 < L /\ A(&0) = mat 0 /\ B(&0) = mat 1`,
  SIMP_TAC[cmp_jsys]);;

let CMPJ_JSYS_AT = prove
 (`!(A:real->real^N^N) B R L t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L
        ==> ((\s. vectorize(A(drop s))) has_vector_derivative vectorize(B t))
            (at (lift t)) /\
            ((\s. vectorize(B(drop s))) has_vector_derivative
             vectorize(--(R t ** A t))) (at (lift t)) /\
            transp(R t) = R t /\ R t ** basis 1 = vec 0 /\
            A t ** basis 1 = t % basis 1 /\ B t ** basis 1 = basis 1 /\
            transp(A t) ** B t = transp(B t) ** A t`,
  SIMP_TAC[cmp_jsys]);;

(* Derivatives of the columns (and of any combination A c, B c). *)

let CMPJ_JSYS_VD = prove
 (`!(A:real->real^N^N) B R L (c:real^N) t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L
        ==> ((\s. A(drop s) ** c) has_vector_derivative B t ** c) (at (lift t)) /\
            ((\s. B(drop s) ** c) has_vector_derivative --(R t ** (A t ** c)))
            (at (lift t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_AT) THEN
  SUBGOAL_THEN `--((R:real->real^N^N) t ** (A:real->real^N^N) t ** (c:real^N)) =
                --(R t ** A t) ** c` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG; MATRIX_VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC CMPF_HAS_VD_MATVEC THEN ASM_REWRITE_TAC[]);;

(* Real derivatives from vector derivatives. *)

let CMPJ_COMPONENT_DERIV = prove
 (`!(y:real->real^N) y' t i.
        1 <= i /\ i <= dimindex(:N) /\
        ((\s. y(drop s)) has_vector_derivative y') (at (lift t))
        ==> ((\t. y t$i) has_real_derivative y'$i) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT]) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]);;

let CMPJ_LIFT_DERIV = prove
 (`!(f:real->real) f' t.
        ((\s. lift(f(drop s))) has_vector_derivative lift f') (at (lift t))
        ==> (f has_real_derivative f') (atreal t)`,
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN SIMP_TAC[]);;

(* The first row of R vanishes too. *)

let CMPJ_R_FIRST = prove
 (`!(R:real^N^N) v. transp R = R /\ R ** basis 1 = vec 0 ==> (R ** v)$1 = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((R:real^N^N) ** v)$1 = basis 1 dot (R ** v)` SUBST1_TAC THENL
   [SIMP_TAC[DOT_BASIS; DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[DOT_LZERO]);;

let CMPJ_HALF_LINE = prove
 (`!L. is_realinterval {t | &0 <= t /\ t < L}`,
  REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* Normal vectors stay normal: if c$1 = 0 then (A t c)$1 = (B t c)$1 = 0.  *)

let CMPJ_NORMAL = prove
 (`!(A:real->real^N^N) B R L (c:real^N).
        cmp_jsys A B R L /\ c$1 = &0
        ==> !t. &0 <= t /\ t < L ==> (A t ** c)$1 = &0 /\ (B t ** c)$1 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < L ==> ((B:real->real^N^N) t ** c)$1 = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. ((B:real->real^N^N) t ** c)$1`; `{t | &0 <= t /\ t < L}`;
                   `&0`; `&0`] HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
    REWRITE_TAC[IN_ELIM_THM; CMPJ_HALF_LINE] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; MATRIX_VECTOR_MUL_LID] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                     `L:real`; `x:real`] CMPJ_JSYS_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 = (--((R:real->real^N^N) x ** ((A:real->real^N^N) x ** c)))$1`
      SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_NEG_COMPONENT] THEN
        MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 = --x`) THEN
        MATCH_MP_TAC CMPJ_R_FIRST THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CMPJ_COMPONENT_DERIV THEN
      REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
      MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                     `L:real`; `c:real^N`; `x:real`] CMPJ_JSYS_VD) THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`\t. ((A:real->real^N^N) t ** c)$1`; `{t | &0 <= t /\ t < L}`;
                 `&0`; `&0`] HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[IN_ELIM_THM; CMPJ_HALF_LINE] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; MATRIX_VECTOR_MUL_LZERO; VEC_COMPONENT] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 = ((B:real->real^N^N) x ** c)$1` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMPJ_COMPONENT_DERIV THEN
    REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `c:real^N`; `x:real`] CMPJ_JSYS_VD) THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Limits at 0+ (A/t -> I, B -> I, sn/t -> 1, det A/t^n -> 1,                *)
(* t S -> I) and monotone ratios.                                           *)
(* ========================================================================= *)

let CMPJ_NONTRIVIAL0 = prove
 (`~trivial_limit(atreal (&0) within {t | &0 < t})`,
  REWRITE_TAC[trivial_limit; EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  X_GEN_TAC `d:real` THEN ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `d / &2` THEN ASM_REAL_ARITH_TAC);;

(* A function bounded by M t near 0+ tends to 0. *)

let CMPJ_LIM0_BOUND = prove
 (`!(h:real->real) M d.
        &0 < d /\ (!t. &0 < t /\ t < d ==> abs(h t) <= M * t)
        ==> (h ---> &0) (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min d (e / (abs M + &1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((h:real->real) t) <= M * t` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (abs M + &1) < e` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs t = t` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `t < e / (abs M + &1)` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs M + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `M * t <= (abs M + &1) * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* A(t)/t -> I and B(t) -> I as t -> 0+. *)

let CMPJ_QUOT_LIM = prove
 (`!(A:real->real^N^N) B R L x.
        cmp_jsys A B R L
        ==> ((\t. inv t % (A t ** x)) --> x) (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  MATCH_MP_TAC LIM_ATREAL_WITHINREAL THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `x:real^N`; `&0`] CMPJ_JSYS_VD) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_AT_1D; LIM_ATREAL_AT; o_DEF] THEN
  ASM_REWRITE_TAC[LIFT_NUM; DROP_VEC; VECTOR_SUB_RZERO; MATRIX_VECTOR_MUL_LZERO;
                  MATRIX_VECTOR_MUL_LID]);;

let CMPJ_B_LIM = prove
 (`!(A:real->real^N^N) B R L x.
        cmp_jsys A B R L
        ==> ((\t. B t ** x) --> x) (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  MATCH_MP_TAC LIM_ATREAL_WITHINREAL THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `x:real^N`; `&0`] CMPJ_JSYS_VD) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT) THEN
  REWRITE_TAC[CONTINUOUS_AT; LIM_ATREAL_AT; o_DEF; LIFT_DROP] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

let CMPJ_SN_QUOT_LIM = prove
 (`!k. ((\t. cmp_sn k t / t) ---> &1) (atreal (&0) within {t | &0 < t})`,
  GEN_TAC THEN MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
  MP_TAC(SPECL [`k:real`; `&0`] CMP_SN_HAS_DERIV) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; CMP_SN_ZERO; CMP_CS_ZERO; REAL_SUB_RZERO]);;

(* Monotone ratios with a limit at 0+. *)

let CMPJ_RATIO_LOWER = prove
 (`!p p' q q' L l.
        (!t. &0 < t /\ t < L
             ==> (p has_real_derivative p' t) (atreal t) /\
                 (q has_real_derivative q' t) (atreal t) /\
                 &0 < q t /\ p t * q' t <= p' t * q t) /\
        ((\t. p t / q t) ---> l) (atreal (&0) within {t | &0 < t})
        ==> !t. &0 < t /\ t < L ==> l * q t <= p t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (q:real->real) t` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `l <= (p:real->real) t / q t` MP_TAC THENL
   [MATCH_MP_TAC(ISPEC `atreal (&0) within {t | &0 < t}` REALLIM_UBOUND) THEN
    EXISTS_TAC `\t. (p:real->real) t / q t` THEN
    ASM_REWRITE_TAC[CMPJ_NONTRIVIAL0; EVENTUALLY_WITHINREAL; IN_ELIM_THM;
                    REAL_SUB_RZERO] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (q:real->real) a` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. --((p:real->real) x)`; `\x. --((p':real->real) x)`;
                   `q:real->real`; `q':real->real`; `L:real`; `a:real`; `t:real`]
      CMPO_RATIO_DECREASING) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
      SUBGOAL_THEN
       `(p:real->real) t / q t - p a / q a = (p t * q a - p a * q t) / (q t * q a)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < (q:real->real) t` THEN UNDISCH_TAC `&0 < (q:real->real) a` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ]]);;

let CMPJ_RATIO_UPPER = prove
 (`!p p' q q' L l.
        (!t. &0 < t /\ t < L
             ==> (p has_real_derivative p' t) (atreal t) /\
                 (q has_real_derivative q' t) (atreal t) /\
                 &0 < q t /\ p' t * q t <= p t * q' t) /\
        ((\t. p t / q t) ---> l) (atreal (&0) within {t | &0 < t})
        ==> !t. &0 < t /\ t < L ==> p t <= l * q t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --((p:real->real) x)`; `\x. --((p':real->real) x)`;
                 `q:real->real`; `q':real->real`; `L:real`; `--l`] CMPJ_RATIO_LOWER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
      MATCH_MP_TAC REALLIM_NEG THEN ASM_REWRITE_TAC[GSYM real_div]];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The same limits in matrix form. *)

let CMPJ_MAT_QUOT_LIM = prove
 (`!(A:real->real^N^N) B R L.
        cmp_jsys A B R L
        ==> !x. ((\t. (inv t %% A t) ** x) --> mat 1 ** x)
                (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  MATCH_MP_TAC CMPJ_QUOT_LIM THEN
  MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
  ASM_REWRITE_TAC[]);;

(* det A(t) / t^n -> 1, so det A > 0 near 0+. *)

let CMPJ_DET_QUOT_LIM = prove
 (`!(A:real->real^N^N) B R L.
        cmp_jsys A B R L
        ==> ((\t. det(A t) / t pow dimindex(:N)) ---> &1)
            (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. det((A:real->real^N^N) t) / t pow dimindex(:N)) =
                (\t. det(inv t %% A t))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DET_CMUL; REAL_POW_INV; real_div] THEN
    GEN_TAC THEN MATCH_ACCEPT_TAC REAL_MUL_SYM;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMPJ_MAT_QUOT_LIM) THEN
  REWRITE_TAC[LIM_MATRIX_COMPONENTWISE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_LIFT_DET) THEN
  REWRITE_TAC[DET_I; TENDSTO_REAL; o_DEF]);;

let CMPJ_DET_POS_NEAR0 = prove
 (`!(A:real->real^N^N) B R L.
        cmp_jsys A B R L
        ==> ?d. &0 < d /\ d <= L /\ !t. &0 < t /\ t < d ==> &0 < det(A t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMPJ_DET_QUOT_LIM) THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d L` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < t pow dimindex(:N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det((A:real->real^N^N) t) / t pow dimindex(:N)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]]);;

(* t S(t) -> I where S = B A^-1: in bilinear form and for the trace. *)

let CMPJ_TS_LIM = prove
 (`!(A:real->real^N^N) B R L e1 e2.
        cmp_jsys A B R L
        ==> ((\t. t * (e1 dot ((B t ** matrix_inv(A t)) ** e2))) ---> e1 dot e2)
            (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. t * ((e1:real^N) dot (((B:real->real^N^N) t **
                                matrix_inv((A:real->real^N^N) t)) ** e2))) =
    (\t. (transp(B t) ** e1) dot (matrix_inv(inv t %% A t) ** e2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_INV_CMUL; REAL_INV_INV; MATRIX_VECTOR_LMUL;
                DOT_RMUL; DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC;
                MATRIX_MUL_RMUL];
    ALL_TAC] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  SUBGOAL_THEN
   `lift((e1:real^N) dot e2) =
    lift((transp(mat 1:real^N^N) ** e1) dot (matrix_inv(mat 1:real^N^N) ** e2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[TRANSP_MAT; MATRIX_INV_I; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[]
   (ISPECL [`atreal (&0) within {t | &0 < t}`; `\x y:real^N. lift(x dot y)`]
     LIM_BILINEAR)) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN CONJ_TAC THENL
   [SPEC_TAC(`e1:real^N`,`e1:real^N`) THEN REWRITE_TAC[LIM_MATRIX_TRANSP] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN X_GEN_TAC `x:real^N` THEN
    MATCH_MP_TAC CMPJ_B_LIM THEN
    MAP_EVERY EXISTS_TAC [`A:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
    ASM_REWRITE_TAC[];
    SPEC_TAC(`e2:real^N`,`e2:real^N`) THEN MATCH_MP_TAC LIM_MATRIX_INV THEN
    REWRITE_TAC[DET_I; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    MATCH_MP_TAC CMPJ_MAT_QUOT_LIM THEN
    MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
    ASM_REWRITE_TAC[]]);;

let CMPJ_TS_TRACE_LIM = prove
 (`!(A:real->real^N^N) B R L.
        cmp_jsys A B R L
        ==> ((\t. t * trace(B t ** matrix_inv(A t))) ---> &(dimindex(:N)))
            (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. t * trace((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t))) =
    (\t. sum(1..dimindex(:N))
            (\i. t * (basis i dot ((B t ** matrix_inv(A t)) ** basis i))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; trace; GSYM SUM_LMUL] THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; column; LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(dimindex(:N)) = sum(1..dimindex(:N)) (\i. basis i dot (basis i:real^N))`
  SUBST1_TAC THENL
   [SIMP_TAC[DOT_BASIS_BASIS; SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ADD_SUB; REAL_MUL_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPJ_TS_LIM THEN
  MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `L:real`] THEN ASM_REWRITE_TAC[]);;

(* A(t) c -> 0, cs -> 1, and limits of dot products. *)

let CMPJ_A_LIM = prove
 (`!(A:real->real^N^N) B R L x.
        cmp_jsys A B R L
        ==> ((\t. A t ** x) --> vec 0) (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  MATCH_MP_TAC LIM_ATREAL_WITHINREAL THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `x:real^N`; `&0`] CMPJ_JSYS_VD) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFFERENTIABLE_IMP_CONTINUOUS_AT) THEN
  REWRITE_TAC[CONTINUOUS_AT; LIM_ATREAL_AT; o_DEF; LIFT_DROP] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO]);;

let CMPJ_CS_LIM = prove
 (`!k. (cmp_cs k ---> &1) (atreal (&0) within {t | &0 < t})`,
  GEN_TAC THEN MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
  MP_TAC(SPECL [`k:real`; `&0`] CMP_CS_HAS_DERIV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; CMP_CS_ZERO]);;

let CMPJ_DOT_LIM = prove
 (`!(net:A net) (f:A->real^N) g l m.
        (f --> l) net /\ (g --> m) net ==> ((\x. f x dot g x) ---> l dot m) net`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
  MATCH_MP_TAC(REWRITE_RULE[]
   (ISPECL [`net:A net`; `\x y:real^N. lift(x dot y)`] LIM_BILINEAR)) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT]);;

(* ========================================================================= *)
(* sec <= K.  For normal c, m(t) = Ac.Bc - ct_K |Ac|^2 is                    *)
(* non-decreasing from m(0+) = 0, so |A c| >= sn_K |c|.                      *)
(* ========================================================================= *)

let CMPJ_M_ALGEBRA = prove
 (`!(y:real^N) z w ct K.
        (z - ct % y) dot (z - ct % y) + (K * (y dot y) - y dot w) =
        (y dot --w + z dot z) -
        (ct * (y dot z + z dot y) + (--K - ct pow 2) * (y dot y))`,
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL; DOT_RNEG] THEN
  CONV_TAC REAL_RING);;

let CMPJ_M_DERIV = prove
 (`!(A:real->real^N^N) B R L (c:real^N) K t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L /\ ~(cmp_sn K t = &0)
        ==> ((\t. (A t ** c) dot (B t ** c) -
                  cmp_cs K t / cmp_sn K t * ((A t ** c) dot (A t ** c)))
             has_real_derivative
             ((B t ** c - (cmp_cs K t / cmp_sn K t) % (A t ** c)) dot
              (B t ** c - (cmp_cs K t / cmp_sn K t) % (A t ** c)) +
              (K * ((A t ** c) dot (A t ** c)) -
               (A t ** c) dot (R t ** (A t ** c))))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `c:real^N`; `t:real`] CMPJ_JSYS_VD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\t. ((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** c))
     has_real_derivative
     ((A t ** c) dot --((R:real->real^N^N) t ** (A t ** c)) +
      (B t ** c) dot (B t ** c))) (atreal t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPJ_LIFT_DERIV THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\t. (A:real->real^N^N) t ** (c:real^N)`;
                   `\t. (B:real->real^N^N) t ** (c:real^N)`;
                   `(B:real->real^N^N) t ** (c:real^N)`;
                   `--((R:real->real^N^N) t ** ((A:real->real^N^N) t ** (c:real^N)))`;
                   `t:real`] CMPF_DOT_DERIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. ((A:real->real^N^N) t ** c) dot (A t ** c)) has_real_derivative
     ((A t ** c) dot ((B:real->real^N^N) t ** c) + (B t ** c) dot (A t ** c)))
    (atreal t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPJ_LIFT_DERIV THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\t. (A:real->real^N^N) t ** (c:real^N)`;
                   `\t. (A:real->real^N^N) t ** (c:real^N)`;
                   `(B:real->real^N^N) t ** (c:real^N)`; `(B:real->real^N^N) t ** (c:real^N)`;
                   `t:real`] CMPF_DOT_DERIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `t:real`] CMP_CT_HAS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t. cmp_cs K t / cmp_sn K t`;
                 `--K - (cmp_cs K t / cmp_sn K t) pow 2`;
                 `\t. ((A:real->real^N^N) t ** c) dot (A t ** c)`;
                 `((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** c) +
                  (B t ** c) dot (A t ** c)`;
                 `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[CMPJ_M_ALGEBRA] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[]);;

(* m(0+) = 0. *)

let CMPJ_M_LIM0 = prove
 (`!(A:real->real^N^N) B R L (c:real^N) K.
        cmp_jsys A B R L
        ==> ((\t. (A t ** c) dot (B t ** c) -
                  cmp_cs K t / cmp_sn K t * ((A t ** c) dot (A t ** c))) ---> &0)
            (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
   [prove(`&0 = vec 0 dot (c:real^N) - &1 * (inv(&1) * (c dot vec 0))`,
          REWRITE_TAC[DOT_LZERO; DOT_RZERO] THEN REAL_ARITH_TAC)] THEN
  MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_DOT_LIM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_A_LIM THEN
      MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`];
      MATCH_MP_TAC CMPJ_B_LIM THEN
      MAP_EVERY EXISTS_TAC [`A:real->real^N^N`; `R:real->real^N^N`; `L:real`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\t. cmp_cs K t * (inv(cmp_sn K t / t) *
                                ((inv t % ((A:real->real^N^N) t ** c)) dot (A t ** c)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN REWRITE_TAC[REAL_INV_DIV; DOT_LMUL] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[ETA_AX; CMPJ_CS_LIM] THEN
  MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_INV THEN REWRITE_TAC[CMPJ_SN_QUOT_LIM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CMPJ_DOT_LIM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_QUOT_LIM; MATCH_MP_TAC CMPJ_A_LIM] THEN
    MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC]);;

(* First components: (A t c)$1 = t c$1 and (B t c)$1 = c$1. *)

let CMPJ_FIRST_COMPONENTS = prove
 (`!(A:real->real^N^N) B R L (c:real^N) t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L
        ==> (A t ** c)$1 = t * c$1 /\ (B t ** c)$1 = c$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `c - (c:real^N)$1 % basis 1`] CMPJ_NORMAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_JSYS_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_GE_1; LE_REFL] THEN
  REAL_ARITH_TAC);;

(* m >= 0, that is ct_K |A c|^2 <= Ac.Bc, for normal c. *)

let CMPJ_M_NONNEG = prove
 (`!(A:real->real^N^N) B R L (c:real^N) K.
        cmp_jsys A B R L /\ c$1 = &0 /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t)
        ==> !t. &0 < t /\ t < L
                ==> cmp_cs K t / cmp_sn K t * ((A t ** c) dot (A t ** c)) <=
                    (A t ** c) dot (B t ** c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. ((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** c) -
         cmp_cs K t / cmp_sn K t * ((A t ** c) dot (A t ** c))`;
    `\t. ((B:real->real^N^N) t ** c - (cmp_cs K t / cmp_sn K t) %
          ((A:real->real^N^N) t ** c)) dot
         (B t ** c - (cmp_cs K t / cmp_sn K t) % (A t ** c)) +
         (K * ((A t ** c) dot (A t ** c)) -
          (A t ** c) dot ((R:real->real^N^N) t ** (A t ** c)))`;
    `L:real`] CMPO_INCREASING_LIM0) THEN
  REWRITE_TAC[REAL_SUB_LE] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_M_DERIV THEN EXISTS_TAC `L:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ];
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[DOT_POS_LE; REAL_SUB_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                     `L:real`; `c:real^N`] CMPJ_NORMAL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC CMPJ_M_LIM0 THEN
    MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `L:real`] THEN ASM_REWRITE_TAC[]]);;

(* Rauch's lower bound |A t c| >= sn_K(t) |c| for normal c. *)

let CMPJ_NORM_LOWER = prove
 (`!(A:real->real^N^N) B R L (c:real^N) K.
        cmp_jsys A B R L /\ c$1 = &0 /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t)
        ==> !t. &0 < t /\ t < L
                ==> cmp_sn K t pow 2 * (c dot c) <= (A t ** c) dot (A t ** c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `c:real^N`; `K:real`] CMPJ_M_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L
        ==> ((c:real^N) dot c) * (cmp_sn K t * cmp_sn K t) <=
            ((A:real->real^N^N) t ** c) dot (A t ** c)`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC CMPJ_RATIO_LOWER THEN
  EXISTS_TAC `\t. ((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** c) +
                  (B t ** c) dot (A t ** c)` THEN
  EXISTS_TAC `\t. cmp_sn K t * cmp_cs K t + cmp_cs K t * cmp_sn K t` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn K t` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `c:real^N`; `t:real`] CMPJ_JSYS_VD) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_LIFT_DERIV THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\t. (A:real->real^N^N) t ** (c:real^N)`;
                     `\t. (A:real->real^N^N) t ** (c:real^N)`;
                     `(B:real->real^N^N) t ** (c:real^N)`;
                     `(B:real->real^N^N) t ** (c:real^N)`;
                     `t:real`] CMPF_DOT_DERIV) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ABBREV_TAC `yy = ((A:real->real^N^N) t ** c) dot (A t ** c)` THEN
      ABBREV_TAC `yz = ((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** c)` THEN
      SUBGOAL_THEN `((B:real->real^N^N) t ** c) dot ((A:real->real^N^N) t ** c) = yz`
      SUBST1_TAC THENL [EXPAND_TAC "yz" THEN MATCH_ACCEPT_TAC DOT_SYM; ALL_TAC] THEN
      SUBGOAL_THEN `cmp_cs K t / cmp_sn K t * yy <= yz` MP_TAC THENL
       [MAP_EVERY EXPAND_TAC ["yy"; "yz"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `yy * (cmp_sn K t * cmp_cs K t + cmp_cs K t * cmp_sn K t) =
        (&2 * cmp_sn K t * cmp_sn K t) * (cmp_cs K t / cmp_sn K t * yy)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < cmp_sn K t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN
       `(yz + yz) * (cmp_sn K t * cmp_sn K t) = (&2 * cmp_sn K t * cmp_sn K t) * yz`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
   [prove(`(c:real^N) dot c = ((c dot c) / (&1 * &1))`,
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_DIV_1])] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\t. ((inv t % ((A:real->real^N^N) t ** c)) dot (inv t % (A t ** c))) /
                  ((cmp_sn K t / t) * (cmp_sn K t / t))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn K t` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_DIV THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_DOT_LIM THEN CONJ_TAC THEN MATCH_MP_TAC CMPJ_QUOT_LIM THEN
    MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_MUL THEN REWRITE_TAC[CMPJ_SN_QUOT_LIM];
    REAL_ARITH_TAC]);;

(* Before pi / sqrt K the Jacobi matrix is invertible (no conjugate points). *)

let CMPJ_INVERTIBLE = prove
 (`!(A:real->real^N^N) B R L K.
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t)
        ==> !t. &0 < t /\ t < L ==> invertible(A t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_KER] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N)$1 = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `x:real^N`; `t:real`] CMPJ_FIRST_COMPONENTS) THEN
    ASM_REWRITE_TAC[VEC_COMPONENT] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_RING `~(t = &0) ==> &0 = t * x ==> x = &0`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `x:real^N`; `K:real`] CMPJ_NORM_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[DOT_LZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cmp_sn K t pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM DOT_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[DOT_POS_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cmp_sn K t pow 2 * ((x:real^N) dot x)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;

(* The shape operator S = B A^-1 is >= ct_K on normal vectors. *)

let CMPJ_SHAPE_LOWER = prove
 (`!(A:real->real^N^N) B R L K (e:real^N).
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t) /\ e$1 = &0
        ==> !t. &0 < t /\ t < L
                ==> cmp_cs K t / cmp_sn K t * (e dot e) <=
                    e dot ((B t ** matrix_inv(A t)) ** e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((A:real->real^N^N) t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `K:real`] CMPJ_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = matrix_inv((A:real->real^N^N) t) ** (e:real^N)` THEN
  SUBGOAL_THEN `(A:real->real^N^N) t ** c = e` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N)$1 = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `c:real^N`; `t:real`] CMPJ_FIRST_COMPONENTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_RING `~(t = &0) ==> &0 = t * x ==> x = &0`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `c:real^N`; `K:real`] CMPJ_M_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The determinant (volume density).  det A > 0 while A is                   *)
(* invertible, tr S >= 1/t + (n-1) ct_K under sec <= K, and Gunther's       *)
(* bound det A(t) >= t sn_K(t)^(n-1).                                        *)
(* ========================================================================= *)

let CMPJ_DET_HAS_DERIV = prove
 (`!(A:real->real^N^N) B R L t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L /\ ~(det(A t) = &0)
        ==> ((\t. det(A t)) has_real_derivative
             det(A t) * trace(matrix_inv(A t) ** B t)) (atreal t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPJ_LIFT_DERIV THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPF_DET_DERIV THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_JSYS_AT) THEN
  ASM_SIMP_TAC[]);;

let CMPJ_DET_POSITIVE = prove
 (`!(A:real->real^N^N) B R L.
        cmp_jsys A B R L /\ (!t. &0 < t /\ t < L ==> invertible(A t))
        ==> !t. &0 < t /\ t < L ==> &0 < det(A t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o MATCH_MP CMPJ_DET_POS_NEAR0) THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s. det((A:real->real^N^N) s)`; `min d t / &2`; `t:real`; `&0`]
    REAL_IVT_DECREASING) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `det((A:real->real^N^N) s) *
                  trace(matrix_inv(A s) ** (B:real->real^N^N) s)` THEN
      MATCH_MP_TAC CMPJ_DET_HAS_DERIV THEN
      MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `L:real`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < s /\ s < L` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM INVERTIBLE_DET_NZ];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o REWRITE_RULE[IN_REAL_INTERVAL]) ASSUME_TAC)) THEN
    SUBGOAL_THEN `invertible((A:real->real^N^N) s)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]]]);;

(* S e1 = e1 / t. *)

let CMPJ_S_FIRST = prove
 (`!(A:real->real^N^N) B R L t.
        cmp_jsys A B R L /\ &0 < t /\ t < L /\ invertible(A t)
        ==> (B t ** matrix_inv(A t)) ** basis 1 = inv t % basis 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_JSYS_AT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `matrix_inv((A:real->real^N^N) t) ** basis 1 = inv t % basis 1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `basis 1:real^N = inv t % ((A:real->real^N^N) t ** basis 1)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_RMUL]);;

let CMPJ_TRACE_BASIS = prove
 (`!M:real^N^N. trace M = sum(1..dimindex(:N)) (\i. basis i dot (M ** basis i))`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS; column; LAMBDA_BETA]);;

(* tr S >= 1/t + (n-1) ct_K under sec <= K. *)

let CMPJ_TRACE_LOWER = prove
 (`!(A:real->real^N^N) B R L K.
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t)
        ==> !t. &0 < t /\ t < L
                ==> inv t + &(dimindex(:N) - 1) * (cmp_cs K t / cmp_sn K t) <=
                    trace(B t ** matrix_inv(A t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((A:real->real^N^N) t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `K:real`] CMPJ_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CMPJ_TRACE_BASIS] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_S_FIRST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[DOT_RMUL; DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  SUBGOAL_THEN
   `&(dimindex(:N) - 1) * (cmp_cs K t / cmp_sn K t) =
    sum(1 + 1..dimindex(:N)) (\i. cmp_cs K t / cmp_sn K t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE `(n + 1) - (1 + 1) = n - 1`]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `K:real`; `basis i:real^N`] CMPJ_SHAPE_LOWER) THEN
  ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL; DOT_BASIS_BASIS;
               ARITH_RULE `1 + 1 <= i ==> ~(1 = i) /\ 1 <= i`; REAL_MUL_RID]);;

let CMPJ_GUNTHER_ALG = prove
 (`!s c m. ~(s = &0) ==> &m * s pow (m - 1) * c = &m * (c / s) * s pow m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  REWRITE_TAC[REAL_MUL_LZERO; SUC_SUB1; real_pow] THEN
  UNDISCH_TAC `~(s = &0)` THEN CONV_TAC REAL_FIELD);;

let CMPJ_POW_SPLIT = prove
 (`!t n. 1 <= n ==> t pow n = t * t pow (n - 1)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[real_pow; SUC_SUB1] THEN ARITH_TAC);;

(* Gunther's density bound: det A(t) >= t sn_K(t)^(n-1) under sec <= K. *)

let CMPJ_GUNTHER = prove
 (`!(A:real->real^N^N) B R L K.
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t)
        ==> !t. &0 < t /\ t < L
                ==> t * cmp_sn K t pow (dimindex(:N) - 1) <= det(A t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `K:real`] CMPJ_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`] CMPJ_DET_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L
        ==> &1 * (t * cmp_sn K t pow (dimindex(:N) - 1)) <=
            det((A:real->real^N^N) t)`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID]] THEN
  MATCH_MP_TAC CMPJ_RATIO_LOWER THEN
  EXISTS_TAC `\t. det((A:real->real^N^N) t) *
                  trace(matrix_inv(A t) ** (B:real->real^N^N) t)` THEN
  EXISTS_TAC `\t. t * (&(dimindex(:N) - 1) *
                       cmp_sn K t pow (dimindex(:N) - 1 - 1) * cmp_cs K t) +
                  &1 * cmp_sn K t pow (dimindex(:N) - 1)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn K t` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_DET_HAS_DERIV THEN
      MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `L:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM INVERTIBLE_DET_NZ];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_POW_ATREAL THEN
      REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `K:real`] CMPJ_TRACE_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cmp_sn K t`; `cmp_cs K t`; `dimindex(:N) - 1`] CMPJ_GUNTHER_ALG) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `&0 <= det((A:real->real^N^N) t) * t * cmp_sn K t pow (dimindex(:N) - 1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(det((A:real->real^N^N) t) * t * cmp_sn K t pow (dimindex(:N) - 1)) *
                (inv t + &(dimindex(:N) - 1) * (cmp_cs K t / cmp_sn K t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < cmp_sn K t` THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN
       `(det((A:real->real^N^N) t) * trace((B:real->real^N^N) t ** matrix_inv(A t))) *
        (t * cmp_sn K t pow (dimindex(:N) - 1)) =
        (det(A t) * t * cmp_sn K t pow (dimindex(:N) - 1)) *
        trace(B t ** matrix_inv(A t))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
   [prove(`&1 = &1 / &1 pow (dimindex(:N) - 1)`,
          REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1])] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\t. (det((A:real->real^N^N) t) / t pow dimindex(:N)) /
                  ((cmp_sn K t / t) pow (dimindex(:N) - 1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn K t` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    MP_TAC(SPECL [`t:real`; `dimindex(:N)`] CMPJ_POW_SPLIT) THEN
    REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(t pow (dimindex(:N) - 1) = &0) /\
                  ~(cmp_sn K t pow (dimindex(:N) - 1) = &0)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REALLIM_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_DET_QUOT_LIM THEN
      MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_POW THEN REWRITE_TAC[CMPJ_SN_QUOT_LIM];
      REWRITE_TAC[REAL_POW_ONE] THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* sec >= k.  While A is invertible, s = e.S e (e normal, unit)              *)
(* satisfies s' <= -s^2 - k and t s -> 1, so s sn_k <= cs_k (Riccati         *)
(* comparison): the shape operator is <= ct_k on normal vectors.             *)
(* ========================================================================= *)

let CMPJ_DOT_SQUARE_LE = prove
 (`!x y:real^N. (x dot y) pow 2 <= (x dot x) * (y dot y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS]);;

(* The derivative of e.S e (Riccati), with S symmetric. *)

let CMPJ_QUAD_DERIV = prove
 (`!(A:real->real^N^N) B R L (e:real^N) t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L /\ invertible(A t)
        ==> ((\t. e dot ((B t ** matrix_inv(A t)) ** e)) has_real_derivative
             (--(e dot (R t ** e)) -
              ((B t ** matrix_inv(A t)) ** e) dot ((B t ** matrix_inv(A t)) ** e)))
            (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_JSYS_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(det((A:real->real^N^N) t) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `transp((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) =
    B t ** matrix_inv(A t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPF_SHAPE_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CMPJ_LIFT_DERIV THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPF_RICCATI_QUAD THEN ASM_REWRITE_TAC[]);;

let CMPJ_SHAPE_UPPER = prove
 (`!(A:real->real^N^N) B R L k (e:real^N).
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> k * (v dot v) <= v dot (R t ** v)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn k t) /\
        e$1 = &0 /\ e dot e = &1
        ==> !t. &0 < t /\ t < L
                ==> (e dot ((B t ** matrix_inv(A t)) ** e)) * cmp_sn k t <= cmp_cs k t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CMP_RICCATI_COMPARISON THEN
  EXISTS_TAC `\t. --(e dot ((R:real->real^N^N) t ** e)) -
                  (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) ** e) dot
                  ((B t ** matrix_inv(A t)) ** e)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_QUAD_DERIV THEN EXISTS_TAC `L:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `k <= r /\ s2 <= q ==> --r - q <= --s2 - k`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `e:real^N`]) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_RID];
        MP_TAC(ISPECL [`e:real^N`;
                       `((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) **
                        (e:real^N)`] CMPJ_DOT_SQUARE_LE) THEN
        ASM_REWRITE_TAC[REAL_MUL_LID]]];
    MATCH_MP_TAC CMPO_RICCATI_INIT THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `e:real^N`; `e:real^N`] CMPJ_TS_LIM) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`&2`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* The same for any normal vector: e.S e sn_k <= cs_k |e|^2. *)

let CMPJ_SHAPE_UPPER_GEN = prove
 (`!(A:real->real^N^N) B R L k (e:real^N).
        cmp_jsys A B R L /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> k * (v dot v) <= v dot (R t ** v)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn k t) /\
        e$1 = &0
        ==> !t. &0 < t /\ t < L
                ==> (e dot ((B t ** matrix_inv(A t)) ** e)) * cmp_sn k t <=
                    cmp_cs k t * (e dot e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `e:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO; REAL_MUL_LZERO;
                  REAL_MUL_RZERO; REAL_LE_REFL] THEN
  SUBGOAL_THEN `&0 < norm(e:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `k:real`; `inv(norm(e:real^N)) % e`] CMPJ_SHAPE_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RZERO] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2] THEN
    UNDISCH_TAC `&0 < norm(e:real^N)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ABBREV_TAC `X = (e:real^N) dot (((B:real->real^N^N) t **
                                   matrix_inv((A:real->real^N^N) t)) ** e)` THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `X * cmp_sn k t =
    norm(e:real^N) pow 2 * (inv(norm e) * inv(norm e) * X) * cmp_sn k t`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(e:real^N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Ric >= -(n-1) K.  m = tr S - 1/t satisfies                                *)
(* m' <= (n-1) K - m^2/(n-1), so m sn_(-K) <= (n-1) cs_(-K) (Laplacian       *)
(* comparison), and Bishop's bound det A(t) <= t sn_(-K)(t)^(n-1).           *)
(* ========================================================================= *)

(* Cauchy-Schwarz for finite sums. *)

let CMPJ_SUM_CS = prove
 (`!(f:num->real) s.
        FINITE s ==> (sum s f) pow 2 <= &(CARD s) * sum s (\i. f i pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum s (\i. sum s (\j. ((f:num->real) i - f j) pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a - b) pow 2 = (a pow 2 - &2 * a * b) + b pow 2`] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_SUB; SUM_LMUL; SUM_RMUL; SUM_CONST] THEN
  ABBREV_TAC `Q = sum s (\i. (f:num->real) i pow 2)` THEN
  ABBREV_TAC `S = sum s (f:num->real)` THEN REAL_ARITH_TAC);;

(* The derivative of tr S. *)

let CMPJ_TRACE_DERIV = prove
 (`!(A:real->real^N^N) B R L t.
        cmp_jsys A B R L /\ &0 <= t /\ t < L /\ invertible(A t)
        ==> ((\t. trace(B t ** matrix_inv(A t))) has_real_derivative
             sum(1..dimindex(:N))
                (\i. --(basis i dot (R t ** basis i)) -
                     ((B t ** matrix_inv(A t)) ** basis i) dot
                     ((B t ** matrix_inv(A t)) ** basis i))) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CMPJ_TRACE_BASIS] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPJ_QUAD_DERIV THEN EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[]);;

(* sum_i |S e_i|^2 >= 1/t^2 + (tr S - 1/t)^2/(n-1). *)

let CMPJ_SUMSQ_LOWER = prove
 (`!(A:real->real^N^N) B R L t.
        cmp_jsys A B R L /\ &0 < t /\ t < L /\ invertible(A t) /\ 2 <= dimindex(:N)
        ==> inv t pow 2 +
            (trace(B t ** matrix_inv(A t)) - inv t) pow 2 / &(dimindex(:N) - 1) <=
            sum(1..dimindex(:N))
               (\i. ((B t ** matrix_inv(A t)) ** basis i) dot
                    ((B t ** matrix_inv(A t)) ** basis i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_S_FIRST) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = (B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)` THEN
  DISCH_TAC THEN REWRITE_TAC[CMPJ_TRACE_BASIS] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ADD_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `a = a' /\ x <= y ==> a + x <= a' + y`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N) - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1 + 1..dimindex(:N)) (\i. (basis i dot ((S:real^N^N) ** basis i)) pow 2) *
              &(dimindex(:N) - 1)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\i. basis i dot ((S:real^N^N) ** basis i)`; `1 + 1..dimindex(:N)`]
      CMPJ_SUM_CS) THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG; ARITH_RULE `(n + 1) - (1 + 1) = n - 1`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`basis i:real^N`; `(S:real^N^N) ** basis i`] CMPJ_DOT_SQUARE_LE) THEN
    ASM_SIMP_TAC[DOT_BASIS_BASIS; ARITH_RULE `1 + 1 <= i ==> 1 <= i`; REAL_MUL_LID]]);;

(* Laplacian comparison: (tr S - 1/t) sn_(-K) <= (n-1) cs_(-K). *)

let CMPJ_TRACE_UPPER = prove
 (`!(A:real->real^N^N) B R L K.
        cmp_jsys A B R L /\
        (!t. &0 <= t /\ t < L ==> --(&(dimindex(:N) - 1) * K) <= trace(R t)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn (--K) t)
        ==> !t. &0 < t /\ t < L
                ==> (trace(B t ** matrix_inv(A t)) - inv t) * cmp_sn (--K) t <=
                    &(dimindex(:N) - 1) * cmp_cs (--K) t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ric") STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUB_REFL; REAL_MUL_LZERO] THEN
    SUBGOAL_THEN
     `trace((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) = inv t`
    SUBST1_TAC THENL
     [REWRITE_TAC[CMPJ_TRACE_BASIS] THEN ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
      MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                     `L:real`; `t:real`] CMPJ_S_FIRST) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[DOT_RMUL] THEN
      SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID];
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `n1 = &(dimindex(:N) - 1)` THEN
  SUBGOAL_THEN `&1 <= n1` ASSUME_TAC THENL
   [EXPAND_TAC "n1" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(dimindex(:N)) = n1 + &1` ASSUME_TAC THENL
   [EXPAND_TAC "n1" THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L
        ==> (inv n1 * (trace((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) -
                       inv t)) * cmp_sn (--K) t <= cmp_cs (--K) t`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `n1 * (inv n1 * (trace((B:real->real^N^N) t **
                                     matrix_inv((A:real->real^N^N) t)) - inv t)) *
                cmp_sn (--K) t` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= n1` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC]] THEN
  MATCH_MP_TAC CMP_RICCATI_COMPARISON THEN
  EXISTS_TAC
   `\t. inv n1 *
        (sum(1..dimindex(:N))
           (\i. --(basis i dot ((R:real->real^N^N) t ** basis i)) -
                (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) ** basis i) dot
                ((B t ** matrix_inv(A t)) ** basis i)) -
         --inv(t pow 2))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMPJ_TRACE_DERIV THEN EXISTS_TAC `L:real` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_INV_BASIC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `t:real`] CMPJ_SUMSQ_LOWER) THEN
    ASM_SIMP_TAC[] THEN
    USE_THEN "ric" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    REWRITE_TAC[SUM_SUB_NUMSEG; SUM_NEG; GSYM CMPJ_TRACE_BASIS] THEN
    REWRITE_TAC[REAL_POW_INV] THEN
    ABBREV_TAC `m = trace((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) - inv t` THEN
    ABBREV_TAC `Q = sum(1..dimindex(:N))
                      (\i. (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) **
                            basis i) dot ((B t ** matrix_inv(A t)) ** basis i))` THEN
    ABBREV_TAC `tr = trace((R:real->real^N^N) t)` THEN
    ABBREV_TAC `u = inv(t pow 2)` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(--tr - Q) - --u <= n1 * K - m pow 2 / n1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv n1 * (n1 * K - m pow 2 / n1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= n1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPO_RICCATI_INIT THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`] CMPJ_TS_TRACE_LIM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`&(dimindex(:N))`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `t * (inv n1 * (trace((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) -
                   inv t)) =
    inv n1 * (t * trace(B t ** matrix_inv(A t)) - &1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `y = t * trace((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t))` THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
  SUBGOAL_THEN `abs n1 = n1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * abs(y - &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_INV_LE_1; REAL_ABS_POS];
    ASM_REAL_ARITH_TAC]);;

(* Bishop's density bound: det A(t) <= t sn_(-K)(t)^(n-1) under            *)
(* Ric >= -(n-1) K, while A is invertible.                                   *)

let CMPJ_BISHOP = prove
 (`!(A:real->real^N^N) B R L K.
        cmp_jsys A B R L /\
        (!t. &0 <= t /\ t < L ==> --(&(dimindex(:N) - 1) * K) <= trace(R t)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn (--K) t)
        ==> !t. &0 < t /\ t < L
                ==> det(A t) <= t * cmp_sn (--K) t pow (dimindex(:N) - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`] CMPJ_DET_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L
        ==> det((A:real->real^N^N) t) <=
            &1 * (t * cmp_sn (--K) t pow (dimindex(:N) - 1))`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID]] THEN
  MATCH_MP_TAC CMPJ_RATIO_UPPER THEN
  EXISTS_TAC `\t. det((A:real->real^N^N) t) *
                  trace(matrix_inv(A t) ** (B:real->real^N^N) t)` THEN
  EXISTS_TAC `\t. t * (&(dimindex(:N) - 1) *
                       cmp_sn (--K) t pow (dimindex(:N) - 1 - 1) * cmp_cs (--K) t) +
                  &1 * cmp_sn (--K) t pow (dimindex(:N) - 1)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn (--K) t` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_DET_HAS_DERIV THEN
      MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `L:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM INVERTIBLE_DET_NZ];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_POW_ATREAL THEN
      REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `K:real`] CMPJ_TRACE_UPPER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN DISCH_THEN(LABEL_TAC "tr") THEN
    MP_TAC(SPECL [`cmp_sn (--K) t`; `cmp_cs (--K) t`; `dimindex(:N) - 1`]
      CMPJ_GUNTHER_ALG) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `&0 <= det((A:real->real^N^N) t) * t * cmp_sn (--K) t pow (dimindex(:N) - 1)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(det((A:real->real^N^N) t) * t * cmp_sn (--K) t pow (dimindex(:N) - 1)) *
                (inv t + &(dimindex(:N) - 1) * (cmp_cs (--K) t / cmp_sn (--K) t))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(det((A:real->real^N^N) t) * trace((B:real->real^N^N) t ** matrix_inv(A t))) *
        (t * cmp_sn (--K) t pow (dimindex(:N) - 1)) =
        (det(A t) * t * cmp_sn (--K) t pow (dimindex(:N) - 1)) *
        trace(B t ** matrix_inv(A t))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x - a <= b ==> x <= a + b`) THEN
      USE_THEN "tr" MP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < cmp_sn (--K) t` THEN UNDISCH_TAC `&0 < t` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
   [prove(`&1 = &1 / &1 pow (dimindex(:N) - 1)`,
          REWRITE_TAC[REAL_POW_ONE; REAL_DIV_1])] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\t. (det((A:real->real^N^N) t) / t pow dimindex(:N)) /
                  ((cmp_sn (--K) t / t) pow (dimindex(:N) - 1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn (--K) t` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    MP_TAC(SPECL [`t:real`; `dimindex(:N)`] CMPJ_POW_SPLIT) THEN
    REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(t pow (dimindex(:N) - 1) = &0) /\
                  ~(cmp_sn (--K) t pow (dimindex(:N) - 1) = &0)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REALLIM_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMPJ_DET_QUOT_LIM THEN
      MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `L:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_POW THEN REWRITE_TAC[CMPJ_SN_QUOT_LIM];
      REWRITE_TAC[REAL_POW_ONE] THEN REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The manifold wrapper.  A parallel orthonormal frame with                  *)
(* E1 = gamma' and Jacobi fields Y_j (Y_j(0) = 0, D Y_j(0) = E_j(0),          *)
(* Y_1 = t gamma') give Jacobi matrix data; sectional and Ricci bounds give  *)
(* the matrix hypotheses.                                                    *)
(* ========================================================================= *)

let CMPJ_FMAT_COLUMN = prove
 (`!(a:num->real->real^N) t j.
        1 <= j /\ j <= dimindex(:N) ==> cmp_fmat a t ** basis j = a j t`,
  SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; CART_EQ; column; cmp_fmat; LAMBDA_BETA]);;

(* D(t gamma') = gamma' along a geodesic. *)

let CMPJ_COVD_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        (!s. s IN J ==> Y s = s % mfd_vel atlas gamma s) /\ t IN J
        ==> mfd_covd atlas g gamma Y t = mfd_vel atlas gamma t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    MFD_GEODESIC_VEL_PARALLEL) THEN
  ASM_REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t =
    mfd_covd atlas g gamma (\s. s % mfd_vel atlas gamma s) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:real) IN J` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
    `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)`;
    `\s:real. s`; `&1`; `t:real`] CMPG_COVD_SCALAR)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_MUL_LID]]);;

(* The frame coordinates of gamma' are e1. *)

let CMPJ_FCOORD_VEL = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) t.
        cmp_pframe atlas g gamma J E /\ t IN J /\ E 1 t = mfd_vel atlas gamma t
        ==> transp(cmp_fmat E t) ** g(gamma t) ** mfd_vel atlas gamma t = basis 1`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM cmp_fcoord] THEN MATCH_MP_TAC CMPF_FCOORD_FRAME THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
  ASM_REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]);;

(* Frame and Jacobi fields give Jacobi matrix data. *)

let CMPJ_FRAME_JSYS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)
    (Y:num->real->real^N) L.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E /\
        (!t. t IN J ==> E 1 t = mfd_vel atlas gamma t) /\
        (!j. 1 <= j /\ j <= dimindex(:N) ==> mfd_jacobi atlas g gamma J (Y j)) /\
        (!j. 1 <= j /\ j <= dimindex(:N)
             ==> Y j (&0) = vec 0 /\ mfd_covd atlas g gamma (Y j) (&0) = E j (&0)) /\
        (!t. t IN J ==> Y 1 t = t % mfd_vel atlas gamma t) /\
        &0 < L /\ (!t. &0 <= t /\ t < L ==> t IN J)
        ==> cmp_jsys (cmp_fmat (\j. cmp_fcoord g gamma E (Y j)))
                     (cmp_fmat (\j. cmp_fcoord g gamma E (mfd_covd atlas g gamma (Y j))))
                     (cmp_rmat atlas g gamma E) L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&0:real) IN J` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `Y:num->real->real^N`; `&0`]
    CMPF_JACOBI_MATRIX) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "jm")] THEN
  REWRITE_TAC[cmp_jsys] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA; MAT_COMPONENT; COND_ID] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMPF_FCOORD_ZERO; VEC_COMPONENT];
    SUBGOAL_THEN
     `!j. 1 <= j /\ j <= dimindex(:N)
          ==> cmp_fcoord (g:A->real^N^N) (gamma:real->A) E
                (mfd_covd atlas g gamma ((Y:num->real->real^N) j)) (&0) = basis j`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `cmp_fcoord (g:A->real^N^N) (gamma:real->A) E
          (mfd_covd atlas g gamma ((Y:num->real->real^N) j)) (&0) =
        cmp_fcoord g gamma E (E j) (&0)`
      SUBST1_TAC THENL [REWRITE_TAC[cmp_fcoord] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CMPF_FCOORD_FRAME THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA; MAT_COMPONENT] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  USE_THEN "jm"
   (STRIP_ASSUME_TAC o C MP (ASSUME `(t:real) IN J`) o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPF_RMAT_SYM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_GE_1; LE_REFL; CART_EQ; column;
             LAMBDA_BETA; VEC_COMPONENT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `E:num->real->real^N`;
                   `t:real`; `&1`; `i:num`] CMPF_RMAT_TANGENT) THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID];
    SIMP_TAC[CMPJ_FMAT_COLUMN; DIMINDEX_GE_1; LE_REFL] THEN
    ASM_SIMP_TAC[cmp_fcoord; MATRIX_VECTOR_MUL_RMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CMPJ_FCOORD_VEL THEN EXISTS_TAC `J:real->bool` THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[CMPJ_FMAT_COLUMN; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[cmp_fcoord] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `(Y:num->real->real^N) 1`; `t:real`] CMPJ_COVD_RADIAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC CMPJ_FCOORD_VEL THEN EXISTS_TAC `J:real->bool` THEN
    ASM_SIMP_TAC[]]);;

(* Sectional curvature at a point, in the preferred coordinates. *)

let CMPJ_MFD_SECTIONAL_AT = prove
 (`!top atlas (g:A->real^N^N) x u v.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        x IN topspace top
        ==> mfd_sectional atlas g x u v =
            (u dot (g x ** mfd_riemann atlas g x u v v)) /
            ((u dot (g x ** u)) * (v dot (g x ** v)) - (u dot (g x ** v)) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sectional; lsectional; mfd_riemann] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Inner products of frame combinations F v. *)

let CMPJ_FRAME_GRAM = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) u v t.
        cmp_pframe atlas g gamma J E /\ t IN J
        ==> (cmp_fmat E t ** u) dot (g(gamma t) ** (cmp_fmat E t ** v)) = u dot v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)` THEN
  REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN SIMP_TAC[MATRIX_VECTOR_MUL_LID]);;

(* v.R v = <F v, R(F v, T) T> in the frame. *)

let CMPJ_FRAME_QUAD = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) v t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_pframe atlas g gamma J E /\ t IN J /\ gamma t IN topspace top
        ==> v dot (cmp_rmat atlas g gamma E t ** v) =
            (cmp_fmat E t ** v) dot
            (g(gamma t) ** mfd_riemann atlas g (gamma t) (cmp_fmat E t ** v)
                             (mfd_vel atlas gamma t) (mfd_vel atlas gamma t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `cmp_fcoord (g:A->real^N^N) (gamma:real->A) E
      (\s. cmp_fmat (E:num->real->real^N) s ** (v:real^N)) t = v`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmp_fcoord; MATRIX_VECTOR_MUL_ASSOC] THEN
    UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)` THEN
    REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN SIMP_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`;
                 `\s. cmp_fmat (E:num->real->real^N) s ** (v:real^N)`; `t:real`]
    CMPF_RIEMANN_FCOORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                 `\s. cmp_fmat (E:num->real->real^N) s ** (v:real^N)`;
                 `\s. mfd_riemann atlas (g:A->real^N^N) ((gamma:real->A) s)
                        (cmp_fmat (E:num->real->real^N) s ** (v:real^N))
                        (mfd_vel atlas gamma s) (mfd_vel atlas gamma s)`;
                 `t:real`] CMPF_FCOORD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* g-orthogonal vectors of positive length are not collinear. *)

let CMPJ_NOT_COLLINEAR_ORTH = prove
 (`!(G:real^N^N) x y.
        &0 < x dot (G ** x) /\ &0 < y dot (G ** y) /\ x dot (G ** y) = &0
        ==> ~collinear {vec 0, x, y}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&0 < (x:real^N) dot ((G:real^N^N) ** x)` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LT_REFL];
    DISCH_TAC THEN UNDISCH_TAC `&0 < (y:real^N) dot ((G:real^N^N) ** y)` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LT_REFL];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) dot ((G:real^N^N) ** y) = c * (x dot (G ** y))` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
      REWRITE_TAC[DOT_LMUL];
      UNDISCH_TAC `(x:real^N) dot ((G:real^N^N) ** y) = &0` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
      ASM_REAL_ARITH_TAC]]);;

(* The sectional curvature of the plane (F v, T) in the frame. *)

let CMPJ_FRAME_SEC = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) v t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_pframe atlas g gamma J E /\ t IN J /\ gamma t IN topspace top /\
        E 1 t = mfd_vel atlas gamma t /\ v$1 = &0 /\ ~(v = vec 0)
        ==> ~collinear {vec 0, cmp_fmat E t ** v, mfd_vel atlas gamma t} /\
            v dot (cmp_rmat atlas g gamma E t ** v) =
            mfd_sectional atlas g (gamma t) (cmp_fmat E t ** v)
                          (mfd_vel atlas gamma t) * (v dot v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t =
                cmp_fmat (E:num->real->real^N) t ** (basis 1:real^N)`
  ASSUME_TAC THENL
   [SIMP_TAC[CMPJ_FMAT_COLUMN; DIMINDEX_GE_1; LE_REFL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (v:real^N) dot v` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u w. (cmp_fmat (E:num->real->real^N) t ** u) dot
          ((g:A->real^N^N)((gamma:real->A) t) ** (cmp_fmat E t ** w)) = u dot w`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CMPJ_FRAME_GRAM THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_NOT_COLLINEAR_ORTH THEN
    EXISTS_TAC `(g:A->real^N^N)((gamma:real->A) t)` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DOT_BASIS; DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`;
                 `cmp_fmat (E:num->real->real^N) t ** (v:real^N)`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    CMPJ_MFD_SECTIONAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `v:real^N`; `t:real`] CMPJ_FRAME_QUAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `X = (cmp_fmat (E:num->real->real^N) t ** v) dot
                  ((g:A->real^N^N)((gamma:real->A) t) **
                   mfd_riemann atlas g (gamma t) (cmp_fmat E t ** v)
                     (cmp_fmat E t ** basis 1) (cmp_fmat E t ** basis 1))` THEN
  SIMP_TAC[DOT_BASIS; DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < (v:real^N) dot v` THEN CONV_TAC REAL_FIELD);;

(* Curvature bounds along gamma in frame form. *)

let CMPJ_FRAME_SEC_UPPER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) K.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E /\
        (!t. t IN J ==> E 1 t = mfd_vel atlas gamma t) /\
        (!t u. t IN J /\ ~collinear {vec 0,u,mfd_vel atlas gamma t}
               ==> mfd_sectional atlas g (gamma t) u (mfd_vel atlas gamma t) <= K)
        ==> !t v. t IN J /\ v$1 = &0
                  ==> v dot (cmp_rmat atlas g gamma E t ** v) <= K * (v dot v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO; REAL_MUL_RZERO;
                  REAL_LE_REFL] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `v:real^N`; `t:real`] CMPJ_FRAME_SEC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CMPJ_FRAME_SEC_LOWER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E /\
        (!t. t IN J ==> E 1 t = mfd_vel atlas gamma t) /\
        (!t u. t IN J /\ ~collinear {vec 0,u,mfd_vel atlas gamma t}
               ==> k <= mfd_sectional atlas g (gamma t) u (mfd_vel atlas gamma t))
        ==> !t v. t IN J /\ v$1 = &0
                  ==> k * (v dot v) <= v dot (cmp_rmat atlas g gamma E t ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO; REAL_MUL_RZERO;
                  REAL_LE_REFL] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `v:real^N`; `t:real`] CMPJ_FRAME_SEC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The trace of the curvature matrix is Ric(T,T). *)

let CMPJ_TRANSP_FMAT_COMPONENT = prove
 (`!(E:num->real->real^N) t x i.
        1 <= i /\ i <= dimindex(:N) ==> (transp(cmp_fmat E t) ** x)$i = E i t dot x`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; transp; cmp_fmat; LAMBDA_BETA; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA]);;

let CMPJ_FRAME_RICCI = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_pframe atlas g gamma J E /\ t IN J /\ gamma t IN topspace top
        ==> trace(cmp_rmat atlas g gamma E t) =
            mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `transp(cmp_fmat (E:num->real->real^N) t) ** (g:A->real^N^N)((gamma:real->A) t) **
    cmp_fmat E t = mat 1`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)` THEN
    REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `invertible(transp(cmp_fmat (E:num->real->real^N) t) **
               (g:A->real^N^N)((gamma:real->A) t)) /\
    matrix_inv(transp(cmp_fmat E t) ** g(gamma t)) = cmp_fmat E t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[INVERTIBLE_LEFT_INVERSE] THEN
      EXISTS_TAC `cmp_fmat (E:num->real->real^N) t` THEN
      ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
      ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
      MATCH_MP_TAC MATRIX_INV_UNIQUE_LEFT THEN
      ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
      ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_ricci; lricci; GSYM mfd_riemann] THEN
  MP_TAC(ISPECL
   [`\u. mfd_riemann atlas (g:A->real^N^N) ((gamma:real->A) t) u
           (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)`;
    `transp(cmp_fmat (E:num->real->real^N) t) ** (g:A->real^N^N)((gamma:real->A) t)`]
    LRG_TRACE_FRAME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPF_RIEMANN_LINEAR THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o BETA_RULE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMPJ_FMAT_COLUMN; cmp_rmat; LAMBDA_BETA; GSYM MATRIX_VECTOR_MUL_ASSOC;
               CMPJ_TRANSP_FMAT_COMPONENT]);;

let CMPJ_VEL_UNIT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) t.
        cmp_pframe atlas g gamma J E /\ t IN J /\ E 1 t = mfd_vel atlas gamma t
        ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = &1`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(E:num->real->real^N) 1 t = cmp_fmat E t ** basis 1` SUBST1_TAC THENL
   [SIMP_TAC[CMPJ_FMAT_COLUMN; DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                 `basis 1:real^N`; `basis 1:real^N`; `t:real`] CMPJ_FRAME_GRAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL]);;

let CMPJ_FRAME_RIC_LOWER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) K.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E /\
        (!t. t IN J ==> E 1 t = mfd_vel atlas gamma t) /\
        (!t. t IN J
             ==> --(&(dimindex(:N) - 1) * K) *
                 (mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t)) <=
                 mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t)
                           (mfd_vel atlas gamma t))
        ==> !t. t IN J ==> --(&(dimindex(:N) - 1) * K) <=
                           trace(cmp_rmat atlas g gamma E t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `t:real`] CMPJ_FRAME_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                 `t:real`] CMPJ_VEL_UNIT) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[REAL_MUL_RID]);;

