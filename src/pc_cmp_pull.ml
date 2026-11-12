(* ========================================================================= *)
(* Unit pc_cmp_pull (comparison-geometry layer CMP): S4, the exp_x pullback *)
(* metric on a tangent ball (Petersen 6.4.2-6.4.3), proved as               *)
(* CMP_EXP_PULLBACK: |- !u n. CMP_EXP_PULLBACK_STATEMENT u n (the statement *)
(* constant of pc_cmp_defs).  In the coordinates w of an orthonormal frame *)
(* E at x, G(w) is the pullback of g by the map w |-> exp_x(E w).  Along a  *)
(* ray w = t u, the quadratic form of G(t u) is |A(t) P^T a|^2 / t^2 with A *)
(* the Jacobi matrix of the unit-speed geodesic in direction u             *)
(* (pc_cmp_jcomp) and P an orthogonal matrix with P e1 = u.  With the Gauss *)
(* lemma G w = w, the Hessian of r = |w| for G is                           *)
(* (G(a,a) - (w.a)^2/r^2)/r + (D_w G)(a,a)/(2r), so the Hessian bounds      *)
(* reduce to the shape-operator bounds of pc_cmp_jcomp and the scalar       *)
(* bounds of pc_cmp_ode.  d exp along rays: MFD_EXP_DIFFERENTIAL_JACOBI_RAY *)
(* (pc_geo_jvar).                                                           *)
(* ========================================================================= *)

needs "src/pc_cmp_jcomp.ml";;
needs "src/pc_geo_jacobi.ml";;
needs "src/pc_geo_jvar.ml";;
needs "src/pc_rfa_sec.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The upper Rauch bound and the bounds along one ray.  For a               *)
(* Jacobi system with |sec| <= K on normal vectors and K L^2 <= 1:          *)
(* |A c|^2 / t^2 is within a factor 2 of |c|^2, and the quadratic form      *)
(* (B c).(A c) / t^2 - c_1^2 / t (the Hessian of r along the ray) is        *)
(* between 1/t - K t and 1/t + K t times |A c|^2 / t^2 - c_1^2.             *)
(* ========================================================================= *)

let CMPP_SPLIT = prove
 (`!c:real^N. c = c$1 % basis 1 + (c - c$1 % basis 1) /\
              (c - c$1 % basis 1)$1 = &0`,
  GEN_TAC THEN CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_GE_1; LE_REFL] THEN
  REAL_ARITH_TAC);;

let CMPP_DOT_SPLIT = prove
 (`!a (p:real^N). p$1 = &0
                  ==> (a % basis 1 + p) dot (a % basis 1 + p) = a pow 2 + p dot p /\
                      (a % basis 1 + p)$1 = a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[DOT_BASIS; DOT_BASIS_BASIS; BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CMPP_GRAM_SPLIT = prove
 (`!(A:real->real^N^N) B R L a (p:real^N) t.
        cmp_jsys A B R L /\ p$1 = &0 /\ &0 <= t /\ t < L
        ==> (A t ** (a % basis 1 + p)) dot (A t ** (a % basis 1 + p)) =
            (a * t) pow 2 + (A t ** p) dot (A t ** p) /\
            (B t ** (a % basis 1 + p)) dot (A t ** (a % basis 1 + p)) =
            a pow 2 * t + (B t ** p) dot (A t ** p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `p:real^N`] CMPJ_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `t:real`] CMPJ_JSYS_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS; DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* sn_K and sn_(-K) are positive on (0,L) when K L^2 <= 1. *)

let CMPP_SN_POS = prove
 (`!K L t. &0 <= K /\ K * L pow 2 <= &1 /\ &0 < t /\ t < L
           ==> &0 < cmp_sn K t /\ &0 < cmp_sn (--K) t /\ K * t pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `K * t pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * L pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN
  ASM_REWRITE_TAC[] THENL [DISJ2_TAC; DISJ1_TAC THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `sqrt K * t = sqrt(K * t pow 2)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt(&1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    REWRITE_TAC[SQRT_1] THEN MP_TAC CMPO_ONE_LT_PI2 THEN MP_TAC PI_POS THEN
    REAL_ARITH_TAC]);;

(* The upper Rauch bound: sec >= k on normal vectors (while A is            *)
(* invertible) gives |A c| <= sn_k |c| for normal c.                        *)

let CMPP_NORM_UPPER = prove
 (`!(A:real->real^N^N) B R L (c:real^N) k.
        cmp_jsys A B R L /\ c$1 = &0 /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> k * (v dot v) <= v dot (R t ** v)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn k t)
        ==> !t. &0 < t /\ t < L
                ==> (A t ** c) dot (A t ** c) <= cmp_sn k t pow 2 * (c dot c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPJ_JSYS_INIT) THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L
        ==> ((A:real->real^N^N) t ** c) dot (A t ** c) <=
            ((c:real^N) dot c) * (cmp_sn k t * cmp_sn k t)`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC CMPJ_RATIO_UPPER THEN
  EXISTS_TAC `\t. ((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** c) +
                  (B t ** c) dot (A t ** c)` THEN
  EXISTS_TAC `\t. cmp_sn k t * cmp_cs k t + cmp_cs k t * cmp_sn k t` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn k t` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
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
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
      REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(((A:real->real^N^N) t ** (c:real^N)) dot ((B:real->real^N^N) t ** c)) *
      cmp_sn k t <= cmp_cs k t * ((A t ** c) dot (A t ** c))`
    MP_TAC THENL
     [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                     `L:real`; `k:real`; `(A:real->real^N^N) t ** (c:real^N)`]
        CMPJ_SHAPE_UPPER_GEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                       `L:real`; `c:real^N`] CMPJ_NORMAL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) **
        (A t ** (c:real^N)) = B t ** c`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN
        REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `invertible((A:real->real^N^N) t)` MP_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
        REWRITE_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `yy = ((A:real->real^N^N) t ** c) dot (A t ** (c:real^N))` THEN
    ABBREV_TAC `yz = ((A:real->real^N^N) t ** c) dot ((B:real->real^N^N) t ** (c:real^N))` THEN
    SUBGOAL_THEN `((B:real->real^N^N) t ** c) dot ((A:real->real^N^N) t ** (c:real^N)) = yz`
    SUBST1_TAC THENL [EXPAND_TAC "yz" THEN MATCH_ACCEPT_TAC DOT_SYM; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(yz + yz) * (cmp_sn k t * cmp_sn k t) = (&2 * cmp_sn k t) * (yz * cmp_sn k t)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `yy * (cmp_sn k t * cmp_cs k t + cmp_cs k t * cmp_sn k t) =
      (&2 * cmp_sn k t) * (cmp_cs k t * yy)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
   [prove(`(c:real^N) dot c = ((c dot c) / (&1 * &1))`,
          CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_DIV_1])] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\t. ((inv t % ((A:real->real^N^N) t ** c)) dot (inv t % (A t ** c))) /
                  ((cmp_sn k t / t) * (cmp_sn k t / t))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < cmp_sn k t` MP_TAC THENL
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

(* Positivity and invertibility on (0,L) from |sec| <= K and K L^2 <= 1. *)

let CMPP_RAY_FACTS = prove
 (`!(A:real->real^N^N) B R L K.
        cmp_jsys A B R L /\ &0 <= K /\ K * L pow 2 <= &1 /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> --K * (v dot v) <= v dot (R t ** v))
        ==> (!t. &0 < t /\ t < L ==> &0 < cmp_sn K t) /\
            (!t. &0 < t /\ t < L ==> &0 < cmp_sn (--K) t) /\
            (!t. &0 < t /\ t < L ==> K * t pow 2 <= &1) /\
            (!t. &0 < t /\ t < L ==> invertible(A t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L
        ==> &0 < cmp_sn K t /\ &0 < cmp_sn (--K) t /\ K * t pow 2 <= &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC CMPP_SN_POS THEN
    EXISTS_TAC `L:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CMPJ_INVERTIBLE THEN
  MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `K:real`] THEN
  ASM_SIMP_TAC[]);;

(* The Gram form |A c|^2 / t^2 is within a factor 2 of |c|^2. *)

let CMPP_RAY_GRAM = prove
 (`!(A:real->real^N^N) B R L K (c:real^N) t.
        cmp_jsys A B R L /\ &0 <= K /\ K * L pow 2 <= &1 /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> --K * (v dot v) <= v dot (R t ** v)) /\
        &0 < t /\ t < L
        ==> inv(&2) * (c dot c) <= ((A t ** c) dot (A t ** c)) / t pow 2 /\
            ((A t ** c) dot (A t ** c)) / t pow 2 <= &2 * (c dot c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `K:real`] CMPP_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:real^N` CMPP_SPLIT) THEN
  ABBREV_TAC `p:real^N = c - c$1 % basis 1` THEN
  ABBREV_TAC `a = (c:real^N)$1` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real`; `p:real^N`] CMPP_DOT_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `a:real`; `p:real^N`; `t:real`] CMPP_GRAM_SPLIT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `cmp_sn K t pow 2 * ((p:real^N) dot p) <= ((A:real->real^N^N) t ** p) dot (A t ** p)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `p:real^N`; `K:real`] CMPJ_NORM_LOWER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((A:real->real^N^N) t ** p) dot (A t ** p) <= cmp_sn (--K) t pow 2 * ((p:real^N) dot p)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `p:real^N`; `--K`] CMPP_NORM_UPPER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `K * t pow 2 <= &1` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 * ((p:real^N) dot p) <= (&2 * cmp_sn K t pow 2) * (p dot p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
    MATCH_MP_TAC CMP_SN_LOWER_HALF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_sn (--K) t pow 2 * ((p:real^N) dot p) <= (&2 * t pow 2) * (p dot p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DOT_POS_LE] THEN
    MATCH_MP_TAC CMP_SN_UPPER_NEG_TWO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
  MP_TAC(SPEC `a * t` REAL_LE_POW_2) THEN
  MP_TAC(ISPEC `p:real^N` DOT_POS_LE) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_REAL_ARITH_TAC);;

(* The Hessian form along the ray: (B c).(A c)/t^2 - c_1^2/t lies between  *)
(* (1/t - K t) and (1/t + K t) times |A c|^2/t^2 - c_1^2.                   *)

let CMPP_RAY_HESS = prove
 (`!(A:real->real^N^N) B R L K (c:real^N) t.
        cmp_jsys A B R L /\ &0 <= K /\ K * L pow 2 <= &1 /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t v. &0 <= t /\ t < L /\ v$1 = &0 ==> --K * (v dot v) <= v dot (R t ** v)) /\
        &0 < t /\ t < L
        ==> (inv t - K * t) * (((A t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2) <=
            ((B t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2 / t /\
            ((B t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2 / t <=
            (inv t + K * t) * (((A t ** c) dot (A t ** c)) / t pow 2 - c$1 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `K:real`] CMPP_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:real^N` CMPP_SPLIT) THEN
  ABBREV_TAC `p:real^N = c - c$1 % basis 1` THEN
  ABBREV_TAC `a = (c:real^N)$1` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `a:real`; `p:real^N`; `t:real`] CMPP_GRAM_SPLIT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((a * t) pow 2 + ((A:real->real^N^N) t ** p) dot (A t ** (p:real^N))) / t pow 2 -
    a pow 2 = ((A t ** p) dot (A t ** p)) / t pow 2 /\
    (a pow 2 * t + ((B:real->real^N^N) t ** p) dot ((A:real->real^N^N) t ** (p:real^N))) /
    t pow 2 - a pow 2 / t = ((B t ** p) dot (A t ** p)) / t pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_LT_INV_EQ] THEN
  SUBGOAL_THEN
   `((B:real->real^N^N) t ** p) dot ((A:real->real^N^N) t ** (p:real^N)) =
    (A t ** p) dot ((B t ** matrix_inv(A t)) ** (A t ** p))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `matrix_inv((A:real->real^N^N) t) ** A t ** (p:real^N) = p`
    SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `invertible((A:real->real^N^N) t)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      MATCH_ACCEPT_TAC DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((A:real->real^N^N) t ** (p:real^N))$1 = &0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `p:real^N`] CMPJ_NORMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `e:real^N = (A:real->real^N^N) t ** p` THEN
  ABBREV_TAC `Y = (e:real^N) dot (((B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)) ** e)` THEN
  ABBREV_TAC `X = (e:real^N) dot e` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cmp_sn K t /\ &0 < cmp_sn (--K) t /\ K * t pow 2 <= &1`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cmp_cs K t / cmp_sn K t * X` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC CMP_CT_LOWER_BOUND THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                     `L:real`; `K:real`; `e:real^N`] CMPJ_SHAPE_LOWER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y * cmp_sn (--K) t <= cmp_cs (--K) t * X` MP_TAC THENL
   [MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                   `L:real`; `--K`; `e:real^N`] CMPJ_SHAPE_UPPER_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_cs (--K) t * X <= ((inv t + K * t) * cmp_sn (--K) t) * X` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMP_CT_UPPER_NEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((inv t + K * t) * cmp_sn (--K) t) * X = ((inv t + K * t) * X) * cmp_sn (--K) t`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `Y * cmp_sn (--K) t <= ((inv t + K * t) * X) * cmp_sn (--K) t` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;


(* ========================================================================= *)
(* The Hessian of r = |w| for a metric field G with G w = w                 *)
(* (the Gauss lemma in coordinates): it equals                              *)
(* (G(a,a) - (w.a)^2/r^2)/r + (D_w G)(a,a)/(2r).                            *)
(* ========================================================================= *)

(* The norm is differentiable away from 0 (as P2C_NORM_DERIV and          *)
(* MOI_PDL_NORM_DERIV, which live in units this layer does not load).      *)

let CMPP_NORM_DERIV = prove
 (`!x:real^N.
     ~(x = vec 0)
     ==> ((\y. lift(norm y)) has_derivative (\h. lift((x dot h) / norm x))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt`; `inv(&2 * sqrt(norm(x:real^N) pow 2))`;
                 `\z:real^N. lift(norm z pow 2)`; `\h:real^N. &2 % lift(x dot h)`;
                 `x:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT; HAS_REAL_DERIVATIVE_SQRT] THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
  GEN_TAC THEN SUBGOAL_THEN `~(norm(x:real^N) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

(* The directional derivative z |-> (z.a)/|z| and its derivative. *)

let CMPP_NORM_DIR_DERIV = prove
 (`!(y:real^N) a.
     ~(y = vec 0)
     ==> ((\z. lift((z dot a) / norm z)) has_derivative
          (\h. lift((h dot a) / norm y - (y dot a) * (y dot h) / norm y pow 3)))
         (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^N. lift((z dot a) / norm z)) =
                (\z. inv(norm z) % lift(z dot a))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; real_div; REAL_MUL_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. inv(norm z)`;
                 `\h:real^N. --inv(norm(y:real^N) pow 2) * ((y dot h) / norm y)`;
                 `\z:real^N. lift(z dot a)`; `\h:real^N. lift(h dot a)`;
                 `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_CMUL] THEN
      MP_TAC(ISPECL [`inv`; `--inv(norm(y:real^N) pow 2)`;
                     `\x:real^N. lift(norm x)`; `\h:real^N. lift((y dot h) / norm y)`;
                     `y:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
      ASM_SIMP_TAC[CMPP_NORM_DERIV; LIFT_DROP; HAS_REAL_DERIVATIVE_INV_BASIC;
                   REAL_LT_IMP_NZ];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ] THEN
  X_GEN_TAC `h:real^N` THEN UNDISCH_TAC `&0 < norm(y:real^N)` THEN
  CONV_TAC REAL_FIELD);;

(* The derivative of z |-> G z z at y; with G z z = z this is the identity. *)

let CMPP_GAUSS_DERIV = prove
 (`!U (G:real^N->real^N^N) y h.
        metric_field U G /\ y IN U /\ (!z. z IN U ==> G z ** z = z)
        ==> mderiv G y h ** y + G y ** h = h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\h. mderiv G y h ** y + (G:real^N->real^N^N) y ** h) = (\h. h)`
  MP_TAC THENL
   [MATCH_MP_TAC LRG_HAS_DERIVATIVE_UNIQUE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\z. (G:real^N->real^N^N) z ** z`; `\z:real^N. z`;
                          `U:real^N->bool`; `y:real^N`] THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_ID] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    REWRITE_TAC[mderiv] THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`;
                   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        (G:real^N->real^N^N)) (at y)`;
                   `\z:real^N. z`; `\h:real^N. h`; `y:real^N`]
      LRG_HAS_DERIVATIVE_MATVEC) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
      LRG_METRIC_FIELD_DIFF) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN REWRITE_TAC[]]);;

(* y . Gamma(a,a) when G y y = y near y. *)

let CMPP_CHRISTOFFEL_RADIAL = prove
 (`!U (G:real^N->real^N^N) y a.
        metric_field U G /\ y IN U /\ (!z. z IN U ==> G z ** z = z)
        ==> y dot christoffel G y a a =
            a dot a - a dot (G y ** a) - inv(&2) * (a dot (mderiv G y y ** a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y ** y = y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) dot christoffel G y a a = y dot (G y ** christoffel G y a a)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `y:real^N`;
                   `christoffel (G:real^N->real^N^N) y a a`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `a:real^N`; `y:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `y:real^N`; `a:real^N`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`]
    CMPP_GAUSS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. (a:real^N) dot v`) THEN
  REWRITE_TAC[DOT_RADD] THEN REAL_ARITH_TAC);;

(* The Hessian of the norm for a metric field with G w = w. *)

let CMPP_LHESS_NORM = prove
 (`!U (G:real^N->real^N^N) y a.
        metric_field U G /\ y IN U /\ ~(y = vec 0) /\
        (!z. z IN U ==> G z ** z = z)
        ==> cmp_lhess G (\z. norm z) y a a =
            (a dot (G y ** a)) / norm y - (y dot a) pow 2 / norm y pow 3 +
            (a dot (mderiv G y y ** a)) / (&2 * norm y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z b:real^N. ~(z = vec 0)
                 ==> drop(frechet_derivative (\x. lift(norm x)) (at z) b) =
                     (z dot b) / norm z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
                MATCH_MP CMPP_NORM_DERIV) THEN
    REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. lift(drop(frechet_derivative (\x. lift(norm x)) (at z) (a:real^N))))
      (at y) =
    (\h. lift((h dot a) / norm y - (y dot a) * (y dot h) / norm y pow 3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `frechet_derivative (\z:real^N. lift((z dot a) / norm z)) (at y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `(:real^N) DELETE (vec 0)` THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN ASM_SIMP_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      ASM_SIMP_TAC[CMPP_NORM_DIR_DERIV]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_lhess; lnabla; COND_ID; SUM_SING_NUMSEG] THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`]
    CMPP_CHRISTOFFEL_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN
  UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD);;


(* ========================================================================= *)
(* The S4 bounds from ray data.  If G is a metric field on                   *)
(* ball(0,rho) with G w = w, and along the ray through w the quadratic form *)
(* of G is |A(s) P^T a|^2 / s^2 for a Jacobi system A, B, R with           *)
(* |sec| <= K and an orthogonal P with P e1 = w/|w|, then G is within a    *)
(* factor 2 of the identity at w and the Hessian of |w| satisfies the S4    *)
(* bounds at w.                                                              *)
(* ========================================================================= *)

(* The derivative of s |-> a.(G(s u) a). *)

let CMPP_GDOT_RAY_DERIV = prove
 (`!(G:real^N->real^N^N) u a t.
        (vectorize o G) differentiable at (t % u)
        ==> ((\s. a dot (G(s % u) ** a)) has_real_derivative
             a dot (mderiv G (t % u) u ** a)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative] THEN
  SUBGOAL_THEN
   `(lift o (\s. (a:real^N) dot ((G:real^N->real^N^N)(s % u) ** a)) o drop) =
    (\z. lift(a dot (G z ** a))) o (\x:real^1. drop x % u)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF; FUN_EQ_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. drop x % lift((a:real^N) dot (mderiv (G:real^N->real^N^N) (t % u) u ** a))) =
    (\w. lift(a dot (mderiv G (t % u) w ** a))) o (\x:real^1. drop x % u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LRG_MDERIV_LINEAR th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; LIFT_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC LRG_HAS_DERIVATIVE_GDOT THEN
    ASM_REWRITE_TAC[]]);;

(* The derivative of s |-> |A(s) c|^2 / s^2. *)

let CMPP_GRAM_RAY_DERIV = prove
 (`!(A:real->real^N^N) B R L (c:real^N) t.
        cmp_jsys A B R L /\ &0 < t /\ t < L
        ==> ((\s. ((A s ** c) dot (A s ** c)) / s pow 2) has_real_derivative
             &2 * ((B t ** c) dot (A t ** c)) / t pow 2 -
             &2 * ((A t ** c) dot (A t ** c)) / t pow 3) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `c:real^N`; `t:real`] CMPJ_JSYS_VD) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\s. ((A:real->real^N^N) s ** (c:real^N)) dot (A s ** c)) has_real_derivative
     (A t ** c) dot ((B:real->real^N^N) t ** c) + (B t ** c) dot (A t ** c)) (atreal t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPJ_LIFT_DERIV THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\t. (A:real->real^N^N) t ** (c:real^N)`;
                   `\t. (A:real->real^N^N) t ** (c:real^N)`;
                   `(B:real->real^N^N) t ** (c:real^N)`;
                   `(B:real->real^N^N) t ** (c:real^N)`;
                   `t:real`] CMPF_DOT_DERIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. ((A:real->real^N^N) s ** (c:real^N)) dot (A s ** c)`;
                 `((A:real->real^N^N) t ** (c:real^N)) dot ((B:real->real^N^N) t ** c) +
                  (B t ** c) dot (A t ** c)`;
                 `\s:real. s pow 2`; `&2 * t`; `t:real`] HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DOT_SYM] THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD);;

(* The S4 bounds at one point w from ray data. *)

let CMPP_PULLBACK_CORE = prove
 (`!(G:real^N->real^N^N) rho K (w:real^N) (P:real^N^N) (A:real->real^N^N) B R.
        metric_field (ball(vec 0,rho)) G /\
        (!z. z IN ball(vec 0,rho) ==> G z ** z = z) /\
        &0 <= K /\ K * rho pow 2 <= &1 /\
        &0 < norm w /\ norm w < rho /\
        orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
        cmp_jsys A B R rho /\
        (!t v. &0 <= t /\ t < rho /\ v$1 = &0 ==> v dot (R t ** v) <= K * (v dot v)) /\
        (!t v. &0 <= t /\ t < rho /\ v$1 = &0 ==> --K * (v dot v) <= v dot (R t ** v)) /\
        (!s a. &0 < s /\ s < rho
               ==> a dot (G(s % inv(norm w) % w) ** a) =
                   ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)
        ==> !a. inv(&2) * (a dot a) <= a dot (G w ** a) /\
                a dot (G w ** a) <= &2 * (a dot a) /\
                (inv(norm w) - K * norm w) *
                (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2) <=
                cmp_lhess G (\z. norm z) w a a /\
                cmp_lhess G (\z. norm z) w a a <=
                (inv(norm w) + K * norm w) *
                (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "ray") THEN
  X_GEN_TAC `a:real^N` THEN
  ABBREV_TAC `t = norm(w:real^N)` THEN
  SUBGOAL_THEN `t % inv t % (w:real^N) = w` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `c:real^N = transp(P:real^N^N) ** a` THEN
  SUBGOAL_THEN `(c:real^N) dot c = (a:real^N) dot a` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    UNDISCH_TAC `orthogonal_matrix(P:real^N^N)` THEN
    SIMP_TAC[orthogonal_matrix; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N)$1 = inv t * ((w:real^N) dot a)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    MP_TAC(ISPECL [`transp(P:real^N^N) ** (a:real^N)`; `1`] DOT_BASIS) THEN
    REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    ASM_REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; DOT_RMUL] THEN MESON_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN ball(vec 0,rho) /\ ~(w = vec 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0; GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:real^N) dot ((G:real^N->real^N^N) w ** a) =
    (((A:real->real^N^N) t ** c) dot (A t ** c)) / t pow 2`
  ASSUME_TAC THENL
   [USE_THEN "ray" (MP_TAC o C MP (CONJ (ASSUME `&0 < t`) (ASSUME `t < rho`)) o
                    SPECL [`t:real`; `a:real^N`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at w` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `w:real^N`]
      LRG_METRIC_FIELD_DIFF) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a:real^N) dot (mderiv (G:real^N->real^N^N) w w ** a) =
    t * (&2 * (((B:real->real^N^N) t ** c) dot ((A:real->real^N^N) t ** c)) / t pow 2 -
         &2 * ((A t ** c) dot (A t ** c)) / t pow 3)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mderiv (G:real^N->real^N^N) w w = t %% mderiv G w (inv t % w)`
    SUBST1_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(MATCH_MP LRG_MDERIV_LINEAR th))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. (((A:real->real^N^N) s ** c) dot (A s ** (c:real^N))) / s pow 2` THEN
    EXISTS_TAC `t:real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      EXISTS_TAC `\s. (a:real^N) dot ((G:real^N->real^N^N)(s % inv t % w) ** a)` THEN
      EXISTS_TAC `min t (rho - t)` THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        USE_THEN "ray" (MP_TAC o SPECL [`s:real`; `a:real^N`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN
         `mderiv (G:real^N->real^N^N) w (inv t % w) =
          mderiv G (t % inv t % w) (inv t % w)`
        SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC CMPP_GDOT_RAY_DERIV THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CMPP_GRAM_RAY_DERIV THEN
      MAP_EVERY EXISTS_TAC [`R:real->real^N^N`; `rho:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `rho:real`; `K:real`; `c:real^N`; `t:real`] CMPP_RAY_GRAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `rho:real`; `K:real`; `c:real^N`; `t:real`] CMPP_RAY_HESS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `G:real^N->real^N^N`; `w:real^N`; `a:real^N`]
    CMPP_LHESS_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `X = ((A:real->real^N^N) t ** c) dot (A t ** (c:real^N))` THEN
  ABBREV_TAC `Y = ((B:real->real^N^N) t ** c) dot ((A:real->real^N^N) t ** (c:real^N))` THEN
  ABBREV_TAC `wa = (w:real^N) dot a` THEN
  SUBGOAL_THEN
   `(inv t * wa) pow 2 = wa pow 2 / t pow 2 /\
    (inv t * wa) pow 2 / t = wa pow 2 / t pow 3 /\
    (X / t pow 2) / t - wa pow 2 / t pow 3 +
    (t * (&2 * Y / t pow 2 - &2 * X / t pow 3)) / (&2 * t) =
    Y / t pow 2 - wa pow 2 / t pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(inv t * wa) pow 2 = wa pow 2 / t pow 2`;
                              ASSUME `(inv t * wa) pow 2 / t = wa pow 2 / t pow 3`]) THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The pullback metric G(w) = cmp_expmetric (top,atlas) g x E w              *)
(* pointwise: |sec| <= mfd_rm_norm, the differential of exp_x is linear and *)
(* a derivative, G(w) as a bilinear form, G(0) = I, symmetry, and the       *)
(* Gauss lemma G w w = w.                                                    *)
(* ========================================================================= *)

(* The sectional curvature is bounded by mfd_rm_norm (the same content as   *)
(* RFA_MFD_SECTIONAL_LE_NORM in pc_rfa_doubling, kept independent of the    *)
(* Ricci-flow layers).                                                       *)

let MFD_SECTIONAL_LE_RM_NORM = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ ~collinear {vec 0,u,v}
        ==> abs(mfd_sectional atlas g x u v) <= mfd_rm_norm atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN
  MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
   [EXISTS_TAC `sqrt(lrm_deriv_norm2 0
                  (metric_local atlas (chart_at atlas x) (g:A->real^N^N))
                  (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x))` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mfd_sectional] THEN MATCH_MP_TAC RFA_LSECTIONAL_LRM_BOUND THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
           CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    ASM_MESON_TAC[riemannian_metric];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN ASM_REWRITE_TAC[]]);;

(* exp_x maps its domain into the manifold. *)

let CMPP_EXP_IN_TOPSPACE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> mfd_exp (top,atlas) g x v IN topspace top`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_MESON_TAC[]);;

(* The differential of exp_x at v is the derivative of the chart            *)
(* representation in the preferred chart at exp_x v, and it is linear.     *)

let CMPP_EXP_DIFF = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> ((\y. SND(chart_at atlas (mfd_exp (top,atlas) g x v))
                     (mfd_exp (top,atlas) g x y)) has_derivative
             mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g x) v) (at v) /\
            linear(mfd_differential (open_set_atlas (:real^N)) atlas
                     (mfd_exp (top,atlas) g x) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x v IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_exp (top,atlas) (g:A->real^N^N) x v)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^N),(\y:real^N. y)) IN open_set_atlas (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^N),(\y:real^N. y))`; `c0:(A->bool)#(A->real^N)`;
                 `mfd_exp_dom (top,atlas) (g:A->real^N^N) x`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`((:real^N),(\y:real^N. y))`; `c0:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((A->bool)#(A->real^N))->bool)
                      W (f:real^N->A)`) (concl th))) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. SND (c0:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x y))
    differentiable (at v)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `(\y. SND (c0:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x y)) =
      SND c0 o mfd_exp (top,atlas) g x o chart_inv ((:real^N),(\y:real^N. y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y | y IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                     mfd_exp (top,atlas) g x y IN FST (c0:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR));;

let CMPP_DOT_TRANSP = prove
 (`!(A:real^N^N) x y. x dot (transp A ** y) = (A ** x) dot y`,
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL]);;

(* The tangent norm of E w is |w| for an orthonormal frame E. *)

let CMPP_TNORM_FRAME = prove
 (`!(g:A->real^N^N) x E w.
        mfd_orthonormal_frame g x E ==> mfd_tnorm g x (E ** w) = norm w`,
  REWRITE_TAC[mfd_orthonormal_frame; mfd_tnorm; vector_norm] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM CMPP_DOT_TRANSP; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;

(* The matrix cmp_dexp applied to h is the differential of exp_x at E w    *)
(* applied to E h.                                                          *)

let CMPP_DEXP_APPLY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w h.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> cmp_dexp (top,atlas) g x E w ** h =
            mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (E ** w) (E ** h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_dexp] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`] CMPP_EXP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear (\h. mfd_differential (open_set_atlas (:real^N)) atlas
                  (mfd_exp (top,atlas) (g:A->real^N^N) x) ((E:real^N^N) ** w) (E ** h))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\h. mfd_differential (open_set_atlas (:real^N)) atlas
             (mfd_exp (top,atlas) (g:A->real^N^N) x) ((E:real^N^N) ** w) (E ** h)) =
      mfd_differential (open_set_atlas (:real^N)) atlas
        (mfd_exp (top,atlas) g x) (E ** w) o (\h. E ** h)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

(* G(w) as a bilinear form. *)

let CMPP_EXPMETRIC_DOT = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> a dot (cmp_expmetric (top,atlas) g x E w ** b) =
            mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (E ** w) (E ** a) dot
            (g(mfd_exp (top,atlas) g x (E ** w)) **
             mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g x) (E ** w) (E ** b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_expmetric] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; CMPP_DOT_TRANSP] THEN
  ASM_SIMP_TAC[CMPP_DEXP_APPLY]);;

(* G(0) = I. *)

let CMPP_EXPMETRIC_ZERO = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E
        ==> cmp_expmetric (top,atlas) g x E (vec 0) = mat 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cmp_expmetric; cmp_dexp; MATRIX_VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ETA_AX; MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  ASM_MESON_TAC[mfd_orthonormal_frame]);;

(* G(w) is symmetric. *)

let CMPP_EXPMETRIC_SYM = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> transp(cmp_expmetric (top,atlas) g x E w) = cmp_expmetric (top,atlas) g x E w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp((g:A->real^N^N)(mfd_exp (top,atlas) g x ((E:real^N^N) ** w))) =
                g(mfd_exp (top,atlas) g x (E ** w))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`]
      RIEMANNIAN_METRIC_POS) THEN
    ASM_SIMP_TAC[CMPP_EXP_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_expmetric; MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC]);;

(* The Gauss lemma in the pullback: G(w) w = w. *)

let CMPP_EXPMETRIC_GAUSS = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> cmp_expmetric (top,atlas) g x E w ** w = w`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VECTOR_EQ_RDOT] THEN X_GEN_TAC `h:real^N` THEN
  SUBGOAL_THEN
   `transp(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w) =
    cmp_expmetric (top,atlas) g x E w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXPMETRIC_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w ** w) dot h =
    w dot (cmp_expmetric (top,atlas) g x E w ** h)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[CMPP_DOT_TRANSP];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMPP_EXPMETRIC_DOT] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`; `(E:real^N^N) ** h`]
    MFD_GAUSS_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM CMPP_DOT_TRANSP; MATRIX_VECTOR_MUL_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_orthonormal_frame]) THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]);;


(* ========================================================================= *)
(* Along the radial geodesic s |-> exp_x(s E u), |u| = 1: a                 *)
(* parallel orthonormal frame Fr with Fr_1 = gamma' and Fr(0) = E P, Jacobi *)
(* fields Y_j with Y_j(0) = 0, D Y_j(0) = F_j(0), Y_1 = t gamma', and the   *)
(* ray identity a.(G(s u) a) = |A(s) P^T a|^2 / s^2 for the Jacobi matrix   *)
(* A of the Y_j in the frame Fr, given the ray form of d exp.               *)
(* ========================================================================= *)

(* Points of the radial segment. *)

let CMPP_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) u rho.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x
        ==> !s. abs s * norm u < rho
                ==> E ** (s % u) = s % (E ** u) /\
                    s % (E ** u) IN mfd_exp_dom (top,atlas) g x /\
                    s IN mfd_geo_maxint (top,atlas) g x (E ** u) /\
                    mfd_exp (top,atlas) g x (s % (E ** u)) =
                    mfd_geo (top,atlas) g x (E ** u) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN
  SUBGOAL_THEN `s % ((E:real^N^N) ** u) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_RMUL] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
                check (is_binary "SUBSET" o concl)) THEN
    ASM_SIMP_TAC[mfd_tball; IN_ELIM_THM; CMPP_TNORM_FRAME; NORM_MUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`; `s:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* A parallel orthonormal frame along the radial geodesic with Fr_1 = gamma' *)
(* and Fr(0) = E P (P orthogonal with P e1 = u).                            *)

let CMPP_FRAME_ALONG = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) (P:real^N^N) u.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ orthogonal_matrix P /\ P ** basis 1 = u
        ==> ?Fr. cmp_pframe atlas g (mfd_geo (top,atlas) g x (E ** u))
                          (mfd_geo_maxint (top,atlas) g x (E ** u)) Fr /\
                (!t. t IN mfd_geo_maxint (top,atlas) g x (E ** u)
                     ==> Fr 1 t = mfd_vel atlas (mfd_geo (top,atlas) g x (E ** u)) t) /\
                cmp_fmat Fr (&0) = E ** P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ABBREV_TAC `J0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `cmp_curve_on (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) J0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPF_GEODESIC_CURVE_ON THEN EXISTS_TAC `g:A->real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_curve_on]) THEN
  SUBGOAL_THEN
   `!j. ?Y. mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) J0 Y /\
            Y (&0) = column j ((E:real^N^N) ** (P:real^N^N)) /\
            !Y'. mfd_parallel atlas g gamma J0 Y' /\ Y' (&0) = column j (E ** P)
                 ==> !t. t IN J0 ==> Y' t = Y t`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFD_PARALLEL_EXISTS_UNIQUE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` (LABEL_TAC "F")) THEN
  EXISTS_TAC `Fr:num->real->real^N` THEN
  SUBGOAL_THEN `cmp_fmat (Fr:num->real->real^N) (&0) = (E:real^N^N) ** (P:real^N^N)`
  ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "F" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC `j:num` th))]) THEN
    ASM_SIMP_TAC[column; LAMBDA_BETA];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPF_PFRAME_FROM_POINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `&0`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `transp((E:real^N^N) ** (P:real^N^N)) ** (g:A->real^N^N) x ** (E ** P) =
      transp P ** (transp E ** g x ** E) ** P`
    SUBST1_TAC THENL [REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_orthonormal_frame; orthogonal_matrix]) THEN
    ASM_REWRITE_TAC[MATRIX_MUL_LID];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  USE_THEN "F" (MP_TAC o SPEC `1`) THEN
  DISCH_THEN(MP_TAC o SPEC `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)` o
             CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_GEODESIC_VEL_PARALLEL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[GSYM MATRIX_VECTOR_MUL_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
      ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC]];
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]]);;

(* Jacobi fields Y_j with Y_j(0) = 0, D Y_j(0) = Fr_j(0) and Y_1 = t gamma'. *)

let CMPP_JACOBI_ALONG = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ &0 IN J /\
        (!t. t IN J ==> Fr 1 t = mfd_vel atlas gamma t)
        ==> ?Y. (!j. 1 <= j /\ j <= dimindex(:N) ==> mfd_jacobi atlas g gamma J (Y j)) /\
                (!j. 1 <= j /\ j <= dimindex(:N)
                     ==> Y j (&0) = vec 0 /\
                         mfd_covd atlas g gamma (Y j) (&0) = Fr j (&0)) /\
                (!t. t IN J ==> Y 1 t = t % mfd_vel atlas gamma t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. ?Z. mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) J Z /\
            Z (&0) = vec 0 /\
            mfd_covd atlas g gamma Z (&0) = (Fr:num->real->real^N) j (&0)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `&0`;
                   `vec 0:real^N`; `(Fr:num->real->real^N) j (&0)`]
      MFD_JACOBI_EXISTS_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Z:num->real->real^N`) THEN
  EXISTS_TAC `\j. if j = 1 then (\t. t % mfd_vel atlas (gamma:real->A) t)
                  else (Z:num->real->real^N) j` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) J (\t. t % mfd_vel atlas gamma t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `&0`; `&1`]
      MFD_JACOBI_TANGENTIAL) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\t. t % mfd_vel atlas gamma t) (&0) =
    mfd_vel atlas gamma (&0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPJ_COVD_RADIAL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]);;

(* The ray identity: the quadratic form of the pullback metric at s u is     *)
(* |A(s) P^T a|^2 / s^2, given d exp at s E u on the frame vectors.          *)

let CMPP_RAY_IDENTITY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) (P:real^N^N) u
    (Fr:num->real->real^N) (Y:num->real->real^N) rho s a.
        (!j. 1 <= j /\ j <= dimindex(:N)
             ==> mfd_differential (open_set_atlas (:real^N)) atlas
                   (mfd_exp (top,atlas) g x) (s % (E ** u)) (s % Fr j (&0)) = Y j s) /\
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ orthogonal_matrix P /\ norm u = &1 /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        cmp_pframe atlas g (mfd_geo (top,atlas) g x (E ** u))
                   (mfd_geo_maxint (top,atlas) g x (E ** u)) Fr /\
        cmp_fmat Fr (&0) = E ** P /\
        &0 < s /\ s < rho
        ==> a dot (cmp_expmetric (top,atlas) g x E (s % u) ** a) =
            ((cmp_fmat (\j. cmp_fcoord g (mfd_geo (top,atlas) g x (E ** u)) Fr (Y j)) s **
              (transp P ** a)) dot
             (cmp_fmat (\j. cmp_fcoord g (mfd_geo (top,atlas) g x (E ** u)) Fr (Y j)) s **
              (transp P ** a))) / s pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dexp") STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ABBREV_TAC `J0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `s % (u:real^N)`; `a:real^N`;
                 `a:real^N`] CMPP_EXPMETRIC_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `linear(mfd_differential (open_set_atlas (:real^N)) atlas
             (mfd_exp (top,atlas) (g:A->real^N^N) x) (s % ((E:real^N^N) ** u)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `s % ((E:real^N^N) ** u)`] CMPP_EXP_DIFF) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = mfd_differential (open_set_atlas (:real^N)) atlas
          (mfd_exp (top,atlas) (g:A->real^N^N) x) (s % ((E:real^N^N) ** u))` THEN
  ABBREV_TAC `c:real^N = transp(P:real^N^N) ** a` THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** a =
    vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Fr:num->real->real^N) j (&0))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CMPF_FMAT_MUL] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN
    UNDISCH_TAC `orthogonal_matrix(P:real^N^N)` THEN
    SIMP_TAC[orthogonal_matrix; MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(D:real^N->real^N) ((E:real^N^N) ** a) =
    inv s % vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j s)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LINEAR_VSUM_MUL; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM VSUM_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(Y:num->real->real^N) j s = s % (D:real^N->real^N) ((Fr:num->real->real^N) j (&0))`
    SUBST1_TAC THENL
     [USE_THEN "dexp" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `j:num` th)
        (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`)))]) THEN
      MATCH_MP_TAC LINEAR_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J0:real->bool`; `Fr:num->real->real^N`;
                 `\r. vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j r)`;
                 `\r. vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j r)`;
                 `s:real`] CMPF_FCOORD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `cmp_fcoord (g:A->real^N^N) (gamma:real->A) (Fr:num->real->real^N)
      (\r. vsum(1..dimindex(:N)) (\j. (c:real^N)$j % (Y:num->real->real^N) j r)) s =
    cmp_fmat (\j. cmp_fcoord g gamma Fr (Y j)) s ** c`
  SUBST1_TAC THENL
   [REWRITE_TAC[cmp_fcoord; CMPF_FMAT_MUL; CMPF_MATVEC_VSUM; MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;


(* ========================================================================= *)
(* The radial geodesic stays in the ball B(x,rho), so the                    *)
(* curvature matrix of the frame satisfies |sec| <= K on normal vectors.    *)
(* ========================================================================= *)

let CMPP_RAY_IN_BALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) u rho s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ norm u = &1 /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\ abs s < rho
        ==> mfd_geo (top,atlas) g x (E ** u) s IN mfd_ball (top,atlas) g x rho`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x (s % ((E:real^N^N) ** u)) = abs s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `E:real^N^N`; `s % (u:real^N)`]
      CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `s % ((E:real^N^N) ** u)`]
    GEOD_RADIAL_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
                check (is_binary "SUBSET" o concl)) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs s` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN
    EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) x (s % ((E:real^N^N) ** u))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^N^N)
                  (mfd_geo (top,atlas) g x (s % ((E:real^N^N) ** u))) (&0) (&1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) x (s % ((E:real^N^N) ** u))`;
                     `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* |sec| <= K along the ray, in the frame form used by pc_cmp_jcomp. *)

let CMPP_RAY_SEC = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) u rho K (Fr:num->real->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ norm u = &1 /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K) /\
        cmp_pframe atlas g (mfd_geo (top,atlas) g x (E ** u))
                   (mfd_geo_maxint (top,atlas) g x (E ** u)) Fr /\
        (!t. t IN mfd_geo_maxint (top,atlas) g x (E ** u)
             ==> Fr 1 t = mfd_vel atlas (mfd_geo (top,atlas) g x (E ** u)) t)
        ==> !t v. &0 <= t /\ t < rho /\ v$1 = &0
                  ==> v dot (cmp_rmat atlas g (mfd_geo (top,atlas) g x (E ** u)) Fr t ** v)
                      <= K * (v dot v) /\
                      --K * (v dot v) <=
                      v dot (cmp_rmat atlas g (mfd_geo (top,atlas) g x (E ** u)) Fr t ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ABBREV_TAC `J0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)` THEN
  ASM_CASES_TAC `v:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; DOT_RZERO; REAL_MUL_RZERO;
                  REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN mfd_ball (top,atlas) (g:A->real^N^N) x rho`
  ASSUME_TAC THENL
   [EXPAND_TAC "gamma" THEN MATCH_MP_TAC CMPP_RAY_IN_BALL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J0:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J0:real->bool`;
                 `Fr:num->real->real^N`; `v:real^N`; `t:real`] CMPJ_FRAME_SEC) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`;
                 `cmp_fmat (Fr:num->real->real^N) t ** (v:real^N)`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    MFD_SECTIONAL_LE_RM_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_rm_norm atlas (g:A->real^N^N) ((gamma:real->A) t) <= K` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sc = mfd_sectional atlas (g:A->real^N^N) ((gamma:real->A) t)
                     (cmp_fmat (Fr:num->real->real^N) t ** (v:real^N))
                     (mfd_vel atlas gamma t)` THEN
  SUBGOAL_THEN `&0 <= (v:real^N) dot v` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Smoothness of G(w) = cmp_expmetric (top,atlas) g x E w on                 *)
(* the set of w with E w in the domain of exp_x: near w0, in a chart c near  *)
(* exp_x(E w0), G is the pullback by h(w) = SND c (exp_x(E w)) of the local  *)
(* metric of g in c (GEOC_BILIN_CHART and the chain rule).                   *)
(* ========================================================================= *)

let CMPP_MATRIX_EQ_DOT = prove
 (`!A B:real^N^N. (!a b. a dot (A ** b) = a dot (B ** b)) ==> A = B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `b:real^N` THEN
  REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN ASM_REWRITE_TAC[]);;

(* The set of v in the domain of exp_x mapped into a chart is open. *)

let CMPP_EXP_CHART_OPEN = prove
 (`!top atlas (g:A->real^N^N) (x:A) (c:(A->bool)#(A->real^N)).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ c IN atlas
        ==> open {v | v IN mfd_exp_dom (top,atlas) g x /\
                      mfd_exp (top,atlas) g x v IN FST c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^N),(\y:real^N. y)) IN open_set_atlas (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^N),(\y:real^N. y))`; `c:(A->bool)#(A->real^N)`;
                 `mfd_exp_dom (top,atlas) (g:A->real^N^N) x`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN SIMP_TAC[]);;

(* The chart representation of exp_x in any chart c, and its derivative. *)

let CMPP_EXP_CHART_DERIV = prove
 (`!top atlas (g:A->real^N^N) (x:A) v (c:(A->bool)#(A->real^N)).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\ c IN atlas /\
        mfd_exp (top,atlas) g x v IN FST c
        ==> ((\y. SND c (mfd_exp (top,atlas) g x y)) has_derivative
             (\h. chart_jac (chart_at atlas (mfd_exp (top,atlas) g x v)) c
                    (mfd_exp (top,atlas) g x v)
                    (mfd_differential (open_set_atlas (:real^N)) atlas
                       (mfd_exp (top,atlas) g x) v h))) (at v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPP_EXP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x v IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) (g:A->real^N^N) x) v` THEN
  ABBREV_TAC `p = mfd_exp (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `chart_trans (c0:(A->bool)#(A->real^N)) c o
              (\y. SND c0 (mfd_exp (top,atlas) (g:A->real^N^N) x y))` THEN
  EXISTS_TAC `{y | y IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                   mfd_exp (top,atlas) g x y IN FST (c0:(A->bool)#(A->real^N))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_CHART_OPEN THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. chart_jac (c0:(A->bool)#(A->real^N)) c (p:A) ((D:real^N->real^N) h)) =
    chart_jac c0 c p o D`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]);;

(* In a chart c around exp_x(E w), G is the pullback of the local metric. *)

let CMPP_EXPMETRIC_LOCAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) (c:(A->bool)#(A->real^N)) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ c IN atlas /\
        E ** w IN mfd_exp_dom (top,atlas) g x /\
        mfd_exp (top,atlas) g x (E ** w) IN FST c
        ==> cmp_expmetric (top,atlas) g x E w =
            mpullback (\w. SND c (mfd_exp (top,atlas) g x (E ** w)))
                      (metric_local atlas c g) w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_SIMP_TAC[CMPP_EXPMETRIC_DOT] THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) (g:A->real^N^N) x) ((E:real^N^N) ** w)` THEN
  ABBREV_TAC `p = mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)` THEN
  SUBGOAL_THEN
   `((\w. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x
            ((E:real^N^N) ** w))) has_derivative
     (\h. chart_jac (chart_at atlas (p:A)) c p ((D:real^N->real^N) (E ** h)))) (at w)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x
              ((E:real^N^N) ** w))) =
      (\y. SND c (mfd_exp (top,atlas) g x y)) o (\w. E ** w)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\h. chart_jac (chart_at atlas (p:A)) (c:(A->bool)#(A->real^N)) p
             ((D:real^N->real^N) ((E:real^N^N) ** h))) =
      (\h. chart_jac (chart_at atlas p) c p (D h)) o (\h. E ** h)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      MAP_EVERY EXPAND_TAC ["p"; "D"] THEN MATCH_MP_TAC CMPP_EXP_CHART_DERIV THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LRG_HAS_DERIVATIVE_IMP_LINEAR) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `p:A`;
                 `(D:real^N->real^N) ((E:real^N^N) ** a)`;
                 `(D:real^N->real^N) ((E:real^N^N) ** b)`] GEOC_BILIN_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

(* G is smooth wherever E w is in the domain of exp_x. *)

let CMPP_EXPMETRIC_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> open {w | E ** w IN mfd_exp_dom (top,atlas) g x} /\
            smooth_map_on {w | E ** w IN mfd_exp_dom (top,atlas) g x}
              ((vectorize:real^N^N->real^(N,N)finite_prod) o
               cmp_expmetric (top,atlas) g x E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. open s ==> open {w | (E:real^N^N) ** w IN s}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `w0:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w0) IN topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w0)`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w0))` THEN
  STRIP_TAC THEN
  ABBREV_TAC `V = {v | v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                       mfd_exp (top,atlas) g x v IN FST (c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (V:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC CMPP_EXP_CHART_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{w | (E:real^N^N) ** w IN V}` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `h = \w. SND (c:(A->bool)#(A->real^N))
                       (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w))` THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o
              mpullback (h:real^N->real^N) (metric_local atlas c (g:A->real^N^N))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    STRIP_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "h" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMPP_EXPMETRIC_LOCAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {w | (E:real^N^N) ** w IN V} (h:real^N->real^N)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(h:real^N->real^N) =
      (\v. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x v)) o
      (\w. (E:real^N^N) ** w)`
    SUBST1_TAC THENL [EXPAND_TAC "h" THEN REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
      MP_TAC(ISPECL [`{w | (E:real^N^N) ** w IN V}`; `\x:real^N. x`;
                     `\w. (E:real^N^N) ** w`] SMOOTH_MAP_ON_LINEAR_O) THEN
      REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR] THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `mfd_exp (top,atlas) (g:A->real^N^N) x`;
                     `mfd_exp_dom (top,atlas) (g:A->real^N^N) x`;
                     `c:(A->bool)#(A->real^N)`] GEOP_CHART_REP) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  REWRITE_TAC[LRG_MPULLBACK_EQ] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_TRANSP THEN ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN];
    MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
             ((h:real^N->real^N) z)) =
      (vectorize o metric_local atlas c g) o h`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^N` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Assembly of S4 (CMP_EXP_PULLBACK_STATEMENT of pc_cmp_defs).               *)
(* For 0 < |w| < rho the ray data at w come from an orthogonal P with       *)
(* P e1 = w/|w|, the frame and Jacobi fields of CMPP_FRAME_ALONG and         *)
(* CMPP_JACOBI_ALONG and d exp along the ray                                 *)
(* (MFD_EXP_DIFFERENTIAL_JACOBI_RAY, pc_geo_jvar); then pc_cmp_jcomp's       *)
(* comparisons give the factor-2 bounds, G is a metric field, and            *)
(* CMPP_PULLBACK_CORE gives the Hessian bounds.                              *)
(* ========================================================================= *)

let CMPP_RAY_DATA = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t v. &0 <= t /\ t < rho /\ v$1 = &0
                     ==> v dot (R t ** v) <= K * (v dot v)) /\
              (!t v. &0 <= t /\ t < rho /\ v$1 = &0
                     ==> --K * (v dot v) <= v dot (R t ** v)) /\
              (!s a. &0 < s /\ s < rho
                     ==> a dot (cmp_expmetric (top,atlas) g x E (s % inv(norm w) % w) ** a) =
                         ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u:real^N = inv(norm w) % w` THEN
  SUBGOAL_THEN `norm(u:real^N) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `?P:real^N^N. orthogonal_matrix P /\ P ** basis 1 = u` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^N`; `u:real^N`] ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX];
    ALL_TAC] THEN
  EXISTS_TAC `P:real^N^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `P:real^N^N`; `u:real^N`]
    CMPP_FRAME_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `Fr:num->real->real^N`] CMPP_JACOBI_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(LABEL_TAC "rad") THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                ((Y:num->real->real^N) j))` THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                (mfd_covd atlas g (mfd_geo (top,atlas) g x (E ** u))
                   ((Y:num->real->real^N) j)))` THEN
  EXISTS_TAC `cmp_rmat atlas (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_FRAME_JSYS THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`;
      `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`;
                   `K:real`; `Fr:num->real->real^N`] CMPP_RAY_SEC) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`;
                   `K:real`; `Fr:num->real->real^N`] CMPP_RAY_SEC) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPP_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* E w is in the domain of exp_x on the ball of radius rho. *)

let CMPP_BALL_IN_DOM = prove
 (`!(g:A->real^N^N) (x:A) (E:real^N^N) dom rho w.
        mfd_orthonormal_frame g x E /\ mfd_tball g x rho SUBSET dom /\ norm w < rho
        ==> E ** w IN dom`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_SIMP_TAC[mfd_tball; IN_ELIM_THM; CMPP_TNORM_FRAME]);;

(* The factor-2 bounds of G on the ball. *)

let CMPP_GRAM_BOUND = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w a.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < rho /\ K * rho pow 2 <= &1 /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K) /\
        norm w < rho
        ==> inv(&2) * (a dot a) <= a dot (cmp_expmetric (top,atlas) g x E w ** a) /\
            a dot (cmp_expmetric (top,atlas) g x E w ** a) <= &2 * (a dot a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_SIMP_TAC[CMPP_EXPMETRIC_ZERO; MATRIX_VECTOR_MUL_LID] THEN
    MP_TAC(ISPEC `a:real^N` DOT_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `w:real^N`]
    CMPP_RAY_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` (X_CHOOSE_THEN `A:real->real^N^N`
    (X_CHOOSE_THEN `B:real->real^N^N` (X_CHOOSE_THEN `R:real->real^N^N`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(LABEL_TAC "ray") THEN
  USE_THEN "ray" (MP_TAC o
    C MP (CONJ (ASSUME `&0 < norm(w:real^N)`) (ASSUME `norm(w:real^N) < rho`)) o
    SPECL [`norm(w:real^N)`; `a:real^N`]) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(transp(P:real^N^N) ** a) dot (transp P ** a) = (a:real^N) dot a`
  (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    UNDISCH_TAC `orthogonal_matrix(P:real^N^N)` THEN
    SIMP_TAC[orthogonal_matrix; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPP_RAY_GRAM THEN
  MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `R:real->real^N^N`; `rho:real`; `K:real`] THEN
  ASM_REWRITE_TAC[]);;

(* G is a metric field on the ball. *)

let CMPP_METRIC_FIELD = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < rho /\ K * rho pow 2 <= &1 /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K)
        ==> metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) g x E)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field; OPEN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{w | (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL_0; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
      MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `rho:real`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `E:real^N^N`] CMPP_EXPMETRIC_SMOOTH) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPP_EXPMETRIC_SYM THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `rho:real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                   `y:real^N`; `v:real^N`] CMPP_GRAM_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (v:real^N) dot v` MP_TAC THENL
     [ASM_REWRITE_TAC[DOT_POS_LT]; REAL_ARITH_TAC]]);;

(* S4, the exp_x pullback metric on a tangent ball. *)

let CMP_EXP_PULLBACK = prove
 (`!(u:A->bool) (n:N->bool). CMP_EXP_PULLBACK_STATEMENT u n`,
  REWRITE_TAC[CMP_EXP_PULLBACK_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. norm w < rho
        ==> (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) (g:A->real^N^N) x E)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_METRIC_FIELD THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. norm w < rho
        ==> cmp_expmetric (top,atlas) (g:A->real^N^N) x E w ** w = w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_EXPMETRIC_GAUSS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CMPP_EXPMETRIC_ZERO] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMPP_GRAM_BOUND THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `a:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `w:real^N`]
    CMPP_RAY_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` (X_CHOOSE_THEN `A:real->real^N^N`
    (X_CHOOSE_THEN `B:real->real^N^N` (X_CHOOSE_THEN `R:real->real^N^N`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`cmp_expmetric (top,atlas) (g:A->real^N^N) x E`; `rho:real`; `K:real`;
                 `w:real^N`; `P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                 `R:real->real^N^N`] CMPP_PULLBACK_CORE) THEN
  ASM_SIMP_TAC[IN_BALL_0]);;

