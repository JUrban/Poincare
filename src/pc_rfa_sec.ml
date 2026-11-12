(* ========================================================================= *)
(* Unit pc_rfa_sec: sectional curvature versus the tensor norm of Rm: every  *)
(* sectional curvature is bounded by |Rm|, and |Rm|^2 <= C K^2 when all      *)
(* sectional curvatures are bounded by K in absolute value.                  *)
(* ========================================================================= *)

needs "src/pc_lrg_constcurv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Polarization for algebraic curvature tensors.  With                       *)
(* R(a,b,c,d) antisymmetric in (a,b) and in (c,d), pair symmetric and with  *)
(* the first Bianchi identity in (a,b,c), R is determined by the            *)
(* biquadratic form Q(x,y) = R(x,y,y,x), with explicit bounds.              *)
(* ========================================================================= *)

let RFA_POLAR_T = prove
 (`!R:real^N->real^N->real^N->real^N->real.
     (!a b b' c d. R a (b + b') c d = R a b c d + R a b' c d) /\
     (!a b c c' d. R a b (c + c') d = R a b c d + R a b c' d) /\
     (!a b c d. R b a c d = --(R a b c d)) /\
     (!a b c d. R a b d c = --(R a b c d)) /\
     (!a b c d. R c d a b = R a b c d)
     ==> !a b c. &2 * R a b c a = R a (b + c) (b + c) a - R a b b a - R a c c a`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "add2") (CONJUNCTS_THEN2 (LABEL_TAC "add3")
    (CONJUNCTS_THEN2 (LABEL_TAC "a12") (CONJUNCTS_THEN2 (LABEL_TAC "a34")
     (LABEL_TAC "pair"))))) THEN
  REPEAT GEN_TAC THEN
  USE_THEN "add2" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "add3" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "pair" (MP_TAC o SPECL [`b:real^N`; `a:real^N`; `a:real^N`; `c:real^N`]) THEN
  USE_THEN "a12" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `a:real^N`; `c:real^N`]) THEN
  USE_THEN "a34" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real^N`; `a:real^N`]) THEN
  REAL_ARITH_TAC);;

let RFA_POLAR_S = prove
 (`!R:real^N->real^N->real^N->real^N->real.
     (!a a' b c d. R (a + a') b c d = R a b c d + R a' b c d) /\
     (!a b c d d'. R a b c (d + d') = R a b c d + R a b c d')
     ==> !a b c d. R a b c d + R d b c a =
                   R (a + d) b c (a + d) - R a b c a - R d b c d`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "add1") (LABEL_TAC "add4")) THEN
  REPEAT GEN_TAC THEN USE_THEN "add1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "add4" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let RFA_POLAR_3 = prove
 (`!R:real^N->real^N->real^N->real^N->real.
     (!a b c d. R b a c d = --(R a b c d)) /\
     (!a b c d. R a b d c = --(R a b c d)) /\
     (!a b c d. R c d a b = R a b c d) /\
     (!a b c d. R a b c d + R b c a d + R c a b d = &0)
     ==> !a b c d. &3 * R a b c d = (R a b c d + R d b c a) - (R b a c d + R d a c b)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a12") (CONJUNCTS_THEN2 (LABEL_TAC "a34")
    (CONJUNCTS_THEN2 (LABEL_TAC "pair") (LABEL_TAC "bian")))) THEN
  REPEAT GEN_TAC THEN
  USE_THEN "pair" (MP_TAC o SPECL [`c:real^N`; `a:real^N`; `d:real^N`; `b:real^N`]) THEN
  USE_THEN "a12" (MP_TAC o SPECL [`a:real^N`; `c:real^N`; `d:real^N`; `b:real^N`]) THEN
  USE_THEN "a34" (MP_TAC o SPECL [`a:real^N`; `c:real^N`; `b:real^N`; `d:real^N`]) THEN
  USE_THEN "a12" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`]) THEN
  USE_THEN "pair" (MP_TAC o SPECL [`c:real^N`; `b:real^N`; `d:real^N`; `a:real^N`]) THEN
  USE_THEN "a12" (MP_TAC o SPECL [`b:real^N`; `c:real^N`; `d:real^N`; `a:real^N`]) THEN
  USE_THEN "a34" (MP_TAC o SPECL [`b:real^N`; `c:real^N`; `a:real^N`; `d:real^N`]) THEN
  USE_THEN "bian" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`]) THEN
  USE_THEN "a12" (MP_TAC o SPECL [`a:real^N`; `c:real^N`; `b:real^N`; `d:real^N`]) THEN
  REAL_ARITH_TAC);;

let RFA_POLAR_BOUND = prove
 (`!R:real^N->real^N->real^N->real^N->real nn k a b c d.
     (!a a' b c d. R (a + a') b c d = R a b c d + R a' b c d) /\
     (!a b b' c d. R a (b + b') c d = R a b c d + R a b' c d) /\
     (!a b c c' d. R a b (c + c') d = R a b c d + R a b c' d) /\
     (!a b c d d'. R a b c (d + d') = R a b c d + R a b c d') /\
     (!a b c d. R b a c d = --(R a b c d)) /\
     (!a b c d. R a b d c = --(R a b c d)) /\
     (!a b c d. R c d a b = R a b c d) /\
     (!a b c d. R a b c d + R b c a d + R c a b d = &0) /\
     &0 <= k /\ (!x. &0 <= nn x) /\
     (!x y. abs(R x y y x) <= k * nn x * nn y) /\
     nn a <= &4 /\ nn b <= &4 /\ nn c <= &4 /\ nn d <= &4 /\
     nn(a + d) <= &4 /\ nn(b + c) <= &4 /\ nn(b + d) <= &4 /\ nn(a + c) <= &4
     ==> abs(R a b c d) <= &48 * k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["add1";"add2";"add3";"add4";"a12";"a34";"pair";"bian";"k0";"nn0";"qb";
          "na";"nb";"nc";"nd";"nad";"nbc";"nbd";"nac"] (CONJUNCTS th))) THEN
  MP_TAC(SPEC `R:real^N->real^N->real^N->real^N->real` RFA_POLAR_T) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "T")] THEN
  MP_TAC(SPEC `R:real^N->real^N->real^N->real^N->real` RFA_POLAR_S) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "S")] THEN
  MP_TAC(SPEC `R:real^N->real^N->real^N->real^N->real` RFA_POLAR_3) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "3")] THEN
  MAP_EVERY (fun s -> REMOVE_THEN s (K ALL_TAC))
   ["add1";"add2";"add3";"add4";"a12";"a34";"pair";"bian"] THEN
  SUBGOAL_THEN
   `!x y. (nn:real^N->real) x <= &4 /\ nn y <= &4
          ==> abs((R:real^N->real^N->real^N->real^N->real) x y y x) <= &16 * k`
  (LABEL_TAC "QB") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(nn:real^N->real) x * nn y <= &4 * &4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `k * (nn:real^N->real) x * nn y <= k * (&4 * &4)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "qb" (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    UNDISCH_TAC `k * (nn:real^N->real) x * nn y <= k * (&4 * &4)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x p q. (nn:real^N->real) x <= &4 /\ nn p <= &4 /\ nn q <= &4 /\ nn(p + q) <= &4
            ==> abs(&2 * (R:real^N->real^N->real^N->real^N->real) x p q x) <= &48 * k`
  (LABEL_TAC "TB") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `p:real^N`; `q:real^N`] THEN STRIP_TAC THEN
    USE_THEN "T" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "QB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (x:real^N) <= &4`) (ASSUME `(nn:real^N->real) (p + q:real^N) <= &4`)))) THEN
    USE_THEN "QB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (x:real^N) <= &4`) (ASSUME `(nn:real^N->real) (p:real^N) <= &4`)))) THEN
    USE_THEN "QB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (x:real^N) <= &4`) (ASSUME `(nn:real^N->real) (q:real^N) <= &4`)))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(&2 * ((R:real^N->real^N->real^N->real^N->real) a b c d + R d b c a)) <=
    &144 * k`
  ASSUME_TAC THENL
   [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "TB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (a + d:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (b:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (c:real^N) <= &4`) (ASSUME `(nn:real^N->real) (b + c:real^N) <= &4`)))))) THEN
    USE_THEN "TB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (a:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (b:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (c:real^N) <= &4`) (ASSUME `(nn:real^N->real) (b + c:real^N) <= &4`)))))) THEN
    USE_THEN "TB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (d:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (b:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (c:real^N) <= &4`) (ASSUME `(nn:real^N->real) (b + c:real^N) <= &4`)))))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(&2 * ((R:real^N->real^N->real^N->real^N->real) b a c d + R d a c b)) <=
    &144 * k`
  ASSUME_TAC THENL
   [USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "TB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (b + d:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (a:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (c:real^N) <= &4`) (ASSUME `(nn:real^N->real) (a + c:real^N) <= &4`)))))) THEN
    USE_THEN "TB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (b:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (a:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (c:real^N) <= &4`) (ASSUME `(nn:real^N->real) (a + c:real^N) <= &4`)))))) THEN
    USE_THEN "TB" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(nn:real^N->real) (d:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (a:real^N) <= &4`) (CONJ (ASSUME `(nn:real^N->real) (c:real^N) <= &4`) (ASSUME `(nn:real^N->real) (a + c:real^N) <= &4`)))))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "3" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`]) THEN
  UNDISCH_TAC
   `abs(&2 * ((R:real^N->real^N->real^N->real^N->real) a b c d + R d b c a)) <=
    &144 * k` THEN
  UNDISCH_TAC
   `abs(&2 * ((R:real^N->real^N->real^N->real^N->real) b a c d + R d a c b)) <=
    &144 * k` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The curvature form (a,b,c,d) |-> <R(a,b)c, d> is an                       *)
(* algebraic curvature tensor; the Gram determinant of two independent      *)
(* vectors is positive; the biquadratic form is bounded by the sectional     *)
(* curvatures.                                                               *)
(* ========================================================================= *)

let RFA_LRIEMANN_ALGEBRAIC = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> (!a a' b c d. d dot (G y ** lriemann G y (a + a') b c) =
                       d dot (G y ** lriemann G y a b c) +
                       d dot (G y ** lriemann G y a' b c)) /\
         (!a b b' c d. d dot (G y ** lriemann G y a (b + b') c) =
                       d dot (G y ** lriemann G y a b c) +
                       d dot (G y ** lriemann G y a b' c)) /\
         (!a b c c' d. d dot (G y ** lriemann G y a b (c + c')) =
                       d dot (G y ** lriemann G y a b c) +
                       d dot (G y ** lriemann G y a b c')) /\
         (!a b c d d'. (d + d') dot (G y ** lriemann G y a b c) =
                       d dot (G y ** lriemann G y a b c) +
                       d' dot (G y ** lriemann G y a b c)) /\
         (!a b c d. d dot (G y ** lriemann G y b a c) =
                    --(d dot (G y ** lriemann G y a b c))) /\
         (!a b c d. c dot (G y ** lriemann G y a b d) =
                    --(d dot (G y ** lriemann G y a b c))) /\
         (!a b c d. b dot (G y ** lriemann G y c d a) =
                    d dot (G y ** lriemann G y a b c)) /\
         (!a b c d. d dot (G y ** lriemann G y a b c) +
                    d dot (G y ** lriemann G y b c a) +
                    d dot (G y ** lriemann G y c a b) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1")
    (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "l3"))) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "l1" (MP_TAC o MATCH_MP LINEAR_ADD o SPECL [`b:real^N`; `c:real^N`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD];
    REPEAT GEN_TAC THEN
    USE_THEN "l2" (MP_TAC o MATCH_MP LINEAR_ADD o SPECL [`a:real^N`; `c:real^N`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD];
    REPEAT GEN_TAC THEN
    USE_THEN "l3" (MP_TAC o MATCH_MP LINEAR_ADD o SPECL [`a:real^N`; `b:real^N`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_RADD];
    REWRITE_TAC[DOT_LADD];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `a:real^N`; `b:real^N`; `c:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `a:real^N`; `b:real^N`; `d:real^N`; `c:real^N`]
           LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`]
           LRIEMANN_PAIR_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `c:real^N`; `d:real^N`; `b:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `c:real^N`; `d:real^N`; `b:real^N`; `a:real^N`]
           LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `a:real^N`; `b:real^N`; `c:real^N`] LRIEMANN_BIANCHI1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM DOT_RADD; GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]]);;

(* ========================================================================= *)
(* The biquadratic form is bounded by the sectional curvatures,              *)
(* an orthonormal frame from a factorisation of G^-1, and the curvature      *)
(* form is bounded on that frame.                                             *)
(* ========================================================================= *)

let RFA_METRIC_QPOS = prove
 (`!U (G:real^N->real^N^N) y x.
        metric_field U G /\ y IN U ==> &0 <= x dot (G y ** x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[metric_field]);;

let RFA_LRIEMANN_SELF = prove
 (`!U (G:real^N->real^N^N) y x w.
        metric_field U G /\ y IN U ==> lriemann G y x x w = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `x:real^N`; `x:real^N`; `w:real^N`] LRIEMANN_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let RFA_Q_BOUND = prove
 (`!U (G:real^N->real^N^N) y K.
        metric_field U G /\ y IN U /\
        (!u v. ~collinear {vec 0,u,v} ==> abs(lsectional G y u v) <= K)
        ==> !x z. abs(x dot (G y ** lriemann G y x z z)) <=
                  abs K * (x dot (G y ** x)) * (z dot (G y ** z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `z:real^N`] THEN
  SUBGOAL_THEN `&0 <= x dot ((G:real^N->real^N^N) y ** x) /\ &0 <= z dot (G y ** z)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[RFA_METRIC_QPOS]; ALL_TAC] THEN
  ASM_CASES_TAC `collinear {vec 0:real^N,x,z}` THENL
   [SUBGOAL_THEN `x dot ((G:real^N->real^N^N) y ** lriemann G y x z z) = &0`
    SUBST1_TAC THENL
     [UNDISCH_TAC `collinear {vec 0:real^N,x,z}` THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
      STRIP_TAC THENL
       [ASM_REWRITE_TAC[DOT_LZERO];
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
               LRIEMANN_TRILINEAR) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0 o SPECL [`x:real^N`; `vec 0:real^N`] o
                   CONJUNCT2 o CONJUNCT2) THEN
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
               LRIEMANN_TRILINEAR) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`c:real`; `x:real^N`] o MATCH_MP LINEAR_CMUL o
                   SPECL [`x:real^N`; `c % x:real^N`] o CONJUNCT1 o CONJUNCT2) THEN
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                       `x:real^N`; `c % x:real^N`] RFA_LRIEMANN_SELF) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]];
      REWRITE_TAC[REAL_ABS_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `x:real^N`; `z:real^N`] APX_SECT_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `z:real^N`]) THEN
  ASM_REWRITE_TAC[lsectional] THEN
  ABBREV_TAC `D = (x dot ((G:real^N->real^N^N) y ** x)) * (z dot (G y ** z)) -
                  (x dot (G y ** z)) pow 2` THEN
  ABBREV_TAC `Nn = x dot ((G:real^N->real^N^N) y ** lriemann G y x z z)` THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < D ==> abs D = D`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `K * D <= abs K * D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs K * D <= abs K * (x dot ((G:real^N->real^N^N) y ** x)) * (z dot (G y ** z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN EXPAND_TAC "D" THEN
    MP_TAC(SPEC `x dot ((G:real^N->real^N^N) y ** z)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_FRAME_ORTHO = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N).
        metric_field U G /\ y IN U /\ invertible S /\
        matrix_inv(G y) = transp S ** S
        ==> !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                  ==> (transp S ** basis i) dot (G y ** (transp S ** basis j)) =
                      if i = j then &1 else &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y = matrix_inv(S:real^N^N) ** matrix_inv(transp S)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `matrix_inv(matrix_inv((G:real^N->real^N^N) y))` THEN
    CONJ_TAC THENL [REWRITE_TAC[MATRIX_INV_INV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MATRIX_INV_MUL THEN
    ASM_REWRITE_TAC[INVERTIBLE_TRANSP];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(transp(S:real^N^N)) ** transp S = mat 1 /\
                (S:real^N^N) ** matrix_inv S = mat 1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP]; ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LID; MATRIX_VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[DOT_BASIS_BASIS]);;

let RFA_FRAME_NN = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) i j.
        metric_field U G /\ y IN U /\ invertible S /\
        matrix_inv(G y) = transp S ** S /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp S ** basis i) dot (G y ** (transp S ** basis i)) <= &4 /\
            (transp S ** basis i + transp S ** basis j) dot
            (G y ** (transp S ** basis i + transp S ** basis j)) <= &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`]
         RFA_FRAME_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
  ASM_SIMP_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC);;

let RFA_LRIEMANN_POLAR_BOUND = prove
 (`!U (G:real^N->real^N^N) y K a b c d.
        metric_field U G /\ y IN U /\
        (!u v. ~collinear {vec 0,u,v} ==> abs(lsectional G y u v) <= K) /\
        a dot (G y ** a) <= &4 /\ b dot (G y ** b) <= &4 /\
        c dot (G y ** c) <= &4 /\ d dot (G y ** d) <= &4 /\
        (a + d) dot (G y ** (a + d)) <= &4 /\ (b + c) dot (G y ** (b + c)) <= &4 /\
        (b + d) dot (G y ** (b + d)) <= &4 /\ (a + c) dot (G y ** (a + c)) <= &4
        ==> abs(d dot (G y ** lriemann G y a b c)) <= &48 * abs K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `K:real`]
         RFA_Q_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         RFA_LRIEMANN_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\a b c d. d dot ((G:real^N->real^N^N) y ** lriemann G y a b c)`;
                 `\x. x dot ((G:real^N->real^N^N) y ** x)`; `abs K`;
                 `a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`] RFA_POLAR_BOUND) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[REAL_ABS_POS] THEN
  GEN_TAC THEN MATCH_MP_TAC RFA_METRIC_QPOS THEN EXISTS_TAC `U:real^N->bool` THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* |Rm|^2 <= C K^2 when |sec| <= K. *)

let RFA_LRM_SECTIONAL_BOUND = prove
 (`?C. &0 <= C /\
       !U (G:real^N->real^N^N) y K.
          metric_field U G /\ y IN U /\
          (!u v. ~collinear {vec 0,u,v} ==> abs(lsectional G y u v) <= K)
          ==> lrm_deriv_norm2 0 G y <= C * K pow 2`,
  EXISTS_TAC `&(CARD(index_tuples 4 (:N))) * &2304` THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[lrm4] THEN
  SUBGOAL_THEN
   `!m. 1 <= m /\ m <= 4 ==> 1 <= (p:num->num) m /\ p m <= dimindex(:N)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_INDEX_TUPLES_RANGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((transp(S:real^N^N) ** basis((p:num->num) 3)) dot
        ((G:real^N->real^N^N) y **
         lriemann G y (transp S ** basis(p 1)) (transp S ** basis(p 2))
                      (transp S ** basis(p 4)))) <= &48 * abs K`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_LRIEMANN_POLAR_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`]
           RFA_FRAME_NN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`(p:num->num) 1`; `(p:num->num) 1`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 2`; `(p:num->num) 4`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 3`; `(p:num->num) 3`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 4`; `(p:num->num) 4`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 1`; `(p:num->num) 3`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 2`; `(p:num->num) 3`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 1`; `(p:num->num) 4`] th) THEN
      MP_TAC(SPECL [`(p:num->num) 2`; `(p:num->num) 2`] th)) THEN
    ASM_SIMP_TAC[ARITH] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `X = (transp(S:real^N^N) ** basis((p:num->num) 3)) dot
        ((G:real^N->real^N^N) y **
         lriemann G y (transp S ** basis(p 1)) (transp S ** basis(p 2))
                      (transp S ** basis(p 4)))` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`2`; `abs X`; `&48 * abs K`] REAL_POW_LE2) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_POW2_ABS; REAL_POW_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let RFA_ABS_DIV_LE = prove
 (`!n p s. &0 < p /\ abs n <= s * p ==> abs(n / p) <= s`,
  SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_ARITH `&0 < p ==> abs p = p`]);;

(* Every sectional curvature is bounded by |Rm|. *)

let RFA_LSECTIONAL_LRM_BOUND = prove
 (`!U (G:real^N->real^N^N) y u v.
        metric_field U G /\ y IN U /\ ~collinear {vec 0,u,v}
        ==> abs(lsectional G y u v) <= sqrt(lrm_deriv_norm2 0 G y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`] APX_SECT_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(u:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLLINEAR_LEMMA]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u dot ((G:real^N->real^N^N) y ** u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `v dot ((G:real^N->real^N^N) y ** u) = u dot (G y ** v)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x z. lriemann (G:real^N->real^N^N) y x x z = vec 0` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_LRIEMANN_SELF THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u dot ((G:real^N->real^N^N) y ** lriemann G y u v u) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `u:real^N`; `v:real^N`; `u:real^N`; `u:real^N`]
           LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = (u dot ((G:real^N->real^N^N) y ** v)) / (u dot (G y ** u))` THEN
  ABBREV_TAC `w = v - t % u:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1")
    (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "l3"))) THEN
  SUBGOAL_THEN
   `lriemann (G:real^N->real^N^N) y u w w = lriemann G y u v v - t % lriemann G y u v u`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    USE_THEN "l2" (MP_TAC o SPECL [`u:real^N`; `v - t % u:real^N`]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB th);
                                     BETA_RULE(MATCH_MP LINEAR_CMUL th)]) THEN
    USE_THEN "l3" (MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB th);
                                     BETA_RULE(MATCH_MP LINEAR_CMUL th)]) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `u dot ((G:real^N->real^N^N) y ** lriemann G y u v v) =
    u dot (G y ** lriemann G y u w w)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                    DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
    (u dot (G y ** v)) pow 2 =
    (u dot (G y ** u)) * (w dot (G y ** w))`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    UNDISCH_TAC `&0 < u dot ((G:real^N->real^N^N) y ** u)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "GM"))) THEN
  SUBGOAL_THEN
   `abs(u dot ((G:real^N->real^N^N) y ** lriemann G y u w w)) <=
    sqrt(ltnorm2 4 G (lrm4 G) y) * ((u dot (G y ** u)) * (w dot (G y ** w)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `norm((M:real^N^N) ** u) * norm(M ** u) = u dot ((G:real^N->real^N^N) y ** u) /\
      norm((M:real^N^N) ** w) * norm(M ** w) = w dot ((G:real^N->real^N^N) y ** w)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_2; NORM_POW_2] THEN CONJ_TAC THEN
      MATCH_MP_TAC LRG_FRAME_DOT THEN USE_THEN "GM" ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`; `y:real^N`; `M:real^N^N`;
                   `\m. if m = 1 then u else if m = 2 then w else if m = 3 then u
                        else w:real^N`] LRG_TENSOR_FRAME_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "GM" ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[PRODUCT_4; lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN AP_TERM_TAC THEN
    UNDISCH_TAC `norm((M:real^N^N) ** u) * norm(M ** u) = u dot ((G:real^N->real^N^N) y ** u)` THEN
    UNDISCH_TAC `norm((M:real^N^N) ** w) * norm(M ** w) = w dot ((G:real^N->real^N^N) y ** w)` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REMOVE_THEN "GM" (K ALL_TAC) THEN
  REWRITE_TAC[lsectional; lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
  REWRITE_TAC[ASSUME
   `(u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
    (u dot (G y ** v)) pow 2 =
    (u dot (G y ** u)) * (w dot (G y ** w))`] THEN
  REWRITE_TAC[ASSUME
   `u dot ((G:real^N->real^N^N) y ** lriemann G y u v v) =
    u dot (G y ** lriemann G y u w w)`] THEN
  SUBGOAL_THEN `&0 < (u dot ((G:real^N->real^N^N) y ** u)) * (w dot (G y ** w))`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `&0 < (u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
           (u dot (G y ** v)) pow 2` THEN
    REWRITE_TAC[ASSUME
     `(u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
      (u dot (G y ** v)) pow 2 =
      (u dot (G y ** u)) * (w dot (G y ** w))`];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_ABS_DIV_LE THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

