(* ========================================================================= *)
(* Unit pc_p3_s13neck (Part 3 proofs; MT Ch 13, Lemma 13.13 and            *)
(* Sec 13.3.1): positive curvature of the surgery metric gS on the neck    *)
(* part 1 <= s1 <= 2.  There, in the neck coordinates y = nc(x), gS is the  *)
(* pullback of h^2 e^{-2F(s)} Ht with F = cfr = f and the blend             *)
(*   Ht = alpha(s) h^-2 gN + (1 - alpha(s)) (1 - dl) cyl0,                  *)
(* which is C^2-close to the cylinder: lck_dist2 2 cyl0 Ht <= (Dn dl)^2 by  *)
(* the Leibniz rule (general metric) for alpha(s) times a 2-tensor, with    *)
(* |nabla alpha(s)| = |alpha'| and |nabla^2 alpha(s)| = |alpha''|.  Then     *)
(* P3S_NECK_KHAT and the two-case argument (sigma >= 1/2: f'' wins; sigma   *)
(* < 1/2: (1 - sigma)/2 wins) give positivity for c = C0 dl, C0 large and   *)
(* dl small.  Headline P3S_NECK_GS.                                          *)
(*                                                                           *)
(* Contents: a Leibniz bound for a general metric; blend closeness for a     *)
(* scalar factor; the neck blend; positivity in the neck coordinates;        *)
(* transfer to x-coordinates and the headline.                               *)
(* ========================================================================= *)

needs "src/pc_p3_s13cap.ml";;
needs "src/pc_p2c_cdiff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Leibniz bound for nabla^j of a bilinear operation of the              *)
(* class lbilin_on, for any metric field G (the induction of P2C_LEIBNIZ of  *)
(* pc_p2c_gauge, which is stated for the flat metric only), with the shift   *)
(* rule and the sum shift inequality (copies of P2C_LNABLA_ITER_SHIFT and    *)
(* P2C_SUM_SHIFT_LE; pc_p2c_gauge is not in this closure).                  *)
(* ------------------------------------------------------------------------- *)

let P3S_LNABLA_ITER_SHIFT = prove
 (`!k l (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real).
        lnabla_iter (k + 1) l G (lnabla k G tf) = lnabla_iter k (l + 1) G tf`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES; RFA_LNABLA_ITER_1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lnabla_iter; ARITH_RULE `SUC l + 1 = SUC(l + 1)`] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + l = k + l + 1`]);;

let P3S_SUM_SHIFT_LE = prove
 (`!(f:num->real) g j.
     (!a. &0 <= f a) /\ (!a. &0 <= g a)
     ==> sum(0..j) (\a. f(a + 1) * g(j - a)) <=
         sum(0..j + 1) (\a. f a * g((j + 1) - a)) /\
         sum(0..j) (\a. f a * g((j - a) + 1)) <=
         sum(0..j + 1) (\a. f a * g((j + 1) - a))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`1`; `\a. (f:num->real) a * g((j + 1) - a)`; `0`; `j:num`] SUM_OFFSET) THEN
    REWRITE_TAC[ARITH_RULE `(j + 1) - (i + 1) = j - i`; ARITH_RULE `0 + 1 = 1`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 = 1`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s <= x + s`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sum(0..j) (\a. (f:num->real) a * g((j - a) + 1)) =
                  sum(0..j) (\a. f a * g((j + 1) - a))` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[SUM_ADD_SPLIT; LE_0; ARITH_RULE `0 <= j + 1`; SUM_SING_NUMSEG] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> s <= s + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]]);;

let P3S_LNABLA_FIELD1 = prove
 (`!k U (G:real^N->real^N^N) tf.
     metric_field U G /\ ltensor_field k U tf /\ (!u. smooth_map_on U (\y. lift(tf y u)))
     ==> ltensor_field (k + 1) U (lnabla k G tf) /\
         (!u. smooth_map_on U (\y. lift(lnabla k G tf y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o MATCH_MP LRG_LNABLA_ITER_FIELD) THEN
  REWRITE_TAC[RFA_LNABLA_ITER_1]);;

let P3S_LEIBNIZ = prove
 (`!j k p q (B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
     lbilin_on k p q B
     ==> ?c. &0 <= c /\
             !U G tf tg z.
               metric_field U G /\ ltensor_field p U tf /\ ltensor_field q U tg /\
               (!u. smooth_map_on U (\y. lift(tf y u))) /\
               (!u. smooth_map_on U (\y. lift(tg y u))) /\ z IN U
               ==> ltnorm2 (k + j) G
                     (lnabla_iter k j G (B G tf tg)) z <=
                   c * sum(0..j)
                         (\a. ltnorm2 (p + a) G (lnabla_iter p a G tf) z *
                              ltnorm2 (q + (j - a)) G
                                (lnabla_iter q (j - a) G tg) z)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RFA_LBILIN_ON_NORM) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[lnabla_iter; ADD_CLAUSES; SUM_SING_NUMSEG; SUB_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2C_LBILIN_ON_NABLA) THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (X_CHOOSE_THEN `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
               (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nab"))))) THEN
  USE_THEN "ih" (fun ih -> MP_TAC(MATCH_MP (SPECL [`k + 1`; `p + 1`; `q:num`;
    `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] ih)
    (ASSUME `lbilin_on (k + 1) (p + 1) q
       (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b1"))) THEN
  USE_THEN "ih" (fun ih -> MP_TAC(MATCH_MP (SPECL [`k + 1`; `p:num`; `q + 1`;
    `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] ih)
    (ASSUME `lbilin_on (k + 1) p (q + 1)
       (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
           (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b2"))) THEN
  EXISTS_TAC `&2 * c1 + &2 * c2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`; `tf:real^N->(num->real^N)->real`]
                P3S_LNABLA_FIELD1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`; `tg:real^N->(num->real^N)->real`]
                P3S_LNABLA_FIELD1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `p + 1`; `q:num`;
    `E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LBILIN_ON_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `lnabla p G (tf:real^N->(num->real^N)->real)`; `tg:real^N->(num->real^N)->real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `p:num`; `q + 1`;
    `E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] P2C_LBILIN_ON_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `tf:real^N->(num->real^N)->real`; `lnabla q G (tg:real^N->(num->real^N)->real)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `X1 = (E1:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
        G (lnabla p G (tf:real^N->(num->real^N)->real)) tg` THEN
  ABBREV_TAC `X2 = (E2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
        (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
        G (tf:real^N->(num->real^N)->real) (lnabla q G tg)` THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`; `X1:real^N->(num->real^N)->real`]
                LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`; `X2:real^N->(num->real^N)->real`]
                LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. lnabla_iter k (SUC j) G
          ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
           G tf tg) z u =
        lnabla_iter (k + 1) j G X1 z u + lnabla_iter (k + 1) j G X2 z u`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ADD1; GSYM P3S_LNABLA_ITER_SHIFT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla_iter (k + 1) j G
                  (\y u. &1 * (X1:real^N->(num->real^N)->real) y u +
                         &1 * (X2:real^N->(num->real^N)->real) y u) z u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`k + 1`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
        `lnabla k G ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
              (real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg)`;
        `\y u. &1 * (X1:real^N->(num->real^N)->real) y u +
               &1 * (X2:real^N->(num->real^N)->real) y u`;
        `U:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
        MAP_EVERY EXPAND_TAC ["X1"; "X2"] THEN
        USE_THEN "nab" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(MP_TAC o SPECL [`j:num`; `z:real^N`; `u:num->real^N`]) THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                     `X1:real^N->(num->real^N)->real`; `X2:real^N->(num->real^N)->real`;
                     `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
      ASM_SIMP_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 (k + SUC j) G
      (lnabla_iter k (SUC j) G
         ((B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->
             (real^N->(num->real^N)->real)->real^N->(num->real^N)->real)
          G tf tg)) z =
    ltnorm2 ((k + 1) + j) G
      (\y u. lnabla_iter (k + 1) j G X1 y u + lnabla_iter (k + 1) j G X2 y u) z`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `k + SUC j = (k + 1) + j`] THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * ltnorm2 ((k + 1) + j) G
                     (lnabla_iter (k + 1) j G (X1:real^N->(num->real^N)->real)) z +
              &2 * ltnorm2 ((k + 1) + j) G
                     (lnabla_iter (k + 1) j G (X2:real^N->(num->real^N)->real)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "b1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `lnabla p G (tf:real^N->(num->real^N)->real)`;
    `tg:real^N->(num->real^N)->real`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[P3S_LNABLA_ITER_SHIFT; ARITH_RULE `(p + 1) + a = p + (a + 1)`] THEN
  DISCH_TAC THEN
  USE_THEN "b2" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
    `tf:real^N->(num->real^N)->real`;
    `lnabla q G (tg:real^N->(num->real^N)->real)`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[P3S_LNABLA_ITER_SHIFT; ARITH_RULE `(q + 1) + b = q + (b + 1)`] THEN
  DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\a. ltnorm2 (p + a) G (lnabla_iter p a G (tf:real^N->(num->real^N)->real)) z`;
    `\b. ltnorm2 (q + b) G (lnabla_iter q b G (tg:real^N->(num->real^N)->real)) z`;
    `j:num`] P3S_SUM_SHIFT_LE)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `a:num` THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`p:num`; `U:real^N->bool`; `G:real^N->real^N^N`; `tf:real^N->(num->real^N)->real`]
                    LRG_LNABLA_ITER_FIELD);
      MP_TAC(ISPECL [`q:num`; `U:real^N->bool`; `G:real^N->real^N^N`; `tg:real^N->(num->real^N)->real`]
                    LRG_LNABLA_ITER_FIELD)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN STRIP_TAC THEN
  ABBREV_TAC `S = sum(0..j + 1)
    (\a. ltnorm2 (p + a) G (lnabla_iter p a G (tf:real^N->(num->real^N)->real)) z *
         ltnorm2 (q + ((j + 1) - a)) G
           (lnabla_iter q ((j + 1) - a) G (tg:real^N->(num->real^N)->real)) z)` THEN
  SUBGOAL_THEN `c1 * sum(0..j) (\a. ltnorm2 (p + (a + 1)) G
         (lnabla_iter p (a + 1) G (tf:real^N->(num->real^N)->real)) z *
         ltnorm2 (q + (j - a)) G
           (lnabla_iter q (j - a) G (tg:real^N->(num->real^N)->real)) z) <= c1 * S /\
    c2 * sum(0..j) (\a. ltnorm2 (p + a) G
         (lnabla_iter p a G (tf:real^N->(num->real^N)->real)) z *
         ltnorm2 (q + ((j - a) + 1)) G
           (lnabla_iter q ((j - a) + 1) G (tg:real^N->(num->real^N)->real)) z) <= c2 * S`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bilinear operations used below, as members of lbilin_on              *)
(* (contractions of ltprod at two slots, RFA_LBILIN_ON_CTR_AT, then slot    *)
(* permutations and linear combinations), and their values for the flat    *)
(* metric:                                                                   *)
(*   p2c_mp   (S,T)(u1,u2)    = S(u1,e_c) T(e_c,u2)          (2 2 -> 2)      *)
(*   p2c_wop  (S,T)(u1,u2,u3) = S(u1,e_c) T(e_c,u2,u3)       (2 3 -> 3)      *)
(*   p2c_vop  (S,T)(u1,u2,u3) = S(u1,e_c,u3) T(e_c,u2)       (3 2 -> 3)      *)
(*   p2c_gam  (S,T)(u1,u2,u3) = S(u3,e_c) 1/2 (T(e_c,u2,u1) + T(e_c,u1,u2)  *)
(*                               - T(u1,u2,e_c))              (2 3 -> 3)      *)
(*   p2c_q1op (S,T)(u1,u2,u3) = S(e_c,u2,u1,u3) T(e_c)       (4 1 -> 3)      *)
(*   p2c_q2op (S,T)(u1,u2)    = S(u1,u2,e_c) T(e_c)          (3 1 -> 2)      *)
(* (summation over c, contraction with the inverse metric in general).      *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* C^2 closeness of the blend Ht = a Hn + (1 - a)(1 - dl) G0                *)
(* to G0 for a scalar a with bounded first and second covariant           *)
(* derivatives: lck_dist2 2 G0 Ht <= C (1 + A0 + A1 + A2)(lck_dist2 2 G0 Hn  *)
(* + dl^2), by the Leibniz rule for a function times a 2-tensor and the    *)
(* parallel metric (nabla G0 = 0).                                         *)
(* ------------------------------------------------------------------------- *)

let P3S_LGRAD2_CDF = prove
 (`!U (G:real^N->real^N^N) cf y.
     metric_field U G /\ y IN U /\ (\z. lift(cf z)) differentiable at y
     ==> lgrad2 G cf y = p3s_cdf cf y (p3s_cgrad G cf y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `frechet_derivative (\z. lift((cf:real^N->real) z)) (at y)`]
         APX_LGRAD2_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `((lambda i. drop(frechet_derivative (\z. lift((cf:real^N->real) z)) (at y) (basis i)))
     :real^N) = G y ** p3s_cgrad G cf y`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                   `basis i:real^N`] P3S_CGRAD_DOT) THEN
    ASM_SIMP_TAC[DOT_BASIS; p3s_cdf];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  MATCH_MP_TAC P3S_CGRAD_DOT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P3S_LNABLA0_CDF = prove
 (`!(G:real^N->real^N^N) cf.
     lnabla 0 G (\z u. cf z) = \y u. p3s_cdf cf y (u 1)`,
  REWRITE_TAC[FUN_EQ_THM; lnabla; p3s_cdf] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

let P3S_LNABLA1_CHESS = prove
 (`!(G:real^N->real^N^N) cf y u.
     lnabla 1 G (lnabla 0 G (\z u. cf z)) y u = p3s_chess G cf y (u 2) (u 1)`,
  REWRITE_TAC[P3S_LNABLA0_CDF] THEN
  REWRITE_TAC[lnabla; p3s_chess; p3s_cd2f; p3s_cdf; LIFT_DROP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUM_SING_NUMSEG] THEN
  REWRITE_TAC[ETA_AX]);;

let P3S_SUM_012 = prove
 (`!f. sum(0..1) f = f 0 + f 1 /\ sum(0..2) f = f 0 + f 1 + f 2`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[REAL_ADD_ASSOC]);;

let p3s_bw = new_definition
 `p3s_bw (G0:real^N->real^N^N) (Hn:real^N->real^N^N) (dl:real) =
    \z u. &1 * (lmetric2 Hn z u - lmetric2 G0 z u) + dl * lmetric2 G0 z u`;;

let P3S_BW_FIELD = prove
 (`!U (G0:real^N->real^N^N) Hn dl.
     metric_field U G0 /\ metric_field U Hn
     ==> ltensor_field 2 U (p3s_bw G0 Hn dl) /\
         (!u. smooth_map_on U (\y. lift(p3s_bw G0 Hn dl y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `Hn:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[p3s_bw] THEN MATCH_MP_TAC RFA_TENSOR_FIELD_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[p3s_bw; LIFT_ADD; LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:num->real^N`) THEN REWRITE_TAC[]]);;

let P3S_BW_ITER = prove
 (`!U (G0:real^N->real^N^N) Hn dl.
     metric_field U G0 /\ metric_field U Hn
     ==> !l y u. y IN U
                 ==> lnabla_iter 2 l G0 (p3s_bw G0 Hn dl) y u =
                     &1 * lnabla_iter 2 l G0 (\z u. lmetric2 Hn z u - lmetric2 G0 z u) y u +
                     dl * lnabla_iter 2 l G0 (lmetric2 G0) y u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `Hn:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (Hn:real^N->real^N^N) z u - lmetric2 G0 z u`;
                 `lmetric2 (G0:real^N->real^N^N)`; `&1`; `dl:real`]
         LRG_LNABLA_ITER_LINCOMB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `y:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[p3s_bw]);;

let P3S_BW_NORMS = prove
 (`!U (G0:real^N->real^N^N) Hn dl y.
     metric_field U G0 /\ metric_field U Hn /\ y IN U
     ==> ltnorm2 2 G0 (p3s_bw G0 Hn dl) y <=
         &2 * ltnorm2 2 G0 (\z u. lmetric2 Hn z u - lmetric2 G0 z u) y +
         &2 * dl pow 2 * &(dimindex(:N)) /\
         (!m. ltnorm2 (2 + SUC m) G0 (lnabla_iter 2 (SUC m) G0 (p3s_bw G0 Hn dl)) y =
              ltnorm2 (2 + SUC m) G0
                (lnabla_iter 2 (SUC m) G0 (\z u. lmetric2 Hn z u - lmetric2 G0 z u)) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `Hn:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[p3s_bw] THEN
    MP_TAC(BETA_RULE(ISPECL [`2`; `U:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. &1 * (lmetric2 (Hn:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                 `\z u. dl * lmetric2 (G0:real^N->real^N^N) z u`; `y:real^N`]
                 RFA_LTNORM2_ADD_LE)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[LRG_LTNORM2_CMUL] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
           LRG_LTNORM2_METRIC) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN X_GEN_TAC `u:num->real^N` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `Hn:real^N->real^N^N`;
                   `dl:real`] P3S_BW_ITER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`SUC m`; `y:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`] LRG_LNABLA_ITER_METRIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `y:real^N`; `u:num->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let P3S_HT_TENSOR = prove
 (`!(G0:real^N->real^N^N) Hn (a:real^N->real) dl.
     (\z u. lmetric2 (\z. a z %% Hn z + (&1 - a z) %% ((&1 - dl) %% G0 z)) z u -
            lmetric2 G0 z u) =
     (\z u. &1 * ltprod 0 (\z (u:num->real^N). a z) (p3s_bw G0 Hn dl) z u +
            --dl * lmetric2 G0 z u)`,
  REWRITE_TAC[FUN_EQ_THM; lmetric2; ltprod; p3s_bw; ADD_CLAUSES; ETA_AX] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL;
              GSYM MATRIX_CMUL_ASSOC] THEN
  REAL_ARITH_TAC);;

let P3S_LEIB_PROD0 = prove
 (`?c1 c2. &0 <= c1 /\ &0 <= c2 /\
     !U (G:real^N->real^N^N) tf tg z.
       metric_field U G /\ ltensor_field 0 U tf /\ ltensor_field 2 U tg /\
       (!u. smooth_map_on U (\y. lift(tf y u))) /\
       (!u. smooth_map_on U (\y. lift(tg y u))) /\ z IN U
       ==> ltnorm2 3 G (lnabla_iter 2 1 G (ltprod 0 tf tg)) z <=
           c1 * (ltnorm2 0 G tf z * ltnorm2 3 G (lnabla_iter 2 1 G tg) z +
                 ltnorm2 1 G (lnabla 0 G tf) z * ltnorm2 2 G tg z) /\
           ltnorm2 4 G (lnabla_iter 2 2 G (ltprod 0 tf tg)) z <=
           c2 * (ltnorm2 0 G tf z * ltnorm2 4 G (lnabla_iter 2 2 G tg) z +
                 ltnorm2 1 G (lnabla 0 G tf) z * ltnorm2 3 G (lnabla_iter 2 1 G tg) z +
                 ltnorm2 2 G (lnabla_iter 0 2 G tf) z * ltnorm2 2 G tg z)`,
  MP_TAC(ISPECL [`1`; `0 + 2`; `0`; `2`;
    `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
      (tg:real^N->(num->real^N)->real). ltprod 0 tf tg`] P3S_LEIBNIZ) THEN
  MP_TAC(ISPECL [`2`; `0 + 2`; `0`; `2`;
    `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
      (tg:real^N->(num->real^N)->real). ltprod 0 tf tg`] P3S_LEIBNIZ) THEN
  REWRITE_TAC[RFA_LBILIN_ON_PROD] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L1"))) THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `c2:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REMOVE_THEN "L1" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
      `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`; `z:real^N`]);
    REMOVE_THEN "L2" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
      `tf:real^N->(num->real^N)->real`; `tg:real^N->(num->real^N)->real`; `z:real^N`])] THEN
  ASM_REWRITE_TAC[P3S_SUM_012] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lnabla_iter; RFA_LNABLA_ITER_1] THEN REWRITE_TAC[REAL_ADD_ASSOC]);;

let P3S_BLEND_ARITH = prove
 (`!t0 t1 t2 x0 x1 x2 w0 e0 e1 e2 A0 A1 A2 c1 c2 dd.
     &0 <= c1 /\ &0 <= c2 /\ &0 <= x0 /\ x0 <= A0 /\ &0 <= x1 /\ x1 <= A1 /\
     &0 <= x2 /\ x2 <= A2 /\ &0 <= w0 /\ w0 <= &2 * e0 + &6 * dd /\
     &0 <= e0 /\ &0 <= e1 /\ &0 <= e2 /\ &0 <= dd /\
     t0 <= &2 * (x0 * w0) + &6 * dd /\ t1 <= c1 * (x0 * e1 + x1 * w0) /\
     t2 <= c2 * (x0 * e2 + x1 * e1 + x2 * w0)
     ==> t0 + t1 + t2 <=
         (&8 * (&3 + &2 * c1 + &3 * c2)) * (&1 + A0 + A1 + A2) * ((e0 + e1 + e2) + dd)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = &1 + A0 + A1 + A2` THEN ABBREV_TAC `L = (e0 + e1 + e2) + dd` THEN
  SUBGOAL_THEN `x0 <= S /\ x1 <= S /\ x2 <= S /\ &1 <= S /\ &0 <= L /\
                w0 <= &8 * L /\ e1 <= &8 * L /\ e2 <= &8 * L /\ dd <= L`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "L"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x v. &0 <= x /\ x <= S /\ &0 <= v /\ v <= &8 * L ==> x * v <= S * (&8 * L)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `x0 * w0 <= S * (&8 * L) /\ x0 * e1 <= S * (&8 * L) /\
                x1 * w0 <= S * (&8 * L) /\ x0 * e2 <= S * (&8 * L) /\
                x1 * e1 <= S * (&8 * L) /\ x2 * w0 <= S * (&8 * L)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `L <= S * L` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1 * (x0 * e1 + x1 * w0) <= c1 * (&2 * (S * (&8 * L))) /\
                c2 * (x0 * e2 + x1 * e1 + x2 * w0) <= c2 * (&3 * (S * (&8 * L)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3S_SCALAR_FIELD0 = prove
 (`!U (a:real^N->real).
     smooth_map_on U (\z. lift(a z))
     ==> ltensor_field 0 U (\z (u:num->real^N). a z) /\
         (!u. smooth_map_on U (\y. lift((\z (u:num->real^N). a z) y u)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX] THEN
  REWRITE_TAC[ltensor_field; ARITH_RULE `~(1 <= i /\ i <= 0)`]);;

let P3S_BLEND_LCK = prove
 (`?C. &0 <= C /\
       !U (G0:real^3->real^3^3) Hn (a:real^3->real) dl y A0 A1 A2.
         metric_field U G0 /\ metric_field U Hn /\ y IN U /\
         smooth_map_on U (\z. lift(a z)) /\
         a y pow 2 <= A0 /\
         ltnorm2 1 G0 (lnabla 0 G0 (\z u. a z)) y <= A1 /\
         ltnorm2 2 G0 (lnabla_iter 0 2 G0 (\z u. a z)) y <= A2
         ==> lck_dist2 2 G0 (\z. a z %% Hn z + (&1 - a z) %% ((&1 - dl) %% G0 z)) y <=
             C * (&1 + A0 + A1 + A2) * (lck_dist2 2 G0 Hn y + dl pow 2)`,
  X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LB"))))
    (INST_TYPE [`:3`,`:N`] P3S_LEIB_PROD0) THEN
  EXISTS_TAC `&8 * (&3 + &2 * c1 + &3 * c2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real^3->real`] P3S_SCALAR_FIELD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`; `Hn:real^3->real^3^3`;
                 `dl:real`] P3S_BW_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Atf = \z (u:num->real^3). (a:real^3->real) z` THEN
  ABBREV_TAC `W = p3s_bw (G0:real^3->real^3^3) Hn dl` THEN
  SUBGOAL_THEN `ltensor_field 2 U (ltprod 0 Atf (W:real^3->(num->real^3)->real)) /\
                (!u. smooth_map_on U (\y. lift(ltprod 0 Atf W y u)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`0`; `2`; `U:real^3->bool`; `Atf:real^3->(num->real^3)->real`;
                     `W:real^3->(num->real^3)->real`] RFA_LTPROD_FIELD) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES];
      MATCH_MP_TAC RFA_LTPROD_SMOOTH THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Atf" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[lck_dist2; P3S_HT_TENSOR; P3S_SUM_012] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lnabla_iter] THEN
  REWRITE_TAC[ASSUME `(\z (u:num->real^3). (a:real^3->real) z) = Atf`;
              ASSUME `p3s_bw (G0:real^3->real^3^3) Hn dl = W`] THEN
  SUBGOAL_THEN
   `!l u. lnabla_iter 2 (SUC l) (G0:real^3->real^3^3)
            (\z u. &1 * ltprod 0 Atf (W:real^3->(num->real^3)->real) z u +
                   --dl * lmetric2 G0 z u) y u =
          lnabla_iter 2 (SUC l) G0 (ltprod 0 Atf W) y u`
  (LABEL_TAC "TI") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G0:real^3->real^3^3`;
                   `ltprod 0 Atf (W:real^3->(num->real^3)->real)`;
                   `lmetric2 (G0:real^3->real^3^3)`; `&1`; `--dl`]
           LRG_LNABLA_ITER_LINCOMB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`SUC l`; `y:real^3`; `u:num->real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`] LRG_LNABLA_ITER_METRIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`l:num`; `y:real^3`; `u:num->real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 3 (G0:real^3->real^3^3)
      (lnabla_iter 2 1 G0 (\z u. &1 * ltprod 0 Atf (W:real^3->(num->real^3)->real) z u +
                                 --dl * lmetric2 G0 z u)) y =
    ltnorm2 3 G0 (lnabla_iter 2 1 G0 (ltprod 0 Atf W)) y /\
    ltnorm2 4 (G0:real^3->real^3^3)
      (lnabla_iter 2 2 G0 (\z u. &1 * ltprod 0 Atf (W:real^3->(num->real^3)->real) z u +
                                 --dl * lmetric2 G0 z u)) y =
    ltnorm2 4 G0 (lnabla_iter 2 2 G0 (ltprod 0 Atf W)) y`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN
    X_GEN_TAC `u:num->real^3` THENL
     [USE_THEN "TI" (ACCEPT_TAC o CONV_RULE NUM_REDUCE_CONV o SPECL [`0`; `u:num->real^3`]);
      USE_THEN "TI" (ACCEPT_TAC o CONV_RULE NUM_REDUCE_CONV o SPECL [`1`; `u:num->real^3`])];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 2 (G0:real^3->real^3^3)
      (\z u. &1 * ltprod 0 Atf (W:real^3->(num->real^3)->real) z u +
             --dl * lmetric2 G0 z u) y <=
    &2 * (ltnorm2 0 G0 Atf y * ltnorm2 2 G0 W y) + &2 * dl pow 2 * &3`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * ltnorm2 2 (G0:real^3->real^3^3)
                  (\z u. &1 * ltprod 0 Atf (W:real^3->(num->real^3)->real) z u) y +
                &2 * ltnorm2 2 G0 (\z u. --dl * lmetric2 G0 z u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RFA_TENSOR_FIELD_CMUL THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[LRG_LTNORM2_CMUL; ETA_AX] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`; `y:real^3`]
           LRG_LTNORM2_METRIC) THEN
    MP_TAC(REWRITE_RULE[ADD_CLAUSES] (ISPECL [`0`; `2`; `U:real^3->bool`;
      `G0:real^3->real^3^3`; `Atf:real^3->(num->real^3)->real`;
      `W:real^3->(num->real^3)->real`; `y:real^3`] RFA_LTNORM2_LTPROD)) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "LB" (MP_TAC o SPECL [`U:real^3->bool`; `G0:real^3->real^3^3`;
    `Atf:real^3->(num->real^3)->real`; `W:real^3->(num->real^3)->real`; `y:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Atf" THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `ltnorm2 0 (G0:real^3->real^3^3) Atf y = a y pow 2` SUBST_ALL_TAC THENL
   [REWRITE_TAC[P2C_LTNORM2_0] THEN EXPAND_TAC "Atf" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`; `Hn:real^3->real^3^3`;
                 `dl:real`; `y:real^3`] P3S_BW_NORMS) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `0` th)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC `1` th)))) THEN
  REPEAT(DISCH_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN
   `&0 <= ltnorm2 2 (G0:real^3->real^3^3) (\z u. lmetric2 Hn z u - lmetric2 G0 z u) y /\
    &0 <= ltnorm2 3 G0 (lnabla_iter 2 1 G0 (\z u. lmetric2 Hn z u - lmetric2 G0 z u)) y /\
    &0 <= ltnorm2 4 G0 (lnabla_iter 2 2 G0 (\z u. lmetric2 Hn z u - lmetric2 G0 z u)) y /\
    &0 <= ltnorm2 1 G0 (lnabla 0 G0 Atf) y /\
    &0 <= ltnorm2 2 G0 (lnabla_iter 0 2 G0 Atf) y /\
    &0 <= ltnorm2 2 G0 (W:real^3->(num->real^3)->real) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`0`] (ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`;
        `Hn:real^3->real^3^3`; `y:real^3`] LRG_LCK_DIST2_SUMMAND_POS));
      MP_TAC(SPECL [`1`] (ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`;
        `Hn:real^3->real^3^3`; `y:real^3`] LRG_LCK_DIST2_SUMMAND_POS));
      MP_TAC(SPECL [`2`] (ISPECL [`U:real^3->bool`; `G0:real^3->real^3^3`;
        `Hn:real^3->real^3^3`; `y:real^3`] LRG_LCK_DIST2_SUMMAND_POS));
      MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`0`; `U:real^3->bool`; `G0:real^3->real^3^3`;
                     `Atf:real^3->(num->real^3)->real`] P3S_LNABLA_FIELD1) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Atf" THEN ASM_REWRITE_TAC[];
                      SIMP_TAC[ADD_CLAUSES]];
      MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`0`; `U:real^3->bool`; `G0:real^3->real^3^3`;
                     `Atf:real^3->(num->real^3)->real`] LRG_LNABLA_ITER_FIELD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Atf" THEN ASM_REWRITE_TAC[];
                      DISCH_THEN(MP_TAC o SPEC `2`) THEN SIMP_TAC[ADD_CLAUSES]];
      MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[lnabla_iter];
    ALL_TAC] THEN
  MATCH_MP_TAC P3S_BLEND_ARITH THEN
  MAP_EVERY EXISTS_TAC [`(a:real^3->real) y pow 2`;
                        `ltnorm2 1 (G0:real^3->real^3^3) (lnabla 0 G0 Atf) y`;
                        `ltnorm2 2 (G0:real^3->real^3^3) (lnabla_iter 0 2 G0 Atf) y`;
                        `ltnorm2 2 (G0:real^3->real^3^3) W y`] THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The neck blend.  For a = alpha o s on the cylinder the                   *)
(* covariant gradient and Hessian norms are alpha'(s)^2 and alpha''(s)^2     *)
(* (|ds| = 1, Hess s = 0), so the blend alpha h^-2 gN + (1 - alpha)(1 - dl)  *)
(* cyl0 is C^2-close to cyl0 with lck_dist2 <= Cn (lck_dist2(h^-2 gN) + dl^2) *)
(* where -1 <= s <= 4.                                                       *)
(* ------------------------------------------------------------------------- *)

let P3S_ALPHA_DERIVS = prove
 (`(!t. (p3s_alpha has_real_derivative real_derivative p3s_alpha t) (atreal t)) /\
   (!t. (real_derivative p3s_alpha has_real_derivative
         real_derivative (real_derivative p3s_alpha) t) (atreal t)) /\
   smooth_map_on (:real^1) (lift o real_derivative p3s_alpha o drop) /\
   smooth_map_on (:real^1) (lift o real_derivative (real_derivative p3s_alpha) o drop)`,
  MP_TAC P3S_ALPHA THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`(:real^1)`; `p3s_alpha`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `real_derivative p3s_alpha`] P3S_S1_RDERIV) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let P3S_SY_LGRAD2 = prove
 (`!U y. open U /\ U SUBSET (:real^3) DELETE vec 0 /\ y IN U
         ==> ltnorm2 1 (cylinder_flow (&0)) (lnabla 0 (cylinder_flow (&0)) (\z u. p3s_sy z)) y
             = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P2C_LGRAD2_LTNORM2] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `p3s_sy`; `y:real^3`]
         P3S_LGRAD2_CDF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_SIMP_TAC[P3S_SY_SMOOTH_ON];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_GRADSQ]);;

let P3S_ASY_NORMS = prove
 (`!U y. open U /\ U SUBSET (:real^3) DELETE vec 0 /\ y IN U
     ==> ltnorm2 1 (cylinder_flow (&0))
           (lnabla 0 (cylinder_flow (&0)) (\z u. p3s_alpha(p3s_sy z))) y =
         real_derivative p3s_alpha (p3s_sy y) pow 2 /\
         ltnorm2 2 (cylinder_flow (&0))
           (lnabla_iter 0 2 (cylinder_flow (&0)) (\z u. p3s_alpha(p3s_sy z))) y =
         real_derivative (real_derivative p3s_alpha) (p3s_sy y) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  MP_TAC P3S_ALPHA_DERIVS THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(p3s_sy z)) /\
                smooth_map_on U (\z. lift(p3s_alpha(p3s_sy z)))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_SY_SMOOTH_ON] THEN MATCH_MP_TAC P3S_COMPOSE_1D THEN
    EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON; P3S_ALPHA];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM P2C_LGRAD2_LTNORM2] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `\z. p3s_alpha(p3s_sy z)`;
                   `y:real^3`] P3S_LGRAD2_CDF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `cylinder_flow (&0)`; `p3s_sy`; `p3s_alpha`;
                   `real_derivative p3s_alpha (p3s_sy y)`; `y:real^3`]
           P3S_GRADSQ_COMPOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[P3S_SY_GRADSQ; REAL_MUL_RID];
    ALL_TAC] THEN
  ABBREV_TAC `D1 = lnabla 0 (cylinder_flow (&0)) (\z (u:num->real^3). p3s_sy z)` THEN
  SUBGOAL_THEN `!u. lnabla_iter 0 2 (cylinder_flow (&0)) (\z u. p3s_alpha(p3s_sy z)) y u =
                    real_derivative (real_derivative p3s_alpha) (p3s_sy y) *
                    ltprod 1 D1 D1 y u` ASSUME_TAC THENL
   [X_GEN_TAC `u:num->real^3` THEN
    REWRITE_TAC[RFA_LNABLA_ITER_2; ADD_CLAUSES; P3S_LNABLA1_CHESS] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `(:real)`; `cylinder_flow (&0)`; `p3s_sy`;
                   `p3s_alpha`; `real_derivative p3s_alpha`;
                   `real_derivative (real_derivative p3s_alpha) (p3s_sy y)`;
                   `y:real^3`; `(u:num->real^3) 2`; `(u:num->real^3) 1`]
           P3S_CHESS_COMPOSE) THEN
    ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[P3S_SY_CHESS; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    EXPAND_TAC "D1" THEN REWRITE_TAC[ltprod; P3S_LNABLA0_CDF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `p3s_sy`] P3S_SCALAR_FIELD0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^3->bool`; `cylinder_flow (&0)`; `\z (u:num->real^3). p3s_sy z`]
         P3S_LNABLA_FIELD1) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltnorm2 2 (cylinder_flow (&0))
                (\z u. real_derivative (real_derivative p3s_alpha) (p3s_sy y) *
                       ltprod 1 D1 D1 z u) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LRG_LTNORM2_CMUL; ETA_AX] THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `1 + 1 = 2`] (ISPECL [`1`; `1`; `U:real^3->bool`;
    `cylinder_flow (&0)`; `D1:real^3->(num->real^3)->real`;
    `D1:real^3->(num->real^3)->real`; `y:real^3`] RFA_LTNORM2_LTPROD)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "D1" THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `y:real^3`] P3S_SY_LGRAD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P3S_NECK_BLEND = prove
 (`?Cn. &0 <= Cn /\
        !U (Hn:real^3->real^3^3) dl y.
          open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Hn /\ y IN U /\
          --(&1) <= p3s_sy y /\ p3s_sy y <= &4
          ==> lck_dist2 2 (cylinder_flow (&0))
                (\z. p3s_alpha(p3s_sy z) %% Hn z +
                     (&1 - p3s_alpha(p3s_sy z)) %% ((&1 - dl) %% cylinder_flow (&0) z)) y <=
              Cn * (lck_dist2 2 (cylinder_flow (&0)) Hn y + dl pow 2)`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BL")) P3S_BLEND_LCK THEN
  MP_TAC P3S_ALPHA_DERIVS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`real_derivative p3s_alpha`; `--(&1)`; `&4`] P3S_RCONT_BOUNDED) THEN
  ASM_SIMP_TAC[P2C_S1_CONTINUOUS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B1"))) THEN
  MP_TAC(ISPECL [`real_derivative (real_derivative p3s_alpha)`; `--(&1)`; `&4`]
         P3S_RCONT_BOUNDED) THEN
  ASM_SIMP_TAC[P2C_S1_CONTINUOUS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B2"))) THEN
  EXISTS_TAC `C * (&1 + &1 + B1 pow 2 + B2 pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `B1:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `B2:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `y:real^3`] P3S_ASY_NORMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "BL" (MP_TAC o BETA_RULE o SPECL [`U:real^3->bool`; `cylinder_flow (&0)`;
    `Hn:real^3->real^3^3`; `\z. p3s_alpha(p3s_sy z)`; `dl:real`; `y:real^3`; `&1`;
    `B1 pow 2`; `B2 pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON; P3S_ALPHA];
      MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC[P3S_ALPHA];
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B1:real` THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B2:real` THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Positivity of the conformal blend on 1 <= s <= 2 in the                  *)
(* neck coordinates (MT Lemma 13.13 with the two-case plane argument):     *)
(* with c = C0 dl, C0 >= 256 K Dn e^q / q^2 + 1 and dl small, the bracket    *)
(* of P3S_NECK_KHAT is positive whether sigma >= 1/2 (f'' wins) or not     *)
(* ((1 - sigma)/2 wins).                                                     *)
(* ------------------------------------------------------------------------- *)

let P3S_NECK_POS_ARITH = prove
 (`!Kh K sg D F1 F2 f c q.
     abs(Kh - (&1 - sg) / &2) <= K * D /\ &0 <= sg /\ sg <= &1 /\
     &0 <= D /\ &0 < q /\ &0 <= f /\ f <= c /\
     &0 <= F1 /\ F1 <= q * f /\ q pow 2 / &32 * f <= F2 /\ F2 <= (q pow 2 + &2 * q) * f /\
     c <= &1 / &128 /\
     D * (&6 * q + &7 * (q pow 2 + &2 * q) + &9 * q pow 2) <= q pow 2 / &256 /\
     K * D < q pow 2 / &256 * f /\
     K * D + q pow 2 * c pow 2 +
     D * c * (&6 * q + &7 * (q pow 2 + &2 * q) + &9 * q pow 2) < &1 / &4
     ==> &0 < Kh + F2 * sg - F1 pow 2 * (&1 - sg) -
              D * (&6 * abs F1 + &7 * abs F2 + &9 * F1 pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = &6 * q + &7 * (q pow 2 + &2 * q) + &9 * q pow 2` THEN
  SUBGOAL_THEN `&0 <= q pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q pow 2 / &32 * f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c /\ c <= &1 /\ &0 <= F2 /\ &0 <= P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN `F1 pow 2 <= q pow 2 * (c * f)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(q * f) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 * (c * f) <= q pow 2 * (&1 / &128 * f) /\
                q pow 2 * (c * f) <= q pow 2 * (c * c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_RMUL; MATCH_MP_TAC REAL_LE_LMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `D * (&6 * F1 + &7 * F2 + &9 * F1 pow 2) <= D * (f * P)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f * (D * P) <= f * (q pow 2 / &256) /\ D * (f * P) <= D * (c * P)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= F1 pow 2 * sg /\ &0 <= F2 * sg` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 / &2 <= sg` THENL
   [SUBGOAL_THEN `&0 <= F2 * (sg - &1 / &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P3S_HT_FIELD = prove
 (`!U (Hn:real^3->real^3^3) dl.
     open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Hn /\ dl < &1
     ==> metric_field U (\z. p3s_alpha(p3s_sy z) %% Hn z +
                             (&1 - p3s_alpha(p3s_sy z)) %%
                             ((&1 - dl) %% cylinder_flow (&0) z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(p3s_alpha(p3s_sy z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON; P3S_ALPHA];
    ALL_TAC] THEN
  MATCH_MP_TAC P3S_METRIC_FIELD_COMB THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`; ETA_AX];
      REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    MP_TAC P3S_ALPHA THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    MESON_TAC[REAL_ARITH `&0 <= a /\ a <= &1 ==> &0 <= a /\ &0 <= &1 - a /\ &0 < a + (&1 - a)`]]);;

let P3S_F_BOUNDS12 = prove
 (`!c q s. &0 <= c /\ &8 <= q /\ &1 <= s /\ s <= &2
     ==> &0 <= p3s_f c q s /\ p3s_f c q s <= c /\ c * exp(--q) <= p3s_f c q s /\
         &0 <= (q / s pow 2) * p3s_f c q s /\
         (q / s pow 2) * p3s_f c q s <= q * p3s_f c q s /\
         q pow 2 / &32 * p3s_f c q s <=
         (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s /\
         (q pow 2 / s pow 4 - &2 * q / s pow 3) * p3s_f c q s <=
         (q pow 2 + &2 * q) * p3s_f c q s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q /\ &0 < s` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p3s_f c q s /\ p3s_f c q s <= c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[P3S_F_NONNEG; P3S_F_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= s pow 2 /\ &1 <= s pow 3 /\ &1 <= s pow 4 /\ s pow 4 <= &16`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1; MATCH_MP_TAC REAL_POW_LE_1; MATCH_MP_TAC REAL_POW_LE_1;
      MP_TAC(SPECL [`4`; `s:real`; `&2`] REAL_POW_LE2) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s pow 2 /\ &0 < s pow 3 /\ &0 < s pow 4` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q / s pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `q / s pow 2 <= q` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 / &32 <= q pow 2 / (&2 * s pow 4)` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * q / s pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 / s pow 4 <= q pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_SIMP_TAC[P3S_F_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `q pow 2 / (&2 * s pow 4) * p3s_f c q s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P3S_F_D2_LOWER THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3S_POS_FROM_EXP = prove
 (`!a b e. a <= e * b ==> &0 < e /\ &0 < a ==> &0 < b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < b` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e * b <= &0` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM REAL_MUL_RNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P3S_LE_INV_MUL = prove
 (`!x a. &0 < a /\ x <= inv a ==> a * x <= &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * inv a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

let P3S_NECK_POS_Y = prove
 (`!q. &8 <= q
       ==> ?C0m. &0 < C0m /\
             !C0. C0m <= C0
                  ==> ?dm. &0 < dm /\ dm <= &1 /\
                       !A0 r0 dl U (Hn:real^3->real^3^3) y u v.
                         &0 < A0 /\ &0 < r0 /\ r0 <= &1 /\ &0 < dl /\ dl <= dm /\
                         open U /\ U SUBSET (:real^3) DELETE vec 0 /\ metric_field U Hn /\
                         y IN U /\ lck_dist2 2 (cylinder_flow (&0)) Hn y <= dl pow 2 /\
                         &1 <= p3s_sy y /\ p3s_sy y <= &2 /\ ~collinear {vec 0,u,v}
                         ==> &0 < lsectional
                                    (\z. exp(--(&2 * p3s_cfr (C0 * dl) q A0 r0 (p3s_sy z))) %%
                                         (p3s_alpha(p3s_sy z) %% Hn z +
                                          (&1 - p3s_alpha(p3s_sy z)) %%
                                          ((&1 - dl) %% cylinder_flow (&0) z))) y u v`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KH")) P3S_NECK_KHAT THEN
  X_CHOOSE_THEN `Cn:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB")) P3S_NECK_BLEND THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Dn = &2 * (Cn + &1)` THEN
  ABBREV_TAC `P = &6 * q + &7 * (q pow 2 + &2 * q) + &9 * q pow 2` THEN
  SUBGOAL_THEN `&2 <= Dn /\ &0 < P /\ &0 < q pow 2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Dn"; "P"] THEN
    SUBGOAL_THEN `&0 < q pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&256 * K * Dn * exp q / q pow 2 + &1` THEN
  SUBGOAL_THEN `&0 <= Dn` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &256 * K * Dn * exp q / q pow 2` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_EXP_POS_LE; REAL_LE_POW_2; REAL_POS];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `C0:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < C0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `M = K * Dn + q pow 2 * C0 pow 2 + Dn * C0 * P + &1` THEN
  SUBGOAL_THEN `&1 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    SUBGOAL_THEN `&0 <= K * Dn /\ &0 <= q pow 2 * C0 pow 2 /\ &0 <= Dn * C0 * P` MP_TAC THENL
     [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &2) (min (inv(&128 * C0)) (min (q pow 2 / (&256 * Dn * P))
                (min (inv(&8 * M)) (inv(&10 * Dn)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_MIN_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  MAP_EVERY X_GEN_TAC [`A0:real`; `r0:real`; `dl:real`; `U:real^3->bool`;
                       `Hn:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `s0 = p3s_sy (y:real^3)` THEN
  SUBGOAL_THEN `&128 * C0 * dl <= &1 /\ dl * (&256 * Dn * P) <= q pow 2 /\
                &8 * M * dl <= &1 /\ &10 * Dn * dl <= &1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3S_LE_INV_MUL THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < &256 * Dn * P` ASSUME_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3S_LE_INV_MUL THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC P3S_LE_INV_MUL THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl < &1 /\ &0 <= Cn` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 2 (cylinder_flow (&0))
      (\z. p3s_alpha(p3s_sy z) %% (Hn:real^3->real^3^3) z +
           (&1 - p3s_alpha(p3s_sy z)) %% ((&1 - dl) %% cylinder_flow (&0) z)) y <=
    (Dn * dl) pow 2`
  ASSUME_TAC THENL
   [REMOVE_THEN "NB" (MP_TAC o SPECL [`U:real^3->bool`; `Hn:real^3->real^3^3`; `dl:real`;
                                     `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cn * (&2 * dl pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "Dn" THEN
    SUBGOAL_THEN `&0 <= (&4 * Cn * Cn + &6 * Cn + &4) * (dl * dl)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
      MP_TAC(SPEC `Cn:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C0 * dl`; `q:real`; `A0:real`; `r0:real`] P3S_CFR_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "KH" (MP_TAC o BETA_RULE o SPECL
   [`U:real^3->bool`;
    `\z. p3s_alpha(p3s_sy z) %% (Hn:real^3->real^3^3) z +
         (&1 - p3s_alpha(p3s_sy z)) %% ((&1 - dl) %% cylinder_flow (&0) z)`;
    `p3s_cfr (C0 * dl) q A0 r0`; `real_derivative (p3s_cfr (C0 * dl) q A0 r0)`;
    `real_derivative (real_derivative (p3s_cfr (C0 * dl) q A0 r0)) s0`;
    `y:real^3`; `u:real^3`; `v:real^3`; `Dn * dl`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3S_HT_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P3S_CFR_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` MP_TAC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C0 * dl`; `q:real`; `A0:real`; `r0:real`; `s0:real`] P3S_CFR_LOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(SPECL [`C0 * dl`; `q:real`; `s0:real`] P3S_F_BOUNDS12) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `f = p3s_f (C0 * dl) q s0` THEN
  SUBGOAL_THEN `K * Dn < q pow 2 / &256 * (C0 * exp(--q))` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < q pow 2 / &256 * exp(--q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_EXP_POS_LT; REAL_ARITH `&0 < &256`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&256 * K * Dn * exp q / q pow 2) * (q pow 2 / &256 * exp(--q)) = K * Dn`
    ASSUME_TAC THENL
     [MP_TAC(SPEC `q:real` REAL_EXP_NEG_MUL) THEN UNDISCH_TAC `&0 < q pow 2` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `C0 * (q pow 2 / &256 * exp(--q))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `K * (Dn * dl) < q pow 2 / &256 * f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `q pow 2 / &256 * ((C0 * dl) * exp(--q))` THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`K * Dn`; `q pow 2 / &256 * (C0 * exp(--q))`; `dl:real`]
             REAL_LT_RMUL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl * dl <= dl` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 * (C0 * dl) pow 2 <= q pow 2 * C0 pow 2 * dl /\
                (Dn * dl) * (C0 * dl) * P <= Dn * C0 * P * dl` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_POW_2];
      SUBGOAL_THEN `&0 <= Dn * C0 * P` ASSUME_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`Dn * C0 * P`; `dl * dl`; `dl:real`] REAL_LE_LMUL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `M * dl = K * Dn * dl + q pow 2 * C0 pow 2 * dl + Dn * C0 * P * dl + dl`
  ASSUME_TAC THENL [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP P3S_POS_FROM_EXP o
    check (fun th -> is_binary "real_le" (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "exp" with _ -> false))
                         (rand(concl th)))) THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC P3S_NECK_POS_ARITH THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `f:real`; `C0 * dl`; `q:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Transfer to the x-coordinates.  On 0 < s1 < 3 the surgery               *)
(* metric is the pullback by nc of h^2 e^{-2 cfr(s)} Ht (P3S_GS_PULLBACK); *)
(* nc is a diffeomorphism onto the annulus 1 < |y| < e^{3/sqrt 2}, so the  *)
(* sectional curvature of gS is that of the conformal blend divided by    *)
(* h^2 on the image planes.  Headline P3S_NECK_GS.                         *)
(* ------------------------------------------------------------------------- *)

let P3S_SY_NC = prove
 (`!g0 A0 (z:real^3). ~(z = vec 0)
     ==> ~(p3_std_nc g0 A0 z = vec 0) /\
         p3s_sy (p3_std_nc g0 A0 z) = A0 + &4 - p3_std_dist g0 z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_NC_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(p3_std_nc g0 A0 (z:real^3) = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_EQ; LOG_EXP] THEN
  MP_TAC P3S_SQRT2_POS THEN CONV_TAC REAL_FIELD);;

let P3S_GS_PULLBACK = prove
 (`!g0 A0 c q r0 dl h (gN:real^3->real^3^3) (z:real^3).
     p3_std_initial g0 A0 /\ &0 <= c /\ &0 < q /\ &0 < r0 /\ &0 < h /\ ~(z = vec 0) /\
     A0 + &4 - p3_std_dist g0 z < &3
     ==> p3s_gs g0 A0 c q r0 dl h gN z =
         mpullback (p3_std_nc g0 A0)
           (\y. h pow 2 %%
                (exp(--(&2 * p3s_cfr c q A0 r0 (p3s_sy y))) %%
                 (p3s_alpha(p3s_sy y) %% (inv(h pow 2) %% gN y) +
                  (&1 - p3s_alpha(p3s_sy y)) %% ((&1 - dl) %% cylinder_flow (&0) y)))) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `c:real`; `q:real`; `r0:real`;
                 `dl:real`; `h:real`; `gN:real^3->real^3^3`; `z:real^3`] P3S_GS_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(g0:real^3->real^3^3) z = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) z`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o REWRITE_RULE[p3_std_initial]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3S_SY_NC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[mpullback; P3S_CFR_EXP] THEN
  ABBREV_TAC `J = matrix(frechet_derivative (p3_std_nc g0 A0) (at (z:real^3)))` THEN
  ABBREV_TAC `t = A0 + &4 - p3_std_dist g0 (z:real^3)` THEN
  REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB; MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
  SUBGOAL_THEN `~(h pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH_EQ]; ALL_TAC] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(h pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let P3S_DIFFEO_NONCOLL = prove
 (`!U U' (h:real^N->real^N) h' y u v.
     diffeomorphism_on U' U h h' /\ y IN U' /\ ~collinear {vec 0,u,v}
     ==> ~collinear {vec 0, frechet_derivative h (at y) u, frechet_derivative h (at y) v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`frechet_derivative (h:real^N->real^N) (at y)`; `{vec 0:real^N,u,v}`]
         COLLINEAR_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `frechet_derivative (h':real^N->real^N) (at (h(y:real^N)))`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN ASM_REWRITE_TAC[]);;

let P3S_ANN_FACTS = prove
 (`!y:real^3. exp(&0 / sqrt(&2)) < norm y /\ norm y < exp(&3 / sqrt(&2))
              ==> ~(y = vec 0) /\ &0 < p3s_sy y /\ p3s_sy y < &3`,
  GEN_TAC THEN REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[P3S_SY_EQ] THEN
  MP_TAC P3S_SQRT2_POS THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < log(norm(y:real^3)) /\ log(norm y) < &3 * inv(sqrt(&2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(&2) * &3 * inv(sqrt(&2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD]);;

let P3S_NECK_GS = prove
 (`!g0 A0 q. p3_std_initial g0 A0 /\ &8 <= q
     ==> ?C0m. &0 < C0m /\
           !C0. C0m <= C0
                ==> ?dm. &0 < dm /\ dm <= &1 / &4 /\
                     !r0 dl h gN (x:real^3) u v.
                       &0 < r0 /\ r0 <= &1 /\ &0 < dl /\ dl <= dm /\ &0 < h /\
                       metric_field (rfs_neck_dom dl) gN /\
                       rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                                    (\y. inv(h pow 2) %% gN y) /\
                       &1 <= A0 + &4 - p3_std_dist g0 x /\
                       A0 + &4 - p3_std_dist g0 x <= &2 /\ ~collinear {vec 0,u,v}
                       ==> &0 < mfd_sectional
                                  (open_set_atlas
                                     {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                                  (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P3S_A0_POS) THEN
  MP_TAC(SPEC `q:real` P3S_NECK_POS_Y) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0m:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Y"))) THEN
  EXISTS_TAC `C0m:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `C0:real` THEN DISCH_TAC THEN
  REMOVE_THEN "Y" (MP_TAC o SPEC `C0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dm0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Y")))) THEN
  EXISTS_TAC `min dm0 (&1 / &4)` THEN
  REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_MIN_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r0:real`; `dl:real`; `h:real`; `gN:real^3->real^3^3`;
                       `x:real^3`; `u:real^3`; `v:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q /\ &0 < inv dl /\ &4 <= inv dl` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &4)` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the open set atlas *)
  MP_TAC(ISPECL [`{z:real^3 | --(inv dl) < A0 + &4 - p3_std_dist g0 z}`;
                 `p3s_gs g0 A0 (C0 * dl) q r0 dl h gN`; `x:real^3`; `u:real^3`; `v:real^3`]
         P3S_OPEN_MFD_SECTIONAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P3S_OPEN_S1 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`; `&3`] P3S_NC_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `W = {x:real^3 | &0 < A0 + &4 - p3_std_dist g0 x /\
                              A0 + &4 - p3_std_dist g0 x < &3}` THEN
  ABBREV_TAC `Ann = {y:real^3 | exp(&0 / sqrt(&2)) < norm y /\
                                norm y < exp(&3 / sqrt(&2))}` THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ open(Ann:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN Ann ==> ~(y = vec 0) /\ &0 < p3s_sy y /\ p3s_sy y < &3`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ann" THEN REWRITE_TAC[IN_ELIM_THM; P3S_ANN_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `Ann SUBSET (:real^3) DELETE vec 0 /\ Ann SUBSET rfs_neck_dom dl`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[P3S_NECK_DOM_S; GSYM P3S_SY_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C0 * dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < inv(h pow 2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Ann (\y:real^3. inv(h pow 2) %% gN y)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field Ann
      (\y. exp(--(&2 * p3s_cfr (C0 * dl) q A0 r0 (p3s_sy y))) %%
           (p3s_alpha(p3s_sy y) %% (inv(h pow 2) %% (gN:real^3->real^3^3) y) +
            (&1 - p3s_alpha(p3s_sy y)) %% ((&1 - dl) %% cylinder_flow (&0) y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`Ann:real^3->bool`;
      `\y. p3s_alpha(p3s_sy y) %% (inv(h pow 2) %% (gN:real^3->real^3^3) y) +
           (&1 - p3s_alpha(p3s_sy y)) %% ((&1 - dl) %% cylinder_flow (&0) y)`;
      `\y:real^3. p3s_cfr (C0 * dl) q A0 r0 (p3s_sy y)`] P3S_CONF_FIELD)) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`Ann:real^3->bool`; `\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y`; `dl:real`]
             P3S_HT_FIELD) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      MATCH_MP_TAC P3S_COMPOSE_1D THEN EXISTS_TAC `(:real^1)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; P3S_SY_SMOOTH_ON; P3S_CFR_SMOOTH]];
    ALL_TAC] THEN
  ABBREV_TAC
   `Gc = \y. exp(--(&2 * p3s_cfr (C0 * dl) q A0 r0 (p3s_sy y))) %%
             (p3s_alpha(p3s_sy y) %% (inv(h pow 2) %% (gN:real^3->real^3^3) y) +
              (&1 - p3s_alpha(p3s_sy y)) %% ((&1 - dl) %% cylinder_flow (&0) y))` THEN
  SUBGOAL_THEN `metric_field Ann (\y:real^3. h pow 2 %% Gc y)` ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lsectional (p3s_gs g0 A0 (C0 * dl) q r0 dl h gN) x u v =
    lsectional (mpullback (p3_std_nc g0 A0) (\y:real^3. h pow 2 %% Gc y)) x u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN EXPAND_TAC "Gc" THEN
    MATCH_MP_TAC P3S_GS_PULLBACK THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
                 `p3s_ncinv g0 A0`; `\y:real^3. h pow 2 %% (Gc:real^3->real^3^3) y`; `x:real^3`;
                 `u:real^3`; `v:real^3`] MFDR_LSECTIONAL_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`Ann:real^3->bool`; `W:real^3->bool`; `p3_std_nc g0 A0`;
                 `p3s_ncinv g0 A0`; `x:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Ann:real^3->bool`; `Gc:real^3->real^3^3`; `h pow 2`;
                 `p3_std_nc g0 A0 x`;
                 `frechet_derivative (p3_std_nc g0 A0) (at x) u`;
                 `frechet_derivative (p3_std_nc g0 A0) (at x) v`] APX_LSECTIONAL_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Gc" THEN ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 (x:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom dl) (\y:real^3. inv(h pow 2) %% gN y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3S_METRIC_FIELD_FMUL THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 2 (cylinder_flow (&0)) (\y:real^3. inv(h pow 2) %% gN y)
                  (p3_std_nc g0 A0 x) <= dl pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_exists o concl) o
      REWRITE_RULE[rfs_close_on] o check (can (find_term (fun t -> try fst(dest_const t) = "rfs_close_on"
                                       with Failure _ -> false)) o concl)) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                  (\y:real^3. inv(h pow 2) %% gN y) (p3_std_nc g0 A0 x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom dl` THEN
      ASM_SIMP_TAC[P3S_NECK_CYL_FIELD] THEN MATCH_MP_TAC APX_KREG_TWO THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  EXPAND_TAC "Gc" THEN
  REMOVE_THEN "Y" (MP_TAC o BETA_RULE o SPECL
    [`A0:real`; `r0:real`; `dl:real`; `Ann:real^3->bool`;
     `\y:real^3. inv(h pow 2) %% (gN:real^3->real^3^3) y`; `p3_std_nc g0 A0 x`;
     `frechet_derivative (p3_std_nc g0 A0) (at x) u`;
     `frechet_derivative (p3_std_nc g0 A0) (at x) v`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_SY_NC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P3S_DIFFEO_NONCOLL THEN
    MAP_EVERY EXISTS_TAC [`Ann:real^3->bool`; `W:real^3->bool`; `p3s_ncinv g0 A0`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

