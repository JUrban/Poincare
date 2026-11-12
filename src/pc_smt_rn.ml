(* ========================================================================= *)
(* pc_smt_rn: flow-free real^N lemmas of the Smale chain.                    *)
(*                                                                           *)
(* S4a (SMT_PERTURB_ID_STATEMENT).  x + U t x with U(t,.)                    *)
(* c-Lipschitz, c < 1, is a smooth isotopy of diffeomorphisms: inverses by   *)
(* the Banach fixed point theorem (BANACH_FIX), joint smoothness of the      *)
(* inverse by the inverse function theorem for (t,x) |-> (t, x + U t x),     *)
(* whose derivative is injective because the x-derivative of U has norm at   *)
(* most c.                                                                   *)
(* ========================================================================= *)

needs "src/pc_smt_sphere.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_REAL_LE_EPS = prove
 (`!a b. (!e. &0 < e ==> a <= b + e) ==> a <= b`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(a - b) / &2`) THEN
  REAL_ARITH_TAC);;

(* A Lipschitz bound in a direction bounds the derivative in that direction. *)

let HAS_DERIVATIVE_LIPSCHITZ_DIRECTION = prove
 (`!(f:real^M->real^N) f' x k c.
        (f has_derivative f') (at x) /\
        (!s. &0 < s ==> norm(f(x + s % k) - f x) <= c * s * norm k)
        ==> norm(f' k) <= c * norm k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))
    (LABEL_TAC "lip")) THEN
  ASM_CASES_TAC `k:real^M = vec 0` THENL
   [FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(k:real^M)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC SMT_REAL_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "d" (MP_TAC o SPEC `e / norm(k:real^M)`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `x + (d / (&2 * norm(k:real^M))) % k`) THEN
  SUBGOAL_THEN `&0 < d / (&2 * norm(k:real^M))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm((d / (&2 * norm(k:real^M))) % k) = d / &2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
    UNDISCH_TAC `&0 < norm(k:real^M)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(x + a) - x:real^N = a`] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "lip" (MP_TAC o SPEC `d / (&2 * norm(k:real^M))`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ABBREV_TAC `s = d / (&2 * norm(k:real^M))` THEN
  REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  SUBGOAL_THEN `e / norm(k:real^M) * d / &2 = e * s` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN UNDISCH_TAC `&0 < norm(k:real^M)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `s * norm((f':real^M->real^N) k) <= s * (c * norm k + e)` MP_TAC THENL
   [MP_TAC(NORM_ARITH
     `!a b c:real^N u v. norm(a - b - c) <= u /\ norm(a - b) <= v
                         ==> norm c <= u + v`) THEN
    DISCH_THEN(MP_TAC o SPECL [`(f:real^M->real^N)(x + s % k)`; `(f:real^M->real^N) x`;
                               `s % (f':real^M->real^N) k`; `e * s`;
                               `c * s * norm(k:real^M)`]) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]);;

(* Time slices of smooth families are smooth. *)

let SMT_FAMILY_SLICE = prove
 (`!s (H:real->real^M->real^N) t.
        open s /\ smooth_family s H ==> smooth_map_on s (H t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_family] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(H:real->real^M->real^N) t =
                (\z. H (drop(fstcart z)) (sndcart z)) o (\x. pastecart (lift t) x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^1) PCROSS (s:real^M->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV] THEN
    SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID; ETA_AX]]);;

(* S4a. *)

let SMT_PERTURB_ID = prove
 (`!n:N->bool. SMT_PERTURB_ID_STATEMENT n`,
  REWRITE_TAC[SMT_PERTURB_ID_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`U:real->real^N->real^N`; `c:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lip")))) THEN
  (* injectivity of x + U t x *)
  SUBGOAL_THEN `!t x x':real^N. x + (U:real->real^N->real^N) t x = x' + U t x'
                                ==> x = x'`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "lip" (MP_TAC o SPECL [`t:real`; `x':real^N`; `x:real^N`]) THEN
    SUBGOAL_THEN `(U:real->real^N->real^N) t x' - U t x = x - x'` SUBST1_TAC THENL
     [UNDISCH_TAC `x + (U:real->real^N->real^N) t x = x' + U t x'` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(x' - x:real^N) = norm(x - x')` SUBST1_TAC THENL
     [MATCH_ACCEPT_TAC NORM_SUB; DISCH_TAC] THEN
    ASM_CASES_TAC `norm(x - x':real^N) = &0` THENL
     [ASM_MESON_TAC[NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x - x':real^N)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `x - x':real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real`; `&1`; `norm(x - x':real^N)`] REAL_LT_RMUL) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* existence of the inverse, by the contraction principle *)
  SUBGOAL_THEN `!t (y:real^N). ?x. x + (U:real->real^N->real^N) t x = y` MP_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. y - (U:real->real^N->real^N) t x`; `(:real^N)`;
                   `c:real`] BANACH_FIX) THEN
    ASM_REWRITE_TAC[COMPLETE_UNIV; UNIV_NOT_EMPTY; SUBSET_UNIV; IN_UNIV; dist] THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
      REWRITE_TAC[VECTOR_ARITH `(y - u) - (y - v):real^N = v - u`] THEN
      USE_THEN "lip" (MP_TAC o SPECL [`t:real`; `b:real^N`; `a:real^N`]) THEN
      SUBGOAL_THEN `norm(a - b:real^N) = norm(b - a)` SUBST1_TAC THENL
       [MATCH_ACCEPT_TAC NORM_SUB; SIMP_TAC[]];
      DISCH_THEN(X_CHOOSE_TAC `x:real^N` o CONJUNCT1 o
        REWRITE_RULE[EXISTS_UNIQUE_THM]) THEN
      EXISTS_TAC `x:real^N` THEN
      UNDISCH_TAC `y - (U:real->real^N->real^N) t x = x` THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^N->real^N` (LABEL_TAC "G")) THEN
  SUBGOAL_THEN `!t x. (G:real->real^N->real^N) t (x + (U:real->real^N->real^N) t x) = x`
  (LABEL_TAC "GF") THENL
   [REPEAT GEN_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    EXISTS_TAC `t:real` THEN USE_THEN "G" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the forward family is smooth *)
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,N)finite_sum)
      (\z. sndcart z + (U:real->real^N->real^N) (drop(fstcart z)) (sndcart z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\z:real^(1,N)finite_sum. z`]
        SMOOTH_MAP_ON_SNDCART_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      UNDISCH_TAC `smooth_family (:real^N) (U:real->real^N->real^N)` THEN
      REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV]];
    ALL_TAC] THEN
  (* the inverse family is jointly smooth: inverse function theorem *)
  SUBGOAL_THEN
   `smooth_map_on (:real^(1,N)finite_sum)
      (\z. (G:real->real^N->real^N) (drop(fstcart z)) (sndcart z))`
  ASSUME_TAC THENL
   [ABBREV_TAC
     `Phi = \z:real^(1,N)finite_sum.
              pastecart (fstcart z)
                (sndcart z + (U:real->real^N->real^N) (drop(fstcart z)) (sndcart z))` THEN
    ABBREV_TAC
     `Psi = \z:real^(1,N)finite_sum.
              pastecart (fstcart z) ((G:real->real^N->real^N) (drop(fstcart z)) (sndcart z))` THEN
    SUBGOAL_THEN
     `smooth_map_on (:real^(1,N)finite_sum)
                    (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum)`
    ASSUME_TAC THENL
     [EXPAND_TAC "Phi" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV] THEN
      MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\z:real^(1,N)finite_sum. z`]
        SMOOTH_MAP_ON_FSTCART_OPEN) THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!z. (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum)
            ((Psi:real^(1,N)finite_sum->real^(1,N)finite_sum) z) = z`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Phi"; "Psi"] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      USE_THEN "G" (fun th -> REWRITE_TAC[th; PASTECART_FST_SND]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!z w. (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) z = Phi w ==> z = w`
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:real^(1,N)finite_sum`; `w:real^(1,N)finite_sum`] THEN
      EXPAND_TAC "Phi" THEN REWRITE_TAC[PASTECART_INJ] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[PASTECART_EQ] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inj" MATCH_MP_TAC THEN
      EXISTS_TAC `drop(fstcart(w:real^(1,N)finite_sum))` THEN
      UNDISCH_TAC
       `sndcart z + (U:real->real^N->real^N) (drop(fstcart z)) (sndcart z) =
        sndcart w + U (drop(fstcart(w:real^(1,N)finite_sum))) (sndcart w)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* the derivative of Phi is injective *)
    SUBGOAL_THEN
     `!w. ~(det(matrix(frechet_derivative
               (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) (at w))) = &0)`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN
      ABBREV_TAC `DU = frechet_derivative
                        (\z:real^(1,N)finite_sum. (U:real->real^N->real^N)
                            (drop(fstcart z)) (sndcart z)) (at w)` THEN
      SUBGOAL_THEN
       `((\z:real^(1,N)finite_sum. (U:real->real^N->real^N)
           (drop(fstcart z)) (sndcart z)) has_derivative DU) (at w)`
      ASSUME_TAC THENL
       [EXPAND_TAC "DU" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        UNDISCH_TAC `smooth_family (:real^N) (U:real->real^N->real^N)` THEN
        REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV; OPEN_UNIV; IN_UNIV];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `((Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) has_derivative
         (\h. pastecart (fstcart h) (sndcart h + DU h))) (at w)`
      ASSUME_TAC THENL
       [EXPAND_TAC "Phi" THEN
        MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
          REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_FSTCART];
          MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
          REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_SNDCART]];
        ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      SUBGOAL_THEN `linear (DU:real^(1,N)finite_sum->real^N)` ASSUME_TAC THENL
       [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
      SUBGOAL_THEN `linear (\h:real^(1,N)finite_sum. pastecart (fstcart h)
                                (sndcart h + (DU:real^(1,N)finite_sum->real^N) h))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LINEAR_PASTECART THEN
        REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_FSTCART] THEN
        MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
        ASM_REWRITE_TAC[REWRITE_RULE[ETA_AX] LINEAR_SNDCART];
        ALL_TAC] THEN
      ASM_SIMP_TAC[DET_MATRIX_EQ_0_LEFT] THEN
      MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN
      X_GEN_TAC `h:real^(1,N)finite_sum` THEN
      REWRITE_TAC[GSYM PASTECART_VEC; PASTECART_INJ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(h:real^(1,N)finite_sum) = pastecart (vec 0) (sndcart h)` SUBST_ALL_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC `k = sndcart(h:real^(1,N)finite_sum)` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SNDCART_PASTECART]) THEN
      REWRITE_TAC[PASTECART_INJ] THEN
      MP_TAC(ISPECL
       [`\z:real^(1,N)finite_sum. (U:real->real^N->real^N) (drop(fstcart z)) (sndcart z)`;
        `DU:real^(1,N)finite_sum->real^N`; `w:real^(1,N)finite_sum`;
        `pastecart (vec 0) k:real^(1,N)finite_sum`; `c:real`]
       HAS_DERIVATIVE_LIPSCHITZ_DIRECTION) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
        REWRITE_TAC[FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                    FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_RZERO;
                    VECTOR_ADD_RID; NORM_PASTECART_0] THEN
        USE_THEN "lip" (MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                        `sndcart(w:real^(1,N)finite_sum) + r % k`;
                                        `sndcart(w:real^(1,N)finite_sum)`]) THEN
        REWRITE_TAC[VECTOR_ADD_SUB; NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_AC];
        ALL_TAC] THEN
      REWRITE_TAC[NORM_PASTECART_0] THEN
      UNDISCH_TAC `k + (DU:real^(1,N)finite_sum->real^N) (pastecart (vec 0) k) = vec 0` THEN
      REWRITE_TAC[VECTOR_ARITH `k + d = vec 0 <=> d = --k:real^N`] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_NEG] THEN DISCH_TAC THEN
      ASM_CASES_TAC `k:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < norm(k:real^N)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:real`; `&1`; `norm(k:real^N)`] REAL_LT_RMUL) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z0:real^(1,N)finite_sum` THEN
    MP_TAC(ISPECL [`Phi:real^(1,N)finite_sum->real^(1,N)finite_sum`;
                   `(:real^(1,N)finite_sum)`;
                   `(Psi:real^(1,N)finite_sum->real^(1,N)finite_sum) z0`]
      SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `T0:real^(1,N)finite_sum->bool` (X_CHOOSE_THEN
      `V:real^(1,N)finite_sum->bool` (X_CHOOSE_THEN
      `g:real^(1,N)finite_sum->real^(1,N)finite_sum` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `V:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `diffeomorphism_on T0 V
                   (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) g` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `sndcart o (g:real^(1,N)finite_sum->real^(1,N)finite_sum)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `v:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(g:real^(1,N)finite_sum->real^(1,N)finite_sum) v =
                    (Psi:real^(1,N)finite_sum->real^(1,N)finite_sum) v`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!z w. (Phi:real^(1,N)finite_sum->real^(1,N)finite_sum) z =
                                    Phi w ==> z = w`) (concl th))) THEN
        ASM_SIMP_TAC[];
        EXPAND_TAC "Psi" THEN REWRITE_TAC[SNDCART_PASTECART]];
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `G:real->real^N->real^N` THEN
  REWRITE_TAC[diffeo_isotopy; smooth_family; UNIV_PCROSS_UNIV] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `(G:real->real^N->real^N) t y` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `y + (U:real->real^N->real^N) t y` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`(:real^N)`; `\t x:real^N. x + (U:real->real^N->real^N) t x`;
                   `t:real`] SMT_FAMILY_SLICE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; smooth_family; UNIV_PCROSS_UNIV] THEN
    REWRITE_TAC[ETA_AX];
    MP_TAC(ISPECL [`(:real^N)`; `G:real->real^N->real^N`; `t:real`]
      SMT_FAMILY_SLICE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; smooth_family; UNIV_PCROSS_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* S3a (SMT_SMOOTH_ANGLE_STATEMENT).  A nonvanishing smooth                  *)
(* planar field is cexp of a continuous logarithm (the plane is              *)
(* contractible, CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE); the logarithm is     *)
(* smooth because cexp is a local diffeomorphism; it is normalised to 0 on   *)
(* the connected complement of the ball, where the field is e_1.             *)
(* ------------------------------------------------------------------------- *)

let SMT_SMOOTH_CEXP = prove
 (`smooth_map_on (:complex) cexp`,
  MP_TAC(ISPECL [`(:complex)`; `cexp`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIMINDEX_2] THEN
  REWRITE_TAC[ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CEXP; IM_CEXP] THEN
  REWRITE_TAC[RE_DEF; IM_DEF] THENL
   [MP_TAC(ISPECL [`(:complex)`; `\x:complex. lift(exp(x$1))`;
                   `\x:complex. lift(cos(x$2))`] SMOOTH_MAP_ON_LIFT_MUL);
    MP_TAC(ISPECL [`(:complex)`; `\x:complex. lift(exp(x$1))`;
                   `\x:complex. lift(sin(x$2))`] SMOOTH_MAP_ON_LIFT_MUL)] THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:complex)`; `\x:complex. lift(x$1)`] SMOOTH_MAP_ON_LIFT_EXP);
    MP_TAC(ISPECL [`(:complex)`; `\x:complex. lift(x$2)`] SMOOTH_MAP_ON_LIFT_COS);
    MP_TAC(ISPECL [`(:complex)`; `\x:complex. lift(x$1)`] SMOOTH_MAP_ON_LIFT_EXP);
    MP_TAC(ISPECL [`(:complex)`; `\x:complex. lift(x$2)`] SMOOTH_MAP_ON_LIFT_SIN)] THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[SMOOTH_MAP_ON_LIFT_COORDINATE; OPEN_UNIV]);;

let SMT_CEXP_DERIVATIVE_INVERTIBLE = prove
 (`!w. ~(det(matrix(frechet_derivative cexp (at w))) = &0)`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:complex` HAS_COMPLEX_DERIVATIVE_CEXP) THEN
  REWRITE_TAC[has_complex_derivative] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)] THEN
                       ASSUME_TAC th) THEN
  SUBGOAL_THEN `linear (\x. cexp w * x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  ASM_SIMP_TAC[DET_MATRIX_EQ_0_LEFT] THEN
  MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CEXP_NZ]);;

(* A continuous logarithm of a smooth nonvanishing map is smooth. *)

let SMT_SMOOTH_CONTINUOUS_LOG = prove
 (`!s (f:real^N->complex) g.
        open s /\ smooth_map_on s f /\ g continuous_on s /\
        (!x. x IN s ==> f x = cexp(g x))
        ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x0:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cexp`; `(:complex)`; `(g:real^N->complex) x0`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMT_SMOOTH_CEXP; SMT_CEXP_DERIVATIVE_INVERTIBLE;
              SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` (X_CHOOSE_THEN `u:complex->bool`
    (X_CHOOSE_THEN `L:complex->complex` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `{x | x IN s /\ (g:real^N->complex) x IN t}` THEN
  SUBGOAL_THEN `open {x | x IN s /\ (g:real^N->complex) x IN t}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  UNDISCH_TAC `diffeomorphism_on t u cexp (L:complex->complex)` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(L:complex->complex) o (f:real^N->complex)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* Solutions of cexp z = 1 are 2 pi i apart. *)

let SMT_CEXP_EQ_1_SEPARATED = prove
 (`!z w. cexp z = Cx(&1) /\ cexp w = Cx(&1) /\ ~(z = w) ==> &1 <= norm(w - z)`,
  REWRITE_TAC[CEXP_EQ_1] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC))
      ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(n - m = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(z:complex = w)` THEN
    REWRITE_TAC[COMPLEX_EQ] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `n - m = &0` THEN REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `n - m:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_SIMP_TAC[INTEGER_SUB] THEN DISCH_TAC THEN
  MP_TAC(SPEC `w - z:complex` COMPLEX_NORM_GE_RE_IM) THEN
  ASM_REWRITE_TAC[IM_SUB] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(&2 * n * pi - &2 * m * pi)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&2 * n * pi - &2 * m * pi = (&2 * pi) * (n - m)`;
              REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(abs(&2) * abs pi) * &1` THEN
  CONJ_TAC THENL
   [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS]]);;

(* S3a. *)

let SMT_SMOOTH_ANGLE = prove
 (`SMT_SMOOTH_ANGLE_STATEMENT`,
  REWRITE_TAC[SMT_SMOOTH_ANGLE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`v:real^2->real^2`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "far"))) THEN
  MP_TAC(ISPECL [`v:real^2->complex`; `(:real^2)`]
    CONTINUOUS_LOGARITHM_ON_CONTRACTIBLE) THEN
  ASM_SIMP_TAC[CONTRACTIBLE_UNIV; IN_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_UNIV;
               GSYM COMPLEX_VEC_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->complex` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "vg"))) THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (g:real^2->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_SMOOTH_CONTINUOUS_LOG THEN
    EXISTS_TAC `v:real^2->complex` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  (* g is constant (a multiple of 2 pi i) off the ball *)
  SUBGOAL_THEN `?c0. cexp c0 = Cx(&1) /\
                     !x. x IN (:real^2) DIFF ball(vec 0,r) ==> (g:real^2->complex) x = c0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x. x IN (:real^2) DIFF ball(vec 0,r) ==> cexp((g:real^2->complex) x) = Cx(&1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL_0; REAL_NOT_LT] THEN
      REPEAT STRIP_TAC THEN
      USE_THEN "vg" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "far" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_BASIS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^2->complex`; `(:real^2) DIFF ball(vec 0,r)`]
      CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
        MATCH_MP_TAC PATH_CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
        REWRITE_TAC[DIMINDEX_2; BOUNDED_BALL; CONVEX_BALL] THEN ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
        MATCH_MP_TAC SMT_CEXP_EQ_1_SEPARATED THEN ASM_SIMP_TAC[]];
      DISCH_THEN(X_CHOOSE_TAC `c0:complex`) THEN EXISTS_TAC `c0:complex` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(?x:real^2. x IN (:real^2) DIFF ball(vec 0,r))` MP_TAC THENL
       [EXISTS_TAC `(abs r + &1) % basis 1:real^2` THEN
        REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL_0; NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
        STRIP_TAC THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^2. Im((g:real^2->complex) x - c0)` THEN
  EXISTS_TAC `\x:real^2. exp(Re((g:real^2->complex) x - c0))` THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (\x. (g:real^2->complex) x - c0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. (g:real^2->complex) x - c0`;
                   `\z:complex. lift(z$2)`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LINEAR_LIFT_COMPONENT; o_DEF; IM_DEF];
    MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift(Re((g:real^2->complex) x - c0))`]
      SMOOTH_MAP_ON_LIFT_EXP) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. (g:real^2->complex) x - c0`;
                   `\z:complex. lift(z$1)`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LINEAR_LIFT_COMPONENT; o_DEF; RE_DEF];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^2->complex) x = c0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL_0; REAL_NOT_LT];
      REWRITE_TAC[COMPLEX_SUB_REFL; RE_CX; IM_CX; REAL_EXP_0]];
    X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN `(v:real^2->real^2) x = cexp((g:real^2->complex) x - c0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CEXP_SUB; COMPLEX_DIV_1] THEN
      USE_THEN "vg" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CEXP; IM_CEXP]]);;

