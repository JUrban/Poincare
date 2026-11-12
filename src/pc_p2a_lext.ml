(* ========================================================================= *)
(* pc_p2a_lext: extension of solutions of the L-geodesic system to the ends  *)
(* of an interval (used for the regularity of minimizers, L2, at s = 0 and   *)
(* at stage changes).  The acceleration is quadratic in the velocity, so     *)
(* finite energy bounds the variation of the velocity; it then has limits at *)
(* the ends, and the system holds there one-sidedly.                         *)
(*                                                                           *)
(* First: the quadratic bound and one-sided derivatives at the ends.         *)
(* ========================================================================= *)

needs "src/pc_p2a_pconv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The acceleration along rays: quadratic plus linear plus constant.        *)
(* ------------------------------------------------------------------------- *)

(* P2A_LRICOP_LINEAR (linearity of p2a_lricop) is in pc_p2a_rflow.          *)

let P2A_LACC_RAY = prove
 (`!U (Gt:real->real^N->real^N^N) tt s y (e:real^N) t.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> p2a_lacc Gt tt s y (t % e) =
         (t pow 2) % (inv(&2) % (p2a_lacc Gt tt s y e + p2a_lacc Gt tt s y (--e)) -
                      p2a_lacc Gt tt s y (vec 0)) +
         t % (inv(&2) % (p2a_lacc Gt tt s y e - p2a_lacc Gt tt s y (--e))) +
         p2a_lacc Gt tt s y (vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lacc] THEN
  ABBREV_TAC `G0 = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  SUBGOAL_THEN `bilinear (christoffel (G0:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (p2a_lricop (G0:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LRICOP_LINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC(map (fun th -> MATCH_MP th
                    (ASSUME `bilinear (christoffel (G0:real^N->real^N^N) y)`))
                  [BILINEAR_LMUL; BILINEAR_RMUL; BILINEAR_LNEG; BILINEAR_RNEG;
                   BILINEAR_LZERO; BILINEAR_RZERO] @
              map (fun th -> MATCH_MP th (ASSUME `linear (p2a_lricop (G0:real^N->real^N^N) y)`))
                  [LINEAR_CMUL; LINEAR_NEG; LINEAR_0]) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_MUL_ASSOC; REAL_POW_2] THEN
  VECTOR_ARITH_TAC);;

let P2A_LACC_QUAD_BOUND = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt p q Kc.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < p /\ p <= q /\ q < sb /\
     compact Kc /\ Kc SUBSET U
     ==> ?C. &0 < C /\
             !s y a. p <= s /\ s <= q /\ y IN Kc
                     ==> norm(p2a_lacc Gt tt s y a) <= C * (&1 + norm a pow 2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LFIELD_SMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o BETA_RULE o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  ABBREV_TAC `K3 = interval[lift p,lift q] PCROSS
                   ((Kc:real^N->bool) PCROSS cball(vec 0:real^N,&1))` THEN
  SUBGOAL_THEN `compact(K3:real^(1,(N,N)finite_sum)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K3" THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p2a_lfield (Gt:real->real^N->real^N^N) tt) continuous_on K3` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    EXPAND_TAC "K3" THEN REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_lfield (Gt:real->real^N->real^N^N) tt`; `K3:real^(1,(N,N)finite_sum)finite_sum->bool`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s y a. p <= s /\ s <= q /\ y IN Kc /\ norm(a:real^N) <= &1
            ==> norm(p2a_lacc (Gt:real->real^N->real^N^N) tt s y a) <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (pastecart (y:real^N) (a:real^N))`) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "K3" THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_CBALL_0];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= b ==> x <= b`) THEN
    REWRITE_TAC[p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REWRITE_TAC[NORM_PASTECART] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_LE_ADDL; REAL_LE_POW_2];
    ALL_TAC] THEN
  EXISTS_TAC `&3 * B` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `a:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2)) /\ (y:real^N) IN U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B:real` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_0; REAL_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `e:real^N = inv(norm a) % a` THEN
  SUBGOAL_THEN `norm(e:real^N) = &1 /\ norm(--e:real^N) = &1 /\ (a:real^N) = norm a % e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; VECTOR_MUL_ASSOC; REAL_MUL_RINV;
                 VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`;
                 `y:real^N`; `e:real^N`; `norm(a:real^N)`] P2A_LACC_RAY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `norm(p2a_lacc (Gt:real->real^N->real^N^N) tt s y e) <= B /\
    norm(p2a_lacc Gt tt s y (--e)) <= B /\ norm(p2a_lacc Gt tt s y (vec 0)) <= B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_0; REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `t = norm(a:real^N)` THEN
  SUBGOAL_THEN `&0 <= t /\ abs t = t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_NORM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `t pow 2 * (B + B) + t * B + B` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^N) <= a /\ norm(y:real^N) <= b /\ norm(z:real^N) <= c
      ==> norm(x + y + z) <= a + b + c`) THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [NORM_MUL] THEN ASM_REWRITE_TAC[REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) <= B /\ norm(y:real^N) <= B /\ norm(z:real^N) <= B
        ==> norm(inv(&2) % (x + y) - z) <= B + B`) THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) <= B /\ norm(y:real^N) <= B ==> norm(inv(&2) % (x - y)) <= B`) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t <= &1 + t pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `t - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * B <= (&1 + t pow 2) * B` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= B` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* One-sided derivatives at the ends of an interval from limits of the       *)
(* derivative (fundamental theorem of calculus), and the extension of        *)
(* finite-energy solutions of the L-geodesic system to the closed interval.  *)
(* ========================================================================= *)

let P2A_ENDPOINT_DERIV_LEFT = prove
 (`!(f:real^1->real^N) f' a b L.
     a < b /\ f continuous_on interval[lift a,lift b] /\
     (!s. a < s /\ s < b ==> (f has_vector_derivative f'(lift s)) (at (lift s))) /\
     (!e. &0 < e
          ==> ?d. &0 < d /\ !s. a < s /\ s < a + d ==> norm(f'(lift s) - L) <= e)
     ==> (f has_vector_derivative L) (at (lift a) within interval[lift a,lift b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN_ALT] THEN
  CONJ_TAC THENL [MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (b - a)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real = a` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; REAL_SUB_REFL; VECTOR_MUL_LZERO; NORM_0;
                    REAL_ABS_0; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < x /\ x < b /\ x < a + d` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^N`;
                 `\v:real^1. if drop v = a then L else (f':real^1->real^N) v`;
                 `{}:real->bool`; `a:real`; `x:real`] P2A_PW_HAS_INTEGRAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift a,lift b]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(s:real = a)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. (if drop v = a then L else (f':real^1->real^N) v) - L`;
                 `lift a`; `lift x`;
                 `((f:real^1->real^N)(lift x) - f(lift a)) -
                  content(interval[lift a,lift x]) % (L:real^N)`; `e:real`]
                HAS_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_REWRITE_TAC[HAS_INTEGRAL_CONST];
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ b = c ==> x <= b ==> y <= c`) THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN VECTOR_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2A_ENDPOINT_DERIV_RIGHT = prove
 (`!(f:real^1->real^N) f' a b L.
     a < b /\ f continuous_on interval[lift a,lift b] /\
     (!s. a < s /\ s < b ==> (f has_vector_derivative f'(lift s)) (at (lift s))) /\
     (!e. &0 < e
          ==> ?d. &0 < d /\ !s. b - d < s /\ s < b ==> norm(f'(lift s) - L) <= e)
     ==> (f has_vector_derivative L) (at (lift b) within interval[lift a,lift b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN_ALT] THEN
  CONJ_TAC THENL [MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (b - a)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real = b` THENL
   [ASM_REWRITE_TAC[VECTOR_SUB_REFL; REAL_SUB_REFL; VECTOR_MUL_LZERO; NORM_0;
                    REAL_ABS_0; REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < x /\ x < b /\ b - d < x` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^N`;
                 `\v:real^1. if drop v = b then L else (f':real^1->real^N) v`;
                 `{}:real->bool`; `x:real`; `b:real`] P2A_PW_HAS_INTEGRAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift a,lift b]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(s:real = b)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. (if drop v = b then L else (f':real^1->real^N) v) - L`;
                 `lift x`; `lift b`;
                 `((f:real^1->real^N)(lift b) - f(lift x)) -
                  content(interval[lift x,lift b]) % (L:real^N)`; `e:real`]
                HAS_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_REWRITE_TAC[HAS_INTEGRAL_CONST];
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTENT_1; LIFT_DROP; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ b = c ==> x <= b ==> y <= c`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `u = --v ==> norm u = norm (v:real^N)`) THEN VECTOR_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The extension.                                                            *)

let P2A_LODE_EXTEND = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt p q Kc (Y:real^1->real^N) A.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < p /\ p < q /\ q < sb /\
     compact Kc /\ Kc SUBSET U /\
     Y continuous_on interval[lift p,lift q] /\
     (!s. p <= s /\ s <= q ==> Y(lift s) IN Kc) /\
     (!s. p < s /\ s < q
          ==> (Y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (Y(lift s)) (A(lift s)))
                (at (lift s))) /\
     (\s. norm(A(lift s)) pow 2) real_integrable_on real_interval[p,q]
     ==> ?A'. (!s. p < s /\ s < q ==> A'(lift s) = A(lift s)) /\
              A' continuous_on interval[lift p,lift q] /\
              (!s. p <= s /\ s <= q
                   ==> (Y has_vector_derivative A'(lift s))
                         (at (lift s) within interval[lift p,lift q]) /\
                       (A' has_vector_derivative p2a_lacc Gt tt s (Y(lift s)) (A'(lift s)))
                         (at (lift s) within interval[lift p,lift q]))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K")
     (CONJUNCTS_THEN2 (LABEL_TAC "D") ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `p:real`; `q:real`; `Kc:real^N->bool`] P2A_LACC_QUAD_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LFIELD_SMOOTH) THEN
  (* A is continuous on the open interval *)
  SUBGOAL_THEN `!s. p < s /\ s < q ==> (A:real^1->real^N) continuous (at (lift s))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2) real_integrable_on real_interval[p,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
  (* the variation bound *)
  SUBGOAL_THEN
   `!s t. p < s /\ s <= t /\ t < q
          ==> norm((A:real^1->real^N)(lift t) - A(lift s)) <=
              C * real_integral (real_interval[s,t]) (\u. &1 + norm(A(lift u)) pow 2)`
  (LABEL_TAC "var") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(A:real^1->real^N) continuous_on interval[lift s,lift t] /\
                  (Y:real^1->real^N) continuous_on interval[lift s,lift t]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift p,lift q]` THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `H = \v:real^1. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop v)
                                        ((Y:real^1->real^N) v) ((A:real^1->real^N) v)` THEN
    SUBGOAL_THEN `(H:real^1->real^N) continuous_on interval[lift s,lift t]` ASSUME_TAC THENL
     [EXPAND_TAC "H" THEN
      SUBGOAL_THEN
       `(\v:real^1. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop v) ((Y:real^1->real^N) v)
                              ((A:real^1->real^N) v)) =
        sndcart o p2a_lfield Gt tt o (\v. pastecart v (pastecart (Y v) (A v)))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV; FORALL_LIFT;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(Y:real^1->real^N)(lift u) IN Kc` MP_TAC THENL
       [USE_THEN "K" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:real^1->real^N`; `interval[lift s,lift t]`] COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `MH:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\v:real^1. (A:real^1->real^N) v - A(lift s)`; `H:real^1->real^N`;
                   `{}:real->bool`; `s:real`; `t:real`; `MH:real`; `t:real`]
                  P2A_VNORM_FTC_BOUND_PW) THEN
    REWRITE_TAC[VECTOR_SUB_REFL; FINITE_EMPTY; NOT_IN_EMPTY; REAL_LE_REFL] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]; ALL_TAC] THEN
      TRY(CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[] THEN NO_TAC]) THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [VECTOR_ARITH `v:real^N = v - vec 0`] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
      EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
      USE_THEN "D" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    SUBGOAL_THEN `(\u. norm((H:real^1->real^N)(lift u))) real_integrable_on real_interval[s,t]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MP_TAC(ISPECL [`\x:real^1. norm((H:real^1->real^N) x)`; `s:real`; `t:real`]
                    P2A_REAL_CONT_OF_VEC) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM_COMPOSE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2) real_integrable_on real_interval[s,t]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "K" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* uniform continuity of A on the open interval *)
  SUBGOAL_THEN `(A:real^1->real^N) uniformly_continuous_on interval(lift p,lift q)`
  ASSUME_TAC THENL
   [REWRITE_TAC[uniformly_continuous_on] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2`; `p:real`; `q:real`]
                  REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x. real_integral (real_interval[p,x])
                           (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)`;
                   `real_interval[p,q]`] REAL_COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; real_uniformly_continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e / C`) THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; DIST_LIFT] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `x':real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!s t. p < s /\ s <= t /\ t < q /\ abs(t - s) < d
            ==> dist((A:real^1->real^N)(lift t),A(lift s)) < e`
    (fun th -> ASM_CASES_TAC `x <= x':real` THENL
      [MATCH_MP_TAC th THEN ASM_REAL_ARITH_TAC;
       ONCE_REWRITE_TAC[DIST_SYM] THEN MATCH_MP_TAC th THEN ASM_REAL_ARITH_TAC]) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `C * real_integral (real_interval[s,t])
                      (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)` THEN
    CONJ_TAC THENL [USE_THEN "var" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `t:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2`; `p:real`; `t:real`;
                   `s:real`] REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 <= real_integral (real_interval[s,t])
                          (\u. &1 + norm((A:real^1->real^N)(lift u)) pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`p:real`; `q:real`] THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        MP_TAC(SPEC `norm((A:real^1->real^N)(lift x''))` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the extension to the closed interval *)
  FIRST_ASSUM(MP_TAC o MATCH_MP UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE) THEN
  SUBGOAL_THEN `closure(interval(lift p,lift q)) = interval[lift p,lift q]` SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `h:real^1->real^N`)) (concl th))) THEN
  SUBGOAL_THEN `!s. p < s /\ s < q ==> (g:real^1->real^N)(lift s) = A(lift s)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^1->real^N) continuous_on interval[lift p,lift q]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS]; ALL_TAC] THEN
  EXISTS_TAC `g:real^1->real^N` THEN ASM_REWRITE_TAC[] THEN
  (* derivatives of g at interior points *)
  SUBGOAL_THEN
   `!s. p < s /\ s < q
        ==> ((g:real^1->real^N) has_vector_derivative
             p2a_lacc (Gt:real->real^N->real^N^N) tt s ((Y:real^1->real^N)(lift s)) (g(lift s)))
            (at (lift s))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`A:real^1->real^N`; `min (s - p) (q - s)`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_LIFT; DIST_LIFT] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "D" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the field along the extended solution is continuous on the closed interval *)
  ABBREV_TAC `H = \v:real^1. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop v)
                                      ((Y:real^1->real^N) v) ((g:real^1->real^N) v)` THEN
  SUBGOAL_THEN `(H:real^1->real^N) continuous_on interval[lift p,lift q]` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    SUBGOAL_THEN
     `(\v:real^1. p2a_lacc (Gt:real->real^N->real^N^N) tt (drop v) ((Y:real^1->real^N) v)
                            ((g:real^1->real^N) v)) =
      sndcart o p2a_lfield Gt tt o (\v. pastecart v (pastecart (Y v) (g v)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p2a_lfield; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Y:real^1->real^N)(lift u) IN Kc` MP_TAC THENL
     [USE_THEN "K" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x0. p <= x0 /\ x0 <= q
         ==> !e. &0 < e ==> ?d. &0 < d /\
                                !s. p <= s /\ s <= q /\ abs(s - x0) < d
                                    ==> norm((H:real^1->real^N)(lift s) - H(lift x0)) <= e /\
                                        norm((g:real^1->real^N)(lift s) - g(lift x0)) <= e`
  ASSUME_TAC THENL
   [X_GEN_TAC `x0:real` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(H:real^1->real^N) continuous_on interval[lift p,lift q]` THEN
    UNDISCH_TAC `(g:real^1->real^N) continuous_on interval[lift p,lift q]` THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `lift x0`) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `lift x0`) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `lift s IN interval[lift p,lift q] /\ dist(lift s,lift x0) < d1 /\
                  dist(lift s,lift x0) < d2` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = p` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ENDPOINT_DERIV_LEFT THEN EXISTS_TAC `A:real^1->real^N` THEN
      ASM_SIMP_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `x0:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (q - p)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(A:real^1->real^N)(lift u) = g(lift u)` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC P2A_ENDPOINT_DERIV_LEFT THEN EXISTS_TAC `H:real^1->real^N` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `x0:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (q - p)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `p2a_lacc (Gt:real->real^N->real^N^N) tt p ((Y:real^1->real^N)(lift p))
                             ((g:real^1->real^N)(lift p)) = H(lift p)` SUBST1_TAC THENL
       [EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = q` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ENDPOINT_DERIV_RIGHT THEN EXISTS_TAC `A:real^1->real^N` THEN
      ASM_SIMP_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `x0:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (q - p)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(A:real^1->real^N)(lift u) = g(lift u)` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC P2A_ENDPOINT_DERIV_RIGHT THEN EXISTS_TAC `H:real^1->real^N` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `u:real` THEN STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `x0:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min d (q - p)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `p2a_lacc (Gt:real->real^N->real^N^N) tt q ((Y:real^1->real^N)(lift q))
                             ((g:real^1->real^N)(lift q)) = H(lift q)` SUBST1_TAC THENL
       [EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p < s /\ s < q` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[] THEN
  USE_THEN "D" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]);;

