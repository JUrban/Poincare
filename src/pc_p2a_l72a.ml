(* ========================================================================= *)
(* pc_p2a_l72a: chart-level analysis for O10 (P2A_ROUTE_LEMMA_7_2_X).  Chart *)
(* curves z on [a,b] that are continuous and differentiable off a finite     *)
(* set, with square-integrable derivative (no bound on z'; the pieces of     *)
(* p2a_admx curves have singular corners): the displacement bound by         *)
(* Cauchy-Schwarz, the chord regularization, and the comparison with the     *)
(* local boundary value problem (P2A_LOC_BVP_PW).  Generic in N.             *)
(*                                                                           *)
(* The first part: integrability of the speed and the displacement bound.    *)
(* ========================================================================= *)

needs "src/pc_p2a_pconv.ml";;

prioritize_real();;
type_invention_error := true;;

(* Square-integrable derivative off a finite set: the speed is integrable,  *)
(* bounds the displacement, and |z b - z a|^2 <= (b - a) int |z'|^2.        *)

let P2AK_FE_DISP = prove
 (`!(z:real^1->real^N) z' K a b.
     a <= b /\ FINITE K /\ z continuous_on interval[lift a,lift b] /\
     (!s. a < s /\ s < b /\ ~(s IN K)
          ==> (z has_vector_derivative z'(lift s)) (at (lift s))) /\
     (\s. norm(z'(lift s)) pow 2) real_integrable_on real_interval[a,b]
     ==> (\s. norm(z'(lift s))) real_integrable_on real_interval[a,b] /\
         norm(z(lift b) - z(lift a)) <=
         real_integral (real_interval[a,b]) (\s. norm(z'(lift s))) /\
         norm(z(lift b) - z(lift a)) pow 2 <=
         (b - a) * real_integral (real_interval[a,b]) (\s. norm(z'(lift s)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`; `a:real`; `b:real`]
                P2A_PW_HAS_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`; `a:real`; `b:real`]
                P2A_PW_MEASURABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\s. norm((z':real^1->real^N)(lift s))) real_integrable_on real_interval[a,b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x:real^1. lift((&1 + norm((z':real^1->real^N) x) pow 2) / &2)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`z':real^1->real^N`; `interval[lift a,lift b]`] MEASURABLE_ON_NORM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\s. (&1 + norm((z':real^1->real^N)(lift s)) pow 2) / &2) real_integrable_on
        real_interval[a,b]`
      MP_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN
        MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_NORM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `norm((z':real^1->real^N) x) - &1` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `norm((z:real^1->real^N)(lift b) - z(lift a)) <=
    real_integral (real_interval[a,b]) (\s. norm((z':real^1->real^N)(lift s)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
    SUBGOAL_THEN `(z:real^1->real^N)(lift b) - z(lift a) =
                  integral (interval[lift a,lift b]) (z':real^1->real^N)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(\s. norm((z':real^1->real^N)(lift s))) real_integrable_on real_interval[a,b]` THEN
    REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[a,b]) (\s. norm((z':real^1->real^N)(lift s))) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    MP_TAC(ISPECL [`\s. norm((z':real^1->real^N)(lift s))`; `a:real`; `b:real`] P2A_REAL_CS) THEN
    ASM_REWRITE_TAC[]]);;

(* Upper bounds for the metric and the scalar curvature of a smooth family *)
(* on a compact set (with P2A_UNIFORM_BOUNDS for the lower bound).          *)

let P2AK_LLAG_UPPER = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt K a b.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ compact K /\ K SUBSET U /\
     sa < a /\ b < sb
     ==> ?Gm Rm. &0 <= Gm /\ &0 <= Rm /\
                 !s y u. a <= s /\ s <= b /\ y IN K
                         ==> u dot (Gt(tt - s pow 2) y ** u) <= Gm * norm u pow 2 /\
                             abs(lscalar (Gt(tt - s pow 2)) y) <= Rm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `K:real^N->bool`; `a:real`; `b:real`] P2A_UB_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = interval[lift a,lift b] PCROSS (K:real^N->bool)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `bounded(IMAGE (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2) (sndcart z)))
                  (S:real^(1,N)finite_sum->bool)) /\
    bounded(IMAGE (\z. lift(lscalar ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2))
                                    (sndcart z)))
                  (S:real^(1,N)finite_sum->bool))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`B1:real`; `B2:real`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `u:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift s) (y:real^N) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (y:real^N)` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "vectorize")) (concl th))) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize((Gt:real->real^N->real^N^N)(tt - s pow 2) y)) *
                norm(u:real^N) * norm u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(Gt:real->real^N->real^N^N)(tt - s pow 2) y`; `u:real^N`; `u:real^N`]
                    P2A_QF_BOUND) THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (y:real^N)`) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; NORM_LIFT]]);;

(* ------------------------------------------------------------------------- *)
(* Curves with square-integrable derivative whose derivative is bounded     *)
(* away from a finite set B of bad points (p2ak_sq), and the chord step:    *)
(* the curve is replaced by the chord on a small interval around one bad    *)
(* point c; the energy does not increase (Cauchy-Schwarz), the L-functional *)
(* increases by at most eta, c is no longer bad.                            *)
(* ------------------------------------------------------------------------- *)

let p2ak_sq = new_definition
 `p2ak_sq (U:real^N->bool) (a:real) (b:real) (z:real^1->real^N) (z':real^1->real^N)
          (K:real->bool) (B:real->bool) <=>
    a <= b /\ FINITE K /\ B SUBSET K /\ B SUBSET real_interval[a,b] /\
    z continuous_on interval[lift a,lift b] /\
    (!s. a <= s /\ s <= b ==> z(lift s) IN U) /\
    (!s. a < s /\ s < b /\ ~(s IN K)
         ==> (z has_vector_derivative z'(lift s)) (at (lift s))) /\
    (\s. norm(z'(lift s)) pow 2) real_integrable_on real_interval[a,b] /\
    (!e. &0 < e
         ==> ?M. !s. a <= s /\ s <= b /\ ~(s IN K) /\ (!c. c IN B ==> e <= abs(s - c))
                     ==> norm(z'(lift s)) <= M)`;;

(* An affine chart curve and the chord between two values.                  *)

let P2AK_AFFINE_VD = prove
 (`!(p:real^N) w u x. ((\x:real^1. p + (drop x - u) % w) has_vector_derivative w) (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL [`\x:real^1. (p:real^N) - u % w`; `\h:real^1. vec 0:real^N`;
                 `\x:real^1. drop x % (w:real^N)`; `\h:real^1. drop h % (w:real^N)`;
                 `at (x:real^1)`] HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC);;

let P2AK_CHORD_END = prove
 (`!(p:real^N) q u v. u < v ==> p + (v - u) % (inv(v - u) % (q - p)) = q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `(v - u) * inv(v - u) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  VECTOR_ARITH_TAC);;

(* Integrals of a function changed on (u,v) only.                          *)

let P2AK_THREE_PIECES = prove
 (`!f0 f1 g a u v b.
     a <= u /\ u <= v /\ v <= b /\
     f0 real_integrable_on real_interval[a,b] /\ g real_integrable_on real_interval[u,v] /\
     (!s. a <= s /\ s <= u ==> f1 s = f0 s) /\ (!s. v <= s /\ s <= b ==> f1 s = f0 s) /\
     (!s. u < s /\ s < v ==> f1 s = g s)
     ==> f1 real_integrable_on real_interval[a,b] /\
         real_integral (real_interval[a,b]) f1 =
         real_integral (real_interval[a,b]) f0 - real_integral (real_interval[u,v]) f0 +
         real_integral (real_interval[u,v]) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `f0 real_integrable_on real_interval[a,u] /\ f0 real_integrable_on real_interval[u,v] /\
    f0 real_integrable_on real_interval[v,b] /\ f0 real_integrable_on real_interval[u,b]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f1 real_integrable_on real_interval[a,u] /\ f1 real_integrable_on real_interval[u,v] /\
    f1 real_integrable_on real_interval[v,b] /\
    real_integral (real_interval[a,u]) f1 = real_integral (real_interval[a,u]) f0 /\
    real_integral (real_interval[u,v]) f1 = real_integral (real_interval[u,v]) g /\
    real_integral (real_interval[v,b]) f1 = real_integral (real_interval[v,b]) f0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN EXISTS_TAC `f0:real->real` THEN
      ASM_SIMP_TAC[IN_REAL_INTERVAL];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `g:real->real` THEN EXISTS_TAC `{u:real,v}` THEN
      ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN EXISTS_TAC `f0:real->real` THEN
      ASM_SIMP_TAC[IN_REAL_INTERVAL];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_SIMP_TAC[IN_REAL_INTERVAL];
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{u:real,v}` THEN
      ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_SIMP_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `f1 real_integrable_on real_interval[u,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `f1 real_integrable_on real_interval[a,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,u]) f1 + real_integral (real_interval[u,b]) f1 =
    real_integral (real_interval[a,b]) f1 /\
    real_integral (real_interval[u,v]) f1 + real_integral (real_interval[v,b]) f1 =
    real_integral (real_interval[u,b]) f1 /\
    real_integral (real_interval[a,u]) f0 + real_integral (real_interval[u,b]) f0 =
    real_integral (real_interval[a,b]) f0 /\
    real_integral (real_interval[u,v]) f0 + real_integral (real_interval[v,b]) f0 =
    real_integral (real_interval[u,b]) f0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The chord-modified curve has the p2ak_sq properties, c no longer bad.    *)

let P2AK_CHORD_SQ = prove
 (`!U a b (z:real^1->real^N) z' K B c ep u v w ch z1 z1'.
     p2ak_sq U a b z z' K B /\ c IN B /\ &0 < ep /\
     a <= u /\ u < v /\ v <= b /\ (a < u ==> u = c - ep) /\ (v < b ==> v = c + ep) /\
     (!x. (ch has_vector_derivative w) (at x)) /\
     (!s. u <= s /\ s <= v ==> ch(lift s) IN U) /\
     ch(lift u) = z(lift u) /\ ch(lift v) = z(lift v) /\
     (!s. s <= u ==> z1(lift s) = z(lift s)) /\
     (!s. u <= s /\ s <= v ==> z1(lift s) = ch(lift s)) /\
     (!s. v <= s ==> z1(lift s) = z(lift s)) /\
     (!s. ~(u < s /\ s < v) ==> z1'(lift s) = z'(lift s)) /\
     (!s. u < s /\ s < v ==> z1'(lift s) = w) /\
     (\s. norm(z1'(lift s)) pow 2) real_integrable_on real_interval[a,b]
     ==> p2ak_sq U a b z1 z1' (u INSERT v INSERT K) (B DELETE c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN
                       MP_TAC(GEN_REWRITE_RULE I [p2ak_sq] (CONJUNCT1 th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inU")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "z1a") (CONJUNCTS_THEN2 (LABEL_TAC "z1b")
    (CONJUNCTS_THEN2 (LABEL_TAC "z1c") (CONJUNCTS_THEN2 (LABEL_TAC "d1a")
    (CONJUNCTS_THEN2 (LABEL_TAC "d1b") ASSUME_TAC)))))))))))))))) THEN
  REWRITE_TAC[p2ak_sq] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[FINITE_INSERT];
    UNDISCH_TAC `(B:real->bool) SUBSET K` THEN SET_TAC[];
    UNDISCH_TAC `(B:real->bool) SUBSET real_interval[a,b]` THEN SET_TAC[];
    (* continuity *)
    SUBGOAL_THEN `(z1:real^1->real^N) =
                  (\x. if drop x <= u then z x else if drop x <= v then ch x else z x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      ASM_CASES_TAC `drop(x:real^1) <= u` THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "z1a" (MP_TAC o SPEC `drop(x:real^1)`) THEN REWRITE_TAC[LIFT_DROP] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_CASES_TAC `drop(x:real^1) <= v` THENL
         [ASM_REWRITE_TAC[] THEN
          USE_THEN "z1b" (MP_TAC o SPEC `drop(x:real^1)`) THEN REWRITE_TAC[LIFT_DROP] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[] THEN
          USE_THEN "z1c" (MP_TAC o SPEC `drop(x:real^1)`) THEN REWRITE_TAC[LIFT_DROP] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift a,lift b]` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `\h:real^1. drop h % (w:real^N)` THEN
        ASM_REWRITE_TAC[GSYM has_vector_derivative];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[lift a,lift b]` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        DISCH_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[COND_ID]];
    (* values in U *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s <= u` THENL
     [USE_THEN "z1a" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `s <= u`)]) THEN
      USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `s <= v` THENL
     [SUBGOAL_THEN `u <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "z1b" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `u <= s`)
                                                             (ASSUME `s <= v`))]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `v <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "z1c" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `v <= s`)]) THEN
      USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* the derivative *)
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < u` THENL
     [USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th
        (UNDISCH(REAL_ARITH `s < u ==> ~(u < s /\ s < v)`))]) THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`z:real^1->real^N`; `u - s`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
        USE_THEN "z1a" (MP_TAC o SPEC `drop y`) THEN REWRITE_TAC[LIFT_DROP] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
        USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `s < v` THENL
     [SUBGOAL_THEN `u < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "d1b" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `u < s`)
                                                             (ASSUME `s < v`))]) THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`ch:real^1->real^N`; `min (s - u) (v - s)`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
        USE_THEN "z1b" (MP_TAC o SPEC `drop y`) THEN REWRITE_TAC[LIFT_DROP] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `v < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th
        (UNDISCH(REAL_ARITH `v < s ==> ~(u < s /\ s < v)`))]) THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`z:real^1->real^N`; `s - v`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN DISCH_TAC THEN
        USE_THEN "z1c" (MP_TAC o SPEC `drop y`) THEN REWRITE_TAC[LIFT_DROP] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
        USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    (* square-integrable derivative *)
    ASM_REWRITE_TAC[];
    (* bounded away from the remaining bad points *)
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o SPEC `min e ep`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `M0:real` (LABEL_TAC "M0"))] THEN
    EXISTS_TAC `max M0 (norm(w:real^N))` THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_INSERT; DE_MORGAN_THM; IN_DELETE] THEN STRIP_TAC THEN
    ASM_CASES_TAC `u < s /\ s < v` THENL
     [USE_THEN "d1b" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `u < s /\ s < v`)]) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(u < s /\ s < v)`)]) THEN
    MATCH_MP_TAC(REAL_ARITH `x <= M0 ==> x <= max M0 n`) THEN
    USE_THEN "M0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c':real` THEN DISCH_TAC THEN ASM_CASES_TAC `c':real = c` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `s < u \/ v < s` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `a < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `u = c - ep` ASSUME_TAC THENL
         [UNDISCH_TAC `a < u ==> u = c - ep` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `v < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `v = c + ep` ASSUME_TAC THENL
         [UNDISCH_TAC `v < b ==> v = c + ep` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `e <= x ==> min e ep <= x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The chord step.                                                            *)

let P2AK_CHORD_STEP = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt a b z z' K B c eta.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < a /\ a < b /\ b < sb /\
     p2ak_sq U a b z z' K B /\ c IN B /\
     (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) real_integrable_on real_interval[a,b] /\
     &0 < eta
     ==> ?z1 z1' K1.
           p2ak_sq U a b z1 z1' K1 (B DELETE c) /\
           z1(lift a) = z(lift a) /\ z1(lift b) = z(lift b) /\
           real_integral (real_interval[a,b]) (\s. norm(z1'(lift s)) pow 2) <=
           real_integral (real_interval[a,b]) (\s. norm(z'(lift s)) pow 2) /\
           (\s. p2a_llag Gt tt s (z1(lift s)) (z1'(lift s))) real_integrable_on
           real_interval[a,b] /\
           real_integral (real_interval[a,b])
             (\s. p2a_llag Gt tt s (z1(lift s)) (z1'(lift s))) <=
           real_integral (real_interval[a,b])
             (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) + eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_sq]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inU")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))))))) THEN
  SUBGOAL_THEN `a <= c /\ c <= b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(B:real->bool) SUBSET real_interval[a,b]` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  (* a closed ball around z c inside U, and the bounds of the Lagrangian there *)
  SUBGOAL_THEN `?r. &0 < r /\ cball((z:real^1->real^N)(lift c),r) SUBSET U`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`] OPEN_CONTAINS_CBALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `cball((z:real^1->real^N)(lift c),r)`; `a:real`; `b:real`] P2AK_LLAG_UPPER) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Gm:real` (X_CHOOSE_THEN `Rm:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `Sm = abs a + abs b` THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> s pow 2 <= Sm pow 2` (LABEL_TAC "Sm") THENL
   [EXPAND_TAC "Sm" THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `abs a + abs b = Sm` (K ALL_TAC) THEN
  (* continuity of z at c *)
  SUBGOAL_THEN
   `?e1. &0 < e1 /\
         !s. a <= s /\ s <= b /\ abs(s - c) < e1
             ==> (z:real^1->real^N)(lift s) IN ball(z(lift c),r)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^1->real^N) continuous_on interval[lift a,lift b]` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift c`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DIST_LIFT; IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  (* small integrals near c *)
  MP_TAC(ISPECL [`\s. norm((z':real^1->real^N)(lift s)) pow 2`; `a:real`; `b:real`; `c:real`;
                 `c:real`; `eta / (&3 * (Gm / &2 + &1))`] REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k1"))) THEN
  MP_TAC(ISPECL [`\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                                ((z':real^1->real^N)(lift s))`; `a:real`; `b:real`; `c:real`;
                 `c:real`; `eta / &3`] REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "k2"))) THEN
  ABBREV_TAC `ep = min (min (e1 / &2) (min k1 k2)) (eta / (&12 * (Sm pow 2 * Rm + &1)))` THEN
  SUBGOAL_THEN `&0 < ep /\ ep < e1 /\ ep <= k1 /\ ep <= k2 /\
                &12 * (Sm pow 2 * Rm + &1) * ep <= eta`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &12 * (Sm pow 2 * Rm + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta / (&12 * (Sm pow 2 * Rm + &1)) /\
                  (&12 * (Sm pow 2 * Rm + &1)) * (eta / (&12 * (Sm pow 2 * Rm + &1))) = eta`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV] THEN
      UNDISCH_TAC `&0 < &12 * (Sm pow 2 * Rm + &1)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `ep <= eta / (&12 * (Sm pow 2 * Rm + &1))` ASSUME_TAC THENL
     [EXPAND_TAC "ep" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&12 * (Sm pow 2 * Rm + &1)) * (eta / (&12 * (Sm pow 2 * Rm + &1)))` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  UNDISCH_THEN `min (min (e1 / &2) (min k1 k2)) (eta / (&12 * (Sm pow 2 * Rm + &1))) = ep`
    (K ALL_TAC) THEN
  (* the chord interval [u,v] *)
  ABBREV_TAC `u = max a (c - ep)` THEN ABBREV_TAC `v = min b (c + ep)` THEN
  SUBGOAL_THEN `a <= u /\ u <= c /\ c <= v /\ v <= b /\ u < v /\ u <= v /\ v - u <= &2 * ep /\
                abs(u - c) <= ep /\ abs(v - c) <= ep /\
                (a < u ==> u = c - ep) /\ (v < b ==> v = c + ep)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_THEN `max a (c - ep) = u` (K ALL_TAC) THEN
  UNDISCH_THEN `min b (c + ep) = v` (K ALL_TAC) THEN
  SUBGOAL_THEN `sa < u /\ v < sb` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the chord on [u,v] *)
  ABBREV_TAC `w = inv(v - u) % ((z:real^1->real^N)(lift v) - z(lift u))` THEN
  ABBREV_TAC `ch = \x:real^1. (z:real^1->real^N)(lift u) + (drop x - u) % w` THEN
  SUBGOAL_THEN `(ch:real^1->real^N)(lift u) = z(lift u) /\ ch(lift v) = z(lift v)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ch" THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[LIFT_DROP; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    MATCH_MP_TAC P2AK_CHORD_END THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ((ch:real^1->real^N) has_vector_derivative w) (at x)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "ch" THEN REWRITE_TAC[P2AK_AFFINE_VD]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. u <= s /\ s <= v ==> (ch:real^1->real^N)(lift s) IN ball(z(lift c),r)`
  (LABEL_TAC "chb") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^1->real^N)(lift u) IN ball(z(lift c),r) /\
                  z(lift v) IN ball(z(lift c),r)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(ch:real^1->real^N)(lift s) =
      (&1 - (s - u) / (v - u)) % z(lift u) + ((s - u) / (v - u)) % z(lift v)`
    SUBST1_TAC THENL
     [EXPAND_TAC "ch" THEN EXPAND_TAC "w" THEN
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_ASSOC; real_div] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(z:real^1->real^N)(lift c)`; `r:real`] CONVEX_BALL) THEN
    REWRITE_TAC[convex] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= (s - u) / (v - u) /\ (s - u) / (v - u) <= &1` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the new curve and its derivative *)
  ABBREV_TAC `z1 = \x:real^1. if drop x <= u then (z:real^1->real^N) x
                              else if drop x <= v then ch x else z x` THEN
  ABBREV_TAC `z1' = \x:real^1. if u < drop x /\ drop x < v then w
                               else (z':real^1->real^N) x` THEN
  SUBGOAL_THEN
   `(!s. s <= u ==> (z1:real^1->real^N)(lift s) = z(lift s)) /\
    (!s. u <= s /\ s <= v ==> z1(lift s) = ch(lift s)) /\
    (!s. v <= s ==> z1(lift s) = z(lift s)) /\
    (!s. ~(u < s /\ s < v) ==> (z1':real^1->real^N)(lift s) = z'(lift s)) /\
    (!s. u < s /\ s < v ==> z1'(lift s) = w)`
  (CONJUNCTS_THEN2 (LABEL_TAC "z1a") (CONJUNCTS_THEN2 (LABEL_TAC "z1b")
    (CONJUNCTS_THEN2 (LABEL_TAC "z1c") (CONJUNCTS_THEN2 (LABEL_TAC "d1a") (LABEL_TAC "d1b")))))
  THENL
   [MAP_EVERY EXPAND_TAC ["z1"; "z1'"] THEN REWRITE_TAC[LIFT_DROP] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `s <= u` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s:real = u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `s <= u` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `s <= v` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `s:real = v` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the pieces of z restricted to [u,v]: displacement bound *)
  SUBGOAL_THEN `interval[lift u,lift v] SUBSET interval[lift a,lift b] /\
                real_interval[u,v] SUBSET real_interval[a,b]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; SUBSET_REAL_INTERVAL; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`; `u:real`; `v:real`]
                P2AK_FE_DISP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REPEAT STRIP_TAC THEN USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (ASSUME_TAC o CONJUNCT2))] THEN
  SUBGOAL_THEN
   `(v - u) * norm(w:real^N) pow 2 <=
    real_integral (real_interval[u,v]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
    SUBGOAL_THEN `abs(v - u) = v - u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < v - u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_INV] THEN
    SUBGOAL_THEN
     `(v - u) * (inv((v - u) pow 2) * norm((z:real^1->real^N)(lift v) - z(lift u)) pow 2) =
      norm(z(lift v) - z(lift u)) pow 2 / (v - u)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < v - u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. u <= s /\ s <= v ==> (ch:real^1->real^N)(lift s) IN U` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      can (find_term ((=) `U:real^N->bool`)) (concl th))) THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN
    USE_THEN "chb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the energy and the L-functional of the new curve, by P2AK_THREE_PIECES *)
  SUBGOAL_THEN
   `(\s. norm((z1':real^1->real^N)(lift s)) pow 2) real_integrable_on real_interval[a,b] /\
    real_integral (real_interval[a,b]) (\s. norm((z1':real^1->real^N)(lift s)) pow 2) <=
    real_integral (real_interval[a,b]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. norm((z':real^1->real^N)(lift s)) pow 2`;
                   `\s. norm((z1':real^1->real^N)(lift s)) pow 2`;
                   `\s:real. norm(w:real^N) pow 2`; `a:real`; `u:real`; `v:real`; `b:real`]
                  P2AK_THREE_PIECES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN REPEAT CONJ_TAC THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THENL
       [USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th
          (UNDISCH(REAL_ARITH `s <= u ==> ~(u < s /\ s < v)`))]);
        USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th
          (UNDISCH(REAL_ARITH `v <= s ==> ~(u < s /\ s < v)`))]);
        USE_THEN "d1b" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `u < s`)
                                                               (ASSUME `s < v`))])];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `(v - u) * norm(w:real^N) pow 2 <=
                 real_integral (real_interval[u,v]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `gc = \s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((ch:real^1->real^N)(lift s))
                                (w:real^N)` THEN
  SUBGOAL_THEN
   `(gc:real->real) real_integrable_on real_interval[u,v] /\
    real_integral (real_interval[u,v]) gc <=
    (inv(&2) * Gm * norm(w:real^N) pow 2 + &2 * Sm pow 2 * Rm) * (v - u)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(gc:real->real) real_continuous_on real_interval[u,v]` ASSUME_TAC THENL
     [EXPAND_TAC "gc" THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`;
                     `tt:real`; `ch:real^1->real^N`; `(\x:real^1. (w:real^N))`; `u:real`; `v:real`]
                    P2A_LLAG_CURVE_CONTINUOUS) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^1. drop h % (w:real^N)` THEN
      ASM_REWRITE_TAC[GSYM has_vector_derivative];
      ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[u,v])
                  (\s:real. inv(&2) * Gm * norm(w:real^N) pow 2 + &2 * Sm pow 2 * Rm)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_INTEGRABLE_CONST] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(ch:real^1->real^N)(lift s) IN cball(z(lift c),r)` ASSUME_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN
        USE_THEN "chb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `a <= s /\ s <= b` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
         [EXISTS_TAC `u:real`; EXISTS_TAC `v:real`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `(ch:real^1->real^N)(lift s)`; `w:real^N`] o
        check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "lscalar"))
                             (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s pow 2 * lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                                      ((ch:real^1->real^N)(lift s)) <= Sm pow 2 * Rm`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2 * Rm` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
          UNDISCH_TAC `abs(lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                                   ((ch:real^1->real^N)(lift s))) <= Rm` THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN USE_THEN "Sm" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      EXPAND_TAC "gc" THEN REWRITE_TAC[p2a_llag] THEN
      UNDISCH_TAC `s pow 2 * lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                                     ((ch:real^1->real^N)(lift s)) <= Sm pow 2 * Rm` THEN
      UNDISCH_TAC `w dot ((Gt:real->real^N->real^N^N)(tt - s pow 2) ((ch:real^1->real^N)(lift s))
                          ** w) <= Gm * norm(w:real^N) pow 2` THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                              ((z':real^1->real^N)(lift s))`;
                 `\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z1:real^1->real^N)(lift s))
                              ((z1':real^1->real^N)(lift s))`;
                 `gc:real->real`; `a:real`; `u:real`; `v:real`; `b:real`] P2AK_THREE_PIECES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    BETA_TAC THENL
     [USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th
        (UNDISCH(REAL_ARITH `s <= u ==> ~(u < s /\ s < v)`))]) THEN
      USE_THEN "z1a" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `s <= u`)]);
      USE_THEN "d1a" (fun th -> REWRITE_TAC[MATCH_MP th
        (UNDISCH(REAL_ARITH `v <= s ==> ~(u < s /\ s < v)`))]) THEN
      USE_THEN "z1c" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `v <= s`)]);
      EXPAND_TAC "gc" THEN
      USE_THEN "d1b" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `u < s`)
                                                             (ASSUME `s < v`))]) THEN
      USE_THEN "z1b" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (MATCH_MP REAL_LT_IMP_LE
                                    (ASSUME `u < s`)) (MATCH_MP REAL_LT_IMP_LE (ASSUME `s < v`)))])];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g1int") (LABEL_TAC "g1eq")) THEN
  (* the three small terms *)
  USE_THEN "k1" (MP_TAC o SPECL [`u:real`; `v:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "k2" (MP_TAC o SPECL [`u:real`; `v:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[u,v]) gc <=
    real_integral (real_interval[u,v])
      (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                    ((z':real^1->real^N)(lift s))) + eta`
  (LABEL_TAC "small") THENL
   [ABBREV_TAC `X = (v - u) * norm(w:real^N) pow 2` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ABBREV_TAC `Fi = real_integral (real_interval[u,v])
                       (\s. norm((z':real^1->real^N)(lift s)) pow 2)` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    ABBREV_TAC `Gi = real_integral (real_interval[u,v])
                       (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                                     ((z':real^1->real^N)(lift s)))` THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2) * Gm * X <= eta / &3` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < Gm / &2 + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `X <= Fi /\ Fi < eta / (&3 * (Gm / &2 + &1))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          UNDISCH_TAC `abs(Fi) < eta / (&3 * (Gm / &2 + &1))` THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Gm / &2 + &1) * X` THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 <= X` THEN UNDISCH_TAC `&0 <= Gm` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(Gm / &2 + &1) * (eta / (&3 * (Gm / &2 + &1)))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `X <= Fi` THEN UNDISCH_TAC `Fi < eta / (&3 * (Gm / &2 + &1))` THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < Gm / &2 + &1` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * Sm pow 2 * Rm * (v - u) <= eta / &3` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= Sm pow 2 * Rm` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (Sm pow 2 * Rm) * ep` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(Sm pow 2 * Rm) * (v - u) <= (Sm pow 2 * Rm) * (&2 * ep)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
        SUBGOAL_THEN `(Sm pow 2 * Rm) * ep <= (Sm pow 2 * Rm + &1) * ep` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN
          UNDISCH_TAC `&0 < ep` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `&12 * (Sm pow 2 * Rm + &1) * ep <= eta` THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `real_integral (real_interval[u,v]) gc <=
                 (inv(&2) * Gm * norm(w:real^N) pow 2 + &2 * Sm pow 2 * Rm) * (v - u)` THEN
    SUBGOAL_THEN `(inv(&2) * Gm * norm(w:real^N) pow 2 + &2 * Sm pow 2 * Rm) * (v - u) =
                  inv(&2) * Gm * X + &2 * Sm pow 2 * Rm * (v - u)` SUBST1_TAC THENL
     [EXPAND_TAC "X" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(Gi) < eta / &3` THEN
    UNDISCH_TAC `inv(&2) * Gm * X <= eta / &3` THEN
    UNDISCH_TAC `&2 * Sm pow 2 * Rm * (v - u) <= eta / &3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the witnesses *)
  MAP_EVERY EXISTS_TAC [`z1:real^1->real^N`; `z1':real^1->real^N`;
                        `(u:real) INSERT v INSERT (K:real->bool)`] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "z1a" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "z1c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "g1int" ACCEPT_TAC;
    USE_THEN "g1eq" SUBST1_TAC THEN USE_THEN "small" MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC P2AK_CHORD_SQ THEN
  MAP_EVERY EXISTS_TAC [`z:real^1->real^N`; `z':real^1->real^N`; `ep:real`; `w:real^N`;
                        `ch:real^1->real^N`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* All bad points removed (induction over B with P2AK_CHORD_STEP) and the   *)
(* comparison with the local boundary value problem: a chart curve with     *)
(* square-integrable derivative and small energy is no shorter than the BVP *)
(* solution with its end points (the minimality clause of P2A_LOC_BVP_PW,   *)
(* applied to the chord-regularized curves).                                *)
(* ------------------------------------------------------------------------- *)

let P2AK_CHORD_ALL = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt a b.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < a /\ a < b /\ b < sb
     ==> !B. FINITE B
             ==> !z z' K eta.
                   p2ak_sq U a b z z' K B /\
                   (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) real_integrable_on
                   real_interval[a,b] /\
                   &0 < eta
                   ==> ?z1 z1' K1.
                         p2ak_sq U a b z1 z1' K1 {} /\
                         z1(lift a) = z(lift a) /\ z1(lift b) = z(lift b) /\
                         real_integral (real_interval[a,b]) (\s. norm(z1'(lift s)) pow 2) <=
                         real_integral (real_interval[a,b]) (\s. norm(z'(lift s)) pow 2) /\
                         (\s. p2a_llag Gt tt s (z1(lift s)) (z1'(lift s))) real_integrable_on
                         real_interval[a,b] /\
                         real_integral (real_interval[a,b])
                           (\s. p2a_llag Gt tt s (z1(lift s)) (z1'(lift s))) <=
                         real_integral (real_interval[a,b])
                           (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) + eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `B:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`; `eta:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `a:real`; `b:real`; `z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`;
                 `(c:real) INSERT B`; `c:real`; `eta / &2`] P2AK_CHORD_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((c:real) INSERT B) DELETE c = B` SUBST1_TAC THENL
   [UNDISCH_TAC `~((c:real) IN B)` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:real^1->real^N` (X_CHOOSE_THEN `z2':real^1->real^N`
    (X_CHOOSE_THEN `K2:real->bool` STRIP_ASSUME_TAC))) THEN
  USE_THEN "IH" (MP_TAC o SPECL [`z2:real^1->real^N`; `z2':real^1->real^N`; `K2:real->bool`;
                                 `eta / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:real^1->real^N` (X_CHOOSE_THEN `z3':real^1->real^N`
    (X_CHOOSE_THEN `K3:real->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`z3:real^1->real^N`; `z3':real^1->real^N`; `K3:real->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The comparison with the BVP solution.                                     *)

let P2AK_BVP_SQ = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt E s1 s2 (sol:real^1->real^N) z z' K B.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 < s2 /\ s2 < sb /\
     (!sig' K M. sig'(lift s1) = z(lift s1) /\ sig'(lift s2) = z(lift s2) /\
                 (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                 FINITE K /\ sig' continuous_on interval[lift s1,lift s2] /\
                 (!s. s1 < s /\ s < s2 /\ ~(s IN K)
                      ==> sig' differentiable (at (lift s)) /\
                          norm(vector_derivative sig' (at (lift s))) <= M) /\
                 p2a_cE Gt tt sig' s1 s2 <= E
                 ==> p2a_cL Gt tt sol s1 s2 <= p2a_cL Gt tt sig' s1 s2) /\
     p2ak_sq U s1 s2 z z' K B /\
     real_integral (real_interval[s1,s2]) (\s. norm(z'(lift s)) pow 2) <= E /\
     (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) real_integrable_on real_interval[s1,s2]
     ==> p2a_cL Gt tt sol s1 s2 <=
         real_integral (real_interval[s1,s2])
           (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(B:real->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2ak_sq (U:real^N->bool) s1 s2 z z' K B` THEN REWRITE_TAC[p2ak_sq] THEN
    MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(prove
   (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN ASM_REAL_ARITH_TAC)) THEN
  X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `s1:real`; `s2:real`] P2AK_CHORD_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `B:real->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`;
                             `eta:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^1->real^N` (X_CHOOSE_THEN `z1':real^1->real^N`
    (X_CHOOSE_THEN `K1:real->bool` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ak_sq] o check (fun th ->
    can (find_term ((=) `z1:real^1->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2ak_sq")) (concl th))) THEN
  REWRITE_TAC[NOT_IN_EMPTY; EMPTY_SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  (* the vector derivative of z1 off K1 *)
  SUBGOAL_THEN `!s. s1 < s /\ s < s2 /\ ~(s IN K1)
                    ==> vector_derivative (z1:real^1->real^N) (at (lift s)) = z1'(lift s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_negligible((s1:real) INSERT s2 INSERT K1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_NEGLIGIBLE_FINITE THEN ASM_REWRITE_TAC[FINITE_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt z1 s1 s2 =
    real_integral (real_interval[s1,s2]) (\s. p2a_llag Gt tt s (z1(lift s)) (z1'(lift s))) /\
    p2a_cE Gt tt z1 s1 s2 =
    real_integral (real_interval[s1,s2]) (\s. norm((z1':real^1->real^N)(lift s)) pow 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2a_cL; p2a_cE] THEN CONJ_TAC THEN
    (MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
     EXISTS_TAC `(s1:real) INSERT s2 INSERT K1` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; DE_MORGAN_THM] THEN
     REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `s1 < x /\ x < s2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[NORM_POW_2]);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p2a_cL (Gt:real->real^N->real^N^N) tt z1 s1 s2` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `sol:real^1->real^N`)) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`K1:real->bool`; `M:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `((z1:real^1->real^N) has_vector_derivative z1'(lift s)) (at (lift s))`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN EXISTS_TAC `\h:real^1. drop h % (z1':real^1->real^N)(lift s)` THEN
      ASM_REWRITE_TAC[GSYM has_vector_derivative];
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ASM_REAL_ARITH_TAC]);;

