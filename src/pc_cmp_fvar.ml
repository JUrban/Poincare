(* ========================================================================= *)
(* Unit pc_cmp_fvar (comparison-geometry layer CMP): CMP_R7_FIRST_VARIATION, *)
(* the first variation of the distance from p along a C^1 curve gamma whose  *)
(* velocity makes a uniformly obtuse angle with every minimizing direction   *)
(* from gamma(t) to p.  No curvature hypothesis.  At a time u with gamma(u)  *)
(* <> p the function y |-> delta + d(b,y) with b on a minimizing segment     *)
(* from p to gamma(u), d(b,y) bounded by |exp_b^-1 y| near gamma(u), is a    *)
(* smooth upper barrier of d(p,.) touching at gamma(u); the first variation  *)
(* of |exp_b^-1| (Gauss lemma) gives a left Dini bound for d(p,gamma t) - c  *)
(* (length up to t), and a Dini monotonicity lemma finishes; times with      *)
(* gamma = p are handled by the zero set argument.  The statement assumes    *)
(* that p is joinable to gamma(a): without this hypothesis it fails on a     *)
(* disconnected M, where the distance is a junk value.                       *)
(* ========================================================================= *)

needs "src/pc_cmp_hup.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Real-variable tools.  A Dini monotonicity lemma (a copy of P4_DINI_MONO   *)
(* and P4_DINI_MONO_OPEN of pc_p4_cm, which this unit does not load; HOL     *)
(* Light has no Dini derivatives), its reflection to left difference         *)
(* quotients, the left Dini bound from a one-sided derivative, and the       *)
(* length of a constant curve over any interval.                             *)
(* ========================================================================= *)

let CMPFV_LE_EPS = prove
 (`!x y. (!e. &0 < e ==> x <= y + e) ==> x <= y`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN
  REAL_ARITH_TAC);;

let CMPFV_DINI_RIGHT = prove
 (`!f a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!t. a <= t /\ t < b
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             !h. &0 < h /\ h < d /\ t + h <= b
                                 ==> f(t + h) <= f t + e * h)
        ==> f b <= f a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cont")
    (LABEL_TAC "dini"))) THEN
  SUBGOAL_THEN `!e. &0 < e ==> (f:real->real) b <= f a + e * (b - a) + e`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CMPFV_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (b - a + &1)`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = e ==> x <= f + y ==> x <= f + e`) THEN
    REWRITE_TAC[REAL_ARITH `x * y + x = x * (y + &1)`] THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `S = {t | t IN real_interval[a,b] /\
                       (f:real->real) a + e * (t - a) + e < f t}` THEN
  SUBGOAL_THEN `(b:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN S <=> a <= t /\ t <= b /\
                               (f:real->real) a + e * (t - a) + e < f t`
  (LABEL_TAC "Sdef") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = inf S` THEN
  SUBGOAL_THEN `!t. t IN S ==> s <= t` (LABEL_TAC "infle") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `t:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (!t. t IN S ==> y <= t) ==> y <= s` (LABEL_TAC "infge") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_LE_INF THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a <= s /\ s <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "infge" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "infle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s IN real_interval[a,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) a + e * (s - a) + e <= f s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `q = (f:real->real) a + e * (s - a) + e - f s` THEN
    SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < q / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "cont" (MP_TAC o C MP (ASSUME `&0 < q / &2`) o SPEC `q / &2` o
      C MP (ASSUME `s IN real_interval[a,b]`) o SPEC `s:real` o
      REWRITE_RULE[real_continuous_on]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `m = min d (q / (&2 * e))` THEN
    SUBGOAL_THEN `&0 < m /\ m <= d /\ e * m <= q / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * q / (&2 * e)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?t. t IN S /\ t < s + m` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE
        [NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `s + m <= s` MP_TAC THENL
       [USE_THEN "infge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `s <= t /\ a <= t /\ t <= b /\ (f:real->real) a + e * (t - a) + e < f t`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term (fun u -> u = `abs(x' - s) < d`)) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= e * (t - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < s` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) s <= f a + e * (s - a) + e` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `q = (f:real->real) s - (f a + e * (s - a) + e)` THEN
    SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < q / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "cont" (MP_TAC o C MP (ASSUME `&0 < q / &2`) o SPEC `q / &2` o
      C MP (ASSUME `s IN real_interval[a,b]`) o SPEC `s:real` o
      REWRITE_RULE[real_continuous_on]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `m = min d (q / (&2 * e))` THEN
    SUBGOAL_THEN `&0 < m /\ m <= d /\ e * m <= q / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * q / (&2 * e)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    ABBREV_TAC `t = max a (s - m / &2)` THEN
    SUBGOAL_THEN `a <= t /\ t < s /\ t <= b /\ abs(t - s) < d /\ s - t <= m`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(t:real) IN S` ASSUME_TAC THENL
     [USE_THEN "Sdef" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term (fun u -> u = `abs(x' - s) < d`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      SUBGOAL_THEN `&0 <= e * (s - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "infle" (MP_TAC o C MP (ASSUME `(t:real) IN S`) o SPEC `t:real`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "dini" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
    C MP (CONJ (ASSUME `a <= s`) (ASSUME `s < b`)) o SPEC `s:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s + d <= s` MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  USE_THEN "infge" MATCH_MP_TAC THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s <= t /\ a <= t /\ t <= b /\ (f:real->real) a + e * (t - a) + e < f t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `t:real = s` THENL
   [UNDISCH_TAC `(f:real->real) a + e * (t - a) + e < f t` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - s`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `s + (t - s) = t`] THEN ASM_REAL_ARITH_TAC);;

(* Revision 2: the Dini condition is only needed at interior times, the    *)
(* left end point being handled by continuity.                               *)

let CMPFV_DINI_RIGHT_OPEN = prove
 (`!f a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!t. a < t /\ t < b
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             !h. &0 < h /\ h < d /\ t + h <= b
                                 ==> f(t + h) <= f t + e * h)
        ==> f b <= f a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cont")
    (LABEL_TAC "dini"))) THEN
  ASM_CASES_TAC `a:real = b` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. a < c /\ c <= b ==> (f:real->real) b <= f c` (LABEL_TAC "right")
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPFV_DINI_RIGHT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "dini" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "cont" (MP_TAC o SPEC `a:real` o REWRITE_RULE[real_continuous_on]) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) b - f a`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `c = a + min d (b - a) / &2` THEN
  SUBGOAL_THEN `a < c /\ c <= b /\ abs(c - a) < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) b <= f c` ASSUME_TAC THENL
   [USE_THEN "right" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `d:real`)) (concl th))) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

(* The reflected form: lower left Dini quotients >= 0 at interior times     *)
(* and continuity on [a,b] give f a <= f b.                                  *)

let CMPFV_DINI_LEFT = prove
 (`!f a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!t. a < t /\ t < b
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             !h. &0 < h /\ h < d /\ a <= t - h
                                 ==> f(t - h) <= f t + e * h)
        ==> f a <= f b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "dini"))) THEN
  MP_TAC(ISPECL [`\x:real. (f:real->real)(--x)`; `--b:real`; `--a:real`]
    CMPFV_DINI_RIGHT_OPEN) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(\x:real. (f:real->real)(--x)) = f o (\x. --x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real. x`; `real_interval[--b,--a]`] REAL_CONTINUOUS_ON_NEG) THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "dini" (MP_TAC o SPEC `--x:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `--(x + h) = --x - h`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* A one-sided derivative D' >= 0 gives the left Dini bound. *)

let CMPFV_DERIV_LEFT_DINI = prove
 (`!D D' u s.
        (D has_real_derivative D') (atreal u within s) /\ &0 <= D'
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !h. &0 < h /\ h < d /\ (u - h) IN s
                            ==> D(u - h) <= D u + e * h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; REALLIM_WITHINREAL] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u - h:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = ((D:real->real)(u - h) - D u) / ((u - h) - u)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(D:real->real)(u - h) = D u - q * h` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `--e < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--e * h < q * h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* The length of a constant curve over any interval. *)

let CMPFV_LENGTH_CONST = prove
 (`!atlas (g:A->real^N^N) (x:A) a b.
        mfd_length (atlas:((A->bool)#(A->real^N))->bool) g (\t. x) a b = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_length] THEN
  ASM_CASES_TAC `a < b:real` THENL
   [ALL_TAC; MATCH_MP_TAC REAL_INTEGRAL_NULL THEN ASM_REAL_ARITH_TAC] THEN
  TRANS_TAC EQ_TRANS `real_integral (real_interval[a,b]) (\t. &0)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_INTEGRAL_0]] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_speed; mfd_velocity] THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) (x:A))
      (at (lift t) within interval[lift a,lift b]) = vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; HAS_VECTOR_DERIVATIVE_CONST];
    REWRITE_TAC[DOT_LZERO; SQRT_0]]);;

(* ========================================================================= *)
(* The local inverse of exp_b near the end point of a segment, with no       *)
(* curvature hypothesis (the first-order part of CMPE_PB_SETUP). For a unit  *)
(* vector ub at b with d exp_b injective at s ub, 0 < s <= L', and z =       *)
(* geo(b,ub)(L'): an open set u of chart coordinates at z and a local        *)
(* inverse Fi of w |-> chart_z(exp_b(E w)) (E an orthonormal frame at b)     *)
(* with Fi(chart_z z) = w0, |w0| = L', d(b,y) <= |Fi(chart_z y)|, and the    *)
(* Gauss lemma for its derivative: w0 . Fi'(X) = L' <geo'(L'), X>_g.         *)
(* ========================================================================= *)

let CMPFV_PB_SETUP = prove
 (`!top atlas (g:A->real^N^N) (b:A) ub L' (z:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        b IN topspace top /\ mfd_tnorm g b ub = &1 /\ &0 < L' /\
        (!s h. &0 < s /\ s <= L' /\
               mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g b) (s % ub) h = vec 0
               ==> h = vec 0) /\
        mfd_geo (top,atlas) g b ub L' = z
        ==> ?(u:real^N->bool) (Fi:real^N->real^N) (Fi':real^N->real^N) (w0:real^N).
              open_in top {y | y IN FST(chart_at atlas z) /\
                               SND(chart_at atlas z) y IN u} /\
              z IN FST(chart_at atlas z) /\ SND(chart_at atlas z) z IN u /\
              Fi(SND(chart_at atlas z) z) = w0 /\ norm w0 = L' /\
              (!y. y IN FST(chart_at atlas z) /\ SND(chart_at atlas z) y IN u
                   ==> mfd_joinable (top,atlas) b y /\
                       mfd_dist (top,atlas) g b y <= norm(Fi(SND(chart_at atlas z) y))) /\
              (Fi has_derivative Fi') (at (SND(chart_at atlas z) z)) /\
              (!X. w0 dot Fi' X =
                   L' * (mfd_vel atlas (mfd_geo (top,atlas) g b ub) L' dot (g z ** X)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `!v. mfd_geo_maxint (top,atlas) (g:A->real^N^N) b v = (:real)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) b = (:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_exp_dom; IN_UNIV; EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  ABBREV_TAC `w0 = L' % (matrix_inv(E:real^N^N) ** (ub:real^N))` THEN
  SUBGOAL_THEN `(E:real^N^N) ** w0 = L' % ub` ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(w0:real^N) = L'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w0) = z`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `ub:real^N`; `L':real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h. mfd_differential (open_set_atlas (:real^N)) atlas
                      (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** w0) h = vec 0
                    ==> h = vec 0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `L':real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_differential"
                               with Failure _ -> false)) (concl th))) THEN
    EXISTS_TAC `L':real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`;
                 `(:real^N)`; `z:A`] CMPH_EXP_CHART_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV; OPEN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`; `Fi:real^N->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. SND(chart_at atlas (z:A)) (mfd_exp (top,atlas) (g:A->real^N^N) b y)) has_derivative
     mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g b)
       ((E:real^N^N) ** w0)) (at (E ** w0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `(E:real^N^N) ** w0`] CMPP_EXP_DIFF) THEN
    REWRITE_TAC[ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w0) = z`] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. SND(chart_at atlas (z:A))
            (mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w))) has_derivative
     (\h. cmp_dexp (top,atlas) g b E w0 ** h)) (at w0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\h. cmp_dexp (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** h) =
      mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g b)
        (E ** w0) o (\h. E ** h)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^N` THEN
      MATCH_MP_TAC CMPP_DEXP_APPLY THEN ASM_REWRITE_TAC[IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\w. SND(chart_at atlas (z:A))
             (mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w))) =
      (\y. SND(chart_at atlas z) (mfd_exp (top,atlas) g b y)) o (\w. E ** w)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `t:real^N->bool`;
                 `\w. SND(chart_at atlas (z:A))
                        (mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w))`;
                 `Fi:real^N->real^N`; `w0:real^N`] LRG_DIFFEO_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) b ((E:real^N^N) ** w0) = z`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((Fi:real^N->real^N) has_derivative
     frechet_derivative Fi (at (SND(chart_at atlas (z:A)) z))) (at (SND(chart_at atlas z) z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^N->bool`; `Fi:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `u:real^N->bool` THEN EXISTS_TAC `Fi:real^N->real^N` THEN
  EXISTS_TAC `frechet_derivative (Fi:real^N->real^N) (at (SND(chart_at atlas (z:A)) z))` THEN
  EXISTS_TAC `w0:real^N` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `X:real^N` THEN
  ABBREV_TAC `V0 = frechet_derivative (Fi:real^N->real^N) (at (SND(chart_at atlas (z:A)) z)) X` THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) b) ((E:real^N^N) ** w0) (E ** V0) = X`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `V0:real^N`]
      CMPP_DEXP_APPLY) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "V0" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w0:real^N) dot V0 =
    w0 dot (cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0 ** V0)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_EXPMETRIC_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`] CMPP_EXPMETRIC_GAUSS) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN REPEAT DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM(ASSUME
      `transp(cmp_expmetric (top,atlas) (g:A->real^N^N) b (E:real^N^N) w0) =
       cmp_expmetric (top,atlas) g b E w0`)] THEN
    REWRITE_TAC[CMPP_DOT_TRANSP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `b:A`; `E:real^N^N`; `w0:real^N`; `w0:real^N`;
                 `V0:real^N`] CMPP_EXPMETRIC_DOT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) b) (L' % ub) (L' % ub) =
    L' % mfd_vel atlas (mfd_geo (top,atlas) g b ub) L'`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `b:A`; `\r:real. r % (L' % (ub:real^N))`;
                   `L' % (ub:real^N)`; `&1`] GEOG_DEXP_CURVE) THEN
    ASM_REWRITE_TAC[IN_UNIV; VECTOR_MUL_LID] THEN ANTS_TAC THENL
     [REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `(\r. mfd_exp (top,atlas) (g:A->real^N^N) b (r % L' % ub)) =
      (\r. mfd_geo (top,atlas) g b ub (L' * r + &0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; REAL_ADD_RID] THEN X_GEN_TAC `r:real` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `b:A`; `ub:real^N`; `r * L'`] MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) b ub`; `(:real)`;
                   `L':real`; `&0`] MFD_GEODESIC_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `b:A`; `ub:real^N`] MFD_GEO_MAXIMAL) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT2) THEN
    REWRITE_TAC[IN_UNIV; REAL_MUL_RID; REAL_ADD_RID] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL]);;

(* ========================================================================= *)
(* The upper barrier of d(p,.) at a point z = gamma(u) <> p of a C^1 curve.  *)
(* With v minimizing from z to p (exp_z v = p, |v| = d(z,p)), b = the point  *)
(* at distance |v|/2 from p on the reversed segment (CMPE_REVERSE,           *)
(* CMPE_BASE), and the local inverse Fi of exp_b (above) at b: phi(y) =      *)
(* |v|/2 + |Fi(chart_z y)| >= d(p,b) + d(b,y) >= d(p,y) near z, phi(z) =     *)
(* d(p,z), and (phi o gamma)'(u) = -<gamma'(u), v>_g / |v| within [a,b]      *)
(* (chain rule and the Gauss identity above).                                *)
(* ========================================================================= *)

let CMPFV_BARRIER = prove
 (`!top atlas (g:A->real^N^N) (p:A) gamma a b u v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        mfd_c1_curve (top,atlas) gamma a b /\ u IN real_interval[a,b] /\
        mfd_exp (top,atlas) g (gamma u) v = p /\
        mfd_dist (top,atlas) g (gamma u) p = mfd_tnorm g (gamma u) v /\
        &0 < mfd_tnorm g (gamma u) v
        ==> ?W phi.
              open_in top W /\ gamma u IN W /\
              (!y. y IN W ==> mfd_dist (top,atlas) g p y <= phi y) /\
              phi (gamma u) = mfd_dist (top,atlas) g p (gamma u) /\
              ((\r. phi(gamma r)) has_real_derivative
               --(mfd_velocity atlas gamma a b u dot (g (gamma u) ** v)) /
               mfd_tnorm g (gamma u) v)
              (atreal u within real_interval[a,b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "max" o CONJUNCT2) THEN
  SUBGOAL_THEN `(gamma:real->A) u IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  ABBREV_TAC `z = (gamma:real->A) u` THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) z v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `z:A`; `v:real^N`] CMPE_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `zeta = mfd_geo (top,atlas) (g:A->real^N^N) z (inv L % v)` THEN
  ABBREV_TAC `uq = --(mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (zeta:real->A) L)` THEN
  STRIP_TAC THEN
  UNDISCH_THEN `(p:A) = (zeta:real->A) L` (K ALL_TAC) THEN
  SUBGOAL_THEN `(zeta:real->A) (&0) = z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`; `inv L % (v:real^N)`] MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p uq L = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p (mfd_geo (top,atlas) g p uq L) = L`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `uq:real^N`; `L:real`; `L / &2`] CMPE_BASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `bp = mfd_geo (top,atlas) (g:A->real^N^N) p uq (L / &2)` THEN
  ABBREV_TAC `ub = mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                     (mfd_geo (top,atlas) (g:A->real^N^N) p uq) (L / &2)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) bp ub (L - L / &2) = z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_ADD; REAL_SUB_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `bp:A`; `ub:real^N`; `L - L / &2`; `z:A`]
    CMPFV_PB_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`uo:real^N->bool`; `Fi:real^N->real^N`; `Fi':real^N->real^N`;
                       `w0:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
      (mfd_geo (top,atlas) (g:A->real^N^N) bp ub) (L - L / &2) = --(inv L % v)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) bp ub =
                  (\s. mfd_geo (top,atlas) g p uq (&1 * s + L / &2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; REAL_MUL_LID] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) p uq`; `(:real)`;
                   `&1`; `L / &2`] MFD_GEODESIC_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `uq:real^N`] MFD_GEO_MAXIMAL) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `L - L / &2` o CONJUNCT2) THEN
    REWRITE_TAC[IN_UNIV; REAL_MUL_LID; REAL_SUB_ADD; VECTOR_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w0:real^N = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{y | y IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) /\ SND(chart_at atlas z) y IN uo}` THEN
  EXISTS_TAC `\y:A. L / &2 + norm((Fi:real^N->real^N)(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) y))` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_joinable (top,atlas) bp (y:A) /\
      mfd_dist (top,atlas) (g:A->real^N^N) bp y <=
      norm((Fi:real^N->real^N)(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) y))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) p bp + mfd_dist (top,atlas) g bp y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X = mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b u` THEN
  SUBGOAL_THEN
   `((\s. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) ((gamma:real->A)(drop s))) has_vector_derivative X)
    (at (lift u) within interval[lift a,lift b])`
  ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[mfd_velocity] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)`; `u:real`]
      GRGD_C1_CHART_HAS_VD) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\r. L / &2 + norm((Fi:real^N->real^N)(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) ((gamma:real->A) r))))
     has_real_derivative (w0 dot (Fi':real^N->real^N) X) / norm(w0:real^N))
    (atreal u within real_interval[a,b])`
  MP_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `lift o (\r. L / &2 + norm((Fi:real^N->real^N)
                            (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) ((gamma:real->A) r)))) o drop =
      (\s. lift(L / &2) +
           ((\y:real^N. lift(norm y)) o Fi o (\s. SND(chart_at atlas z) (gamma(drop s)))) s)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_ADD]; ALL_TAC] THEN
    SUBGOAL_THEN
     `lift((w0 dot (Fi':real^N->real^N) X) / norm(w0:real^N)) =
      vec 0 + lift((w0 dot Fi' X) / norm w0)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`(Fi:real^N->real^N) o
                    (\s. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) ((gamma:real->A)(drop s)))`;
                   `\y:real^N. lift(norm y)`; `(Fi':real^N->real^N) X`;
                   `\h:real^N. lift((w0 dot h) / norm(w0:real^N))`;
                   `lift u`; `interval[lift a,lift b]`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\s. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)) ((gamma:real->A)(drop s))`;
                     `Fi:real^N->real^N`; `X:real^N`; `Fi':real^N->real^N`;
                     `lift u`; `interval[lift a,lift b]`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM; LIFT_DROP] THEN
      SUBGOAL_THEN
       `(Fi:real^N->real^N)(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A))
                               ((gamma:real->A) u)) = w0`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CMPP_NORM_DERIV THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`] GEOG_G_SYM_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[DOT_LNEG; DOT_LMUL] THEN
    SUBGOAL_THEN `(v:real^N) dot ((g:A->real^N^N) z ** X) = X dot (g z ** v)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(L - L / &2 = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

(* ========================================================================= *)
(* The local step.  With S(r) the integral of the speed over [a,r] and F(r)  *)
(* = d(p,gamma r) - c S(r): F is continuous on [a,b]; at an interior time u  *)
(* with gamma(u) <> p the barrier above minus c S has a derivative >= 0      *)
(* within [a,b] (the angle hypothesis for the minimizing direction at        *)
(* gamma(u)), which gives the left Dini bound for F at u; so F is            *)
(* non-decreasing on intervals whose interior avoids p.                      *)
(* ========================================================================= *)

let CMPFV_JOIN_CURVE = prove
 (`!top atlas (p:A) gamma a b r.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_joinable (top,atlas) p (gamma a) /\
        mfd_c1_curve (top,atlas) gamma a b /\ a <= r /\ r <= b
        ==> mfd_joinable (top,atlas) p (gamma r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
  EXISTS_TAC `(gamma:real->A) a` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN
  MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let CMPFV_S_DIFF = prove
 (`!top atlas (g:A->real^N^N) gamma a b s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ a <= s /\ s <= t /\ t <= b
        ==> real_integral (real_interval[a,t]) (mfd_speed atlas g gamma a b) -
            real_integral (real_interval[a,s]) (mfd_speed atlas g gamma a b) =
            mfd_length atlas g gamma s t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `s:real`; `t:real`]
    GRGD_LENGTH_SUBINTERVAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b`;
                 `a:real`; `t:real`; `s:real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`]
      MFD_SPEED_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let CMPFV_F_CONT = prove
 (`!top atlas (g:A->real^N^N) (p:A) gamma a b c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b
        ==> (\r. mfd_dist (top,atlas) g p (gamma r) -
                 c * real_integral (real_interval[a,r]) (mfd_speed atlas g gamma a b))
            real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
    SUBGOAL_THEN `(\r. mfd_dist (top,atlas) (g:A->real^N^N) p ((gamma:real->A) r)) =
                  (\y. mfd_dist (top,atlas) g p y) o gamma`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
    EXISTS_TAC `mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b r` THEN
    MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b`;
                   `a:real`; `b:real`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`]
        MFD_SPEED_CONTINUOUS) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let CMPFV_LOCAL_DINI = prove
 (`!top atlas (g:A->real^N^N) p gamma a b c u.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        mfd_joinable (top,atlas) p (gamma a) /\
        mfd_c1_curve (top,atlas) gamma a b /\ &0 < c /\
        (!t v. a <= t /\ t <= b /\ v IN mfd_exp_dom (top,atlas) g (gamma t) /\
               mfd_exp (top,atlas) g (gamma t) v = p /\
               mfd_tnorm g (gamma t) v = mfd_dist (top,atlas) g (gamma t) p
               ==> mfd_velocity atlas gamma a b t dot (g (gamma t) ** v) <=
                   --c * mfd_speed atlas g gamma a b t * mfd_tnorm g (gamma t) v) /\
        a < u /\ u < b /\ ~(gamma u = p)
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !h. &0 < h /\ h < d /\ a <= u - h
                            ==> mfd_dist (top,atlas) g p (gamma(u - h)) -
                                c * real_integral (real_interval[a,u - h])
                                      (mfd_speed atlas g gamma a b) <=
                                (mfd_dist (top,atlas) g p (gamma u) -
                                 c * real_integral (real_interval[a,u])
                                       (mfd_speed atlas g gamma a b)) + e * h`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) u IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) u) p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) u`; `p:A`] MFD_JOINABLE_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CMPFV_JOIN_CURVE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) u`; `p:A`]
    MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `mfd_tnorm (g:A->real^N^N) ((gamma:real->A) u) v =
                mfd_dist (top,atlas) g (gamma u) p` (ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) u) p`
  MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(gamma:real->A) u`; `p:A`] MFD_DIST_EQ_0) THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `mfd_velocity atlas (gamma:real->A) a b u dot ((g:A->real^N^N) (gamma u) ** v) <=
    --c * mfd_speed atlas g gamma a b u * mfd_tnorm g (gamma u) v`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_velocity"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `gamma:real->A`; `a:real`; `b:real`;
                 `u:real`; `v:real^N`] CMPFV_BARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `phi:A->real`] THEN STRIP_TAC THEN
  ABBREV_TAC `sig = mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b` THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) ((gamma:real->A) u) v` THEN
  SUBGOAL_THEN
   `((\r. real_integral (real_interval[a,r]) sig) has_real_derivative sig u)
    (atreal u within real_interval[a,b])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sig:real->real`; `a:real`; `b:real`]
      REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "sig" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`]
        MFD_SPEED_CONTINUOUS) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D1 = --(mfd_velocity atlas (gamma:real->A) a b u dot
                      ((g:A->real^N^N) (gamma u) ** v)) / L` THEN
  SUBGOAL_THEN `c * sig(u:real) <= D1` ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. (phi:A->real)((gamma:real->A) r) - c * real_integral (real_interval[a,r]) sig`;
    `D1 - c * sig(u:real)`; `u:real`; `real_interval[a,b]`] CMPFV_DERIV_LEFT_DINI) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\
                     !r. a <= r /\ r <= b /\ abs(r - u) < d1 ==> (gamma:real->A) r IN W`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`; `W:A->bool`; `u:real`]
      GRGD_CURVE_TIMES_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; DIST_LIFT; IN_REAL_INTERVAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min d0 d1` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(u - h) IN W` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p ((gamma:real->A)(u - h)) <=
                phi(gamma(u - h))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d0:real`)) (concl th))) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMPFV_MONO_AVOID = prove
 (`!top atlas (g:A->real^N^N) p gamma a b c s t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        mfd_joinable (top,atlas) p (gamma a) /\
        mfd_c1_curve (top,atlas) gamma a b /\ &0 < c /\
        (!t v. a <= t /\ t <= b /\ v IN mfd_exp_dom (top,atlas) g (gamma t) /\
               mfd_exp (top,atlas) g (gamma t) v = p /\
               mfd_tnorm g (gamma t) v = mfd_dist (top,atlas) g (gamma t) p
               ==> mfd_velocity atlas gamma a b t dot (g (gamma t) ** v) <=
                   --c * mfd_speed atlas g gamma a b t * mfd_tnorm g (gamma t) v) /\
        a <= s /\ s <= t /\ t <= b /\ (!r. s < r /\ r < t ==> ~(gamma r = p))
        ==> mfd_dist (top,atlas) g p (gamma s) -
            c * real_integral (real_interval[a,s]) (mfd_speed atlas g gamma a b) <=
            mfd_dist (top,atlas) g p (gamma t) -
            c * real_integral (real_interval[a,t]) (mfd_speed atlas g gamma a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\r. mfd_dist (top,atlas) (g:A->real^N^N) p ((gamma:real->A) r) -
         c * real_integral (real_interval[a,r]) (mfd_speed atlas g gamma a b)`;
    `s:real`; `t:real`] CMPFV_DINI_LEFT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[a,b]` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPFV_F_CONT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < r /\ r < b /\ ~((gamma:real->A) r = p)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `gamma:real->A`; `a:real`; `b:real`;
                 `c:real`; `r:real`] CMPFV_LOCAL_DINI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The zero set.  The times in [s,t] with gamma = p form a closed set; every *)
(* time before a time with gamma = p also has gamma = p (otherwise F         *)
(* strictly decreases on a zero-free interval ending at the first zero,      *)
(* against the local step); so if gamma meets p inside (s,t), it sits at p   *)
(* on [s,u2] (u2 the last such time, length 0 there) and F(s) = F(u2) <=     *)
(* F(t).  Then the N-general theorem and CMP_R7_FIRST_VARIATION, whose       *)
(* statement constant has the body of P2B_REQ_CMP_FIRST_VARIATION_STATEMENT. *)
(* ========================================================================= *)

let CMPFV_ZEROS_CLOSED = prove
 (`!top atlas (p:A) gamma a b s t.
        hausdorff_space top /\
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
        p IN topspace top /\ a <= s /\ t <= b
        ==> real_closed {r | r IN real_interval[s,t] /\ gamma r = p}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CLOSED_IN] THEN
  SUBGOAL_THEN
   `{r | r IN real_interval[s,t] /\ (gamma:real->A) r = p} =
    real_interval[s,t] INTER
    {r | r IN topspace(subtopology euclideanreal (real_interval[a,b])) /\ gamma r IN {p}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                IN_SING; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_INTER THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN EXISTS_TAC `real_interval[a,b]` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL]] THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPEC `top:A topology` HAUSDORFF_IMP_T1_SPACE) THEN
  ASM_REWRITE_TAC[T1_SPACE_CLOSED_IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let CMPFV_ZERO_BEFORE = prove
 (`!top atlas (g:A->real^N^N) p gamma a b c r1 r0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        mfd_joinable (top,atlas) p (gamma a) /\
        mfd_c1_curve (top,atlas) gamma a b /\ &0 < c /\
        (!t v. a <= t /\ t <= b /\ v IN mfd_exp_dom (top,atlas) g (gamma t) /\
               mfd_exp (top,atlas) g (gamma t) v = p /\
               mfd_tnorm g (gamma t) v = mfd_dist (top,atlas) g (gamma t) p
               ==> mfd_velocity atlas gamma a b t dot (g (gamma t) ** v) <=
                   --c * mfd_speed atlas g gamma a b t * mfd_tnorm g (gamma t) v) /\
        a <= r1 /\ r1 <= r0 /\ r0 <= b /\ gamma r0 = p
        ==> gamma r1 = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(gamma:real->A) r1 = p` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Z = {r | r IN real_interval[r1,r0] /\ (gamma:real->A) r = p}` THEN
  SUBGOAL_THEN `real_closed(Z:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `p:A`; `gamma:real->A`; `a:real`; `b:real`; `r1:real`; `r0:real`]
      CMPFV_ZEROS_CLOSED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN Z <=> r1 <= r /\ r <= r0 /\ (gamma:real->A) r = p`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL; CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Z:real->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `r0:real` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `inf Z IN (Z:real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CLOSED_CONTAINS_INF THEN EXISTS_TAC `r1:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `Z:real->bool` INF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXISTS_TAC `r1:real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u1 = inf(Z:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r1 <= u1 /\ u1 <= r0 /\ (gamma:real->A) u1 = p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r1 < u1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `gamma:real->A`; `a:real`; `b:real`;
                 `c:real`; `r1:real`; `u1:real`] CMPFV_MONO_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real) IN Z` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `u1:real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p p = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_DIST_REFL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p ((gamma:real->A) r1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPFV_JOIN_CURVE THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^N^N) p ((gamma:real->A) r1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `(gamma:real->A) r1`] MFD_DIST_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `r1:real`; `u1:real`] CMPFV_S_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas (g:A->real^N^N) (gamma:real->A) r1 u1` MP_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S0 = real_integral (real_interval[a,r1])
                     (mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b)` THEN
  ABBREV_TAC `S1 = real_integral (real_interval[a,u1])
                     (mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c * S0 <= c * S1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let CMPFV_FIRST_VARIATION_GEN = prove
 (`!top atlas (g:A->real^N^N) p gamma a b c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        mfd_joinable (top,atlas) p (gamma a) /\
        mfd_c1_curve (top,atlas) gamma a b /\ &0 < c /\
        (!t v. a <= t /\ t <= b /\ v IN mfd_exp_dom (top,atlas) g (gamma t) /\
               mfd_exp (top,atlas) g (gamma t) v = p /\
               mfd_tnorm g (gamma t) v = mfd_dist (top,atlas) g (gamma t) p
               ==> mfd_velocity atlas gamma a b t dot (g (gamma t) ** v) <=
                   --c * mfd_speed atlas g gamma a b t * mfd_tnorm g (gamma t) v)
        ==> !s t. a <= s /\ s <= t /\ t <= b
                  ==> mfd_dist (top,atlas) g p (gamma s) +
                      c * mfd_length atlas g gamma s t
                      <= mfd_dist (top,atlas) g p (gamma t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `s:real`; `t:real`] CMPFV_S_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) p ((gamma:real->A) s) -
    c * real_integral (real_interval[a,s]) (mfd_speed atlas g gamma a b) <=
    mfd_dist (top,atlas) g p (gamma t) -
    c * real_integral (real_interval[a,t]) (mfd_speed atlas g gamma a b)`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `?r. s < r /\ r < t /\ (gamma:real->A) r = p` THENL
   [ALL_TAC;
    MATCH_MP_TAC CMPFV_MONO_AVOID THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Z = {r | r IN real_interval[s,t] /\ (gamma:real->A) r = p}` THEN
  SUBGOAL_THEN `real_closed(Z:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `p:A`; `gamma:real->A`; `a:real`; `b:real`; `s:real`; `t:real`]
      CMPFV_ZEROS_CLOSED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN Z <=> s <= r /\ r <= t /\ (gamma:real->A) r = p`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL; CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Z:real->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `r0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sup Z IN (Z:real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CLOSED_CONTAINS_SUP THEN EXISTS_TAC `t:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `Z:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u2 = sup(Z:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `s <= u2 /\ u2 <= t /\ (gamma:real->A) u2 = p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. s <= r /\ r <= u2 ==> (gamma:real->A) r = p` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPFV_ZERO_BEFORE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `a:real`; `b:real`; `c:real`; `u2:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `gamma:real->A`; `a:real`; `b:real`;
                 `c:real`; `u2:real`; `t:real`] CMPFV_MONO_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real) IN Z` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `u2:real`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= z ==> x <= z`) THEN
  SUBGOAL_THEN `(gamma:real->A) s = p` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `s:real`; `u2:real`] CMPFV_S_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^N^N) (gamma:real->A) s u2 = &0` SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS `mfd_length atlas (g:A->real^N^N) (\r:real. (p:A)) s u2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[CMPFV_LENGTH_CONST]];
    DISCH_THEN(SUBST1_TAC o MATCH_MP (REAL_ARITH `x - y = &0 ==> x = y`)) THEN
    REAL_ARITH_TAC]);;

let CMP_R7_FIRST_VARIATION_STATEMENT = new_definition
 `CMP_R7_FIRST_VARIATION_STATEMENT (w:B->bool) <=>
    !top atlas g p gamma a b c.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
       mfd_joinable (top,atlas) p (gamma a) /\
       mfd_c1_curve (top,atlas) gamma a b /\ &0 < c /\
       (!t v. a <= t /\ t <= b /\ v IN mfd_exp_dom (top,atlas) g (gamma t) /\
              mfd_exp (top,atlas) g (gamma t) v = p /\
              mfd_tnorm g (gamma t) v = mfd_dist (top,atlas) g (gamma t) p
              ==> mfd_velocity atlas gamma a b t dot (g (gamma t) ** v) <=
                  --c * mfd_speed atlas g gamma a b t * mfd_tnorm g (gamma t) v)
       ==> !s t. a <= s /\ s <= t /\ t <= b
                 ==> mfd_dist (top,atlas) g p (gamma s) +
                     c * mfd_length atlas g gamma s t
                     <= mfd_dist (top,atlas) g p (gamma t)`;;

let CMP_R7_FIRST_VARIATION = prove
 (`!w:B->bool. CMP_R7_FIRST_VARIATION_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R7_FIRST_VARIATION_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPFV_FIRST_VARIATION_GEN THEN
  ASM_REWRITE_TAC[]);;

