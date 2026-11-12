(* ========================================================================= *)
(* Unit pc_grg_rfint (Riemannian geometry layer): integrals along a Ricci    *)
(* flow on a closed manifold (MFD_INTEGRAL_RF_DERIV, used by the PDE layer). *)
(* Tools: differentiation under the integral sign over sets of real^N with   *)
(* an integrable majorant, and finite chart partitions of compact manifolds  *)
(* with compact chart closures.                                              *)
(* ========================================================================= *)

needs "src/pc_grg_vol.ml";;
needs "src/pc_pde_iface.ml";;
needs "src/pc_lrg_evol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Differentiation under the integral sign over a set t of real^N, for a     *)
(* real parameter in a real interval s, with an integrable majorant of the   *)
(* derivative.  Adapted from NS_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED of    *)
(* the Navier_Stokes development (github.com/hol-light-family/Navier_Stokes, *)
(* ns_heat_factor.ml; real integrals over sets of reals): the same proof,    *)
(* with DOMINATED_CONVERGENCE for vector integrals.                          *)
(* GRGT_REALLIM_WITHINREAL_SEQUENTIALLY and GRGT_IS_REALINTERVAL_BETWEEN are *)
(* copies of NS_REALLIM_WITHINREAL_SEQUENTIALLY and                          *)
(* NS_IS_REALINTERVAL_BETWEEN of the same file.                              *)
(* ------------------------------------------------------------------------- *)

let GRGT_REALLIM_WITHINREAL_SEQUENTIALLY = prove
 (`!f:real->real l a s.
        (f ---> l) (atreal a within s) <=>
        !x. (!n. x n IN s DELETE a) /\ (x ---> a) sequentially
            ==> ((f o x) ---> l) sequentially`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REALLIM_WITHINREAL_WITHIN; TENDSTO_REAL; LIM_WITHIN_SEQUENTIALLY] THEN
  GEN_REWRITE_TAC LAND_CONV [FORALL_LIFT_FUN] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IN_DELETE; IN_IMAGE_LIFT_DROP; LIFT_EQ]);;

let GRGT_IS_REALINTERVAL_BETWEEN = prove
 (`!s x y d. is_realinterval s /\ x IN s /\ y IN s /\ &0 <= d /\ d <= &1
             ==> x + (y - x) * d IN s`,
  REWRITE_TAC[is_realinterval] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `x <= y \/ y <= x`) THENL
   [SUBGOAL_THEN `&0 <= (y - x) * d /\ (y - x) * d <= (y - x) * &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `y:real`];
    SUBGOAL_THEN `&0 <= (x - y) * d /\ (x - y) * d <= (x - y) * &1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`y:real`; `x:real`]] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED = prove
 (`!(f:real->real^N->real) f' (h:real^N->real) s t.
        is_realinterval s /\
        (!x. x IN s ==> (\v. lift(f x v)) integrable_on t) /\
        (\v. lift(h v)) integrable_on t /\
        (!x v. x IN s /\ v IN t
               ==> ((\x. f x v) has_real_derivative f' x v) (atreal x within s)) /\
        (!x v. x IN s /\ v IN t ==> abs(f' x v) <= h v)
        ==> !x. x IN s /\ (?y. y IN s /\ ~(y = x))
                ==> (\v. lift(f' x v)) integrable_on t /\
                    ((\x. drop(integral t (\v. lift(f x v)))) has_real_derivative
                     drop(integral t (\v. lift(f' x v)))) (atreal x within s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ivl") (CONJUNCTS_THEN2
    (LABEL_TAC "fint") (CONJUNCTS_THEN2 (LABEL_TAC "gint")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (LABEL_TAC "bd"))))) THEN
  X_GEN_TAC `x:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `y0:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!y v. y IN s /\ v IN t
          ==> abs((f:real->real^N->real) y v - f x v) <= h v * abs(y - x)`
  (LABEL_TAC "lip") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\z. (f:real->real^N->real) z v`; `\z. (f':real->real^N->real) z v`;
       `s:real->bool`; `(h:real^N->real) v`] REAL_DIFFERENTIABLE_BOUND)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`y:real`; `x:real`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real.
      (\v. lift(((f:real->real^N->real) z v - f x v) / (z - x))) =
      (\v. inv(z - x) % ((\v. lift(f z v)) v - (\v. lift(f x v)) v))`
  (LABEL_TAC "feq") THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[real_div; GSYM LIFT_SUB; GSYM LIFT_CMUL] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real. z IN s
             ==> (\v. lift(((f:real->real^N->real) z v - f x v) / (z - x)))
                 integrable_on t /\
                 integral t (\v. lift((f z v - f x v) / (z - x))) =
                 inv(z - x) % (integral t (\v. lift(f z v)) -
                               integral t (\v. lift(f x v)))`
  (LABEL_TAC "qint") THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
    USE_THEN "feq" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `(\v. lift((f:real->real^N->real) z v)) integrable_on t /\
      (\v. lift(f x v)) integrable_on t`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_SUB; INTEGRAL_CMUL; INTEGRAL_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:num->real.
        (!n. y n IN s DELETE x) /\ (y ---> x) sequentially
        ==> (\v. lift((f':real->real^N->real) x v)) integrable_on t /\
            ((\n. (drop(integral t (\v. lift((f:real->real^N->real) (y n) v))) -
                   drop(integral t (\v. lift(f x v)))) / (y n - x)) --->
             drop(integral t (\v. lift(f' x v)))) sequentially`
  (LABEL_TAC "seq") THENL
   [X_GEN_TAC `y:num->real` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!n. (drop(integral t (\v. lift((f:real->real^N->real) ((y:num->real) n) v))) -
           drop(integral t (\v. lift(f x v)))) / (y n - x) =
          drop(integral t (\v. lift((f (y n) v - f x v) / (y n - x))))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `(y:num->real) n IN s` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "qint" (MP_TAC o C MATCH_MP (ASSUME `(y:num->real) n IN s`)) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      REWRITE_TAC[DROP_CMUL; DROP_SUB; real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n v. lift(((f:real->real^N->real) ((y:num->real) n) v - f x v) /
                  (y n - x))`;
      `\v. lift((f':real->real^N->real) x v)`; `\v. lift((h:real^N->real) v)`;
      `t:real^N->bool`] DOMINATED_CONVERGENCE) THEN
    REWRITE_TAC[REAL_TENDSTO; o_DEF; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN USE_THEN "gint" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      SUBGOAL_THEN `(y:num->real) n IN s` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "qint" (MP_TAC o C MATCH_MP (ASSUME `(y:num->real) n IN s`)) THEN
      SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `v:real^N`] THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; REAL_ABS_DIV] THEN
      SUBGOAL_THEN `&0 < abs((y:num->real) n - x)` ASSUME_TAC THENL
       [ASM_MESON_TAC[REAL_ABS_NZ; REAL_SUB_0]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "der" (MP_TAC o SPECL [`x:real`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL;
                  GRGT_REALLIM_WITHINREAL_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:num->real`) THEN
      ASM_REWRITE_TAC[IN_DELETE; o_DEF] THEN
      REWRITE_TAC[TENDSTO_REAL; o_DEF]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REMOVE_THEN "seq" (MP_TAC o SPEC `\n:num. x + (y0 - x) * inv(&n + &1)`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN `!n. &0 < inv(&n + &1) /\ inv(&n + &1) <= &1`
    ASSUME_TAC THENL
     [GEN_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV; MATCH_MP_TAC REAL_INV_LE_1] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
       [MATCH_MP_TAC GRGT_IS_REALINTERVAL_BETWEEN THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_ARITH `x + a = x <=> a = &0`; REAL_ENTIRE] THEN
        ASM_SIMP_TAC[REAL_SUB_0; REAL_LT_IMP_NZ]];
      SUBGOAL_THEN
       `((\n. x + (y0 - x) * inv(&n + &1)) ---> x + &0) sequentially`
      MP_TAC THENL
       [MATCH_MP_TAC REALLIM_ADD THEN REWRITE_TAC[REALLIM_CONST] THEN
        MATCH_MP_TAC REALLIM_NULL_LMUL THEN
        REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
        REWRITE_TAC[REAL_ADD_RID]]];
    REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL;
                GRGT_REALLIM_WITHINREAL_SEQUENTIALLY] THEN
    X_GEN_TAC `y:num->real` THEN DISCH_TAC THEN
    REMOVE_THEN "seq" (MP_TAC o SPEC `y:num->real`) THEN
    ASM_REWRITE_TAC[o_DEF] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finite chart partitions of a compact manifold whose pieces have chart     *)
(* images inside closed intervals inside the chart images, and the integral *)
(* over such a partition as a finite sum of chart integrals.                 *)
(* ------------------------------------------------------------------------- *)

let GRGT_COMPACT_PARTITION = prove
 (`!top atlas.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top
        ==> ?k c E p q.
              mfd_chart_partition atlas (topspace top) c E /\
              (!n. ~(n IN 1..k) ==> E n = {}) /\
              (!n. n IN 1..k
                   ==> c n IN atlas /\
                       interval[p n,q n] SUBSET IMAGE (SND(c n)) (FST(c n)) /\
                       IMAGE (SND(c n)) (E n) SUBSET interval[p n,q n])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `{{z:A | z IN FST c /\ SND c z IN interval(a,b)} |
     c IN (atlas:((A->bool)#(A->real^N))->bool) /\
     interval[a:real^N,b] SUBSET IMAGE (SND c) (FST c)}` o
   GEN_REWRITE_RULE I [COMPACT_SPACE_ALT]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `interval(a:real^N,b)`] GRGD_CHART_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; OPEN_INTERVAL];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `x:A`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` THEN
      REWRITE_TAC[OPEN_CONTAINS_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^N)) x`) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`c:(A->bool)#(A->real^N)`; `a:real^N`; `b:real^N`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `k = CARD(V:(A->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i IN 1..k
        ==> ?c p q. c IN atlas /\
                    interval[p:real^N,q] SUBSET IMAGE (SND c) (FST c) /\
                    (w:num->A->bool) i =
                    {z | z IN FST(c:(A->bool)#(A->real^N)) /\ SND c z IN interval(p,q)}`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A->bool) i IN V` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `(V:(A->bool)->bool) SUBSET
      {{z:A | z IN FST c /\ SND c z IN interval(a,b)} |
       c IN (atlas:((A->bool)#(A->real^N))->bool) /\
       interval[a:real^N,b] SUBSET IMAGE (SND c) (FST c)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `p:num->real^N` (X_CHOOSE_THEN `q:num->real^N`
     (LABEL_TAC "W")))) THEN
  SUBGOAL_THEN
   `!i. i IN 1..k
        ==> (c:num->(A->bool)#(A->real^N)) i IN atlas /\
            open_in top ((w:num->A->bool) i) /\ w i SUBSET FST(c i) /\
            IMAGE (SND(c i)) (w i) SUBSET interval((p:num->real^N) i,q i) /\
            interval[p i,q i] SUBSET IMAGE (SND(c i)) (FST(c i))`
  (LABEL_TAC "WF") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `i IN 1..k`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((c:num->(A->bool)#(A->real^N)) i)`;
                     `SND((c:num->(A->bool)#(A->real^N)) i)`;
                     `interval((p:num->real^N) i,q i)`] GRGD_CHART_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; OPEN_INTERVAL];
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN 1..k
        ==> !x y. x IN FST((c:num->(A->bool)#(A->real^N)) i) /\ y IN FST(c i) /\
                  SND(c i) x = SND(c i) y ==> x = y`
  (LABEL_TAC "INJ") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c:num->(A->bool)#(A->real^N)) i`] MFDM_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `E = \n. if n IN 1..k
            then {z:A | z IN (w:num->A->bool) n /\
                        !j. j IN 1..k /\ j < n ==> ~(z IN w j)}
            else {}` THEN
  SUBGOAL_THEN
   `!n z. z IN (E:num->A->bool) n <=>
          n IN 1..k /\ z IN (w:num->A->bool) n /\
          !j. j IN 1..k /\ j < n ==> ~(z IN w j)`
  (LABEL_TAC "EIN") THENL
   [EXPAND_TAC "E" THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (E:num->A->bool) n SUBSET (w:num->A->bool) n`
  (LABEL_TAC "ESUB") THENL
   [ASM_REWRITE_TAC[SUBSET] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(n IN 1..k) ==> (E:num->A->bool) n = {}` (LABEL_TAC "E0") THENL
   [ASM_REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`;
    `p:num->real^N`; `q:num->real^N`] THEN
  USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "WF" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "ESUB" (MP_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(p:num->real^N) n`; `(q:num->real^N) n`]
                  INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[]] THEN
  REWRITE_TAC[mfd_chart_partition] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n IN 1..k` THENL
     [ALL_TAC;
      USE_THEN "E0" (MP_TAC o C MATCH_MP (ASSUME `~(n IN 1..k)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY; EMPTY_SUBSET]] THEN
    USE_THEN "WF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "ESUB" (ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC
     `U = UNIONS {(w:num->A->bool) j | j IN 1..k /\ j < n}` THEN
    SUBGOAL_THEN `(E:num->A->bool) n = (w:num->A->bool) n DIFF U` SUBST1_TAC THENL
     [EXPAND_TAC "U" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      USE_THEN "WF" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((w:num->A->bool) n DIFF U) =
      IMAGE (SND(c n)) (w n) DIFF IMAGE (SND(c n)) (FST(c n) INTER U)`
    SUBST1_TAC THENL
     [USE_THEN "INJ" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
      UNDISCH_TAC `(w:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c:num->(A->bool)#(A->real^N)) n`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN CONJ_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
      (ARITH_RULE `~(m:num = n) ==> m < n \/ n < m`)) THEN
    POP_ASSUM MP_TAC THEN MESON_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `n IN 1..k /\ (x:A) IN (w:num->A->bool) n` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN (E:num->A->bool) n` THEN
        USE_THEN "EIN" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
        ALL_TAC] THEN
      USE_THEN "WF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(c:num->(A->bool)#(A->real^N)) n`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
      ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `?i. i IN 1..k /\ (x:A) IN (w:num->A->bool) i` MP_TAC THENL
       [UNDISCH_TAC `topspace top SUBSET UNIONS (V:(A->bool)->bool)` THEN
        ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
        DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num`
        (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "MIN"))) THEN
      EXISTS_TAC `(E:num->A->bool) i` THEN
      CONJ_TAC THENL [EXISTS_TAC `i:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "EIN" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "MIN" MP_TAC THEN MESON_TAC[]]]);;

(* The integral over a partition with finitely many nonempty pieces. *)

let GRGT_HAS_INTEGRAL_FINITE_PARTITION = prove
 (`!top atlas (g:A->real^N^N) f S k c E.
        mfd_chart_partition atlas S c E /\ (!n. ~(n IN 1..k) ==> E n = {}) /\
        (!n. n IN 1..k
             ==> mfd_chart_integrand atlas g f (c n) absolutely_integrable_on
                 IMAGE (SND(c n)) (E n))
        ==> mfd_has_integral (top,atlas) g f S
              (sum(1..k) (\n. drop(integral (IMAGE (SND(c n)) (E n))
                                     (mfd_chart_integrand atlas g f (c n)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_integral] THEN
  MAP_EVERY EXISTS_TAC [`c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(1..k) INTER from 0 = 1..k` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_FROM; LE_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ~(n IN (1..k) INTER from 0)
        ==> IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n) = {}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n IN 1..k` THEN
    ASM_SIMP_TAC[IMAGE_CLAUSES; ABSOLUTELY_INTEGRABLE_ON_EMPTY];
    REWRITE_TAC[real_summable] THEN
    EXISTS_TAC
     `sum ((1..k) INTER from 0)
          (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                    ((E:num->A->bool) n))
                 (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                  (c n) y)))))` THEN
    MATCH_MP_TAC REAL_SERIES_FINITE_SUPPORT THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; INTEGRAL_EMPTY; DROP_VEC];
    MP_TAC(ISPECL
     [`\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                               ((E:num->A->bool) n))
                 (mfd_chart_integrand atlas (g:A->real^N^N) f (c n)))`;
      `1..k`; `from 0`] REAL_SERIES_FINITE_SUPPORT) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; INTEGRAL_EMPTY; DROP_VEC]]);;

(* ------------------------------------------------------------------------- *)
(* The volume density under a Ricci flow on the manifold: in preferred       *)
(* coordinates d/ds sqrt(det(g s x)) = -R sqrt(det(g t x)), as in           *)
(* LDENSITY_EVOLUTION (stated there for local flows lricci_flow), and then   *)
(* in any chart, where the density is |det J| sqrt(det(g s x)) with J        *)
(* independent of s.                                                         *)
(* ------------------------------------------------------------------------- *)

let GRGT_FLOW_VDERIV_PREF = prove
 (`!top atlas a b (g:real->A->real^N^N) t x.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
        ==> ((\s. vectorize(g (drop s) x)) has_vector_derivative
             vectorize((lambda i j. --(&2) * mfd_ricci_matrix atlas (g t) x$i$j)
                       :real^N^N)) (at (lift t))`,
  REWRITE_TAC[ricci_flow_on] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `k:num` LRG_VECTORIZE_INDEX) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD] THEN
  SPEC_TAC(`1 + (k - 1) MOD dimindex(:N)`, `j:num`) THEN
  SPEC_TAC(`1 + (k - 1) DIV dimindex(:N)`, `i:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN
   `(\s. lift((g:real->A->real^N^N) (drop s) x$i$j)) =
    lift o (\s. g s x$i$j) o drop`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let GRGT_DENSITY_EVOLUTION_PREF = prove
 (`!top atlas a b (g:real->A->real^N^N) t x.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
        ==> ((\s. sqrt(det(g s x))) has_real_derivative
             (--(mfd_scalar atlas (g t) x) * sqrt(det(g t x)))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det((g:real->A->real^N^N) t x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`; `x:A`] GRGV_SQRT_DET_POS) THEN
    ASM_REWRITE_TAC[SQRT_LT_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c ((g:real->A->real^N^N) t))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^N)) x IN IMAGE (SND c) (FST c)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)
                 (SND c x) = g t x`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. det((g:real->A->real^N^N) s x)) has_real_derivative
     (--(&2) * mfd_scalar atlas (g t) x * det(g t x))) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`; `x:A`]
           GRGT_FLOW_VDERIV_PREF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_DET_CURVE) THEN
    REWRITE_TAC[LIFT_DROP; HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MATCH_MP_TAC(MESON[]
     `(f:real^1->real^1) = g /\ (x:real^1) = y
      ==> (f has_vector_derivative x) (net:(real^1)net)
          ==> (g has_vector_derivative y) net`) THEN
    CONJ_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; AP_TERM_TAC] THEN
    ASM_SIMP_TAC[COFACTOR_MATRIX_INV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[mfd_scalar; lscalar; MATRIX_CMUL_COMPONENT; TRANSP_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA; mfd_ricci_matrix] THEN
    REWRITE_TAC[mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^N))
                                 ((g:real->A->real^N^N) t)`;
                   `SND(c:(A->bool)#(A->real^N)) x`; `i:num`; `j:num`]
                  LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. det((g:real->A->real^N^N) s x)`; `sqrt`;
                 `--(&2) * mfd_scalar atlas ((g:real->A->real^N^N) t) x *
                  det(g t x)`;
                 `inv(&2 * sqrt(det((g:real->A->real^N^N) t x)))`;
                 `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; o_DEF] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y
    ==> (f has_real_derivative x) (net:(real)net)
        ==> (f has_real_derivative y) net`) THEN
  SUBGOAL_THEN
   `&0 < sqrt(det((g:real->A->real^N^N) t x)) /\
    sqrt(det(g t x)) pow 2 = det(g t x)`
  MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SPEC_TAC(`sqrt(det((g:real->A->real^N^N) t x))`, `r:real`) THEN
  SPEC_TAC(`det((g:real->A->real^N^N) t x)`, `d:real`) THEN
  SPEC_TAC(`mfd_scalar atlas ((g:real->A->real^N^N) t) x`, `R:real`) THEN
  CONV_TAC REAL_FIELD);;

(* In any chart. *)

let GRGT_CHART_DENSITY_EVOLUTION = prove
 (`!top atlas a b (g:real->A->real^N^N) c t y.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ c IN atlas /\
        y IN IMAGE (SND c) (FST c)
        ==> ((\s. mfd_density atlas c (g s) y) has_real_derivative
             (--(mfd_scalar atlas (g t) (chart_inv c y)) *
              mfd_density atlas c (g t) y)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_density; metric_local; GRGV_DET_PULLBACK_SQRT] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`]
                GRGT_DENSITY_EVOLUTION_PREF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o SPEC
   `abs(det(matrix(chart_jac (c:(A->bool)#(A->real^N))
                     (chart_at atlas (chart_inv c y)) (chart_inv c y))))` o
   MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y
    ==> (f has_real_derivative x) (net:(real)net)
        ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The chart integrand of e s for the metric g s, as a smooth function of    *)
(* (s,y) on an open set of real^1 x real^N containing [a,b) x (chart image), *)
(* built from the smooth extensions past a given by pde_sfun_from and        *)
(* ricci_flow_from; its time derivative; continuity of slices; bounds of     *)
(* continuous functions on compact boxes; continuity from one-sided local    *)
(* continuity.                                                               *)
(* ------------------------------------------------------------------------- *)

let GRGT_RF_METRIC = prove
 (`!top atlas a b (g:real->A->real^N^N).
        ricci_flow_from (top,atlas) a b g
        ==> ricci_flow_on (top,atlas) a b g /\
            smooth_manifold_atlas top atlas /\ a < b /\
            (!s. a <= s /\ s < b ==> riemannian_metric atlas (g s))`,
  REWRITE_TAC[ricci_flow_from] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = a` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let GRGT_PSI_EXISTS = prove
 (`!top atlas a b (g:real->A->real^N^N) (e:real->A->real) c.
        ricci_flow_from (top,atlas) a b g /\ pde_sfun_from atlas a b e /\
        c IN atlas
        ==> ?W (P:real^(1,N)finite_sum->real^1).
               open W /\ smooth_map_on W P /\
               (!s y. a <= s /\ s < b /\ y IN IMAGE (SND c) (FST c)
                      ==> pastecart (lift s) y IN W /\
                          P(pastecart (lift s) y) =
                          mfd_chart_integrand atlas (g s) (e s) c y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_sfun_from (atlas:((A->bool)#(A->real^N))->bool) a b
                             (e:real->A->real)` THEN
  REWRITE_TAC[pde_sfun_from] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (X_CHOOSE_THEN `F1:real^(1,N)finite_sum->real^1` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `ricci_flow_from (top,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
  REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real`
   (X_CHOOSE_THEN `F3:real^(1,N)finite_sum->real^(N,N)finite_prod`
     STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d1:real`; `d3:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `d <= d1 /\ d <= d3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC
   `Om = interval(lift(a - d),lift b) PCROSS
         IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open (Om:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN MATCH_MP_TAC OPEN_PCROSS THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on Om (F1:real^(1,N)finite_sum->real^1) /\
    smooth_map_on Om (F3:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift(a - d1),lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
      EXISTS_TAC `interval(lift(a - d3),lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Om" THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> smooth_map_on Om
                (\z. lift((matrify((F3:real^(1,N)finite_sum->real^(N,N)finite_prod) z)
                           :real^N^N)$i$j))`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
     [`Om:real^(1,N)finite_sum->bool`;
      `\z. (matrify((F3:real^(1,N)finite_sum->real^(N,N)finite_prod) z)
            :real^N^N)`] LRG_SMOOTH_VECTORIZE)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `DF = \z:real^(1,N)finite_sum.
           lift(det(matrify((F3:real^(1,N)finite_sum->real^(N,N)finite_prod) z)
                    :real^N^N))` THEN
  SUBGOAL_THEN `smooth_map_on Om (DF:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "DF" THEN REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_DET_OPEN THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[smooth_map_on];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = {z | z IN Om /\
             (DF:real^(1,N)finite_sum->real^1) z IN {x:real^1 | x$1 > &0}}` THEN
  SUBGOAL_THEN `open (W:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_HALFSPACE_COMPONENT_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^(1,N)finite_sum->bool) SUBSET Om` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN W ==> &0 < drop((DF:real^(1,N)finite_sum->real^1) z)`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM; drop; real_gt] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `SQ = \z:real^(1,N)finite_sum.
           lift(sqrt(drop((DF:real^(1,N)finite_sum->real^1) z)))` THEN
  SUBGOAL_THEN `smooth_map_on W (SQ:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "SQ" THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SQRT THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `Om:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
  EXISTS_TAC
   `\z. lift(drop((F1:real^(1,N)finite_sum->real^1) z) *
             drop((SQ:real^(1,N)finite_sum->real^1) z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `Om:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 < det(metric_local atlas (c:(A->bool)#(A->real^N))
                 ((g:real->A->real^N^N) s) y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) s`; `c:(A->bool)#(A->real^N)`;
                   `y:real^N`] GRGV_DENSITY_POS) THEN
    ASM_SIMP_TAC[mfd_density; SQRT_LT_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(DF:real^(1,N)finite_sum->real^1) (pastecart (lift s) y) =
    lift(det(metric_local atlas (c:(A->bool)#(A->real^N))
                 ((g:real->A->real^N^N) s) y))`
  ASSUME_TAC THENL
   [EXPAND_TAC "DF" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXPAND_TAC "Om" THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; real_gt]];
    EXPAND_TAC "SQ" THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    REWRITE_TAC[mfd_chart_integrand; mfd_density]]);;

let GRGT_TIME_DERIVATIVE = prove
 (`!(P:real^(1,N)finite_sum->real^1) W s y.
        open W /\ smooth_map_on W P /\ pastecart (lift s) y IN W
        ==> ((\t. drop(P(pastecart (lift t) y))) has_real_derivative
             drop(frechet_derivative P (at (pastecart (lift s) y))
                                       (pastecart (lift(&1)) (vec 0))))
            (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(P:real^(1,N)finite_sum->real^1) differentiable at (pastecart (lift s) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_TIME_CURVE) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; has_vector_derivative; o_DEF;
              LIFT_DROP] THEN
  MATCH_MP_TAC(MESON[]
   `(f:real^1->real^1) = f'
    ==> (h has_derivative f) net ==> (h has_derivative f') net`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^1` THEN
  SUBGOAL_THEN
   `pastecart (u:real^1) (vec 0:real^N) = drop u % pastecart (lift(&1)) (vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL; REAL_MUL_RID;
                LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_CMUL THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  ASM_REWRITE_TAC[]);;

let GRGT_SLICE_CONTINUOUS = prove
 (`!(P:real^(1,N)finite_sum->real^K) W s O.
        P continuous_on W /\ (!y. y IN O ==> pastecart (lift s) y IN W)
        ==> (\y. P(pastecart (lift s) y)) continuous_on O`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. (P:real^(1,N)finite_sum->real^K)(pastecart (lift s) y)) =
    P o (\y:real^N. pastecart (lift s) y)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let GRGT_COMPACT_BOUND = prove
 (`!(D:real^(1,N)finite_sum->real^1) W t1 t2 (p:real^N) q.
        D continuous_on W /\
        interval[pastecart (lift t1) p,pastecart (lift t2) q] SUBSET W
        ==> ?B. &0 < B /\
                !s y. t1 <= s /\ s <= t2 /\ y IN interval[p,q]
                      ==> abs(drop(D(pastecart (lift s) y))) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`D:real^(1,N)finite_sum->real^1`;
                 `interval[pastecart (lift t1) (p:real^N),pastecart (lift t2) q]`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; COMPACT_INTERVAL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ABS_DROP] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM PCROSS_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
              LIFT_DROP] THEN
  ASM_REWRITE_TAC[]);;

let GRGT_CONTINUOUS_ON_FROM_LOCAL = prove
 (`!f a b.
        (!x0. a <= x0 /\ x0 < b
              ==> ?b'. x0 < b' /\
                       f real_continuous (atreal x0 within real_interval[a,b']))
        ==> f real_continuous_on {s | a <= s /\ s < b}`,
  REWRITE_TAC[real_continuous_on; IN_ELIM_THM; real_continuous_withinreal] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x0:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b':real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (b' - x0)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x':real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* On one chart piece: the time derivative of the smooth extension is the    *)
(* chart integrand of e' - R e (product rule with GRGT_CHART_DENSITY_        *)
(* EVOLUTION); continuity on [a,b) and differentiation on (a,b) of the       *)
(* piece integrals (GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED with a       *)
(* constant majorant from compactness).                                      *)
(* ------------------------------------------------------------------------- *)

let GRGT_PSI_TIME_DERIV = prove
 (`!top atlas a b (g:real->A->real^N^N) (e:real->A->real) e' c W
    (P:real^(1,N)finite_sum->real^1) t y.
        ricci_flow_from (top,atlas) a b g /\
        (!s x. a < s /\ s < b /\ x IN topspace top
               ==> ((\r. e r x) has_real_derivative e' s x) (atreal s)) /\
        c IN atlas /\ open W /\ smooth_map_on W P /\
        (!s y. a <= s /\ s < b /\ y IN IMAGE (SND c) (FST c)
               ==> pastecart (lift s) y IN W /\
                   P(pastecart (lift s) y) =
                   mfd_chart_integrand atlas (g s) (e s) c y) /\
        a < t /\ t < b /\ y IN IMAGE (SND c) (FST c)
        ==> lift(drop(frechet_derivative P (at (pastecart (lift t) y))
                                          (pastecart (lift(&1)) (vec 0)))) =
            mfd_chart_integrand atlas (g t)
              (\x. e' t x - mfd_scalar atlas (g t) x * e t x) c y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DE")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PW")
     STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. drop((P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y)))
     has_real_derivative
     ((e:real->A->real) t (chart_inv (c:(A->bool)#(A->real^N)) y) *
      --(mfd_scalar atlas ((g:real->A->real^N^N) t) (chart_inv c y)) *
      mfd_density atlas c (g t) y +
      e' t (chart_inv c y) * mfd_density atlas c (g t) y)) (atreal t)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC
     `\s. (e:real->A->real) s (chart_inv (c:(A->bool)#(A->real^N)) y) *
          mfd_density atlas c ((g:real->A->real^N^N) s) y` THEN
    EXISTS_TAC `min (t - a) (b - t)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `a <= s /\ s < b` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `(P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y) =
        mfd_chart_integrand atlas ((g:real->A->real^N^N) s) ((e:real->A->real) s)
                            (c:(A->bool)#(A->real^N)) y`
      SUBST1_TAC THENL
       [USE_THEN "PW" (MP_TAC o SPECL [`s:real`; `y:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        REWRITE_TAC[mfd_chart_integrand; LIFT_DROP]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\r. (e:real->A->real) r (chart_inv (c:(A->bool)#(A->real^N)) y)`;
                   `(e':real->A->real) t (chart_inv (c:(A->bool)#(A->real^N)) y)`;
                   `\s. mfd_density atlas (c:(A->bool)#(A->real^N))
                                    ((g:real->A->real^N^N) s) y`;
                   `--(mfd_scalar atlas ((g:real->A->real^N^N) t)
                         (chart_inv (c:(A->bool)#(A->real^N)) y)) *
                    mfd_density atlas c (g t) y`;
                   `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "DE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC GRGT_CHART_DENSITY_EVOLUTION THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
        ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^(1,N)finite_sum->real^1`; `W:real^(1,N)finite_sum->bool`;
                 `t:real`; `y:real^N`] GRGT_TIME_DERIVATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "PW" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_chart_integrand] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let GRGT_PIECE_INTEGRAL = prove
 (`!top atlas a b (g:real->A->real^N^N) (e:real->A->real) e' c (p:real^N) q K.
        ricci_flow_from (top,atlas) a b g /\ pde_sfun_from atlas a b e /\
        (!s x. a < s /\ s < b /\ x IN topspace top
               ==> ((\r. e r x) has_real_derivative e' s x) (atreal s)) /\
        c IN atlas /\ interval[p,q] SUBSET IMAGE (SND c) (FST c) /\
        K SUBSET interval[p,q] /\ lebesgue_measurable K
        ==> (!s. a <= s /\ s < b
                 ==> mfd_chart_integrand atlas (g s) (e s) c
                     absolutely_integrable_on K) /\
            (\s. drop(integral K (mfd_chart_integrand atlas (g s) (e s) c)))
              real_continuous_on {s | a <= s /\ s < b} /\
            (!t. a < t /\ t < b
                 ==> mfd_chart_integrand atlas (g t)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x) c
                       absolutely_integrable_on K /\
                     ((\s. drop(integral K (mfd_chart_integrand atlas (g s) (e s) c)))
                      has_real_derivative
                      drop(integral K (mfd_chart_integrand atlas (g t)
                             (\x. e' t x - mfd_scalar atlas (g t) x * e t x) c)))
                     (atreal t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "DE") STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `e:real->A->real`;
                 `c:(A->bool)#(A->real^N)`] GRGT_PSI_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(1,N)finite_sum->bool`
   (X_CHOOSE_THEN `P:real^(1,N)finite_sum->real^1`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PW"))))) THEN
  ABBREV_TAC
   `D = \z. frechet_derivative (P:real^(1,N)finite_sum->real^1) (at z)
                               (pastecart (lift(&1)) (vec 0:real^N))` THEN
  SUBGOAL_THEN `(D:real^(1,N)finite_sum->real^1) continuous_on W` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^(1,N)finite_sum->real^1) continuous_on W` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable (K:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `interval[p:real^N,q]` THEN ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. a <= s /\ s < b /\ y IN interval[p,q]
          ==> pastecart (lift s) y IN W /\
              (P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y) =
              mfd_chart_integrand atlas ((g:real->A->real^N^N) s) ((e:real->A->real) s)
                                  (c:(A->bool)#(A->real^N)) y`
  (LABEL_TAC "PI") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "PW" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> (\y. (P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y))
            absolutely_integrable_on K`
  (LABEL_TAC "AIP") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `interval[p:real^N,q]` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC GRGT_SLICE_CONTINUOUS THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "PI" (MP_TAC o SPECL [`s:real`; `y:real^N`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> integral K (mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                          ((e:real->A->real) s) (c:(A->bool)#(A->real^N))) =
            integral K (\y. (P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y))`
  (LABEL_TAC "IEQ") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "PI" (MP_TAC o SPECL [`s:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* The bound and the derivative on a closed box [t1,t2] x [p,q]. *)
  SUBGOAL_THEN
   `!t1 t2. a <= t1 /\ t2 < b
            ==> ?B. &0 < B /\
                    !s y. t1 <= s /\ s <= t2 /\ y IN interval[p,q]
                          ==> abs(drop((D:real^(1,N)finite_sum->real^1)
                                         (pastecart (lift s) y))) <= B`
  (LABEL_TAC "BD") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGT_COMPACT_BOUND THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM PCROSS_INTERVAL; SUBSET; FORALL_PASTECART;
                PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "PI" (MP_TAC o SPECL [`drop u`; `y:real^N`]) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. a <= s /\ s < b /\ y IN interval[p,q]
          ==> ((\s. drop((P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y)))
               has_real_derivative
               drop((D:real^(1,N)finite_sum->real^1) (pastecart (lift s) y)))
              (atreal s)`
  (LABEL_TAC "DP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC GRGT_TIME_DERIVATIVE THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "PI" (MP_TAC o SPECL [`s:real`; `y:real^N`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Dominated differentiation on a real interval S inside [a,b). *)
  SUBGOAL_THEN
   `!S t1 t2 x. is_realinterval S /\ a <= t1 /\ t2 < b /\
                (!s. s IN S ==> t1 <= s /\ s <= t2) /\
                x IN S /\ (?y. y IN S /\ ~(y = x))
                ==> (\v. lift(drop((D:real^(1,N)finite_sum->real^1)
                                    (pastecart (lift x) v)))) integrable_on K /\
                    ((\s. drop(integral K
                            (\v. lift(drop((P:real^(1,N)finite_sum->real^1)
                                             (pastecart (lift s) v)))))) has_real_derivative
                     drop(integral K (\v. lift(drop(D(pastecart (lift x) v))))))
                    (atreal x within S)`
  (LABEL_TAC "DOM") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "BD" (MP_TAC o SPECL [`t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`\s v. drop((P:real^(1,N)finite_sum->real^1) (pastecart (lift s) v))`;
      `\s v. drop((D:real^(1,N)finite_sum->real^1) (pastecart (lift s) v))`;
      `\v:real^N. B:real`; `S:real->bool`; `K:real^N->bool`]
     GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTEGRABLE_ON_CONST; LIFT_DROP; ETA_AX] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        USE_THEN "AIP" MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(s:real) IN S`)) THEN
        ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`s:real`; `v:real^N`] THEN STRIP_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        USE_THEN "DP" MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(s:real) IN S`)) THEN
        DISCH_TAC THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
        MAP_EVERY X_GEN_TAC [`s:real`; `v:real^N`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(s:real) IN S`)) THEN
        ASM SET_TAC[]];
      DISCH_THEN(MATCH_MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* absolute integrability for s in [a,b) *)
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\y. (P:real^(1,N)finite_sum->real^1) (pastecart (lift s) y)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "PI" (MP_TAC o SPECL [`s:real`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      USE_THEN "AIP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* continuity on [a,b) *)
    MATCH_MP_TAC GRGT_CONTINUOUS_ON_FROM_LOCAL THEN
    X_GEN_TAC `x0:real` THEN STRIP_TAC THEN
    EXISTS_TAC `(x0 + b) / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_WITHINREAL THEN
    EXISTS_TAC
     `\s. drop(integral K
                (\v. lift(drop((P:real^(1,N)finite_sum->real^1)
                                 (pastecart (lift s) v)))))` THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "IEQ" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
    EXISTS_TAC `drop(integral K (\v. lift(drop((D:real^(1,N)finite_sum->real^1)
                                                (pastecart (lift x0) v)))))` THEN
    USE_THEN "DOM" (MP_TAC o SPECL
     [`real_interval[a,(x0 + b) / &2]`; `a:real`; `(x0 + b) / &2`; `x0:real`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    EXISTS_TAC `(x0 + b) / &2` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* derivative on (a,b) *)
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  ABBREV_TAC `r = min (t - a) (b - t) / &2` THEN
  SUBGOAL_THEN `&0 < r /\ a < t - r /\ t + r < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "DOM" (MP_TAC o SPECL
   [`real_interval(t - r,t + r)`; `t - r`; `t + r`; `t:real`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    EXISTS_TAC `t + r / &2` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `t IN real_interval(t - r,t + r) /\ real_open(real_interval(t - r,t + r))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN K
        ==> lift(drop((D:real^(1,N)finite_sum->real^1) (pastecart (lift t) y))) =
            mfd_chart_integrand atlas ((g:real->A->real^N^N) t)
              (\x. e' t x - mfd_scalar atlas (g t) x * (e:real->A->real) t x)
              (c:(A->bool)#(A->real^N)) y`
  (LABEL_TAC "DID") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC GRGT_PSI_TIME_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`;
                          `W:real^(1,N)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\v. lift(drop((D:real^(1,N)finite_sum->real^1)
                               (pastecart (lift t) v)))` THEN
    CONJ_TAC THENL [USE_THEN "DID" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
    USE_THEN "BD" (MP_TAC o SPECL [`t - r`; `t + r`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\v:real^N. lift B` THEN
    ASM_REWRITE_TAC[INTEGRABLE_ON_CONST; NORM_LIFT; LIFT_DROP] THEN
    REWRITE_TAC[GSYM ABS_DROP] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC
   `\s. drop(integral K
              (\v. lift(drop((P:real^(1,N)finite_sum->real^1)
                               (pastecart (lift s) v)))))` THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "IEQ" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral K (mfd_chart_integrand atlas ((g:real->A->real^N^N) t)
                  (\x. e' t x - mfd_scalar atlas (g t) x * (e:real->A->real) t x)
                  (c:(A->bool)#(A->real^N))) =
    integral K (\v. lift(drop((D:real^(1,N)finite_sum->real^1)
                                (pastecart (lift t) v))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN USE_THEN "DID" (fun th -> SIMP_TAC[th]);
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MFD_INTEGRAL_RF_DERIV: along a Ricci                                      *)
(* flow smooth up to a, the integral of e over the closed manifold is        *)
(* continuous on [a,b) and d/dt int e dV = int (e' - R e) dV on (a,b).       *)
(* The integral is a finite sum over a fixed partition                       *)
(* (GRGT_COMPACT_PARTITION), and each piece is handled by                    *)
(* GRGT_PIECE_INTEGRAL.  The hypothesis pde_sfun_from atlas a b e' is not    *)
(* needed.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MFD_INTEGRAL_RF_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
     (g:real->A->real^N^N) (e:real->A->real) e'.
        hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b g /\
        pde_sfun_from atlas a b e /\ pde_sfun_from atlas a b e' /\
        (!s x. a < s /\ s < b /\ x IN topspace top
               ==> ((\r. e r x) has_real_derivative e' s x) (atreal s))
        ==> (\s. mfd_integral (top,atlas) (g s) (topspace top) (e s))
              real_continuous_on {s | a <= s /\ s < b} /\
            !t. a < t /\ t < b
                ==> ((\s. mfd_integral (top,atlas) (g s) (topspace top) (e s))
                     has_real_derivative
                     mfd_integral (top,atlas) (g t) (topspace top)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x)) (atreal t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DE")))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGT_RF_METRIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                GRGT_COMPACT_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` (X_CHOOSE_THEN `p:num->real^N`
    (X_CHOOSE_THEN `q:num->real^N` (CONJUNCTS_THEN2 (LABEL_TAC "PART")
      (CONJUNCTS_THEN2 (LABEL_TAC "E0") (LABEL_TAC "PQ")))))))) THEN
  SUBGOAL_THEN
   `!n. n IN 1..k
        ==> lebesgue_measurable (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                       ((E:num->A->bool) n))`
  (LABEL_TAC "MEAS") THENL
   [USE_THEN "PART" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n IN 1..k
        ==> (!s. a <= s /\ s < b
                 ==> mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                       ((e:real->A->real) s) ((c:num->(A->bool)#(A->real^N)) n)
                     absolutely_integrable_on IMAGE (SND(c n)) ((E:num->A->bool) n)) /\
            (\s. drop(integral (IMAGE (SND(c n)) (E n))
                        (mfd_chart_integrand atlas (g s) (e s) (c n))))
              real_continuous_on {s | a <= s /\ s < b} /\
            (!t. a < t /\ t < b
                 ==> mfd_chart_integrand atlas (g t)
                       (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n)
                       absolutely_integrable_on IMAGE (SND(c n)) (E n) /\
                     ((\s. drop(integral (IMAGE (SND(c n)) (E n))
                                  (mfd_chart_integrand atlas (g s) (e s) (c n))))
                      has_real_derivative
                      drop(integral (IMAGE (SND(c n)) (E n))
                             (mfd_chart_integrand atlas (g t)
                               (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n))))
                     (atreal t))`
  (LABEL_TAC "PC") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGT_PIECE_INTEGRAL THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `(p:num->real^N) n`; `(q:num->real^N) n`] THEN
    USE_THEN "PQ" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    USE_THEN "MEAS" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `J = \s. sum(1..k)
              (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                        ((E:num->A->bool) n))
                     (mfd_chart_integrand atlas ((g:real->A->real^N^N) s)
                                         ((e:real->A->real) s) (c n))))` THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> mfd_integral (top,atlas) ((g:real->A->real^N^N) s) (topspace top)
                         ((e:real->A->real) s) = J s`
  (LABEL_TAC "IJ") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) s`; `(e:real->A->real) s`;
                   `topspace top:A->bool`; `(J:real->real) s`]
                  MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
    USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN EXISTS_TAC `J:real->real` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "IJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "J" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `J:real->real` THEN EXISTS_TAC `min (t - a) (b - t)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "IJ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integral (top,atlas) ((g:real->A->real^N^N) t) (topspace top)
      (\x. e' t x - mfd_scalar atlas (g t) x * (e:real->A->real) t x) =
    sum(1..k)
      (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                ((E:num->A->bool) n))
             (mfd_chart_integrand atlas (g t)
               (\x. e' t x - mfd_scalar atlas (g t) x * e t x) (c n))))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`;
                   `\x. (e':real->A->real) t x -
                        mfd_scalar atlas ((g:real->A->real^N^N) t) x *
                        (e:real->A->real) t x`;
                   `topspace top:A->bool`;
                   `sum(1..k)
                      (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                                ((E:num->A->bool) n))
                             (mfd_chart_integrand atlas ((g:real->A->real^N^N) t)
                               (\x. (e':real->A->real) t x -
                                    mfd_scalar atlas (g t) x * (e:real->A->real) t x)
                               (c n))))`]
                  MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC GRGT_HAS_INTEGRAL_FINITE_PARTITION THEN
    USE_THEN "PART" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E0" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "J" THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "PC" (MP_TAC o C MATCH_MP (ASSUME `n IN 1..k`)) THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

