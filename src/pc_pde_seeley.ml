(* Unit pc_pde_seeley: smooth extension of space-time maps past a time
   hyperplane.  First a copy of the file src/ns_time_ext.ml from the
   Navier_Stokes development (github.com/hol-light-family/Navier_Stokes): the
   smooth extension of a space-time map past a time hyperplane (Borel lemma
   with parameters, flat gluing, series), with its needs lines adapted.  Then
   the extension below an initial time for maps with time first
   (PDE_SEELEY_CORE) and on arbitrary open sets of space (PDE_SEELEY), which
   use SMOOTH_MAP_ON_LOCAL of pc_mfd_maps. *)

needs "src/pc_pde_base.ml";;
needs "src/ns_spacetime.ml";;
needs "src/ns_cutoff.ml";;
needs "src/pc_mfd_maps.ml";;
prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The part from ns_time_ext.ml: smooth extension of a space-time map past   *)
(* t = 1 (in the Navier_Stokes development, the generic analysis behind      *)
(* Lemmas 10.2 and 10.3 of its paper).                                       *)
(*                                                                           *)
(* The generic results:                                                      *)
(*   SMOOTH_MAP_ON_PARTIAL_FAMILY : a family of maps H l indexed by lists of *)
(*     coordinate indices, each with derivative v -> sum_i v_i H (i :: l),   *)
(*     consists of smooth maps, and H l is the iterated partial along l of  *)
(*     H [].                                                                 *)
(*   SMOOTH_MAP_ON_SERIES : term-by-term differentiation of series of       *)
(*     smooth maps whose differentiated series converge uniformly.         *)
(*   SMOOTH_MAP_ON_GLUE_FLAT : a map smooth below a time hyperplane, zero    *)
(*     on and above it, whose iterated partials all tend to zero uniformly  *)
(*     at the hyperplane, is smooth everywhere.                             *)
(*   BOREL_EXTENSION_PARAMETRIC : Borel lemma with parameters.              *)
(* Final theorem: NS_SMOOTH_EXTENSION_PAST_ONE.                              *)
(*                                                                           *)
(* First generic facts on partial derivatives, finite lists of indices, and  *)
(* the family criterion for smoothness.                                      *)
(* ========================================================================= *)

let TEXT_VSUM_BASIS_DELTA = prove
 (`!(f:num->real^N) i.
      1 <= i /\ i <= dimindex(:M)
      ==> vsum(1..dimindex(:M)) (\k. (basis i:real^M)$k % f k) = f i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..dimindex(:M)) (\k. if k = i then (f:num->real^N) i else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO];
    ASM_REWRITE_TAC[VSUM_DELTA; IN_NUMSEG]]);;

let TEXT_HAS_DERIVATIVE_PARTIALS = prove
 (`!(f:real^M->real^N) x.
      f differentiable (at x)
      ==> (f has_derivative
           (\v. vsum(1..dimindex(:M)) (\i. v$i % partial_derivative i f x)))
          (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\v. vsum(1..dimindex(:M)) (\i. v$i % partial_derivative i (f:real^M->real^N) x)) =
    frechet_derivative f (at x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^M` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative];
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let TEXT_PARTIAL_DERIVATIVE_FAMILY = prove
 (`!(f:real^M->real^N) (G:num->real^N) x i.
      (f has_derivative (\v. vsum(1..dimindex(:M)) (\k. v$k % G k))) (at x) /\
      1 <= i /\ i <= dimindex(:M)
      ==> partial_derivative i f x = G i`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
    MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[TEXT_VSUM_BASIS_DELTA]);;

let TEXT_ITERATED_PARTIAL_LOCAL_OPEN = prove
 (`!l s (f:real^M->real^N) g.
      open s /\ (!y. y IN s ==> f y = g y)
      ==> !x. x IN s ==> iterated_partial l f x = iterated_partial l g x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_MESON_TAC[]]);;

let TEXT_ITERATED_PARTIAL_LOCAL_AT = prove
 (`!l s (f:real^M->real^N) g x.
      open s /\ x IN s /\ (!y. y IN s ==> f y = g y)
      ==> iterated_partial l f x = iterated_partial l g x`,
  MESON_TAC[TEXT_ITERATED_PARTIAL_LOCAL_OPEN]);;

let TEXT_ITERATED_PARTIAL_ZERO = prove
 (`!l. iterated_partial l (\x:real^M. vec 0:real^N) = (\x. vec 0)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[iterated_partial] THEN
  REWRITE_TAC[FUN_EQ_THM; PARTIAL_DERIVATIVE_CONST]);;

let TEXT_ITERATED_PARTIAL_ZERO_OPEN = prove
 (`!l s (f:real^M->real^N) x.
      open s /\ x IN s /\ (!y. y IN s ==> f y = vec 0)
      ==> iterated_partial l f x = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `s:real^M->bool`; `f:real^M->real^N`;
                 `\x:real^M. vec 0:real^N`] TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
  ASM_REWRITE_TAC[TEXT_ITERATED_PARTIAL_ZERO] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The family criterion.  Lists l of indices in 1..dimindex(:M) index maps  *)
(* H l; if each H l has the derivative v -> sum_i v_i H (CONS i l) x at    *)
(* every x of the open set s, then every H l is smooth on s and the         *)
(* iterated partials of H l' are the maps H (APPEND l l').                  *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MAP_ON_PARTIAL_FAMILY = prove
 (`!s (H:(num)list->real^M->real^N).
      open s /\
      (!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
             ==> (H l has_derivative
                  (\v. vsum(1..dimindex(:M)) (\i. v$i % H (CONS i l) x))) (at x))
      ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l ==> smooth_map_on s (H l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  SUBGOAL_THEN
   `!n l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
          ==> continuously_differentiable n s ((H:(num)list->real^M->real^N) l)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
    EXISTS_TAC `\(x:real^M) (v:real^M).
       vsum(1..dimindex(:M)) (\i. v$i % (H:(num)list->real^M->real^N) (CONS i l) x)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `v:real^M` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[ALL]]);;

let SMOOTH_MAP_ON_PARTIAL_FAMILY_ITERATED = prove
 (`!s (H:(num)list->real^M->real^N).
      open s /\
      (!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
             ==> (H l has_derivative
                  (\v. vsum(1..dimindex(:M)) (\i. v$i % H (CONS i l) x))) (at x))
      ==> !l l' x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\
                   ALL (\i. 1 <= i /\ i <= dimindex(:M)) l' /\ x IN s
                   ==> iterated_partial l (H l') x = H (APPEND l l') x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; APPEND; ALL] THEN
  MAP_EVERY X_GEN_TAC [`l':num list`; `x:real^M`] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h ((H:(num)list->real^M->real^N) (APPEND t l')) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC TEXT_PARTIAL_DERIVATIVE_FAMILY THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL_APPEND]]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness of the lists of bounded length over 1..n, and common choices  *)
(* of deltas and of thresholds for finitely many indices.                   *)
(* ------------------------------------------------------------------------- *)

let TEXT_FINITE_LISTS = prove
 (`!k n. FINITE {l:(num)list | LENGTH l <= k /\ ALL (\i. 1 <= i /\ i <= n) l}`,
  INDUCT_TAC THEN GEN_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{[]:(num)list}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING; LE; LENGTH_EQ_NIL] THEN
    MESON_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `([]:(num)list) INSERT
      IMAGE (\p:num#((num)list). CONS (FST p) (SND p))
            ((1..n) CROSS {l:(num)list | LENGTH l <= k /\ ALL (\i. 1 <= i /\ i <= n) l})` THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_IMAGE; EXISTS_PAIR_THM;
                IN_CROSS; IN_NUMSEG] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ALL; NOT_CONS_NIL; CONS_11; LE_SUC] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`h:num`; `t:(num)list`] THEN ASM_REWRITE_TAC[]]);;

let TEXT_FINITE_DELTA_MIN = prove
 (`!(P:num->real->bool) n.
      (!i d d'. P i d /\ &0 < d' /\ d' <= d ==> P i d') /\
      (!i. 1 <= i /\ i <= n ==> ?d. &0 < d /\ P i d)
      ==> ?d. &0 < d /\ !i. 1 <= i /\ i <= n ==> P i d`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "M") (LABEL_TAC "E")) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "E" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)] THEN
    USE_THEN "E" (MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN USE_THEN "M" MATCH_MP_TAC THEN
    ASM_CASES_TAC `i = SUC n` THENL
     [EXISTS_TAC `d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
      EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; REAL_ARITH_TAC]]]);;

let TEXT_FINITE_N_MAX = prove
 (`!(P:num->num->bool) n.
      (!i N N'. P i N /\ N <= N' ==> P i N') /\
      (!i. 1 <= i /\ i <= n ==> ?N. P i N)
      ==> ?N. !i. 1 <= i /\ i <= n ==> P i N`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `0` THEN ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "M") (LABEL_TAC "E")) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "E" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
    USE_THEN "E" (MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN USE_THEN "M" MATCH_MP_TAC THEN
    ASM_CASES_TAC `i = SUC n` THENL
     [EXISTS_TAC `N2:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXISTS_TAC `N1:num` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ARITH_TAC]]]);;

let TEXT_NORM_VSUM_CMUL_BOUND = prove
 (`!(v:real^M) (G:num->real^N) B.
      (!i. 1 <= i /\ i <= dimindex(:M) ==> norm(G i) <= B)
      ==> norm(vsum(1..dimindex(:M)) (\i. v$i % G i))
          <= &(dimindex(:M)) * B * norm v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:M)) (\i. B * norm(v:real^M))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE; COMPONENT_LE_NORM];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]);;

(* ========================================================================= *)
(* Term-by-term differentiation of series of smooth maps.                    *)
(* ========================================================================= *)

(* The Weierstrass M-test in the form used below: the series converges     *)
(* pointwise to its infsum, uniformly on s.                                  *)
let TEXT_SERIES_UNIFORM = prove
 (`!(s:real^M->bool) (f:num->real^M->real^N) (b:num->real) N.
      summable (from 0) (\n. lift(b n)) /\
      (!n x. N <= n /\ x IN s ==> norm(f n x) <= b n)
      ==> (!x. x IN s ==> ((\n. f n x) sums infsum (from 0) (\n. f n x)) (from 0)) /\
          (!e. &0 < e
               ==> ?N'. !n x. N' <= n /\ x IN s
                              ==> norm(vsum(0..n) (\k. f k x) -
                                       infsum (from 0) (\k. f k x)) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\(x:real^M) (n:num). (f:num->real^M->real^N) n x`; `b:num->real`;
                 `\x:real^M. x IN s`; `from 0`] SERIES_COMPARISON_UNIFORM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_DEF; GSYM summable] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[FROM_INTER_NUMSEG]] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real^M->real^N`) THEN
  SUBGOAL_THEN
   `!x. x IN s ==> ((\n. (f:num->real^M->real^N) n x) sums l x) (from 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[sums; LIM_SEQUENTIALLY; FROM_INTER_NUMSEG] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s ==> infsum (from 0) (\n. (f:num->real^M->real^N) n x) = l x`
  ASSUME_TAC THENL [ASM_MESON_TAC[INFSUM_UNIQUE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N1:num` THEN REWRITE_TAC[GSYM dist] THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* The derivative of the sum of a series of smooth maps whose            *)
(* differentiated series are uniformly dominated, at one point.            *)
let TEXT_SERIES_HAS_DERIVATIVE = prove
 (`!s (f:num->real^M->real^N) l x.
      open s /\ (!n. smooth_map_on s (f n)) /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
           ==> ?b N. summable (from 0) (\n. lift(b n)) /\
                     !n x. N <= n /\ x IN s
                           ==> norm(iterated_partial l (f n) x) <= b n) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
      ==> ((\x. infsum (from 0) (\n. iterated_partial l (f n) x))
           has_derivative
           (\v. vsum(1..dimindex(:M))
                 (\i. v$i % infsum (from 0) (\n. iterated_partial (CONS i l) (f n) x))))
          (at x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "B") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!l1. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l1
        ==> (!x. x IN s
                 ==> ((\n. iterated_partial l1 ((f:num->real^M->real^N) n) x) sums
                      infsum (from 0) (\n. iterated_partial l1 (f n) x)) (from 0)) /\
            (!e. &0 < e
                 ==> ?N'. !n x. N' <= n /\ x IN s
                                ==> norm(vsum(0..n) (\k. iterated_partial l1 (f k) x) -
                                         infsum (from 0) (\k. iterated_partial l1 (f k) x))
                                    < e)`
  (LABEL_TAC "U") THENL
   [X_GEN_TAC `l1:num list` THEN DISCH_TAC THEN
    USE_THEN "B" (MP_TAC o SPEC `l1:num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`s:real^M->bool`;
                   `\n:num. iterated_partial l1 ((f:num->real^M->real^N) n)`;
                   `b:num->real`; `N:num`] TEXT_SERIES_UNIFORM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`ball(x:real^M,r)`;
    `\n:num. iterated_partial l ((f:num->real^M->real^N) n)`;
    `\(n:num) (y:real^M) (v:real^M).
       vsum(1..dimindex(:M)) (\i. v$i % iterated_partial (CONS i l) ((f:num->real^M->real^N) n) y)`;
    `\(y:real^M) (v:real^M).
       vsum(1..dimindex(:M))
         (\i. v$i % infsum (from 0) (\n. iterated_partial (CONS i l) ((f:num->real^M->real^N) n) y))`;
    `from 0`] HAS_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[iterated_partial] THEN
      MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN ASM_MESON_TAC[SUBSET];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < e / &(dimindex(:M))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`\(i:num) (N:num). !n y. N <= n /\ y IN s
           ==> norm(vsum(0..n) (\k. iterated_partial (CONS i l) ((f:num->real^M->real^N) k) y) -
                    infsum (from 0) (\k. iterated_partial (CONS i l) (f k) y))
               < e / &(dimindex(:M))`;
        `dimindex(:M)`] TEXT_FINITE_N_MAX) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MESON_TAC[LE_TRANS];
          X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          USE_THEN "U" (MP_TAC o SPEC `CONS (i:num) (l:num list)`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o SPEC `e / &(dimindex(:M))` o CONJUNCT2) THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`; `v:real^M`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^M) IN s` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[FROM_INTER_NUMSEG] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [VSUM_SWAP_NUMSEG] THEN
      SIMP_TAC[FINITE_NUMSEG; VSUM_LMUL; GSYM VSUM_SUB; GSYM VECTOR_SUB_LDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(dimindex(:M)) * (e / &(dimindex(:M))) * norm(v:real^M)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TEXT_NORM_VSUM_CMUL_BOUND THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_ASSOC] THEN
        SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; DIMINDEX_NONZERO; REAL_LE_REFL]];
      MAP_EVERY EXISTS_TAC
       [`x:real^M`; `infsum (from 0) (\n. iterated_partial l ((f:num->real^M->real^N) n) x)`] THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `gg:real^M->real^N`) THEN
  SUBGOAL_THEN
   `!y. y IN ball(x:real^M,r)
        ==> (gg:real^M->real^N) y =
            infsum (from 0) (\n. iterated_partial l ((f:num->real^M->real^N) n) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
    EXISTS_TAC `\n:num. iterated_partial l ((f:num->real^M->real^N) n) (y:real^M)` THEN
    EXISTS_TAC `from 0` THEN ASM_SIMP_TAC[] THEN
    USE_THEN "U" (MP_TAC o SPEC `l:num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. infsum (from 0) (\n. iterated_partial l ((f:num->real^M->real^N) n) x))
     has_derivative
     (\v. vsum(1..dimindex(:M))
           (\i. v$i % infsum (from 0) (\n. iterated_partial (CONS i l) (f n) x))))
    (at x within ball(x,r))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`gg:real^M->real^N`; `r:real`] THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN; OPEN_BALL; CENTRE_IN_BALL]]);;

(* Term-by-term differentiation: if every differentiated series is         *)
(* dominated by a summable sequence from some index on, the sum is smooth  *)
(* and its iterated partials are the sums of the iterated partials.        *)
let SMOOTH_MAP_ON_SERIES = prove
 (`!s (f:num->real^M->real^N).
      open s /\ (!n. smooth_map_on s (f n)) /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
           ==> ?b N. summable (from 0) (\n. lift(b n)) /\
                     !n x. N <= n /\ x IN s
                           ==> norm(iterated_partial l (f n) x) <= b n)
      ==> smooth_map_on s (\x. infsum (from 0) (\n. f n x)) /\
          !l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
                ==> ((\n. iterated_partial l (f n) x) sums
                     iterated_partial l (\x. infsum (from 0) (\n. f n x)) x) (from 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B"))) THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN s
          ==> ((\x. infsum (from 0) (\n. iterated_partial l ((f:num->real^M->real^N) n) x))
               has_derivative
               (\v. vsum(1..dimindex(:M))
                     (\i. v$i % infsum (from 0) (\n. iterated_partial (CONS i l) (f n) x))))
              (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `f:num->real^M->real^N`; `l:num list`; `x:real^M`]
      TEXT_SERIES_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`;
    `\l (x:real^M). infsum (from 0) (\n. iterated_partial l ((f:num->real^M->real^N) n) x)`]
   SMOOTH_MAP_ON_PARTIAL_FAMILY_ITERATED) THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`;
    `\l (x:real^M). infsum (from 0) (\n. iterated_partial l ((f:num->real^M->real^N) n) x)`]
   SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  ASM_SIMP_TAC[ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `[]:(num)list`) THEN
  REWRITE_TAC[ALL; iterated_partial; ETA_AX] THEN DISCH_TAC THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `[]:(num)list`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[ALL; APPEND_NIL; iterated_partial; ETA_AX] THEN
  DISCH_THEN SUBST1_TAC THEN
  USE_THEN "B" (MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\n:num. iterated_partial l ((f:num->real^M->real^N) n)`;
                 `b:num->real`; `N:num`] TEXT_SERIES_UNIFORM) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Space-time coordinates; maps of tensor form z -> a(time z) E(space z) and *)
(* their iterated partial derivatives.  Space-time points are                *)
(* z:real^(M,1)finite_sum; the time coordinate has index dimindex(:M) + 1.   *)
(* ========================================================================= *)

let TEXT_BASIS_LOW = prove
 (`!i. 1 <= i /\ i <= dimindex(:M)
       ==> fstcart(basis i:real^(M,N)finite_sum) = basis i /\
           sndcart(basis i:real^(M,N)finite_sum) = vec 0`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN CONJ_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FSTCART_COMPONENT; SNDCART_COMPONENT; VEC_COMPONENT] THENL
   [SUBGOAL_THEN `1 <= k /\ k <= dimindex(:(M,N)finite_sum)`
      (fun th -> SIMP_TAC[BASIS_COMPONENT; th]) THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[BASIS_COMPONENT]];
    SUBGOAL_THEN `1 <= k + dimindex(:M) /\ k + dimindex(:M) <= dimindex(:(M,N)finite_sum)`
      (fun th -> SIMP_TAC[BASIS_COMPONENT; th]) THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let TEXT_BASIS_HIGH = prove
 (`!i. 1 <= i /\ i <= dimindex(:N)
       ==> fstcart(basis(dimindex(:M) + i):real^(M,N)finite_sum) = vec 0 /\
           sndcart(basis(dimindex(:M) + i):real^(M,N)finite_sum) = basis i`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN CONJ_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FSTCART_COMPONENT; SNDCART_COMPONENT; VEC_COMPONENT] THENL
   [SUBGOAL_THEN `1 <= k /\ k <= dimindex(:(M,N)finite_sum)`
      (fun th -> SIMP_TAC[BASIS_COMPONENT; th]) THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC];
    SUBGOAL_THEN `1 <= k + dimindex(:M) /\ k + dimindex(:M) <= dimindex(:(M,N)finite_sum)`
      (fun th -> SIMP_TAC[BASIS_COMPONENT; th]) THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[BASIS_COMPONENT] THEN
      REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let TEXT_DIMINDEX_SPACETIME = prove
 (`dimindex(:(M,1)finite_sum) = dimindex(:M) + 1`,
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1]);;

let TEXT_DIFFERENTIABLE_SNDCART_COMPOSE = prove
 (`!(a:real^N->real^P) (z:real^(M,N)finite_sum).
      a differentiable (at (sndcart z))
      ==> (\z. a(sndcart z)) differentiable (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(M,N)finite_sum. (a:real^N->real^P)(sndcart z)) = a o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_SNDCART]);;

let TEXT_DIFFERENTIABLE_FSTCART_COMPOSE = prove
 (`!(a:real^M->real^P) (z:real^(M,N)finite_sum).
      a differentiable (at (fstcart z))
      ==> (\z. a(fstcart z)) differentiable (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(M,N)finite_sum. (a:real^M->real^P)(fstcart z)) = a o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_FSTCART]);;

let TEXT_PARTIAL_DERIVATIVE_SNDCART_COMPOSE = prove
 (`!(a:real^N->real^P) (z:real^(M,N)finite_sum) i.
      a differentiable (at (sndcart z))
      ==> partial_derivative i (\z. a(sndcart z)) z =
          frechet_derivative a (at (sndcart z)) (sndcart(basis i:real^(M,N)finite_sum))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(M,N)finite_sum. (a:real^N->real^P)(sndcart z)) = a o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_CHAIN o lhand o snd) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_SNDCART; PARTIAL_DERIVATIVE_LINEAR]);;

let TEXT_PARTIAL_DERIVATIVE_FSTCART_COMPOSE = prove
 (`!(a:real^M->real^P) (z:real^(M,N)finite_sum) i.
      a differentiable (at (fstcart z))
      ==> partial_derivative i (\z. a(fstcart z)) z =
          frechet_derivative a (at (fstcart z)) (fstcart(basis i:real^(M,N)finite_sum))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(M,N)finite_sum. (a:real^M->real^P)(fstcart z)) = a o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_CHAIN o lhand o snd) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_FSTCART; PARTIAL_DERIVATIVE_LINEAR]);;

let TEXT_PARTIAL_DERIVATIVE_TENSOR_SPACE = prove
 (`!(a:real^1->real^1) (E:real^M->real^N) i (z:real^(M,1)finite_sum).
      a differentiable (at (sndcart z)) /\ E differentiable (at (fstcart z)) /\
      1 <= i /\ i <= dimindex(:M)
      ==> partial_derivative i (\z. drop(a(sndcart z)) % E(fstcart z)) z =
          drop(a(sndcart z)) % partial_derivative i E (fstcart z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `\z:real^(M,1)finite_sum. (a:real^1->real^1)(sndcart z)`;
                 `\z:real^(M,1)finite_sum. (E:real^M->real^N)(fstcart z)`;
                 `z:real^(M,1)finite_sum`] PARTIAL_DERIVATIVE_MUL) THEN
  ASM_SIMP_TAC[TEXT_DIFFERENTIABLE_SNDCART_COMPOSE; TEXT_DIFFERENTIABLE_FSTCART_COMPOSE] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[TEXT_PARTIAL_DERIVATIVE_SNDCART_COMPOSE;
               TEXT_PARTIAL_DERIVATIVE_FSTCART_COMPOSE; TEXT_BASIS_LOW] THEN
  SUBGOAL_THEN `frechet_derivative (a:real^1->real^1) (at (sndcart (z:real^(M,1)finite_sum)))
                  (vec 0) = vec 0` SUBST1_TAC THENL
   [MP_TAC(ISPEC `frechet_derivative (a:real^1->real^1) (at (sndcart (z:real^(M,1)finite_sum)))`
      LINEAR_0) THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE];
    REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; partial_derivative]]);;

let TEXT_PARTIAL_DERIVATIVE_TENSOR_TIME = prove
 (`!(a:real^1->real^1) (E:real^M->real^N) (z:real^(M,1)finite_sum).
      a differentiable (at (sndcart z)) /\ E differentiable (at (fstcart z))
      ==> partial_derivative (dimindex(:M) + 1)
            (\z. drop(a(sndcart z)) % E(fstcart z)) z =
          drop(partial_derivative 1 a (sndcart z)) % E(fstcart z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:M) + 1`;
                 `\z:real^(M,1)finite_sum. (a:real^1->real^1)(sndcart z)`;
                 `\z:real^(M,1)finite_sum. (E:real^M->real^N)(fstcart z)`;
                 `z:real^(M,1)finite_sum`] PARTIAL_DERIVATIVE_MUL) THEN
  ASM_SIMP_TAC[TEXT_DIFFERENTIABLE_SNDCART_COMPOSE; TEXT_DIFFERENTIABLE_FSTCART_COMPOSE] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `1` (INST_TYPE [`:1`,`:N`] TEXT_BASIS_HIGH)) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[TEXT_PARTIAL_DERIVATIVE_SNDCART_COMPOSE;
               TEXT_PARTIAL_DERIVATIVE_FSTCART_COMPOSE] THEN
  SUBGOAL_THEN `frechet_derivative (E:real^M->real^N) (at (fstcart (z:real^(M,1)finite_sum)))
                  (vec 0) = vec 0` SUBST1_TAC THENL
   [MP_TAC(ISPEC `frechet_derivative (E:real^M->real^N) (at (fstcart (z:real^(M,1)finite_sum)))`
      LINEAR_0) THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE];
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; partial_derivative]]);;

let TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART = prove
 (`smooth_map_on (:real^(M,N)finite_sum) fstcart /\
   smooth_map_on (:real^(M,N)finite_sum) sndcart`,
  MP_TAC(ISPECL [`(:real^(M,N)finite_sum)`; `\x:real^(M,N)finite_sum. x`]
    SMOOTH_MAP_ON_FSTCART_OPEN) THEN
  MP_TAC(ISPECL [`(:real^(M,N)finite_sum)`; `\x:real^(M,N)finite_sum. x`]
    SMOOTH_MAP_ON_SNDCART_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN SIMP_TAC[]);;

let TEXT_SMOOTH_MAP_ON_TENSOR = prove
 (`!(a:real^1->real^1) (E:real^M->real^N).
      smooth_map_on (:real^1) a /\ smooth_map_on (:real^M) E
      ==> smooth_map_on (:real^(M,1)finite_sum) (\z. drop(a(sndcart z)) % E(fstcart z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^(M,1)finite_sum)`;
                 `\z:real^(M,1)finite_sum. (a:real^1->real^1)(sndcart z)`;
                 `\z:real^(M,1)finite_sum. (E:real^M->real^N)(fstcart z)`]
         SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\z:real^(M,1)finite_sum. (a:real^1->real^1)(sndcart z)) = a o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
    SUBGOAL_THEN `(\z:real^(M,1)finite_sum. (E:real^M->real^N)(fstcart z)) = E o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^M)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]);;

let TEXT_ITERATED_PARTIAL_TENSOR = prove
 (`!(a:real^1->real^1) (E:real^M->real^N).
      smooth_map_on (:real^1) a /\ smooth_map_on (:real^M) E
      ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
              ==> iterated_partial l
                    (\z:real^(M,1)finite_sum. drop(a(sndcart z)) % E(fstcart z)) =
                  (\z. drop(iterated_partial
                             (REPLICATE (LENGTH(FILTER (\i. i = dimindex(:M) + 1) l)) 1)
                             a (sndcart z)) %
                       iterated_partial (FILTER (\i. ~(i = dimindex(:M) + 1)) l) E
                         (fstcart z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[iterated_partial; FILTER; LENGTH; REPLICATE; ALL; ETA_AX] THEN
  REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `m = LENGTH(FILTER (\i. i = dimindex(:M) + 1) t)` THEN
  ABBREV_TAC `al = FILTER (\i. ~(i = dimindex(:M) + 1)) t` THEN
  SUBGOAL_THEN `!w. iterated_partial (REPLICATE m 1) (a:real^1->real^1) differentiable (at w)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. iterated_partial al (E:real^M->real^N) differentiable (at x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^(M,1)finite_sum` THEN
  ASM_CASES_TAC `h = dimindex(:M) + 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LENGTH; REPLICATE; iterated_partial] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TEXT_PARTIAL_DERIVATIVE_TENSOR_TIME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[iterated_partial] THEN
    MATCH_MP_TAC TEXT_PARTIAL_DERIVATIVE_TENSOR_SPACE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Reordering iterated partials of smooth maps (Schwarz).                    *)
(* For a smooth map on an open set, the partial along a fixed index k can  *)
(* be moved innermost: iterated_partial l f agrees with the iterated        *)
(* partial along the list of the other indices of l followed by the copies *)
(* of k.                                                                     *)
(* ========================================================================= *)

let TEXT_ALL_FILTER_IMP = prove
 (`!P Q (l:A list). ALL P l ==> ALL P (FILTER Q l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_FILTER] THEN
  MATCH_MP_TAC MONO_ALL THEN SIMP_TAC[]);;

let TEXT_FILTER_EQ_REPLICATE = prove
 (`!k l. FILTER (\j:num. j = k) l = REPLICATE (LENGTH (FILTER (\j. j = k) l)) k`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; LENGTH; REPLICATE] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; REPLICATE; CONS_11] THEN
  ASM_MESON_TAC[]);;

let TEXT_PARTIAL_COMMUTE_ITERATED = prove
 (`!s (f:real^M->real^N) i.
      open s /\ smooth_map_on s f /\ 1 <= i /\ i <= dimindex(:M)
      ==> !l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
              ==> !x. x IN s
                      ==> partial_derivative i (iterated_partial l f) x =
                          iterated_partial l (partial_derivative i f) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; ALL] THEN
  STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `partial_derivative h (partial_derivative i (iterated_partial t (f:real^M->real^N))) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:num list`; `s:real^M->bool`; `f:real^M->real^N`]
      SMOOTH_MAP_ON_ITERATED_PARTIAL) THEN
    ASM_REWRITE_TAC[smooth_map_on] THEN SIMP_TAC[];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[]]);;

let TEXT_ITERATED_PARTIAL_CANON = prove
 (`!s (f:real^M->real^N) k.
      open s /\ smooth_map_on s f /\ 1 <= k /\ k <= dimindex(:M)
      ==> !l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
              ==> !x. x IN s
                      ==> iterated_partial l f x =
                          iterated_partial
                            (APPEND (FILTER (\j. ~(j = k)) l) (FILTER (\j. j = k) l)) f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; FILTER; APPEND; ALL] THEN
  STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `h:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `partial_derivative k
        (iterated_partial (FILTER (\j. ~(j = k)) t)
          (iterated_partial (FILTER (\j. j = k) t) (f:real^M->real^N))) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM ITERATED_PARTIAL_APPEND] THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`s:real^M->bool`;
                     `iterated_partial (FILTER (\j. j = k) t) (f:real^M->real^N)`;
                     `k:num`] TEXT_PARTIAL_COMMUTE_ITERATED) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `FILTER (\j:num. ~(j = k)) (t:num list)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[TEXT_ALL_FILTER_IMP]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[APPEND; iterated_partial] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The flat gluing lemma.  A map that is smooth below the time               *)
(* hyperplane t = a, zero on and above it, and whose iterated partials all  *)
(* tend to zero uniformly as t tends to a from below, is smooth everywhere. *)
(* ========================================================================= *)

let TEXT_OPEN_TIME_LT = prove
 (`!a. open {z:real^(M,1)finite_sum | drop(sndcart z) < a}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`sndcart:real^(M,1)finite_sum->real^1`; `{y:real^1 | y$1 < a}`]
         CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; drop] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_SNDCART]);;

let TEXT_OPEN_TIME_GT = prove
 (`!a. open {z:real^(M,1)finite_sum | a < drop(sndcart z)}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`sndcart:real^(M,1)finite_sum->real^1`; `{y:real^1 | y$1 > a}`]
         CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; drop; real_gt] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_SNDCART]);;

let TEXT_CONVEX_TIME_SLAB = prove
 (`!a b. convex {z:real^(M,1)finite_sum | a < drop(sndcart z) /\ drop(sndcart z) < b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[convex; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^(M,1)finite_sum`; `y:real^(M,1)finite_sum`;
                       `u:real`; `v:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[SNDCART_ADD; SNDCART_CMUL; DROP_ADD; DROP_CMUL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONVEX_BOUND_GT; MATCH_MP_TAC REAL_CONVEX_BOUND_LT] THEN
  ASM_REWRITE_TAC[]);;

let TEXT_TIME_DIST = prove
 (`!y z:real^(M,1)finite_sum.
      abs(drop(sndcart y) - drop(sndcart z)) <= norm(y - z)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `y - z:real^(M,1)finite_sum` NORM_SNDCART) THEN
  REWRITE_TAC[SNDCART_SUB; NORM_REAL; GSYM drop; DROP_SUB]);;

(* The key estimate: if u and its first partials tend to zero uniformly at *)
(* the hyperplane, then u is o(a - t) there, by the mean value inequality  *)
(* along time segments in a thin slab below the hyperplane.                *)
let TEXT_FLAT_BOUND = prove
 (`!(u:real^(M,1)finite_sum->real^N) a.
      smooth_map_on {z | drop(sndcart z) < a} u /\
      (!e. &0 < e
           ==> ?d. &0 < d /\
                   !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                       ==> norm(u z) < e) /\
      (!i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(partial_derivative i u z) < e)
      ==> !e. &0 < e
              ==> ?d. &0 < d /\
                      !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                          ==> norm(u z) <= e * (a - drop(sndcart z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Z") (LABEL_TAC "P"))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / &2 / &(dimindex(:(M,1)finite_sum))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_OF_NUM_LT; DIMINDEX_GE_1;
                 ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(i:num) (d:real). !z:real^(M,1)finite_sum.
       a - d < drop(sndcart z) /\ drop(sndcart z) < a
       ==> norm(partial_derivative i (u:real^(M,1)finite_sum->real^N) z)
           < e / &2 / &(dimindex(:(M,1)finite_sum))`;
    `dimindex(:(M,1)finite_sum)`] TEXT_FINITE_DELTA_MIN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "P" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^(M,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. drop(sndcart w) < a ==> (u:real^(M,1)finite_sum->real^N) differentiable (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^(M,1)finite_sum | drop(sndcart z) < a}` THEN
    ASM_REWRITE_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w w'. w IN {w:real^(M,1)finite_sum | a - d < drop(sndcart w) /\ drop(sndcart w) < a} /\
           w' IN {w:real^(M,1)finite_sum | a - d < drop(sndcart w) /\ drop(sndcart w) < a}
           ==> norm((u:real^(M,1)finite_sum->real^N) w - u w') <= e / &2 * norm(w - w')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
    EXISTS_TAC `\w:real^(M,1)finite_sum. frechet_derivative (u:real^(M,1)finite_sum->real^N) (at w)` THEN
    REWRITE_TAC[TEXT_CONVEX_TIME_SLAB; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(M,1)finite_sum` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[];
      X_GEN_TAC `w:real^(M,1)finite_sum` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(u:real^(M,1)finite_sum->real^N) differentiable (at w)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP TEXT_HAS_DERIVATIVE_PARTIALS) THEN
      DISCH_THEN(fun th ->
        SUBST1_TAC(SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)) THEN
        ASSUME_TAC(CONJUNCT1(REWRITE_RULE[has_derivative] th))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN
      X_GEN_TAC `v:real^(M,1)finite_sum` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(dimindex(:(M,1)finite_sum)) *
                  (e / &2 / &(dimindex(:(M,1)finite_sum))) * norm(v:real^(M,1)finite_sum)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TEXT_NORM_VSUM_CMUL_BOUND THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        USE_THEN "D" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN
        SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; DIMINDEX_NONZERO; REAL_LE_REFL]]];
    ALL_TAC] THEN
  USE_THEN "Z" (MP_TAC o SPEC `e / &2 * (a - drop(sndcart(z:real^(M,1)finite_sum)))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_HALF] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `t' = a - min d1 (a - drop(sndcart(z:real^(M,1)finite_sum))) / &2` THEN
  SUBGOAL_THEN
   `drop(sndcart(z:real^(M,1)finite_sum)) < t' /\ t' < a /\ a - d1 < t'`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `z' = pastecart (fstcart(z:real^(M,1)finite_sum)) (lift t')` THEN
  SUBGOAL_THEN `drop(sndcart(z':real^(M,1)finite_sum)) = t'` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((z:real^(M,1)finite_sum) - z') = t' - drop(sndcart z)` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL; NORM_PASTECART_0] THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((u:real^(M,1)finite_sum->real^N) z - u z') <= e / &2 * (t' - drop(sndcart z))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^(M,1)finite_sum`; `z':real^(M,1)finite_sum`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((u:real^(M,1)finite_sum->real^N) z') < e / &2 * (a - drop(sndcart(z:real^(M,1)finite_sum)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `e / &2 * (t' - drop(sndcart(z:real^(M,1)finite_sum))) <=
    e / &2 * (a - drop(sndcart z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`(u:real^(M,1)finite_sum->real^N) z`; `(u:real^(M,1)finite_sum->real^N) z'`]
    (NORM_ARITH `!x y:real^N. norm x <= norm y + norm(x - y)`)) THEN
  ASM_REAL_ARITH_TAC);;

(* The derivative of the glued family at every point.                       *)
let TEXT_GLUE_FLAT_DERIVATIVE = prove
 (`!(h:real^(M,1)finite_sum->real^N) a l z.
      smooth_map_on {z | drop(sndcart z) < a} h /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l h z) < e) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
      ==> ((\z. if drop(sndcart z) < a then iterated_partial l h z else vec 0)
           has_derivative
           (\v. vsum(1..dimindex(:(M,1)finite_sum))
                 (\i. v$i % (if drop(sndcart z) < a
                             then iterated_partial (CONS i l) h z else vec 0))))
          (at z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "L") ASSUME_TAC)) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `drop(sndcart(z:real^(M,1)finite_sum)) < a \/
                a < drop(sndcart z) \/ drop(sndcart z) = a`) THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `iterated_partial l (h:real^(M,1)finite_sum->real^N)` THEN
    EXISTS_TAC `{z:real^(M,1)finite_sum | drop(sndcart z) < a}` THEN
    ASM_SIMP_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM] THEN
    REWRITE_TAC[iterated_partial] THEN
    MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^(M,1)finite_sum | drop(sndcart z) < a}` THEN
    ASM_SIMP_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ASM_SIMP_TAC[REAL_ARITH `a < t ==> ~(t < a)`] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VSUM_0] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\z:real^(M,1)finite_sum. vec 0:real^N` THEN
    EXISTS_TAC `{z:real^(M,1)finite_sum | a < drop(sndcart z)}` THEN
    ASM_SIMP_TAC[TEXT_OPEN_TIME_GT; IN_ELIM_THM; HAS_DERIVATIVE_CONST;
                 REAL_ARITH `a < t ==> ~(t < a)`];
    ASM_REWRITE_TAC[REAL_LT_REFL; VECTOR_MUL_RZERO; VSUM_0] THEN
    REWRITE_TAC[HAS_DERIVATIVE_AT_ALT; LINEAR_ZERO] THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; VECTOR_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`iterated_partial l (h:real^(M,1)finite_sum->real^N)`; `a:real`]
      TEXT_FLAT_BOUND) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; TEXT_OPEN_TIME_LT];
        USE_THEN "L" (MP_TAC o SPEC `l:num list`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        USE_THEN "L" (MP_TAC o SPEC `CONS (i:num) (l:num list)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial]]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^(M,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y:real^(M,1)finite_sum`; `z:real^(M,1)finite_sum`] TEXT_TIME_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO; NORM_0] THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e * (a - drop(sndcart(y:real^(M,1)finite_sum)))` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]]]);;

let SMOOTH_MAP_ON_GLUE_FLAT = prove
 (`!(h:real^(M,1)finite_sum->real^N) a.
      smooth_map_on {z | drop(sndcart z) < a} h /\
      (!z. a <= drop(sndcart z) ==> h z = vec 0) /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l h z) < e)
      ==> smooth_map_on (:real^(M,1)finite_sum) h`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`(:real^(M,1)finite_sum)`;
    `\l (z:real^(M,1)finite_sum).
       if drop(sndcart z) < a then iterated_partial l (h:real^(M,1)finite_sum->real^N) z
       else vec 0`] SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_GLUE_FLAT_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `[]:(num)list`) THEN REWRITE_TAC[ALL; iterated_partial] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^(M,1)finite_sum` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Limits at the hyperplane t = a of maps defined below it.                  *)
(* If every iterated partial of g converges uniformly in space as t tends  *)
(* to a from below, the limits G l are smooth in space, and their spatial  *)
(* partials are the limits along the extended lists.                       *)
(* ========================================================================= *)

let TEXT_UNIFORM_SEQ = prove
 (`!(u:real^(M,1)finite_sum->real^N) (A:real^M->real^N) a.
      (!e. &0 < e
           ==> ?d. &0 < d /\
                   !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                       ==> norm(u z - A(fstcart z)) < e)
      ==> !e. &0 < e
              ==> ?N. !n y. N <= n
                            ==> norm(u(pastecart y (lift(a - inv(&n + &1)))) - A y) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv(&n + &1) /\ inv(&n + &1) < d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y:real^M) (lift(a - inv(&n + &1)))`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let TEXT_UNIFORM_LIM = prove
 (`!(u:real^(M,1)finite_sum->real^N) (A:real^M->real^N) a.
      (!e. &0 < e
           ==> ?d. &0 < d /\
                   !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                       ==> norm(u z - A(fstcart z)) < e)
      ==> !y. ((\n. u(pastecart y (lift(a - inv(&n + &1))))) --> A y) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP TEXT_UNIFORM_SEQ) THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN MESON_TAC[]);;

let TEXT_LIMIT_UNIQUE = prove
 (`!(u:real^(M,1)finite_sum->real^N) (A:real^M->real^N) B a.
      (!e. &0 < e
           ==> ?d. &0 < d /\
                   !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                       ==> norm(u z - A(fstcart z)) < e) /\
      (!e. &0 < e
           ==> ?d. &0 < d /\
                   !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                       ==> norm(u z - B(fstcart z)) < e)
      ==> A = B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP TEXT_UNIFORM_LIM)) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. (u:real^(M,1)finite_sum->real^N)(pastecart y (lift(a - inv(&n + &1))))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

let TEXT_LIMIT_VANISH = prove
 (`!(u:real^(M,1)finite_sum->real^N) (A:real^M->real^N) a x.
      (!e. &0 < e
           ==> ?d. &0 < d /\
                   !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                       ==> norm(u z - A(fstcart z)) < e) /\
      (!t. t < a ==> u(pastecart x (lift t)) = vec 0)
      ==> A x = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:real^M` o MATCH_MP TEXT_UNIFORM_LIM)
                             ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\n. (u:real^(M,1)finite_sum->real^N)(pastecart x (lift(a - inv(&n + &1))))) =
    (\n. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e ==> a - e < a`) THEN MATCH_MP_TAC REAL_LT_INV THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n:num. vec 0:real^N` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIM_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* Spatial slices of space-time maps.                                         *)
(* ------------------------------------------------------------------------- *)

let TEXT_PASTECART_BASIS_LOW = prove
 (`!i. 1 <= i /\ i <= dimindex(:M)
       ==> pastecart (basis i:real^M) (vec 0:real^N) = basis i`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM PASTECART_FST_SND] THEN
  ASM_SIMP_TAC[TEXT_BASIS_LOW]);;

let TEXT_HAS_DERIVATIVE_PASTECART_LEFT = prove
 (`!(c:real^N) (y:real^M).
      ((\y. pastecart y c) has_derivative (\v. pastecart v (vec 0))) (at y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`at (y:real^M)`; `\y:real^M. y`; `\y:real^M. (c:real^N)`;
                 `\v:real^M. v`; `\v:real^M. vec 0:real^N`] HAS_DERIVATIVE_PASTECART) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let TEXT_PARTIAL_DERIVATIVE_SLICE = prove
 (`!(f:real^(M,N)finite_sum->real^P) (c:real^N) y i.
      f differentiable (at (pastecart y c)) /\ 1 <= i /\ i <= dimindex(:M)
      ==> (\y. f(pastecart y c)) differentiable (at y) /\
          partial_derivative i (\y. f(pastecart y c)) y =
          partial_derivative i f (pastecart y c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^M. (f:real^(M,N)finite_sum->real^P)(pastecart y c)) =
                f o (\y. pastecart y c)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^M. pastecart y (c:real^N)) differentiable (at y)` ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN MESON_TAC[TEXT_HAS_DERIVATIVE_PASTECART_LEFT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
    W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_CHAIN o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`i:num`; `\y:real^M. pastecart y (c:real^N)`;
                   `\v:real^M. pastecart v (vec 0:real^N)`; `y:real^M`]
      PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
    REWRITE_TAC[TEXT_HAS_DERIVATIVE_PASTECART_LEFT] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[TEXT_PASTECART_BASIS_LOW; partial_derivative]]);;

let TEXT_SLICE_HAS_DERIVATIVE = prove
 (`!(f:real^(M,N)finite_sum->real^P) (c:real^N) y.
      f differentiable (at (pastecart y c))
      ==> ((\y. f(pastecart y c)) has_derivative
           (\v. vsum(1..dimindex(:M)) (\i. v$i % partial_derivative i f (pastecart y c))))
          (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(M,N)finite_sum->real^P`; `c:real^N`; `y:real^M`; `1`]
    TEXT_PARTIAL_DERIVATIVE_SLICE) THEN
  ASM_REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP TEXT_HAS_DERIVATIVE_PARTIALS o CONJUNCT1) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^M` THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`f:real^(M,N)finite_sum->real^P`; `c:real^N`; `y:real^M`; `i:num`]
    TEXT_PARTIAL_DERIVATIVE_SLICE) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The limits along lists and their spatial derivatives.                     *)
(* ------------------------------------------------------------------------- *)

let TEXT_LIMIT_HAS_DERIVATIVE = prove
 (`!(g:real^(M,1)finite_sum->real^N) (G:(num)list->real^M->real^N) a l x.
      smooth_map_on {z | drop(sndcart z) < a} g /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l g z - G l (fstcart z)) < e) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
      ==> (G l has_derivative
           (\v. vsum(1..dimindex(:M)) (\i. v$i % G (CONS i l) x))) (at x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "U") ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!n:num. &0 < inv(&n + &1)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n (y:real^M) l. iterated_partial l (g:real^(M,1)finite_sum->real^N)
                       differentiable (at (pastecart y (lift(a - inv(&n + &1)))))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^(M,1)finite_sum | drop(sndcart z) < a}` THEN
    ASM_SIMP_TAC[TEXT_OPEN_TIME_LT; SMOOTH_MAP_ON_ITERATED_PARTIAL; IN_ELIM_THM;
                 SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a - e < a <=> &0 < e`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(:real^M)`;
    `\n (y:real^M). iterated_partial l (g:real^(M,1)finite_sum->real^N)
                      (pastecart y (lift(a - inv(&n + &1))))`;
    `\n (y:real^M) (v:real^M).
       vsum(1..dimindex(:M))
         (\i. v$i % iterated_partial (CONS i l) (g:real^(M,1)finite_sum->real^N)
                      (pastecart y (lift(a - inv(&n + &1)))))`;
    `\(y:real^M) (v:real^M).
       vsum(1..dimindex(:M)) (\i. v$i % (G:(num)list->real^M->real^N) (CONS i l) y)`]
   HAS_DERIVATIVE_SEQUENCE) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN
      REWRITE_TAC[iterated_partial] THEN
      MATCH_MP_TAC TEXT_SLICE_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < e / &(dimindex(:M))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_SIMP_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`\(i:num) (N:num). !n (y:real^M). N <= n
           ==> norm(iterated_partial (CONS i l) (g:real^(M,1)finite_sum->real^N)
                      (pastecart y (lift(a - inv(&n + &1)))) -
                    (G:(num)list->real^M->real^N) (CONS i l) y)
               < e / &(dimindex(:M))`;
        `dimindex(:M)`] TEXT_FINITE_N_MAX) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MESON_TAC[LE_TRANS];
          X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          MP_TAC(ISPECL
           [`iterated_partial (CONS i l) (g:real^(M,1)finite_sum->real^N)`;
            `(G:(num)list->real^M->real^N) (CONS i l)`; `a:real`] TEXT_UNIFORM_SEQ) THEN
          ANTS_TAC THENL
           [USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL] THEN
            REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ASM_ARITH_TAC;
            DISCH_THEN(MP_TAC o SPEC `e / &(dimindex(:M))`) THEN ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`; `v:real^M`] THEN
      REWRITE_TAC[GE] THEN DISCH_TAC THEN
      SIMP_TAC[FINITE_NUMSEG; GSYM VSUM_SUB; GSYM VECTOR_SUB_LDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(dimindex(:M)) * (e / &(dimindex(:M))) * norm(v:real^M)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TEXT_NORM_VSUM_CMUL_BOUND THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN
        SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; DIMINDEX_NONZERO; REAL_LE_REFL]];
      MAP_EVERY EXISTS_TAC [`vec 0:real^M`; `(G:(num)list->real^M->real^N) l (vec 0)`] THEN
      MP_TAC(ISPECL
       [`iterated_partial l (g:real^(M,1)finite_sum->real^N)`;
        `(G:(num)list->real^M->real^N) l`; `a:real`] TEXT_UNIFORM_LIM) THEN
      ANTS_TAC THENL [USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g0:real^M->real^N`) THEN
  SUBGOAL_THEN `(G:(num)list->real^M->real^N) l = g0` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. iterated_partial l (g:real^(M,1)finite_sum->real^N)
                      (pastecart y (lift(a - inv(&n + &1))))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MP_TAC(ISPECL
     [`iterated_partial l (g:real^(M,1)finite_sum->real^N)`;
      `(G:(num)list->real^M->real^N) l`; `a:real`] TEXT_UNIFORM_LIM) THEN
    ANTS_TAC THENL [USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* The limits are smooth in space; spatial iterated partials of a limit are *)
(* the limits along the extended lists.                                     *)
let SMOOTH_MAP_ON_LIMIT_FAMILY = prove
 (`!(g:real^(M,1)finite_sum->real^N) (G:(num)list->real^M->real^N) a.
      smooth_map_on {z | drop(sndcart z) < a} g /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l g z - G l (fstcart z)) < e)
      ==> !l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
              ==> smooth_map_on (:real^M) (G l) /\
                  !l' x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l'
                         ==> iterated_partial l' (G l) x = G (APPEND l' l) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l0:num list` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
        ==> ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) (APPEND l l0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[ALL_APPEND] THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l /\ x IN (:real^M)
          ==> ((\l. (G:(num)list->real^M->real^N) (APPEND l l0)) l has_derivative
               (\v. vsum(1..dimindex(:M))
                     (\i. v$i % (\l. G (APPEND l l0)) (CONS i l) x))) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
    MATCH_MP_TAC TEXT_LIMIT_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC [`g:real^(M,1)finite_sum->real^N`; `a:real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^M)`; `\l. (G:(num)list->real^M->real^N) (APPEND l l0)`]
    SMOOTH_MAP_ON_PARTIAL_FAMILY_ITERATED) THEN
  MP_TAC(ISPECL [`(:real^M)`; `\l. (G:(num)list->real^M->real^N) (APPEND l l0)`]
    SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `[]:(num)list`) THEN REWRITE_TAC[ALL; APPEND] THEN
  DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`l':num list`; `x:real^M`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`l':num list`; `[]:(num)list`; `x:real^M`]) THEN
  ASM_REWRITE_TAC[ALL; APPEND; APPEND_NIL; IN_UNIV]);;

(* ========================================================================= *)
(* One-dimensional time profiles.  The iterated derivative of                *)
(* order n of a map real^1 -> real^1 is iterated_partial (REPLICATE n 1).   *)
(* Polynomial profiles s^j / j!, cut-off profiles chi(w) w^j / j!, their    *)
(* derivatives at 0, their bounds, and the effect of an affine change of   *)
(* variable u -> b (u - w).                                                  *)
(* ========================================================================= *)

let TEXT_BASIS_1_LIFT = prove
 (`basis 1:real^1 = lift(&1)`,
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; drop] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_1; LE_REFL]);;

let TEXT_ITERATED_PARTIAL_REAL_SEQUENCE = prove
 (`!(phi:num->real->real).
      (!n x. (phi n has_real_derivative phi (SUC n) x) (atreal x))
      ==> !n. iterated_partial (REPLICATE n 1) (lift o phi 0 o drop) =
              lift o phi n o drop`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; iterated_partial] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^1` THEN
  MP_TAC(ISPECL [`1`; `lift o (phi:num->real->real) n o drop`;
                 `\h:real^1. (phi:num->real->real) (SUC n) (drop u) % h`; `u:real^1`]
    PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `drop u`]) THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT; LIFT_DROP];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[o_THM; TEXT_BASIS_1_LIFT; GSYM LIFT_CMUL; REAL_MUL_RID]]);;

let TEXT_SMOOTH_REAL_SEQUENCE_UNIV = prove
 (`!(phi:num->real->real).
      (!n x. (phi n has_real_derivative phi (SUC n) x) (atreal x))
      ==> !n. smooth_map_on (:real^1) (lift o phi n o drop)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real)`; `phi:num->real->real`] SMOOTH_MAP_ON_REAL_SEQUENCE) THEN
  ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV; IMAGE_LIFT_UNIV] THEN SIMP_TAC[]);;

(* The derivative sequence of s^j / j!.                                      *)
let TEXT_POLY_SEQ_DERIVATIVE = prove
 (`!j n x.
      ((\s. if n <= j then s pow (j - n) / &(FACT(j - n)) else &0) has_real_derivative
       (if SUC n <= j then x pow (j - SUC n) / &(FACT(j - SUC n)) else &0)) (atreal x)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `SUC n <= j` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(n:num) <= j` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(j:num) - n = SUC(j - SUC n)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `k:num = j - SUC n` THEN
    MP_TAC(ISPECL [`\s:real. s`; `&1`; `x:real`; `SUC k`] HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(&(FACT(SUC k)))` o MATCH_MP HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FACT; GSYM REAL_OF_NUM_MUL; SUC_SUB1] THEN
    MP_TAC(SPEC `k:num` FACT_NZ) THEN MP_TAC(SPEC `k:num` NOT_SUC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD;
    ASM_CASES_TAC `(n:num) <= j` THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
    SUBGOAL_THEN `(j:num) - n = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_pow; FACT; REAL_DIV_1; HAS_REAL_DERIVATIVE_CONST]]);;

let TEXT_POLY_PROFILE = prove
 (`!j. smooth_map_on (:real^1) (\u. lift(drop u pow j / &(FACT j))) /\
       !n u. iterated_partial (REPLICATE n 1) (\u. lift(drop u pow j / &(FACT j))) u =
             lift(if n <= j then drop u pow (j - n) / &(FACT(j - n)) else &0)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\n s. if n <= j then s pow (j - n) / &(FACT(j - n)) else &0`
    TEXT_ITERATED_PARTIAL_REAL_SEQUENCE) THEN
  MP_TAC(ISPEC `\n s. if n <= j then s pow (j - n) / &(FACT(j - n)) else &0`
    TEXT_SMOOTH_REAL_SEQUENCE_UNIV) THEN
  REWRITE_TAC[TEXT_POLY_SEQ_DERIVATIVE] THEN
  REWRITE_TAC[o_DEF; LE_0; SUB_0; FUN_EQ_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0; SUB_0] THEN
  SIMP_TAC[ETA_AX]);;

let TEXT_POLY_PROFILE_AT_0 = prove
 (`!j n. iterated_partial (REPLICATE n 1) (\u. lift(drop u pow j / &(FACT j))) (vec 0) =
         if n = j then lift(&1) else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TEXT_POLY_PROFILE; DROP_VEC; REAL_POW_ZERO] THEN
  ASM_CASES_TAC `n:num = j` THEN ASM_REWRITE_TAC[LE_REFL; SUB_REFL; FACT; REAL_DIV_1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM] THEN
  SUBGOAL_THEN `~((j:num) - n = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; LIFT_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Bounded maps with compact support.                                         *)
(* ------------------------------------------------------------------------- *)

let TEXT_BOUNDED_COMPACT_SUPPORT = prove
 (`!(f:real^M->real^N) k.
      f continuous_on (:real^M) /\ compact k /\ (!x. ~(x IN k) ==> f x = vec 0)
      ==> ?B. !x. norm(f x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `k:real^M->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN X_GEN_TAC `x:real^M` THEN
  ASM_CASES_TAC `(x:real^M) IN k` THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE]);;

let TEXT_ITERATED_PARTIAL_BOUNDED_COMPACT_SUPPORT = prove
 (`!(f:real^M->real^N) k l.
      smooth_map_on (:real^M) f /\ compact k /\ (!x. ~(x IN k) ==> f x = vec 0)
      ==> ?B. !x. norm(iterated_partial l f x) <= B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_BOUNDED_COMPACT_SUPPORT THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_UNIV];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `(:real^M) DIFF k` THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* Cut-off profiles chi(w) w^j / j!.                                          *)
(* ------------------------------------------------------------------------- *)

let TEXT_CHI_PROFILE = prove
 (`!(chi:real^1->real) j.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0)
      ==> smooth_map_on (:real^1) (\w. chi w % lift(drop w pow j / &(FACT j))) /\
          (!w. &1 <= norm w ==> chi w % lift(drop w pow j / &(FACT j)) = vec 0) /\
          (!n. iterated_partial (REPLICATE n 1)
                 (\w. chi w % lift(drop w pow j / &(FACT j))) (vec 0) =
               if n = j then lift(&1) else vec 0) /\
          (!n. ?C. !w. norm(iterated_partial (REPLICATE n 1)
                              (\w. chi w % lift(drop w pow j / &(FACT j))) w) <= C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^1) (\w. (chi:real^1->real) w % lift(drop w pow j / &(FACT j)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^1)`; `\u:real^1. lift((chi:real^1->real) u)`;
                   `\u:real^1. lift(drop u pow j / &(FACT j))`]
      SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; TEXT_POLY_PROFILE; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. &1 <= norm w ==> (chi:real^1->real) w % lift(drop w pow j / &(FACT j)) = vec 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM TEXT_POLY_PROFILE_AT_0] THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `ball(vec 0:real^1,&1 / &2)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(chi:real^1->real) y = &1` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[VECTOR_MUL_LID]]];
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_BOUNDED_COMPACT_SUPPORT THEN
    EXISTS_TAC `cball(vec 0:real^1,&1)` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Iterated derivatives under the affine change of variable u -> b (u - w).  *)
(* ------------------------------------------------------------------------- *)

let TEXT_HAS_DERIVATIVE_AFFINE_1D = prove
 (`!b (w:real^N) (u:real^N).
      ((\u. b % (u - w)) has_derivative (\h. b % h)) (at u)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\u:real^N. u`; `\h:real^N. h`; `\u:real^N. w:real^N`;
                 `\h:real^N. vec 0:real^N`; `at (u:real^N)`] HAS_DERIVATIVE_SUB) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST] THEN
  DISCH_THEN(MP_TAC o SPEC `b:real` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  REWRITE_TAC[VECTOR_SUB_RZERO]);;

let TEXT_ITERATED_PARTIAL_1D_AFFINE = prove
 (`!(psi:real^1->real^1) c b w.
      smooth_map_on (:real^1) psi
      ==> !n u. iterated_partial (REPLICATE n 1) (\u. c % psi(b % (u - w))) u =
                (c * b pow n) % iterated_partial (REPLICATE n 1) psi (b % (u - w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REPLICATE; iterated_partial; real_pow; REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial (REPLICATE n 1) (\u. c % (psi:real^1->real^1)(b % (u - w))) =
    (\u. (c * b pow n) % iterated_partial (REPLICATE n 1) psi (b % (u - w)))`
  ASSUME_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `u:real^1` THEN ASM_REWRITE_TAC[REPLICATE; iterated_partial] THEN
  ABBREV_TAC `Q = iterated_partial (REPLICATE n 1) (psi:real^1->real^1)` THEN
  SUBGOAL_THEN `!y. (Q:real^1->real^1) differentiable (at y)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Q" THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^1)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\u. (Q:real^1->real^1)(b % (u - w))) has_derivative
     (\h. frechet_derivative Q (at (b % (u - w))) (b % h))) (at u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\u:real^1. b % (u - w)`; `Q:real^1->real^1`;
                   `\h:real^1. b % h`; `frechet_derivative (Q:real^1->real^1) (at (b % (u - w)))`;
                   `u:real^1`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[TEXT_HAS_DERIVATIVE_AFFINE_1D; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c * b pow n` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (Q:real^1->real^1) (at (b % (u - w))))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[partial_derivative; VECTOR_MUL_ASSOC; real_pow] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Borel lemma with parameters.  Given a cutoff chi (smooth              *)
(* on real^1, equal to 1 on the ball of radius 1/2 and to 0 off the open    *)
(* unit ball) and smooth maps F j with support in a fixed compact set,      *)
(* the series of the maps                                                    *)
(*   z -> chi(b_j (t - a)) (t - a)^j / j! F_j(x)                             *)
(* with fast growing scales b_j has a smooth sum whose iterated partials at *)
(* time a are the spatial partials of F_m, m the number of time indices.    *)
(* ========================================================================= *)

let borel_cutoff_profile = new_definition
 `borel_cutoff_profile (chi:real^1->real) j (w:real^1) =
    chi w % lift(drop w pow j / &(FACT j))`;;

let borel_time_profile = new_definition
 `borel_time_profile (chi:real^1->real) j b a (u:real^1) =
    inv(b pow j) % borel_cutoff_profile chi j (b % (u - lift a))`;;

let TEXT_BOREL_CUTOFF_PROFILE = prove
 (`!(chi:real^1->real) j.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0)
      ==> smooth_map_on (:real^1) (borel_cutoff_profile chi j) /\
          (!w. &1 <= norm w ==> borel_cutoff_profile chi j w = vec 0) /\
          (!n. iterated_partial (REPLICATE n 1) (borel_cutoff_profile chi j) (vec 0) =
               if n = j then lift(&1) else vec 0) /\
          (!n. ?C. !w. norm(iterated_partial (REPLICATE n 1)
                              (borel_cutoff_profile chi j) w) <= C)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `borel_cutoff_profile (chi:real^1->real) j =
                (\w. chi w % lift(drop w pow j / &(FACT j)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; borel_cutoff_profile]; ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC TEXT_CHI_PROFILE THEN ASM_REWRITE_TAC[]);;

let TEXT_SMOOTH_AFFINE_1D = prove
 (`!b (w:real^N). smooth_map_on (:real^N) (\u. b % (u - w))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `b:real`; `\u:real^N. u - w`] SMOOTH_MAP_ON_CMUL_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\u:real^N. u`; `\u:real^N. w:real^N`]
    SMOOTH_MAP_ON_SUB_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let TEXT_BOREL_TIME_PROFILE = prove
 (`!(chi:real^1->real) j b a.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0) /\
      &0 < b
      ==> smooth_map_on (:real^1) (borel_time_profile chi j b a) /\
          (!n u. iterated_partial (REPLICATE n 1) (borel_time_profile chi j b a) u =
                 (inv(b pow j) * b pow n) %
                 iterated_partial (REPLICATE n 1) (borel_cutoff_profile chi j)
                   (b % (u - lift a))) /\
          (!n. iterated_partial (REPLICATE n 1) (borel_time_profile chi j b a) (lift a) =
               if n = j then lift(&1) else vec 0) /\
          (!u. &1 <= b * abs(drop u - a) ==> borel_time_profile chi j b a u = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`chi:real^1->real`; `j:num`] TEXT_BOREL_CUTOFF_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "S0") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!n u. iterated_partial (REPLICATE n 1) (borel_time_profile (chi:real^1->real) j b a) u =
          (inv(b pow j) * b pow n) %
          iterated_partial (REPLICATE n 1) (borel_cutoff_profile chi j) (b % (u - lift a))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `borel_time_profile (chi:real^1->real) j b a =
      (\u. inv(b pow j) % borel_cutoff_profile chi j (b % (u - lift a)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; borel_time_profile]; ALL_TAC] THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_1D_AFFINE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `borel_time_profile (chi:real^1->real) j b a =
      (\u. inv(b pow j) % (borel_cutoff_profile chi j o (\u. b % (u - lift a))) u)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; borel_time_profile; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^1)`; `inv(b pow j)`;
                   `borel_cutoff_profile (chi:real^1->real) j o (\u. b % (u - lift a))`]
      SMOOTH_MAP_ON_CMUL_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; TEXT_SMOOTH_AFFINE_1D];
    X_GEN_TAC `n:num` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_POW_NZ; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN REWRITE_TAC[borel_time_profile] THEN
    SUBGOAL_THEN `borel_cutoff_profile (chi:real^1->real) j (b % (u - lift a)) = vec 0`
      (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
    USE_THEN "S0" MATCH_MP_TAC THEN
    REWRITE_TAC[NORM_MUL; NORM_1; DROP_SUB; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b = b`]]);;

let TEXT_POW_RATIO_LE = prove
 (`!b m j. &1 <= b /\ m < j ==> inv(b pow j) * b pow m <= inv b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b pow j = b pow (j - m) * b pow m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b pow m /\ &0 < b pow (j - m)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INV_MUL; GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
               REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_ARITH_TAC);;

let TEXT_BOREL_SCALE = prove
 (`!(Q:(num)list->real) j.
      ?b. &1 <= b /\
          !l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l /\ LENGTH l < j
              ==> inv b * Q l <= inv(&2) pow j`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`Q:(num)list->real`;
                 `{l:(num)list | LENGTH l <= j /\
                                 ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l}`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[TEXT_FINITE_LISTS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real`) THEN
  EXISTS_TAC `&2 pow j * (abs q + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE_1; REAL_ARITH `&1 <= &2`] THEN REAL_ARITH_TAC;
    X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL; GSYM REAL_POW_INV; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < abs q + &1`] THEN
    ASM_REAL_ARITH_TAC]);;

(* The bound on an iterated partial of one Borel term.                       *)
let TEXT_BOREL_TERM_BOUND = prove
 (`!(chi:real^1->real) (E:real^M->real^N) j b a l Cc Dd.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0) /\
      &0 < b /\ smooth_map_on (:real^M) E /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l /\
      (!w. norm(iterated_partial (REPLICATE (LENGTH(FILTER (\i. i = dimindex(:M) + 1) l)) 1)
                  (borel_cutoff_profile chi j) w) <= Cc) /\
      (!x. norm(iterated_partial (FILTER (\i. ~(i = dimindex(:M) + 1)) l) E x) <= Dd)
      ==> !z. norm(iterated_partial l
                    (\z. drop(borel_time_profile chi j b a (sndcart z)) % E(fstcart z)) z)
              <= (inv(b pow j) * b pow (LENGTH(FILTER (\i. i = dimindex(:M) + 1) l))) *
                 Cc * Dd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^(M,1)finite_sum` THEN
  MP_TAC(SPECL [`chi:real^1->real`; `j:num`; `b:real`; `a:real`] TEXT_BOREL_TIME_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`borel_time_profile (chi:real^1->real) j b a`; `E:real^M->real^N`]
    TEXT_ITERATED_PARTIAL_TENSOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `m = LENGTH(FILTER (\i. i = dimindex(:M) + 1) (l:num list))` THEN
  ABBREV_TAC `al = FILTER (\i. ~(i = dimindex(:M) + 1)) (l:num list)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(b pow j) * b pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; DROP_CMUL; REAL_ABS_MUL; GSYM NORM_1; REAL_ABS_INV; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b = b`] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

(* The value of an iterated partial of a Borel term at time a.               *)
let TEXT_BOREL_TERM_AT_BASE = prove
 (`!(chi:real^1->real) (E:real^M->real^N) j b a l x.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0) /\
      &0 < b /\ smooth_map_on (:real^M) E /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
      ==> iterated_partial l
            (\z. drop(borel_time_profile chi j b a (sndcart z)) % E(fstcart z))
            (pastecart x (lift a)) =
          if LENGTH(FILTER (\i. i = dimindex(:M) + 1) l) = j
          then iterated_partial (FILTER (\i. ~(i = dimindex(:M) + 1)) l) E x
          else vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`borel_time_profile (chi:real^1->real) j b a`; `E:real^M->real^N`]
    TEXT_ITERATED_PARTIAL_TENSOR) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[TEXT_BOREL_TIME_PROFILE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SNDCART_PASTECART; FSTCART_PASTECART] THEN
  MP_TAC(SPECL [`chi:real^1->real`; `j:num`; `b:real`; `a:real`] TEXT_BOREL_TIME_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th))]) THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; LIFT_DROP; VECTOR_MUL_LID]);;

(* The supports of a Borel term.                                              *)
let TEXT_BOREL_TERM_SUPPORT = prove
 (`!(chi:real^1->real) (E:real^M->real^N) k j b a z.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0) /\
      &1 <= b /\ (!x. ~(x IN k) ==> E x = vec 0) /\
      (a + &1 <= drop(sndcart z) \/ ~(fstcart z IN k))
      ==> drop(borel_time_profile chi j b a (sndcart z)) % E(fstcart z) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`chi:real^1->real`; `j:num`; `b:real`; `a:real`] TEXT_BOREL_TIME_PROFILE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `borel_time_profile (chi:real^1->real) j b a (sndcart(z:real^(M,1)finite_sum)) = vec 0`
      (fun th -> REWRITE_TAC[th; DROP_VEC; VECTOR_MUL_LZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= b * x ==> &1 <= b * x`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[VECTOR_MUL_RZERO]]);;

(* ========================================================================= *)
(* Assembly of the Borel lemma with parameters.                              *)
(* ========================================================================= *)

let TEXT_BOREL_SERIES_BOUND = prove
 (`!(chi:real^1->real) (FF:num->real^M->real^N) (C:num->num->real)
    (D:num->(num)list->real) (b:num->real) a l n z.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0) /\
      (!j. smooth_map_on (:real^M) (FF j)) /\
      (!j m w. norm(iterated_partial (REPLICATE m 1) (borel_cutoff_profile chi j) w)
               <= C j m) /\
      (!j l x. norm(iterated_partial l (FF j) x) <= D j l) /\
      (!j. &1 <= b j /\
           !l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l /\ LENGTH l < j
               ==> inv(b j) * (abs(C j (LENGTH(FILTER (\i. i = dimindex(:M) + 1) l))) *
                               abs(D j (FILTER (\i. ~(i = dimindex(:M) + 1)) l)))
                   <= inv(&2) pow j) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l /\ LENGTH l < n
      ==> norm(iterated_partial l
                (\z. drop(borel_time_profile chi n (b n) a (sndcart z)) % FF n (fstcart z)) z)
          <= inv(&2) pow n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "C") (CONJUNCTS_THEN2 (LABEL_TAC "D")
   (CONJUNCTS_THEN2 (LABEL_TAC "B") STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `m = LENGTH(FILTER (\i. i = dimindex(:M) + 1) (l:num list))` THEN
  ABBREV_TAC `al = FILTER (\i. ~(i = dimindex(:M) + 1)) (l:num list)` THEN
  SUBGOAL_THEN `m < n:num` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\i. i = dimindex(:M) + 1`; `l:num list`] LENGTH_FILTER) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "B" (MP_TAC o SPEC `n:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `l:num list`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(inv((b:num->real) n pow n) * b n pow m) *
              abs((C:num->num->real) n m) * abs((D:num->(num)list->real) n al)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`chi:real^1->real`; `(FF:num->real^M->real^N) n`; `n:num`;
                   `(b:num->real) n`; `a:real`; `l:num list`;
                   `abs((C:num->num->real) n m)`; `abs((D:num->(num)list->real) n al)`]
      TEXT_BOREL_TERM_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(C:num->num->real) n m` THEN
        USE_THEN "C" (fun th -> REWRITE_TAC[th; REAL_ABS_LE]);
        GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(D:num->(num)list->real) n al` THEN
        USE_THEN "D" (fun th -> REWRITE_TAC[th; REAL_ABS_LE])];
      SIMP_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv((b:num->real) n) *
                abs((C:num->num->real) n m) * abs((D:num->(num)list->real) n al)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS] THEN
    MATCH_MP_TAC TEXT_POW_RATIO_LE THEN ASM_REWRITE_TAC[]]);;

(* Borel's lemma with parameters: prescribed time derivatives at t = a.     *)
let BOREL_EXTENSION_PARAMETRIC = prove
 (`!(chi:real^1->real) (FF:num->real^M->real^N) k a.
      smooth_map_on (:real^1) (\u. lift(chi u)) /\
      (!u. norm u <= &1 / &2 ==> chi u = &1) /\
      (!u. &1 <= norm u ==> chi u = &0) /\
      compact k /\
      (!j. smooth_map_on (:real^M) (FF j)) /\
      (!j x. ~(x IN k) ==> FF j x = vec 0)
      ==> ?B:real^(M,1)finite_sum->real^N.
            smooth_map_on (:real^(M,1)finite_sum) B /\
            (!z. a + &1 <= drop(sndcart z) ==> B z = vec 0) /\
            (!z. ~(fstcart z IN k) ==> B z = vec 0) /\
            (!l x. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
                   ==> iterated_partial l B (pastecart x (lift a)) =
                       iterated_partial (FILTER (\i. ~(i = dimindex(:M) + 1)) l)
                         (FF (LENGTH (FILTER (\i. i = dimindex(:M) + 1) l))) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?C. !j m w. norm(iterated_partial (REPLICATE m 1)
                     (borel_cutoff_profile (chi:real^1->real) j) w) <= C j m`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MAP_EVERY X_GEN_TAC [`j:num`; `m:num`] THEN
    MP_TAC(SPECL [`chi:real^1->real`; `j:num`] TEXT_BOREL_CUTOFF_PROFILE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?D. !j l x. norm(iterated_partial l ((FF:num->real^M->real^N) j) x) <= D j l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MAP_EVERY X_GEN_TAC [`j:num`; `l:num list`] THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_BOUNDED_COMPACT_SUPPORT THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b. !j. &1 <= b j /\
            !l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l /\ LENGTH l < j
                ==> inv(b j) *
                    (abs((C:num->num->real) j (LENGTH(FILTER (\i. i = dimindex(:M) + 1) l))) *
                     abs((D:num->(num)list->real) j (FILTER (\i. ~(i = dimindex(:M) + 1)) l)))
                    <= inv(&2) pow j`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL
     [`\l:(num)list.
         abs((C:num->num->real) j (LENGTH(FILTER (\i. i = dimindex(:M) + 1) l))) *
         abs((D:num->(num)list->real) j (FILTER (\i. ~(i = dimindex(:M) + 1)) l))`;
      `j:num`] TEXT_BOREL_SCALE) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 < (b:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(:real^(M,1)finite_sum)`;
    `\j (z:real^(M,1)finite_sum).
       drop(borel_time_profile (chi:real^1->real) j ((b:num->real) j) a (sndcart z)) %
       (FF:num->real^M->real^N) j (fstcart z)`]
   SMOOTH_MAP_ON_SERIES) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_TENSOR THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`chi:real^1->real`; `j:num`; `(b:num->real) j`; `a:real`]
        TEXT_BOREL_TIME_PROFILE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      EXISTS_TAC `\n:num. inv(&2) pow n` THEN EXISTS_TAC `SUC(LENGTH(l:num list))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[] THEN MATCH_MP_TAC SUMMABLE_REAL_GP THEN
        CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(M,1)finite_sum`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`chi:real^1->real`; `FF:num->real^M->real^N`; `C:num->num->real`;
                     `D:num->(num)list->real`; `b:num->real`; `a:real`; `l:num list`;
                     `n:num`; `z:real^(M,1)finite_sum`] TEXT_BOREL_SERIES_BOUND) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN
  EXISTS_TAC
   `\z:real^(M,1)finite_sum.
      infsum (from 0)
        (\n. drop(borel_time_profile (chi:real^1->real) n ((b:num->real) n) a (sndcart z)) %
             (FF:num->real^M->real^N) n (fstcart z))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^(M,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INFSUM_UNIQUE THEN MATCH_MP_TAC SUMS_0 THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TEXT_BOREL_TERM_SUPPORT THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^(M,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INFSUM_UNIQUE THEN MATCH_MP_TAC SUMS_0 THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC TEXT_BOREL_TERM_SUPPORT THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`l:num list`; `x:real^M`] THEN DISCH_TAC THEN
    USE_THEN "S" (MP_TAC o SPECL [`l:num list`; `pastecart (x:real^M) (lift a)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. iterated_partial l
            (\z. drop(borel_time_profile (chi:real^1->real) n ((b:num->real) n) a
                        (sndcart z)) %
                 (FF:num->real^M->real^N) n (fstcart z))
            (pastecart x (lift a)) =
          if LENGTH(FILTER (\i. i = dimindex(:M) + 1) l) = n
          then iterated_partial (FILTER (\i. ~(i = dimindex(:M) + 1)) l) (FF n) x
          else vec 0`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC TEXT_BOREL_TERM_AT_BASE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `m = LENGTH(FILTER (\i. i = dimindex(:M) + 1) (l:num list))` THEN
    ABBREV_TAC `al = FILTER (\i. ~(i = dimindex(:M) + 1)) (l:num list)` THEN
    DISCH_TAC THEN MATCH_MP_TAC SERIES_UNIQUE THEN
    EXISTS_TAC `\n. if m = n then iterated_partial al ((FF:num->real^M->real^N) n) x
                    else vec 0` THEN
    EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\n. if m = n then iterated_partial al ((FF:num->real^M->real^N) n) x
                        else vec 0`; `{m:num}`; `from 0`] SERIES_FINITE_SUPPORT) THEN
    SUBGOAL_THEN `{m:num} INTER from 0 = {m}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_FROM; LE_0] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FINITE_SING; IN_SING; VSUM_SING] THEN
    MESON_TAC[]]);;

(* ========================================================================= *)
(* The smooth extension past the hyperplane t = a, and the                   *)
(* theorem NS_SMOOTH_EXTENSION_PAST_ONE (a = 1, space real^3).              *)
(* ========================================================================= *)

let TEXT_OPEN_SPACE_NOTIN = prove
 (`!k:real^M->bool. closed k ==> open {z:real^(M,N)finite_sum | ~(fstcart z IN k)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`; `(:real^M) DIFF k`]
    CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MESON_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
    ASM_REWRITE_TAC[GSYM closed]]);;

let TEXT_SMOOTH_MAP_ON_EQ_OPEN = prove
 (`!s (f:real^M->real^N) g.
      open s /\ smooth_map_on s f /\ (!x. x IN s ==> f x = g x)
      ==> smooth_map_on s g`,
  REWRITE_TAC[smooth_map_on] THEN MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN]);;

let TEXT_ITERATED_PARTIAL_SUB_OPEN = prove
 (`!l s (f:real^M->real^N) g.
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> !x. x IN s
              ==> iterated_partial l (\x. f x - g x) x =
                  iterated_partial l f x - iterated_partial l g x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\x. iterated_partial t (f:real^M->real^N) x - iterated_partial t g x) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

let TEXT_ALL_REPLICATE = prove
 (`!P n (x:A). P x ==> ALL P (REPLICATE n x)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[REPLICATE; ALL]);;

(* Uniform continuity in time, uniformly in space, of a continuous map      *)
(* vanishing outside a compact cylinder.                                     *)
let TEXT_TIME_UNIFORM_CONTINUITY = prove
 (`!(u:real^(M,1)finite_sum->real^N) k a.
      u continuous_on (:real^(M,1)finite_sum) /\ compact k /\
      (!z. ~(fstcart z IN k) ==> u z = vec 0)
      ==> !e. &0 < e
              ==> ?d. &0 < d /\
                      !z. abs(drop(sndcart z) - a) < d
                          ==> norm(u z - u(pastecart (fstcart z) (lift a))) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^(M,1)finite_sum->real^N`;
                 `(k:real^M->bool) PCROSS interval[lift(a - &1),lift(a + &1)]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^1`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^M) IN k` THENL
   [ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; dist; PASTECART_SUB;
                VECTOR_SUB_REFL; NORM_PASTECART_0; NORM_1; DROP_SUB] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(u:real^(M,1)finite_sum->real^N) (pastecart x y) = vec 0 /\
                  u(pastecart x (lift a)) = vec 0`
      (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL; NORM_0] THEN ASM_REWRITE_TAC[]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART]]);;

(* The limit along a list equals the limit along its canonical reordering. *)
let TEXT_LIMIT_CANON = prove
 (`!(g:real^(M,1)finite_sum->real^N) (G:(num)list->real^M->real^N) a l.
      smooth_map_on {z | drop(sndcart z) < a} g /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l g z - G l (fstcart z)) < e) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
      ==> G l = G (APPEND (FILTER (\i. ~(i = dimindex(:M) + 1)) l)
                          (FILTER (\i. i = dimindex(:M) + 1) l))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "U") ASSUME_TAC)) THEN
  ABBREV_TAC `l' = APPEND (FILTER (\i. ~(i = dimindex(:M) + 1)) l)
                          (FILTER (\i. i = dimindex(:M) + 1) (l:num list))` THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) (l':num list)`
  ASSUME_TAC THENL
   [EXPAND_TAC "l'" THEN REWRITE_TAC[ALL_APPEND] THEN
    CONJ_TAC THEN MATCH_MP_TAC TEXT_ALL_FILTER_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. drop(sndcart z) < a
        ==> iterated_partial l (g:real^(M,1)finite_sum->real^N) z = iterated_partial l' g z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "l'" THEN
    MP_TAC(ISPECL [`{z:real^(M,1)finite_sum | drop(sndcart z) < a}`;
                   `g:real^(M,1)finite_sum->real^N`; `dimindex(:M) + 1`]
      TEXT_ITERATED_PARTIAL_CANON) THEN
    REWRITE_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^(M,1)finite_sum`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC TEXT_LIMIT_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`iterated_partial l (g:real^(M,1)finite_sum->real^N)`; `a:real`] THEN
  CONJ_TAC THENL
   [USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "U" (MP_TAC o SPEC `l':num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The iterated partials of the Borel extension at time a agree with the    *)
(* limits of the iterated partials of g.                                     *)
let TEXT_EXTENSION_COMPAT = prove
 (`!(g:real^(M,1)finite_sum->real^N) (G:(num)list->real^M->real^N)
    (B:real^(M,1)finite_sum->real^N) a l x.
      smooth_map_on {z | drop(sndcart z) < a} g /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l g z - G l (fstcart z)) < e) /\
      (!l x. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
             ==> iterated_partial l B (pastecart x (lift a)) =
                 iterated_partial (FILTER (\i. ~(i = dimindex(:M) + 1)) l)
                   (G (REPLICATE (LENGTH (FILTER (\i. i = dimindex(:M) + 1) l))
                                 (dimindex(:M) + 1))) x) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
      ==> iterated_partial l B (pastecart x (lift a)) = G l x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "B") ASSUME_TAC))) THEN
  USE_THEN "B" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) (l:num list)`)]) THEN
  ABBREV_TAC `m = LENGTH(FILTER (\i. i = dimindex(:M) + 1) (l:num list))` THEN
  MP_TAC(ISPECL [`g:real^(M,1)finite_sum->real^N`; `G:(num)list->real^M->real^N`; `a:real`]
    SMOOTH_MAP_ON_LIMIT_FAMILY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `REPLICATE m (dimindex(:M) + 1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC TEXT_ALL_REPLICATE THEN REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`FILTER (\i. ~(i = dimindex(:M) + 1)) (l:num list)`; `x:real^M`] o
             CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALL_FILTER] THEN
    UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) (l:num list)` THEN
    REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "m" THEN REWRITE_TAC[GSYM TEXT_FILTER_EQ_REPLICATE] THEN
  CONV_TAC SYM_CONV THEN AP_THM_TAC THEN MATCH_MP_TAC TEXT_LIMIT_CANON THEN
  MAP_EVERY EXISTS_TAC [`g:real^(M,1)finite_sum->real^N`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Flatness of g - B at the hyperplane, the generic smooth                   *)
(* extension past t = a, and the theorem NS_SMOOTH_EXTENSION_PAST_ONE.      *)
(* ========================================================================= *)

let TEXT_EXTENSION_FLAT = prove
 (`!(g:real^(M,1)finite_sum->real^N) (G:(num)list->real^M->real^N)
    (B:real^(M,1)finite_sum->real^N) k a l.
      compact k /\ smooth_map_on {z | drop(sndcart z) < a} g /\
      smooth_map_on (:real^(M,1)finite_sum) B /\ (!z. ~(fstcart z IN k) ==> B z = vec 0) /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                               ==> norm(iterated_partial l g z - G l (fstcart z)) < e) /\
      (!l x. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
             ==> iterated_partial l B (pastecart x (lift a)) = G l x) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
      ==> !e. &0 < e
              ==> ?d. &0 < d /\
                      !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                          ==> norm(iterated_partial l
                                    (\z. if drop(sndcart z) < a then g z - B z else vec 0) z)
                              < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "U") (CONJUNCTS_THEN2 (LABEL_TAC "C") ASSUME_TAC)))))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "U" (MP_TAC o SPEC `l:num list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  MP_TAC(ISPECL [`iterated_partial l (B:real^(M,1)finite_sum->real^N)`; `k:real^M->bool`;
                 `a:real`] TEXT_TIME_UNIFORM_CONTINUITY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_UNIV];
      X_GEN_TAC `z:real^(M,1)finite_sum` THEN DISCH_TAC THEN
      MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
      EXISTS_TAC `{z:real^(M,1)finite_sum | ~(fstcart z IN k)}` THEN
      ASM_SIMP_TAC[TEXT_OPEN_SPACE_NOTIN; COMPACT_IMP_CLOSED; IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^(M,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `iterated_partial l
      (\z. if drop(sndcart z) < a then (g:real^(M,1)finite_sum->real^N) z - B z else vec 0) z =
    iterated_partial l g z - iterated_partial l B z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `iterated_partial l (\z. (g:real^(M,1)finite_sum->real^N) z - B z) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
      EXISTS_TAC `{z:real^(M,1)finite_sum | drop(sndcart z) < a}` THEN
      ASM_SIMP_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM];
      MP_TAC(ISPECL [`l:num list`; `{z:real^(M,1)finite_sum | drop(sndcart z) < a}`;
                     `g:real^(M,1)finite_sum->real^N`; `B:real^(M,1)finite_sum->real^N`]
        TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[TEXT_OPEN_TIME_LT] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `(:real^(M,1)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^(M,1)finite_sum`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  USE_THEN "D1" (MP_TAC o SPEC `z:real^(M,1)finite_sum`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "D2" (MP_TAC o SPEC `z:real^(M,1)finite_sum`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "C" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) (l:num list)`)]) THEN
  CONV_TAC NORM_ARITH);;

(* The smooth extension of a map defined below the hyperplane t = a.        *)
let SMOOTH_EXTENSION_PAST_HYPERPLANE = prove
 (`!(g:real^(M,1)finite_sum->real^N) (k:real^M->bool) a.
      compact k /\
      smooth_map_on {z | drop(sndcart z) < a} g /\
      (!z. drop(sndcart z) < a /\ ~(fstcart z IN k) ==> g z = vec 0) /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
           ==> ?G:real^M->real^N.
                 !e. &0 < e
                     ==> ?d. &0 < d /\
                             !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                                 ==> norm(iterated_partial l g z - G(fstcart z)) < e)
      ==> ?g'. smooth_map_on (:real^(M,1)finite_sum) g' /\
               (!z. drop(sndcart z) < a ==> g' z = g z) /\
               (!z. a + &1 <= drop(sndcart z) ==> g' z = vec 0) /\
               (!z. ~(fstcart z IN k) ==> g' z = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `G:(num)list->real^M->real^N` (LABEL_TAC "U") o
    GEN_REWRITE_RULE I [SKOLEM_THM] o
    GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l /\ ~(x IN k)
          ==> (G:(num)list->real^M->real^N) l x = vec 0`
  (LABEL_TAC "Z") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_LIMIT_VANISH THEN
    MAP_EVERY EXISTS_TAC [`iterated_partial l (g:real^(M,1)finite_sum->real^N)`; `a:real`] THEN
    CONJ_TAC THENL
     [USE_THEN "U" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
      EXISTS_TAC `{z:real^(M,1)finite_sum | drop(sndcart z) < a} INTER
                  {z:real^(M,1)finite_sum | ~(fstcart z IN k)}` THEN
      ASM_SIMP_TAC[OPEN_INTER; TEXT_OPEN_TIME_LT; TEXT_OPEN_SPACE_NOTIN; COMPACT_IMP_CLOSED;
                   IN_INTER; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(M,1)finite_sum->real^N`; `G:(num)list->real^M->real^N`; `a:real`]
    SMOOTH_MAP_ON_LIMIT_FAMILY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "LF")] THEN
  SUBGOAL_THEN
   `!j. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) (REPLICATE j (dimindex(:M) + 1))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC TEXT_ALL_REPLICATE THEN
    REWRITE_TAC[TEXT_DIMINDEX_SPACETIME] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`smooth_bump (&1 / &2) (&1):real^1->real`;
                 `\j. (G:(num)list->real^M->real^N) (REPLICATE j (dimindex(:M) + 1))`;
                 `k:real^M->bool`; `a:real`] BOREL_EXTENSION_PARAMETRIC) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN
      USE_THEN "LF" (MP_TAC o SPEC `REPLICATE j (dimindex(:M) + 1)`) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "Z" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real^(M,1)finite_sum->real^N`
    (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN
   `!l x. ALL (\i. 1 <= i /\ i <= dimindex(:(M,1)finite_sum)) l
          ==> iterated_partial l (B:real^(M,1)finite_sum->real^N) (pastecart x (lift a)) =
              (G:(num)list->real^M->real^N) l x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_EXTENSION_COMPAT THEN
    EXISTS_TAC `g:real^(M,1)finite_sum->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\z. (if drop(sndcart z) < a then (g:real^(M,1)finite_sum->real^N) z - B z
                   else vec 0) + B z` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^(M,1)finite_sum)`;
                   `\z. if drop(sndcart z) < a then (g:real^(M,1)finite_sum->real^N) z - B z
                        else vec 0`;
                   `B:real^(M,1)finite_sum->real^N`] SMOOTH_MAP_ON_ADD_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_GLUE_FLAT THEN EXISTS_TAC `a:real` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `\z. (g:real^(M,1)finite_sum->real^N) z - B z` THEN
      REWRITE_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM] THEN SIMP_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[TEXT_OPEN_TIME_LT] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^(M,1)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      SIMP_TAC[REAL_ARITH `a <= t ==> ~(t < a)`];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      MATCH_MP_TAC TEXT_EXTENSION_FLAT THEN
      MAP_EVERY EXISTS_TAC [`G:(num)list->real^M->real^N`; `k:real^M->bool`] THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^(M,1)finite_sum` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[VECTOR_SUB_ADD];
    X_GEN_TAC `z:real^(M,1)finite_sum` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `a + &1 <= t ==> ~(t < a)`; VECTOR_ADD_LID];
    X_GEN_TAC `z:real^(M,1)finite_sum` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[VECTOR_SUB_ADD; VECTOR_ADD_LID]]);;

(* ------------------------------------------------------------------------- *)
(* NS_SMOOTH_EXTENSION_PAST_ONE: space real^3, terminal time 1, support in   *)
(* time up to 2.                                                             *)
(* ------------------------------------------------------------------------- *)

let NS_SMOOTH_EXTENSION_PAST_ONE = prove
 (`!(g:real^(3,1)finite_sum->real^N) (K:real^3->bool).
     compact K /\
     smooth_map_on {z | drop(sndcart z) < &1} g /\
     (!z. drop(sndcart z) < &1 /\ ~(fstcart z IN K) ==> g z = vec 0) /\
     (!l. ALL (\i. 1 <= i /\ i <= 4) l
          ==> ?G:real^3->real^N.
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            !z. &1 - d < drop(sndcart z) /\ drop(sndcart z) < &1
                                ==> norm(iterated_partial l g z - G(fstcart z)) < e)
     ==> ?g'. smooth_map_on (:real^(3,1)finite_sum) g' /\
              (!z. drop(sndcart z) < &1 ==> g' z = g z) /\
              (!z. &2 <= drop(sndcart z) ==> g' z = vec 0) /\
              (!z. ~(fstcart z IN K) ==> g' z = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(3,1)finite_sum->real^N`; `K:real^3->bool`; `&1`]
    SMOOTH_EXTENSION_PAST_HYPERPLANE) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_3; DIMINDEX_1; ARITH] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 + &1 = &2`]);;


(* ========================================================================= *)
(* Smooth extension below an initial time of a map U on real^(1,N)finite_sum *)
(* (time first) with compact support in space whose partial derivatives all  *)
(* extend continuously to the initial time: PDE_SEELEY_CORE (the extension   *)
(* keeps the spatial support).  Transfer to the convention of the            *)
(* ns_time_ext.ml part (time last) by the reflection-swap z |-> pastecart    *)
(* (lift(2a - s)) y of z = pastecart y (lift s).                             *)
(* ========================================================================= *)

(* The reflection-swap and its derivative. *)

let PDE_REFLECT_HAS_DERIVATIVE = prove
 (`!a (z:real^(N,1)finite_sum).
     ((\z:real^(N,1)finite_sum. pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))
      has_derivative (\h. pastecart (lift(--drop(sndcart h))) (fstcart h))) (at z)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB; LIFT_NEG; LIFT_DROP] THEN
    SUBGOAL_THEN `(\h:real^(N,1)finite_sum. --sndcart h:real^1) = (\h. vec 0 - sndcart h)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_LZERO]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_FSTCART]]);;

let PDE_BASIS1_REAL1 = prove
 (`basis 1:real^1 = lift(&1)`,
  SIMP_TAC[CART_EQ; DIMINDEX_1; FORALL_1; LIFT_COMPONENT; BASIS_COMPONENT; LE_REFL]);;

let PDE_REFLECT_PARTIAL_BASIS = prove
 (`!a (z:real^(N,1)finite_sum) i.
     1 <= i /\ i <= dimindex(:N) + 1
     ==> partial_derivative i
           (\z:real^(N,1)finite_sum. pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z)) z =
         (if i = dimindex(:N) + 1 then --(&1) else &1) %
         (basis (if i = dimindex(:N) + 1 then 1 else i + 1):real^(1,N)finite_sum)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MP_TAC(SPECL [`a:real`; `z:real^(N,1)finite_sum`] PDE_REFLECT_HAS_DERIVATIVE) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PASTECART_EQ] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_CMUL; SNDCART_CMUL] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPEC `1` (INST_TYPE [`:N`,`:M`; `:1`,`:N`] TEXT_BASIS_HIGH)) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `1` (INST_TYPE [`:1`,`:M`; `:N`,`:N`] TEXT_BASIS_LOW)) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; PDE_BASIS1_REAL1; GSYM LIFT_CMUL] THEN
    REWRITE_TAC[LIFT_DROP; LIFT_EQ] THEN REAL_ARITH_TAC;
    MP_TAC(ISPEC `i:num` (INST_TYPE [`:N`,`:M`; `:1`,`:N`] TEXT_BASIS_LOW)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `i:num` (INST_TYPE [`:1`,`:M`; `:N`,`:N`] TEXT_BASIS_HIGH)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 + i = i + 1`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; DROP_VEC; REAL_NEG_0; GSYM LIFT_NUM; LIFT_DROP]]);;

(* Iterated partials of f o A for a map A whose partial derivatives are     *)
(* signed basis vectors.                                                      *)

let PDE_ITERATED_PARTIAL_COMPOSE = prove
 (`!(f:real^Q->real^K) (A:real^P->real^Q) s sg pp l.
        open s /\ smooth_map_on s f /\
        (!z. A differentiable (at z)) /\
        (!z i. 1 <= i /\ i <= dimindex(:P)
               ==> partial_derivative i A z = sg i % basis (pp i)) /\
        ALL (\i. 1 <= i /\ i <= dimindex(:P)) l
        ==> !z. A z IN s
                ==> iterated_partial l (\z. f(A z)) z =
                    ITLIST (\i r. sg i * r) l (&1) % iterated_partial (MAP pp l) f (A z)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[iterated_partial; MAP; ITLIST; VECTOR_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  REWRITE_TAC[ALL] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `z:real^P` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {w | (A:real^P->real^Q) w IN s}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (iterated_partial (MAP (pp:num->num) (t:num list)) (f:real^Q->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `iterated_partial (MAP (pp:num->num) (t:num list)) (f:real^Q->real^K) differentiable
                (at ((A:real^P->real^Q) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^Q->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[iterated_partial; MAP; ITLIST] THEN
  TRANS_TAC EQ_TRANS
   `partial_derivative h
      (\w. ITLIST (\i r. (sg:num->real) i * r) (t:num list) (&1) %
           iterated_partial (MAP (pp:num->num) (t:num list)) (f:real^Q->real^K) ((A:real^P->real^Q) w)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `{w | (A:real^P->real^Q) w IN s}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w. iterated_partial (MAP (pp:num->num) (t:num list)) (f:real^Q->real^K) ((A:real^P->real^Q) w))
                differentiable (at z)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CMUL] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[PARTIAL_DERIVATIVE_CHAIN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE o
    check (fun th -> can (find_term ((=) `(A:real^P->real^Q) z`)) (concl th) &&
                     is_comb (concl th) &&
                     fst(dest_const(rator(rator(concl th)))) = "differentiable")) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[GSYM partial_derivative; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let PDE_REFLECT_PARTIAL = prove
 (`!(f:real^(1,N)finite_sum->real^K) s a l.
        open s /\ smooth_map_on s f /\
        ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
        ==> !z. pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z) IN s
                ==> iterated_partial l
                      (\z:real^(N,1)finite_sum.
                          f(pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))) z =
                    ITLIST (\i r. (if i = dimindex(:N) + 1 then --(&1) else &1) * r) l (&1) %
                    iterated_partial (MAP (\i. if i = dimindex(:N) + 1 then 1 else i + 1) l) f
                      (pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^K`;
    `\z:real^(N,1)finite_sum.
       pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z):real^(1,N)finite_sum`;
    `s:real^(1,N)finite_sum->bool`;
    `\i. if i = dimindex(:N) + 1 then --(&1) else &1`;
    `\i. if i = dimindex(:N) + 1 then 1 else i + 1`; `l:num list`]
   PDE_ITERATED_PARTIAL_COMPOSE) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^(N,1)finite_sum.
                    pastecart (lift(--drop(sndcart h))) (fstcart h):real^(1,N)finite_sum` THEN
      REWRITE_TAC[PDE_REFLECT_HAS_DERIVATIVE];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_REFLECT_PARTIAL_BASIS THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

(* The reflection-swap and its inverse are smooth.                           *)

let PDE_REFLECT_SMOOTH = prove
 (`!a. smooth_map_on (:real^(N,1)finite_sum)
         (\z. pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z):real^(1,N)finite_sum)`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_SUB; LIFT_DROP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    REWRITE_TAC[GSYM o_DEF] THEN
    SUBGOAL_THEN `(sndcart:real^(N,1)finite_sum->real^1) = sndcart o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN `(fstcart:real^(N,1)finite_sum->real^N) = fstcart o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

let PDE_UNREFLECT_SMOOTH = prove
 (`!a. smooth_map_on (:real^(1,N)finite_sum)
         (\w. pastecart (sndcart w) (lift(&2 * a - drop(fstcart w))):real^(N,1)finite_sum)`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_SUB; LIFT_DROP] THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN `(sndcart:real^(1,N)finite_sum->real^N) = sndcart o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN `(fstcart:real^(1,N)finite_sum->real^1) = fstcart o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

(* Gluing on a time slab (the time-first form of PDE_EXTENSION_GLUE of      *)
(* pc_rf_extend, repeated here so that this unit needs no manifold units).   *)

let PDE_SLAB_GLUE = prove
 (`!a b c e (U:real^N->bool) (F1:real^(1,N)finite_sum->real^K) H.
        open U /\ &0 < e /\ a < b /\ b <= c /\
        smooth_map_on (interval(lift(a - e),lift b) PCROSS U) F1 /\
        smooth_map_on (interval(lift a,lift c) PCROSS U) H /\
        (!t y. a <= t /\ t < b /\ y IN U
               ==> F1(pastecart (lift t) y) = H(pastecart (lift t) y))
        ==> smooth_map_on (interval(lift(a - e),lift c) PCROSS U)
                          (\z. if drop(fstcart z) < a then F1 z else H z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t0 < b` THENL
   [EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `F1:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `interval(lift a,lift c) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `H:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Agreement at t = a of two maps continuous on [a,a+d] x closure V that     *)
(* agree on (a,a+d) x V.                                                     *)

let PDE_AGREE_AT_INITIAL = prove
 (`!a d (V:real^N->bool) (F1:real^(1,N)finite_sum->real^K) G.
        &0 < d /\
        F1 continuous_on interval[lift a,lift(a + d)] PCROSS closure V /\
        G continuous_on interval[lift a,lift(a + d)] PCROSS closure V /\
        (!t y. a < t /\ t < a + d /\ y IN V
               ==> F1(pastecart (lift t) y) = G(pastecart (lift t) y))
        ==> !y. y IN V ==> F1(pastecart (lift a) y) = G(pastecart (lift a) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`F1:real^(1,N)finite_sum->real^K`; `G:real^(1,N)finite_sum->real^K`]
          (ISPEC `interval(lift a,lift(a + d)) PCROSS (V:real^N->bool)`
             (GEN `s:real^M->bool` (INST_TYPE [`:K`,`:N`] CONTINUOUS_AGREE_ON_CLOSURE)))) THEN
  SUBGOAL_THEN `closure(interval(lift a,lift(a + d)) PCROSS (V:real^N->bool)) =
                interval[lift a,lift(a + d)] PCROSS closure V` SUBST1_TAC THENL
   [REWRITE_TAC[CLOSURE_PCROSS] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real`; `y:real^N`]) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_ADDR; REAL_LT_IMP_LE; REWRITE_RULE[SUBSET] CLOSURE_SUBSET]);;

(* Signs and index maps of the reflection-swap. *)

let PDE_ITLIST_SIGN = prove
 (`!n (l:num list). abs(ITLIST (\i r. (if i = n then --(&1) else &1) * r) l (&1)) = &1`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; REAL_ABS_NUM] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

let PDE_ALL_MAP_REFLECT = prove
 (`!n l. ALL (\i. 1 <= i /\ i <= n + 1) l
         ==> ALL (\i. 1 <= i /\ i <= n + 1) (MAP (\i. if i = n + 1 then 1 else i + 1) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* The cut-off reflected map g of the extension argument is smooth below a. *)

let PDE_SEELEY_G_SMOOTH = prove
 (`!a b d1 d2 (U:real^(1,N)finite_sum->real^K).
        &0 < d1 /\ d1 < d2 /\ a + d2 < b /\
        smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) U
        ==> smooth_map_on {z:real^(N,1)finite_sum | drop(sndcart z) < a}
              (\z. (&1 - smooth_step((&2 * a - drop(sndcart z) - (a + d1)) / (d2 - d1))) %
                   U(pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  REWRITE_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `z0:real^(N,1)finite_sum` THEN DISCH_TAC THEN
  ASM_CASES_TAC `&2 * a - drop(sndcart(z0:real^(N,1)finite_sum)) < b` THENL
   [EXISTS_TAC `{z:real^(N,1)finite_sum | drop(sndcart z) < a} INTER
                {z | &2 * a - b < drop(sndcart z)}` THEN
    ASM_SIMP_TAC[OPEN_INTER; TEXT_OPEN_TIME_LT; TEXT_OPEN_TIME_GT; IN_INTER; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `W = {z:real^(N,1)finite_sum | drop(sndcart z) < a} INTER
                    {z | &2 * a - b < drop(sndcart z)}` THEN
    SUBGOAL_THEN `open(W:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN SIMP_TAC[OPEN_INTER; TEXT_OPEN_TIME_LT; TEXT_OPEN_TIME_GT];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`W:real^(N,1)finite_sum->bool`; `\x:real^1 y:real^K. drop x % y`;
      `\z:real^(N,1)finite_sum.
         lift(&1 - smooth_step((&2 * a - drop(sndcart z) - (a + d1)) / (d2 - d1)))`;
      `\z:real^(N,1)finite_sum.
         (U:real^(1,N)finite_sum->real^K)
           (pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))`]
     SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL
       [`W:real^(N,1)finite_sum->bool`;
        `\z:real^(N,1)finite_sum.
           lift((&2 * a - drop(sndcart z) - (a + d1)) / (d2 - d1))`]
       SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN
       `(\z:real^(N,1)finite_sum. lift((&2 * a - drop(sndcart z) - (a + d1)) / (d2 - d1))) =
        (\z. inv(d2 - d1) % (lift(a - d1) - sndcart z))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; LIFT_DROP; DROP_CMUL; DROP_SUB] THEN
        GEN_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      REWRITE_TAC[ETA_AX] THEN
      SUBGOAL_THEN `(sndcart:real^(N,1)finite_sum->real^1) = sndcart o (\x. x)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
      REWRITE_TAC[GSYM o_DEF] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (:real^N)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
       [EXPAND_TAC "W" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; PASTECART_IN_PCROSS;
                    IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV; PDE_REFLECT_SMOOTH]]];
    EXISTS_TAC `{z:real^(N,1)finite_sum | drop(sndcart z) < a - d2}` THEN
    REWRITE_TAC[TEXT_OPEN_TIME_LT; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^(N,1)finite_sum. vec 0:real^K` THEN
    REWRITE_TAC[TEXT_OPEN_TIME_LT; SMOOTH_MAP_ON_CONST; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_step((&2 * a - drop(sndcart(z:real^(N,1)finite_sum)) - (a + d1)) /
                              (d2 - d1)) = &1`
      (fun th -> REWRITE_TAC[th; REAL_SUB_REFL; VECTOR_MUL_LZERO]) THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC]);;

(* The core extension theorem, for a space-time map U (time first).          *)

let PDE_SEELEY_CORE = prove
 (`!a b (k:real^N->bool) (U:real^(1,N)finite_sum->real^K).
        a < b /\ compact k /\
        smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) U /\
        (!t y. a < t /\ t < b /\ ~(y IN k) ==> U(pastecart (lift t) y) = vec 0) /\
        U continuous_on {w | a <= drop(fstcart w) /\ drop(fstcart w) < b} /\
        (!l. ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
             ==> ?h. h continuous_on {w | a <= drop(fstcart w) /\ drop(fstcart w) < b} /\
                     !w. a < drop(fstcart w) /\ drop(fstcart w) < b
                         ==> h w = iterated_partial l U w)
        ==> ?FF. smooth_map_on (interval(lift(a - &1),lift b) PCROSS (:real^N)) FF /\
                 (!w. a <= drop(fstcart w) /\ drop(fstcart w) < b ==> FF w = U w) /\
                 (!w. drop(fstcart w) < a /\ ~(sndcart w IN k) ==> FF w = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `h:(num)list->real^(1,N)finite_sum->real^K` (LABEL_TAC "h") o
         REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])))))) THEN
  ABBREV_TAC `d1 = (b - a) / &4` THEN ABBREV_TAC `d2 = (b - a) / &2` THEN
  SUBGOAL_THEN `&0 < d1 /\ d1 < d2 /\ a + d2 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d1"; "d2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!l t y. a < t /\ t < b /\ ~(y IN k)
            ==> iterated_partial l (U:real^(1,N)finite_sum->real^K)
                  (pastecart (lift t) y) = vec 0`
  (LABEL_TAC "pz") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS ((:real^N) DIFF k)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; GSYM closed; COMPACT_IMP_CLOSED;
                 PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; IN_DIFF;
                IN_UNIV] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
        ==> (h:(num)list->real^(1,N)finite_sum->real^K) l continuous_on
              interval[lift a,lift(a + d1)] PCROSS (:real^N)`
  (LABEL_TAC "hc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b}` THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                IN_ELIM_THM; FSTCART_PASTECART; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l y. ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l /\ ~(y IN k)
          ==> (h:(num)list->real^(1,N)finite_sum->real^K) l (pastecart (lift a) y) = vec 0`
  (LABEL_TAC "hz") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real`; `d1:real`; `(:real^N) DIFF k`;
                   `(h:(num)list->real^(1,N)finite_sum->real^K) l`;
                   `\w:real^(1,N)finite_sum. vec 0:real^K`] PDE_AGREE_AT_INITIAL) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[lift a,lift(a + d1)] PCROSS (:real^N)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_UNIV; SUBSET_REFL];
      REPEAT STRIP_TAC THEN
      USE_THEN "h" (fun th -> MP_TAC(MP (SPEC `l:num list` th)
        (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l`))) THEN
      DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y':real^N)` o CONJUNCT2) THEN
      REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "pz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = \z:real^(N,1)finite_sum.
          (&1 - smooth_step((&2 * a - drop(sndcart z) - (a + d1)) / (d2 - d1))) %
          (U:real^(1,N)finite_sum->real^K)
            (pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))` THEN
  SUBGOAL_THEN `smooth_map_on {z:real^(N,1)finite_sum | drop(sndcart z) < a}
                              (g:real^(N,1)finite_sum->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC PDE_SEELEY_G_SMOOTH THEN
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(N,1)finite_sum. drop(sndcart z) < a /\ ~(fstcart z IN k)
                             ==> (g:real^(N,1)finite_sum->real^K) z = vec 0`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&2 * a - drop(sndcart(z:real^(N,1)finite_sum)) < b` THENL
     [SUBGOAL_THEN
       `(U:real^(1,N)finite_sum->real^K)
          (pastecart (lift(&2 * a - drop(sndcart(z:real^(N,1)finite_sum)))) (fstcart z)) =
        vec 0`
       (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `smooth_step((&2 * a - drop(sndcart(z:real^(N,1)finite_sum)) - (a + d1)) /
                                (d2 - d1)) = &1`
        (fun th -> REWRITE_TAC[th; REAL_SUB_REFL; VECTOR_MUL_LZERO]) THEN
      MATCH_MP_TAC SMOOTH_STEP_1 THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(N,1)finite_sum. a - d1 < drop(sndcart z) /\ drop(sndcart z) < a
       ==> (g:real^(N,1)finite_sum->real^K) z =
           (U:real^(1,N)finite_sum->real^K)
             (pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))`
  (LABEL_TAC "gU") THENL
   [EXPAND_TAC "g" THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_step((&2 * a - drop(sndcart(z:real^(N,1)finite_sum)) - (a + d1)) /
                              (d2 - d1)) = &0`
      (fun th -> REWRITE_TAC[th; REAL_SUB_RZERO; VECTOR_MUL_LID]) THEN
    MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:(N,1)finite_sum)) l
        ==> ?G:real^N->real^K.
              !e. &0 < e
                  ==> ?d. &0 < d /\
                          !z. a - d < drop(sndcart z) /\ drop(sndcart z) < a
                              ==> norm(iterated_partial l (g:real^(N,1)finite_sum->real^K) z -
                                       G(fstcart z)) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num list` THEN REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    DISCH_TAC THEN
    ABBREV_TAC `sg = ITLIST (\i r. (if i = dimindex(:N) + 1 then --(&1) else &1) * r) l (&1)` THEN
    ABBREV_TAC `l' = MAP (\i. if i = dimindex(:N) + 1 then 1 else i + 1) (l:num list)` THEN
    SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) (l':num list)` ASSUME_TAC THENL
     [EXPAND_TAC "l'" THEN MATCH_MP_TAC PDE_ALL_MAP_REFLECT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `\y:real^N. sg % (h:(num)list->real^(1,N)finite_sum->real^K) l'
                                  (pastecart (lift a) y)` THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(h:(num)list->real^(1,N)finite_sum->real^K) l'`;
                   `interval[lift a,lift(a + d1)] PCROSS (k:real^N->bool)`]
                  COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[lift a,lift(a + d1)] PCROSS (:real^N)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_UNIV; SUBSET_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 del` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN STRIP_TAC THEN
    ABBREV_TAC `t = &2 * a - drop(sndcart(z:real^(N,1)finite_sum))` THEN
    SUBGOAL_THEN
     `iterated_partial l (g:real^(N,1)finite_sum->real^K) z =
      sg % (h:(num)list->real^(1,N)finite_sum->real^K) l'
             (pastecart (lift t) (fstcart(z:real^(N,1)finite_sum)))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`l:num list`;
                     `{z:real^(N,1)finite_sum | a - d1 < drop(sndcart z) /\
                                                drop(sndcart z) < a}`;
                     `g:real^(N,1)finite_sum->real^K`;
                     `\z:real^(N,1)finite_sum. (U:real^(1,N)finite_sum->real^K)
                        (pastecart (lift(&2 * a - drop(sndcart z))) (fstcart z))`]
                    TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[SET_RULE `{z:real^(N,1)finite_sum | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
          SIMP_TAC[OPEN_INTER; TEXT_OPEN_TIME_LT; TEXT_OPEN_TIME_GT];
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^(N,1)finite_sum`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`U:real^(1,N)finite_sum->real^K`;
                     `interval(lift a,lift b) PCROSS (:real^N)`; `a:real`; `l:num list`]
                    PDE_REFLECT_PARTIAL) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^(N,1)finite_sum`) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; IN_UNIV] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "h" (fun th -> MP_TAC(MP (SPEC `l':num list` th)
        (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) (l':num list)`))) THEN
      DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (fstcart(z:real^(N,1)finite_sum))` o
                 CONJUNCT2) THEN
      REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    EXPAND_TAC "sg" THEN REWRITE_TAC[PDE_ITLIST_SIGN; REAL_MUL_LID] THEN
    ASM_CASES_TAC `fstcart(z:real^(N,1)finite_sum) IN k` THENL
     [ONCE_REWRITE_TAC[GSYM DIST_EQ_0] THEN REWRITE_TAC[GSYM dist] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DIST_PASTECART_CANCEL;
                      DIST_LIFT] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `(h:(num)list->real^(1,N)finite_sum->real^K) l'
          (pastecart (lift t) (fstcart(z:real^(N,1)finite_sum))) = vec 0 /\
        h l' (pastecart (lift a) (fstcart z)) = vec 0`
      (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL; NORM_0]) THENL
       [CONJ_TAC THENL
         [USE_THEN "h" (fun th -> MP_TAC(MP (SPEC `l':num list` th)
            (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) (l':num list)`))) THEN
          DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (fstcart(z:real^(N,1)finite_sum))` o
                     CONJUNCT2) THEN
          REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          USE_THEN "pz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          USE_THEN "hz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(N,1)finite_sum->real^K`; `k:real^N->bool`; `a:real`]
                SMOOTH_EXTENSION_PAST_HYPERPLANE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^(N,1)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `FE = \w:real^(1,N)finite_sum.
           (g':real^(N,1)finite_sum->real^K)
             (pastecart (sndcart w) (lift(&2 * a - drop(fstcart w))))` THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,N)finite_sum) (FE:real^(1,N)finite_sum->real^K)`
  ASSUME_TAC THENL
   [EXPAND_TAC "FE" THEN REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; PDE_UNREFLECT_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. a < t /\ t < a + d1
          ==> (FE:real^(1,N)finite_sum->real^K) (pastecart (lift t) y) =
              (U:real^(1,N)finite_sum->real^K) (pastecart (lift t) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "FE" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    SUBGOAL_THEN
     `(g':real^(N,1)finite_sum->real^K) (pastecart y (lift(&2 * a - t))) =
      g (pastecart y (lift(&2 * a - t)))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[SNDCART_PASTECART; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "gU" (MP_TAC o SPEC `pastecart (y:real^N) (lift(&2 * a - t))`) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&2 * a - (&2 * a - t) = t`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `d1:real`; `(:real^N)`; `FE:real^(1,N)finite_sum->real^K`;
                 `U:real^(1,N)finite_sum->real^K`] PDE_AGREE_AT_INITIAL) THEN
  ASM_REWRITE_TAC[IN_UNIV; CLOSURE_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b}` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                  IN_ELIM_THM; FSTCART_PASTECART; IN_UNIV] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum. if drop(fstcart w) < a
                                       then (FE:real^(1,N)finite_sum->real^K) w
                                       else (U:real^(1,N)finite_sum->real^K) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SLAB_GLUE THEN EXISTS_TAC `a + d1` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; REAL_LT_01] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = a:real` THENL
       [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    CONJ_TAC THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_NOT_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "FE" THEN
    MATCH_MP_TAC(ASSUME `!z:real^(N,1)finite_sum. ~(fstcart z IN k)
                           ==> (g':real^(N,1)finite_sum->real^K) z = vec 0`) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART]]);;

(* ========================================================================= *)
(* The extension for an arbitrary open set of space (PDE_SEELEY).  A compact *)
(* exhaustion f n of U, smooth cutoffs chi n (1 on f n, 0 off interior       *)
(* f(n+1)), the telescoping partition psi n = chi n - chi(n-1) supported in  *)
(* the compact kk n; the core extension of each psi n u keeps its spatial    *)
(* support, so the sum of the extensions is locally finite and smooth.       *)
(* ========================================================================= *)

(* Smooth cutoffs in R^N: 1 on a compact K, 0 off a compact L inside W. *)

let PDE_RN_CUTOFF = prove
 (`!(K:real^N->bool) W.
        compact K /\ open W /\ K SUBSET W
        ==> ?chi:real^N->real L.
              smooth_map_on (:real^N) (\y. lift(chi y)) /\
              (!y. y IN K ==> chi y = &1) /\
              compact L /\ L SUBSET W /\
              (!y. ~(y IN L) ==> chi y = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?r. !x:real^N. x IN K ==> &0 < r x /\ cball(x,&2 * r x) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `open(W:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `&2 * e / &2 = e`];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:real^N. ball(x,r x)) K`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL] THEN ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `x:real^N` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[EXISTS_FINITE_SUBSET_IMAGE] o
    ONCE_REWRITE_RULE[TAUT `a /\ b /\ c <=> b /\ a /\ c`]) THEN
  SUBGOAL_THEN `!x:real^N. x IN D ==> &0 < r x /\ cball(x,&2 * r x) SUBSET W`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `\y:real^N. &1 - product D (\x. &1 - smooth_bump (r x) (&2 * r x) (y - x))` THEN
  EXISTS_TAC `UNIONS (IMAGE (\x:real^N. cball(x,&2 * r x)) D)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(&1)`;
                   `\y:real^N. lift(product D (\x. &1 - smooth_bump (r x) (&2 * r x) (y - x)))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`(:real^N)`;
                   `\x:real^N y:real^N. lift(&1 - smooth_bump (r x) (&2 * r x) (y - x))`;
                   `D:real^N->bool`] SMOOTH_MAP_ON_LIFT_PRODUCT) THEN
    ASM_REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(&1)`;
                   `\y:real^N. lift(smooth_bump (r x) (&2 * r x) (y - x))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `(\y:real^N. lift(smooth_bump (r x) (&2 * r x) (y - x))) =
                  (\z. lift(smooth_bump (r x) (&2 * r(x:real^N)) z)) o (\y. y - x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN
      SUBGOAL_THEN `&0 < r(x:real^N)` MP_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `&1 - p = &1 <=> p = &0`] THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0] THEN
    UNDISCH_TAC `K SUBSET UNIONS (IMAGE (\x:real^N. ball(x,r x)) D)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    SUBGOAL_THEN `&0 < r(x:real^N) /\ dist(x,y) < r x` MP_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[IN_BALL]]; ALL_TAC] THEN
    REWRITE_TAC[dist] THEN MP_TAC(ISPECL [`x:real^N`; `y:real^N`] NORM_SUB) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPACT_CBALL];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `&1 - p = &0 <=> p = &1`] THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `&1 - b = &1 <=> b = &0`] THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[IN_CBALL; dist] THEN
    SUBGOAL_THEN `&0 < r(x:real^N)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`] NORM_SUB) THEN REAL_ARITH_TAC]);;

(* Iterated partials of a sum (companion of TEXT_ITERATED_PARTIAL_SUB_OPEN). *)

let PDE_ITERATED_PARTIAL_ADD_OPEN = prove
 (`!l s (f:real^M->real^N) g.
      open s /\ smooth_map_on s f /\ smooth_map_on s g
      ==> !x. x IN s
              ==> iterated_partial l (\x. f x + g x) x =
                  iterated_partial l f x + iterated_partial l g x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\x. iterated_partial t (f:real^M->real^N) x + iterated_partial t g x) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

(* Continuous extension of all iterated partials (from the open set s to a  *)
(* set s1) passes to first partials and to products with scalar maps.       *)

let PDE_EXT_PARTIAL = prove
 (`!(s:real^M->bool) (s1:real^M->bool) (f:real^M->real^N) k.
        1 <= k /\ k <= dimindex(:M) /\
        (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
             ==> ?h. h continuous_on s1 /\ !z. z IN s ==> h z = iterated_partial l f z)
        ==> (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
             ==> ?h. h continuous_on s1 /\
                     !z. z IN s ==> h z = iterated_partial l (partial_derivative k f) z)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `APPEND l [k:num]`) THEN
  ASM_REWRITE_TAC[ALL_APPEND; ALL; ITERATED_PARTIAL_APPEND; iterated_partial]);;

let PDE_EXT_MUL = prove
 (`!(s:real^M->bool) (s1:real^M->bool).
        open s
        ==> !l (c:real^M->real^1) (g:real^M->real^N).
              smooth_map_on s c /\ smooth_map_on s g /\
              (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
                   ==> ?h. h continuous_on s1 /\
                           !z. z IN s ==> h z = iterated_partial l c z) /\
              (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
                   ==> ?h. h continuous_on s1 /\
                           !z. z IN s ==> h z = iterated_partial l g z) /\
              ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
              ==> ?h. h continuous_on s1 /\
                      !z. z IN s ==> h z = iterated_partial l (\z. drop(c z) % g z) z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!l (c:real^M->real^1) (g:real^M->real^N).
        smooth_map_on s c /\ smooth_map_on s g /\
        (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
             ==> ?h. h continuous_on s1 /\ !z. z IN s ==> h z = iterated_partial l c z) /\
        (!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
             ==> ?h. h continuous_on s1 /\ !z. z IN s ==> h z = iterated_partial l g z) /\
        ALL (\i. 1 <= i /\ i <= dimindex(:M)) (REVERSE l)
        ==> ?h. h continuous_on s1 /\
                !z. z IN s ==> h z = iterated_partial (REVERSE l) (\z. drop(c z) % g z) z`
  (LABEL_TAC "main") THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "main" (MP_TAC o SPEC `REVERSE l:num list`) THEN
    REWRITE_TAC[REVERSE_REVERSE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[REVERSE; iterated_partial] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN
    REWRITE_TAC[ALL; iterated_partial] THEN
    DISCH_THEN(X_CHOOSE_THEN `hc:real^M->real^1` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `hg:real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\z:real^M. drop(hc z) % (hg:real^M->real^N) z` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  REWRITE_TAC[REVERSE; ALL_APPEND; ALL; ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M->real^1`; `g:real^M->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN s
        ==> iterated_partial (REVERSE t)
              (partial_derivative h (\z. drop(c z) % (g:real^M->real^N) z)) z =
            iterated_partial (REVERSE t) (\z. drop(c z) % partial_derivative h g z) z +
            iterated_partial (REVERSE t) (\z. drop(partial_derivative h c z) % g z) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `iterated_partial (REVERSE t)
                 (\z. drop(c z) % partial_derivative h (g:real^M->real^N) z +
                      drop(partial_derivative h c z) % g z) z` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`REVERSE t:num list`; `s:real^M->bool`;
                     `partial_derivative h (\z. drop(c z) % (g:real^M->real^N) z)`;
                     `\z. drop(c z) % partial_derivative h (g:real^M->real^N) z +
                          drop(partial_derivative h c z) % g z`]
                    TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
        MATCH_MP_TAC PARTIAL_DERIVATIVE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`REVERSE t:num list`; `s:real^M->bool`;
                     `\z. drop(c z) % partial_derivative h (g:real^M->real^N) z`;
                     `\z. drop(partial_derivative h c z) % (g:real^M->real^N) z`]
                    PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
        ==> ?hh. hh continuous_on s1 /\
                 !z. z IN s ==> hh z = iterated_partial l (partial_derivative h (c:real^M->real^1)) z`
  ASSUME_TAC THENL [MATCH_MP_TAC PDE_EXT_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
        ==> ?hh. hh continuous_on s1 /\
                 !z. z IN s ==> hh z = iterated_partial l (partial_derivative h (g:real^M->real^N)) z`
  ASSUME_TAC THENL [MATCH_MP_TAC PDE_EXT_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?h1. h1 continuous_on s1 /\
         !z. z IN s ==> h1 z = iterated_partial (REVERSE t)
                                 (\z. drop(c z) % partial_derivative h (g:real^M->real^N) z) z`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ih" MATCH_MP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?h2. h2 continuous_on s1 /\
         !z. z IN s ==> h2 z = iterated_partial (REVERSE t)
                                 (\z. drop(partial_derivative h c z) % (g:real^M->real^N) z) z`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ih" MATCH_MP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `\z:real^M. (h1:real^M->real^N) z + h2 z` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD]);;

(* The half-open slab [a,b) x U as a set of pasted points. *)

let PDE_SLAB_SET = prove
 (`!a b (U:real^N->bool).
        {pastecart (lift t) y | a <= t /\ t < b /\ y IN U} =
        {w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                  sndcart w IN U}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; FORALL_LIFT; IN_ELIM_THM;
              FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; PASTECART_INJ; LIFT_EQ] THEN
  MESON_TAC[]);;

(* Extension by zero off a compact k inside U of a map continuous on        *)
(* [a,b) x U that vanishes for t > a off k (hence also at t = a).           *)

let PDE_EXT_ZERO = prove
 (`!a b (U:real^N->bool) k (h:real^(1,N)finite_sum->real^K).
        open U /\ a < b /\ compact k /\ k SUBSET U /\
        h continuous_on
          {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U} /\
        (!w. a < drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U /\
             ~(sndcart w IN k)
             ==> h w = vec 0)
        ==> (\w. if sndcart w IN k then h w else vec 0) continuous_on
            {w | a <= drop(fstcart w) /\ drop(fstcart w) < b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U /\
        ~(sndcart w IN k)
        ==> (h:real^(1,N)finite_sum->real^K) w = vec 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART; FORALL_LIFT;
                LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = a:real` THENL
     [ALL_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `open((U:real^N->bool) DIFF k)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`a:real`; `(b - a) / &2`; `ball(y:real^N,r)`;
                   `h:real^(1,N)finite_sum->real^K`;
                   `(\w. vec 0):real^(1,N)finite_sum->real^K`]
                  PDE_AGREE_AT_INITIAL) THEN
    ASM_SIMP_TAC[CLOSURE_BALL; CONTINUOUS_ON_CONST] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                    IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
        MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN
        REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_MESON_TAC[SUBSET; IN_DIFF]];
        MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
        REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`y:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^(1,N)finite_sum. sndcart w IN k`;
                 `h:real^(1,N)finite_sum->real^K`;
                 `(\w. vec 0):real^(1,N)finite_sum->real^K`;
                 `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                            sndcart w IN U}`;
                 `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                            ~(sndcart w IN k)}`]
                CONTINUOUS_ON_CASES_LOCAL_OPEN) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                              sndcart w IN U} UNION
    {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ ~(sndcart w IN k)} =
    {w | a <= drop(fstcart w) /\ drop(fstcart w) < b}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `{w:real^(1,N)finite_sum | sndcart w IN U}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_SNDCART];
      ASM SET_TAC[]];
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `{w:real^(1,N)finite_sum | sndcart w IN (:real^N) DIFF k}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_SNDCART];
      ASM SET_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* Partial sums over 0..p and 0..q agree when all terms beyond p and beyond *)
(* q vanish.                                                                 *)

let PDE_VSUM_NUMSEG_EQ = prove
 (`!(v:num->real^K) p q.
        (!n. p < n ==> v n = vec 0) /\ (!n. q < n ==> v n = vec 0)
        ==> vsum(0..p) v = vsum(0..q) v`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `p:num <= q \/ q <= p`) THENL
   [CONV_TAC SYM_CONV; ALL_TAC] THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
  (CONJ_TAC THENL
    [POP_ASSUM MP_TAC THEN ARITH_TAC;
     ASM_MESON_TAC[ARITH_RULE `~(0 <= n /\ n:num <= m) ==> m < n`]]));;

(* Membership in an open slab, for an arbitrary point. *)

let PDE_IN_SLAB = prove
 (`!a b (s:real^N->bool) (w:real^(1,N)finite_sum).
        w IN interval(lift a,lift b) PCROSS s <=>
        a < drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN s`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; CONJ_ASSOC]);;

(* One piece: the core extension of psi(y) u(t,y) for a smooth psi         *)
(* vanishing off a compact k inside U keeps the spatial support k.          *)

let PDE_SEELEY_PIECE = prove
 (`!a b (U:real^N->bool) k (psi:real^N->real) (uf:real^(1,N)finite_sum->real^K).
        open U /\ a < b /\ compact k /\ k SUBSET U /\
        smooth_map_on (:real^N) (\y. lift(psi y)) /\
        (!y. ~(y IN k) ==> psi y = &0) /\
        smooth_map_on (interval(lift a,lift b) PCROSS U) uf /\
        uf continuous_on
          {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U} /\
        (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
             ==> ?h. h continuous_on
                       {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U} /\
                     !z. z IN interval(lift a,lift b) PCROSS U
                         ==> h z = iterated_partial l uf z)
        ==> ?E. smooth_map_on (interval(lift(a - &1),lift b) PCROSS (:real^N)) E /\
                (!w. a <= drop(fstcart w) /\ drop(fstcart w) < b
                     ==> E w = psi(sndcart w) % uf w) /\
                (!w. drop(fstcart w) < b /\ ~(sndcart w IN k) ==> E w = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (LABEL_TAC "eu"))))))))) THEN
  SUBGOAL_THEN `dimindex(:(1,N)finite_sum) = dimindex(:N) + 1` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,N)finite_sum) (\w. lift(psi(sndcart w)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w:real^(1,N)finite_sum. lift(psi(sndcart w))) = (\y. lift(psi y)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
    ALL_TAC] THEN
  ABBREV_TAC `V = \w:real^(1,N)finite_sum. psi(sndcart w) % (uf:real^(1,N)finite_sum->real^K) w` THEN
  SUBGOAL_THEN `!w. ~(sndcart w IN k) ==> (V:real^(1,N)finite_sum->real^K) w = vec 0`
  ASSUME_TAC THENL [EXPAND_TAC "V" THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) (V:real^(1,N)finite_sum->real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN U` THENL
     [EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS] THEN
      EXPAND_TAC "V" THEN
      MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
                     `\w:real^(1,N)finite_sum. lift(psi(sndcart w))`;
                     `uf:real^(1,N)finite_sum->real^K`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; LIFT_DROP] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^(1,N)finite_sum)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `interval(lift a,lift b) PCROSS ((:real^N) DIFF k)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED;
                   PASTECART_IN_PCROSS; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(\w. vec 0):real^(1,N)finite_sum->real^K` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED;
                   SMOOTH_MAP_ON_CONST; FORALL_IN_PCROSS; IN_DIFF; IN_UNIV;
                   SNDCART_PASTECART]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
        ==> ?h. h continuous_on
                  {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U} /\
                !z. z IN interval(lift a,lift b) PCROSS U
                    ==> h z = iterated_partial l (V:real^(1,N)finite_sum->real^K) z`
  (LABEL_TAC "pv") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN EXPAND_TAC "V" THEN
    MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (U:real^N->bool)`;
                   `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                              sndcart w IN U}`]
                  (INST_TYPE [`:K`,`:N`] PDE_EXT_MUL)) THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; ASSUME `open(U:real^N->bool)`] THEN
    DISCH_THEN(MP_TAC o SPECL [`l:num list`; `\w:real^(1,N)finite_sum. lift(psi(sndcart w))`;
                               `uf:real^(1,N)finite_sum->real^K`]) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `l':num list` THEN DISCH_TAC THEN
        EXISTS_TAC `iterated_partial l' (\w:real^(1,N)finite_sum. lift(psi(sndcart w)))` THEN
        REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
        USE_THEN "eu" ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(V:real^(1,N)finite_sum->real^K) continuous_on
      {w | a <= drop(fstcart w) /\ drop(fstcart w) < b}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\w. if sndcart w IN k then (V:real^(1,N)finite_sum->real^K) w else vec 0` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PDE_EXT_ZERO THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "V" THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `k:real^N->bool`; `V:real^(1,N)finite_sum->real^K`]
                PDE_SEELEY_CORE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[SNDCART_PASTECART]; ALL_TAC] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    USE_THEN "pv" (MP_TAC o SPEC `l:num list`) THEN
    REWRITE_TAC[ASSUME `dimindex(:(1,N)finite_sum) = dimindex(:N) + 1`;
                ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) (l:num list)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\w. if sndcart w IN k then (h:real^(1,N)finite_sum->real^K) w else vec 0` THEN
    SUBGOAL_THEN
     `!w. a < drop(fstcart w) /\ drop(fstcart w) < b /\ ~(sndcart w IN k)
          ==> iterated_partial l (V:real^(1,N)finite_sum->real^K) w = vec 0`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN
      MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS ((:real^N) DIFF k)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED;
                   PDE_IN_SLAB; IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_EXT_ZERO THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN
      SUBGOAL_THEN `w IN interval(lift a,lift b) PCROSS (U:real^N->bool)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[PDE_IN_SLAB]; ASM_SIMP_TAC[]];
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `w IN interval(lift a,lift b) PCROSS (U:real^N->bool)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[PDE_IN_SLAB] THEN ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `E:real^(1,N)finite_sum->real^K` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[];
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop(fstcart(w:real^(1,N)finite_sum)) < a` THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[GSYM REAL_NOT_LT]]);;

(* A locally finite smooth partition of unity of an open set of R^N, in the *)
(* telescoping form psi n = chi n - chi(n-1) over a compact exhaustion.     *)

let PDE_LF_PARTITION = prove
 (`!U:real^N->bool.
        open U
        ==> ?psi kk G.
              (!n. compact(kk n) /\ kk n SUBSET U) /\
              (!n. smooth_map_on (:real^N) (\y. lift(psi n y))) /\
              (!n y. ~(y IN kk n) ==> psi n y = &0) /\
              (!n. open(G n)) /\
              (!y. y IN U ==> ?m. y IN G m) /\
              (!m n y. y IN G m /\ m < n ==> ~(y IN kk n)) /\
              (!m y. y IN G m ==> sum(0..m) (\n. psi n y) = &1)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `U:real^N->bool` OPEN_UNION_COMPACT_SUBSETS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m <= n ==> (f:num->real^N->bool) m SUBSET f n` (LABEL_TAC "mono") THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[SUBSET_REFL] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[ADD1] THEN
    ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?chi:num->real^N->real.
      (!n. smooth_map_on (:real^N) (\y. lift(chi n y))) /\
      (!n y. y IN f n ==> chi n y = &1) /\
      (!n y. ~(y IN interior(f(n + 1))) ==> chi n y = &0)`
  (X_CHOOSE_THEN `chi:num->real^N->real`
     (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2") (LABEL_TAC "c3"))))
  THENL
   [REWRITE_TAC[GSYM FORALL_AND_THM; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`(f:num->real^N->bool) n`; `interior((f:num->real^N->bool)(n + 1))`]
                  PDE_RN_CUTOFF) THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->real`
      (X_CHOOSE_THEN `L:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `c:real^N->real` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m (y:real^N). sum(0..m) (\n. if n = 0 then chi 0 y else chi n y - chi (n - 1) y) =
                   chi m y`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; NOT_SUC; SUC_SUB1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\n (y:real^N). if n = 0 then chi 0 y else chi n y - chi (n - 1) y` THEN
  EXISTS_TAC `\n. if n = 0 then (f:num->real^N->bool) 1
                  else f(n + 1) DIFF interior(f(n - 1))` THEN
  EXISTS_TAC `\m. interior((f:num->real^N->bool) m)` THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[COMPACT_DIFF; OPEN_INTERIOR] THEN
    ASM SET_TAC[];
    GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN USE_THEN "c3" (MP_TAC o SPECL [`0`; `y:real^N`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `n - 1 + 1 = n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; DE_MORGAN_THM] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(chi:num->real^N->real) n y = &0 /\ chi (n - 1) y = &0`
        (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
      CONJ_TAC THEN USE_THEN "c3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
        SUBGOAL_THEN `interior((f:num->real^N->bool) n) SUBSET f(n + 1)` MP_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(f:num->real^N->bool) n` THEN
          REWRITE_TAC[INTERIOR_SUBSET] THEN USE_THEN "mono" MATCH_MP_TAC THEN ARITH_TAC;
          ASM SET_TAC[]]];
      SUBGOAL_THEN `(chi:num->real^N->real) n y = &1 /\ chi (n - 1) y = &1`
        (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
      CONJ_TAC THEN USE_THEN "c2" MATCH_MP_TAC THENL
       [SUBGOAL_THEN `(f:num->real^N->bool) (n - 1) SUBSET f n` MP_TAC THENL
         [USE_THEN "mono" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPEC `(f:num->real^N->bool) (n - 1)` INTERIOR_SUBSET) THEN ASM SET_TAC[];
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]]];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `UNIONS {(f:num->real^N->bool) n | n IN (:num)} = U` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC)) THEN
    EXISTS_TAC `n + 1` THEN ASM_MESON_TAC[SUBSET];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; DE_MORGAN_THM] THEN DISJ2_TAC THEN
    SUBGOAL_THEN `interior((f:num->real^N->bool) m) SUBSET interior(f(n - 1))` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN USE_THEN "mono" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM SET_TAC[]];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "c2" MATCH_MP_TAC THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]]);;

(* PDE_SEELEY: a family u that is smooth on (a,b) x U, continuous on        *)
(* [a,b) x U, and whose iterated partials all extend continuously to        *)
(* [a,b) x U, is the restriction of a map smooth on (a - 1,b) x U.          *)
(* (The continuity of u at t = a is needed: without it the statement is     *)
(* false, since u(a,y) is otherwise unconstrained.)                         *)

let PDE_SEELEY = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ a < b /\
        (\w. u (drop(fstcart w)) (sndcart w)) continuous_on
          {pastecart (lift t) y | a <= t /\ t < b /\ y IN U} /\
        pde_upto_classical a b U u
        ==> pde_upto a b U u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto_classical; pde_upto; PDE_SLAB_SET] THEN
  ABBREV_TAC
   `uf = \w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
        ==> ?h. h continuous_on
                  {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U} /\
                !z. z IN interval(lift a,lift b) PCROSS U
                    ==> h z = iterated_partial l (uf:real^(1,N)finite_sum->real^K) z`
  (LABEL_TAC "eu") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^(1,N)finite_sum->real^K` THEN
    SIMP_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `U:real^N->bool` PDE_LF_PARTITION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:num->real^N->real` (X_CHOOSE_THEN `kk:num->real^N->bool`
    (X_CHOOSE_THEN `G:num->real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!n. ?E:real^(1,N)finite_sum->real^K.
          smooth_map_on (interval(lift(a - &1),lift b) PCROSS (:real^N)) E /\
          (!w. a <= drop(fstcart w) /\ drop(fstcart w) < b
               ==> E w = (psi:num->real^N->real) n (sndcart w) %
                         (uf:real^(1,N)finite_sum->real^K) w) /\
          (!w. drop(fstcart w) < b /\ ~(sndcart w IN (kk:num->real^N->bool) n)
               ==> E w = vec 0)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC PDE_SEELEY_PIECE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:num->real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!w m. drop(fstcart w) < b /\ sndcart w IN (G:num->real^N->bool) m
          ==> vsum(0..(@m. sndcart w IN G m))
                  (\n. (E:num->real^(1,N)finite_sum->real^K) n w) =
              vsum(0..m) (\n. E n w)`
  (LABEL_TAC "stab") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_VSUM_NUMSEG_EQ THEN
    SUBGOAL_THEN
     `sndcart(w:real^(1,N)finite_sum) IN G(@m. sndcart w IN (G:num->real^N->bool) m)`
    ASSUME_TAC THENL [CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `&1` THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum.
                vsum(0..(@m. sndcart w IN (G:num->real^N->bool) m))
                    (\n. (E:num->real^(1,N)finite_sum->real^K) n w)` THEN
  REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?m. (y:real^N) IN (G:num->real^N->bool) m` (X_CHOOSE_TAC `m0:num`) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `interval(lift(a - &1),lift b) PCROSS ((G:num->real^N->bool) m0)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\w. vsum(0..m0) (\n. (E:num->real^(1,N)finite_sum->real^K) n w)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[PDE_IN_SLAB] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "stab" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FINITE_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - &1),lift b) PCROSS (:real^N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET_UNIV]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?m. (y:real^N) IN (G:num->real^N->bool) m` (X_CHOOSE_TAC `m0:num`) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN
    USE_THEN "stab" (MP_TAC o SPECL [`pastecart (lift t) (y:real^N)`; `m0:num`]) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `!n. (E:num->real^(1,N)finite_sum->real^K) n (pastecart (lift t) y) =
          (psi:num->real^N->real) n y % (uf:real^(1,N)finite_sum->real^K) (pastecart (lift t) y)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    REWRITE_TAC[VSUM_RMUL] THEN ASM_SIMP_TAC[VECTOR_MUL_LID] THEN
    EXPAND_TAC "uf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]);;

(* Conversely an extension past a gives the classical regularity, so for an *)
(* open U the two notions agree (PDE_UPTO_EQ_CLASSICAL).                     *)

let PDE_UPTO_IMP_CLASSICAL = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ pde_upto a b U u
        ==> (\w. u (drop(fstcart w)) (sndcart w)) continuous_on
              {pastecart (lift t) y | a <= t /\ t < b /\ y IN U} /\
            pde_upto_classical a b U u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_upto; pde_upto_classical; PDE_SLAB_SET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!w. a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U
        ==> (FF:real^(1,N)finite_sum->real^K) w = u (drop(fstcart w)) (sndcart w)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART; FORALL_LIFT;
                LIFT_DROP] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w:real^(1,N)finite_sum | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U}
    SUBSET interval(lift(a - e),lift b) PCROSS U`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; PDE_IN_SLAB] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interval(lift a,lift b) PCROSS (U:real^N->bool) SUBSET
                interval(lift(a - e),lift b) PCROSS U`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; PDE_IN_SLAB] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `FF:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `FF:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[PDE_IN_SLAB] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    EXISTS_TAC `iterated_partial l (FF:real^(1,N)finite_sum->real^K)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP; PDE_IN_SLAB] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let PDE_UPTO_EQ_CLASSICAL = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ a < b
        ==> (pde_upto a b U u <=>
             (\w. u (drop(fstcart w)) (sndcart w)) continuous_on
               {pastecart (lift t) y | a <= t /\ t < b /\ y IN U} /\
             pde_upto_classical a b U u)`,
  MESON_TAC[PDE_SEELEY; PDE_UPTO_IMP_CLASSICAL]);;

