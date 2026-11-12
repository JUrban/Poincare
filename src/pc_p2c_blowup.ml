(* ========================================================================= *)
(* Unit pc_p2c_blowup (Part 2C): MT Thm 11.1 in view form, the route         *)
(* P2C_THM_11_1_VIEW_ROUTE_STATEMENT u (:real^3), and the common limit       *)
(* infrastructure of the blow-up units (pc_p2c_blowup2, blowup3): flow       *)
(* limits on J as p3_flow_limit (one subsequence for every Tl), the limit    *)
(* flow smooth up to time 0, pinching bounds, and transfers of curvature     *)
(* quantities, canonical neighbourhoods and separation from the approximants *)
(* to the limit.                                                             *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_p2c_fl515.ml";;
needs "src/pc_p2c_lcn.ml";;
needs "src/pc_p2c_t533.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_rfa_pinchrm.ml";;
needs "src/pc_lim_close.ml";;
needs "src/pc_lck_swap.ml";;
needs "src/pc_p2b_slice.ml";;
needs "src/pc_canon_diam.ml";;
needs "src/pc_p2b_limbridge.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A flow limit on an interval J containing every [--c k,0] (c increasing)   *)
(* is, along one subsequence, a p3_flow_limit for every Tl up to sup c       *)
(* (given the smoothness up to time 0 that p3_flow_limit asks).              *)
(* ------------------------------------------------------------------------- *)

let P2BU_STRICT_ABOVE = prove
 (`!k0:num->num. ?sub. (!k. k0 k <= sub k) /\ (!k. sub k < sub (SUC k))`,
  GEN_TAC THEN
  MP_TAC(prove_recursive_functions_exist num_RECURSION
    `(f:num->num) 0 = k0 0 /\ !n. f (SUC n) = MAX (k0 (SUC n)) (f n + 1)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:num->num` THEN CONJ_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let P2BU_SUBSEQ_STEP = prove
 (`!sub. (!k. sub k < sub (SUC k)) ==> p3_subseq sub /\ !k. k <= sub k`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `p3_subseq sub` ASSUME_TAC THENL
   [REWRITE_TAC[p3_subseq] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
    ASM_MESON_TAC[p3_subseq]]);;

(* The times ts k of p3_flow_limit: min(c k, Tl (1 - 1/(k+2))). *)

let P2BU_TS_PROPS = prove
 (`!c:num->real Tl.
     &0 < Tl /\ (!k. &0 < c k /\ c k <= c (SUC k)) /\ (!a. a < Tl ==> ?k. a <= c k)
     ==> (!k. &0 < min (c k) (Tl * (&1 - inv(&k + &2))) /\
              min (c k) (Tl * (&1 - inv(&k + &2))) < Tl /\
              min (c k) (Tl * (&1 - inv(&k + &2))) <=
              min (c (SUC k)) (Tl * (&1 - inv(&(SUC k) + &2))) /\
              min (c k) (Tl * (&1 - inv(&k + &2))) <= c k) /\
         (!a. a < Tl ==> ?k0. !k. k0 <= k ==> a <= min (c k) (Tl * (&1 - inv(&k + &2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. &0 < Tl * (&1 - inv(&k + &2)) /\ Tl * (&1 - inv(&k + &2)) < Tl /\
                    Tl * (&1 - inv(&k + &2)) <= Tl * (&1 - inv(&(SUC k) + &2))`
  (LABEL_TAC "b") THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `&0 < inv(&k + &2) /\ inv(&k + &2) <= inv(&2) /\
                  inv(&(SUC k) + &2) <= inv(&k + &2)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `Tl * (&1 - i) < Tl <=> &0 < Tl * i`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (c:num->real) m <= c n` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> Tl * (&1 - inv(&m + &2)) <= Tl * (&1 - inv(&n + &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN USE_THEN "b" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "b" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    UNDISCH_TAC `!k. &0 < (c:num->real) k /\ c k <= c (SUC k)` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[real_min] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k1:num` o C MATCH_MP (ASSUME `a:real < Tl`) o check (fun th ->
    can (term_match [] `!a. a < Tl ==> ?k. a <= (c:num->real) k`) (concl th))) THEN
  SUBGOAL_THEN `?k2. a <= Tl * (&1 - inv(&k2 + &2))` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `a <= &0` THENL
     [EXISTS_TAC `0` THEN USE_THEN "b" (MP_TAC o SPEC `0`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `Tl / (Tl - a)` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `k2:num`) THEN EXISTS_TAC `k2:num` THEN
    SUBGOAL_THEN `&0 < Tl - a /\ &0 < &k2 + &2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Tl <= (&k2 + &2) * (Tl - a)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k2 * (Tl - a)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `Tl / (Tl - a) <= &k2` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Tl * inv(&k2 + &2) <= Tl - a` MP_TAC THENL
     [REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `MAX k1 k2` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c:num->real) k1` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!m n. m <= n ==> (c:num->real) m <= c n`) (concl th))) THEN
    UNDISCH_TAC `MAX k1 k2 <= k` THEN ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Tl * (&1 - inv(&k2 + &2))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!m n. m <= n ==> Tl * (&1 - inv(&m + &2)) <= Tl * (&1 - inv(&n + &2))`)
          (concl th))) THEN
    UNDISCH_TAC `MAX k1 k2 <= k` THEN ARITH_TAC]);;

(* The conversion.  The subsequence sub depends only on c; for each Tl the  *)
(* exhaustion is W o sub, the maps phi o sub, the times as in TS_PROPS.     *)

let P2BU_FLOW_LIMIT_OF_ON = prove
 (`!V x t Q J (top:B topology) atlas g xl (c:num->real).
     p3_flow_limit_on (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) x t Q J (top,atlas) g xl /\
     (!k. &0 < c k /\ c k <= c (SUC k) /\ real_interval[--(c k),&0] SUBSET J)
     ==> ?sub. p3_subseq sub /\
               !Tl. &0 < Tl /\ (!a. a < Tl ==> ?k. a <= c k) /\
                    (!a. --Tl < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g)
                    ==> p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub) (Q o sub)
                                      (top,atlas) g xl Tl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "c")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->A`
    (CONJUNCTS_THEN2 (LABEL_TAC "ex") (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 (LABEL_TAC "base") (LABEL_TAC "lim")))))) THEN
  SUBGOAL_THEN `!k. (W:num->B->bool) k SUBSET topspace top` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
    USE_THEN "ex" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (W:num->B->bool) m SUBSET W n` (LABEL_TAC "mono") THENL
   [MATCH_MP_TAC P2B_EXHAUST_MONO THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
    ASM_SIMP_TAC[CLOSURE_OF_SUBSET] THEN USE_THEN "ex" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?k0. !n. k0 <= n
                 ==> !s. --((c:num->real) k) <= s /\ s <= &0
                         ==> ?psi. mfd_diffeo (top:B topology)
                                     (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) n)
                                     (rfs_vtop ((V:num->(real->A topology)#
                                                  (real->((A->bool)#(A->real^3))->bool)#
                                                  (real->A->real^3^3)) n)
                                               (t n + s / Q n))
                                     (rfs_vatlas (V n) (t n + s / Q n))
                                     (IMAGE ((phi:num->B->A) n) (W n)) (phi n) psi`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "lim" (MP_TAC o SPECL [`--((c:num->real) k)`; `&0`; `{xl:B}`; `0`; `&1`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01] THEN
      USE_THEN "c" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `k0:num->num` (LABEL_TAC "k0")) THEN
  MP_TAC(SPEC `k0:num->num` P2BU_STRICT_ABOVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BU_SUBSEQ_STEP) THEN
  EXISTS_TAC `sub:num->num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `Tl:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num->real`; `Tl:real`] P2BU_TS_PROPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "c" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ts") (LABEL_TAC "tslim")) THEN
  REWRITE_TAC[p3_flow_limit] THEN ASM_REWRITE_TAC[o_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`\k. (W:num->B->bool) ((sub:num->num) k)`;
    `\k. min ((c:num->real) k) (Tl * (&1 - inv(&k + &2)))`;
    `\k. (phi:num->B->A) ((sub:num->num) k)`] THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN USE_THEN "ex" (MP_TAC o SPEC `(sub:num->num) k`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(W:num->B->bool) (SUC((sub:num->num) k))` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mono" MATCH_MP_TAC THEN
    UNDISCH_TAC `!k:num. (sub:num->num) k < sub (SUC k)` THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "un" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:B` THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `u:B->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k:num` ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && is_var(lhs(concl th)))) THENL
     [EXISTS_TAC `(W:num->B->bool) ((sub:num->num) k)` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      EXISTS_TAC `(W:num->B->bool) ((sub:num->num) k)` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:B) IN (W:num->B->bool) k` THEN
      SUBGOAL_THEN `(W:num->B->bool) k SUBSET W ((sub:num->num) k)` MP_TAC THENL
       [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "ts" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "tslim" (MP_TAC o C MATCH_MP (ASSUME `a:real < Tl`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `k1:num`) THEN EXISTS_TAC `k1:num` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL [GEN_TAC THEN USE_THEN "base" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "k0" (MP_TAC o SPECL [`k:num`; `(sub:num->num) k`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ts" (MP_TAC o SPEC `k:num`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[a,&0] SUBSET (J:real->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `--a:real` o
      check (fun th -> can (term_match [] `!a. a < Tl ==> ?k. a <= (c:num->real) k`)
                           (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[--((c:num->real) k),&0]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "c" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "lim" (MP_TAC o SPECL [`a:real`; `&0`; `K:B->bool`; `m:num`; `eta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num` (LABEL_TAC "k1")) THEN
  USE_THEN "tslim" (MP_TAC o SPEC `--a:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (LABEL_TAC "k2")) THEN
  EXISTS_TAC `MAX k1 k2` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k1" (MP_TAC o SPEC `(sub:num->num) k`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `MAX k1 k2 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "k2" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `MAX k1 k2 <= k` THEN ARITH_TAC; REAL_ARITH_TAC]);;

(* Copy-adapted from P2CR_IDENT (pc_p2c_fl514): the same identification of *)
(* the limit in a chart with the local Arzela-Ascoli limit, on [a0,b]       *)
(* instead of [0,b] (the proof is unchanged up to the endpoint).            *)

let P2BU_IDENT_AB = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g m a0 b N c FF ee cc rr sub' H.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     real_interval[a0,b] SUBSET J /\ c IN atlas /\
     (!c'. c' IN atlas
           ==> p2ca_seqhyp (IMAGE (SND c') (FST c' INTER W m)) a0 b
                 (\n s. metric_local atlas c' (p2cv_P V t Q atlas phi (sub (N + n)) s))) /\
     p2cm_ctx (IMAGE (SND c) (FST c INTER W m)) a0 b
              (\n s. metric_local atlas c (p2cv_P V t Q atlas phi (sub (N + n)) s))
              FF ee cc rr sub' H
     ==> !s0 y. a0 <= s0 /\ s0 <= b /\ y IN IMAGE (SND c) (FST c INTER W m)
                ==> metric_local atlas c (g s0) y =
                    p2cm_lim (\n s. metric_local atlas c
                                      (p2cv_P V t Q atlas phi (sub (N + n)) s))
                             sub' s0 y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 (LABEL_TAC "lck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sh") (LABEL_TAC "ctx"))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n <= (sub':num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN
    USE_THEN "ctx" (MP_TAC o REWRITE_RULE[p2cm_ctx]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?xc:B. xc IN FST(c:(B->bool)#(B->real^3)) /\ xc IN (W:num->B->bool) m /\
                       SND c xc = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3)))
                                     (FST c INTER (W:num->B->bool) m)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xc:B) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. a0 <= s /\ s <= b ==> s IN J` (LABEL_TAC "inJ") THENL
   [UNDISCH_TAC `real_interval[a0,b] SUBSET J` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a0 <= s /\ s <= b
        ==> riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) ((g:real->B->real^3^3) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "riem" MATCH_MP_TAC THEN USE_THEN "inJ" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c' n s. c' IN atlas /\ a0 <= s /\ s <= b
             ==> metric_field (IMAGE (SND c') (FST c' INTER (W:num->B->bool) m))
                   (metric_local atlas c'
                      (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s))`
  (LABEL_TAC "mfall") THENL
   [MAP_EVERY X_GEN_TAC [`c':(B->bool)#(B->real^3)`; `n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "sh" (MP_TAC o C MP (ASSUME `(c':(B->bool)#(B->real^3)) IN atlas`) o
                   SPEC `c':(B->bool)#(B->real^3)`) THEN
    REWRITE_TAC[p2ca_seqhyp] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `s:real`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N1. !n s. N1 <= n /\ a0 <= s /\ s <= b
                       ==> lck_dist2 0
                             (metric_local atlas (chart_at atlas (xc:B)) ((g:real->B->real^3^3) s))
                             (metric_local atlas (chart_at atlas xc)
                                (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s))
                             (SND(chart_at atlas xc) xc) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "lck" (MP_TAC o SPECL [`a0:real`; `b:real`; `{xc:B}`; `0`; `e:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SING]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN EXISTS_TAC `N1:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
    UNDISCH_TAC `N1 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\n s. p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s`;
                 `g:real->B->real^3^3`; `(W:num->B->bool) m`; `c:(B->bool)#(B->real^3)`;
                 `a0:real`; `b:real`; `xc:B`; `0`] P2CR_LCK_CHART_C) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "lc")] THEN
  MATCH_MP_TAC P2CB_LCK_LIM_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
    `\n. metric_local atlas (c:(B->bool)#(B->real^3))
           (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + (sub':num->num) n)) s0)`;
    `0`] THEN
  REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CR_RIEM_FIELD THEN EXISTS_TAC `top:B topology` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a0:real`; `b:real`;
                          `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                          `cc:num->real^3`; `rr:num->real`;
                          `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "mfall" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "lc" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN EXISTS_TAC `N2:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y = SND(c:(B->bool)#(B->real^3)) (xc:B)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "N2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                   `a0:real`; `b:real`;
                   `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
                            (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s)`;
                   `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                   `cc:num->real^3`; `rr:num->real`; `sub':num->num`;
                   `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`;
                   `{y:real^3}`; `0`; `e:real`] P2CM_CTX_LCK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_SING] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s0:real`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[]]);;


(* Copy-adapted from P2CR_CHART_UPTO (pc_p2c_fl514): the extension past the *)
(* final time 0 of [a,0] in every chart, with P2CD_UPTO_TOP_CTX (pc_p2c_lcn) *)
(* in place of P2CB_UPTO_CTX and P2BU_IDENT_AB in place of P2CR_IDENT.        *)

let P2BU_CHART_UPTO_TOP = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) sub g a c.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ p3_subseq sub /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
     (!a b K k e. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < e
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                                  ==> lck_dist2 k (metric_local atlas (chart_at atlas y) (g s))
                                        (metric_local atlas (chart_at atlas y)
                                           (p2cv_P V t Q atlas phi (sub n) s))
                                        (SND(chart_at atlas y) y) < e) /\
     a < &0 /\ real_interval[a,&0] SUBSET J /\ c IN atlas
     ==> ?e (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod).
           &0 < e /\
           smooth_map_on (interval(lift a,lift(&0 + e)) PCROSS IMAGE (SND c) (FST c)) Fx /\
           !s y. a < s /\ s <= &0 /\ y IN IMAGE (SND c) (FST c)
                 ==> Fx(pastecart (lift s) y) = vectorize(metric_local atlas c (g s) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "lck") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `&0`; `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`;
                 `\s y. metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) s) y`]
                P2CD_UPTO_TOP_CTX) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "rf" (MP_TAC o C MP (CONJ (ASSUME `a < &0`) (ASSUME `real_interval[a,&0] SUBSET J`)) o
                   SPECL [`a:real`; `&0`]) THEN
    REWRITE_TAC[ricci_flow_on] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)` o CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z0:B. z0 IN FST(c:(B->bool)#(B->real^3)) /\ SND c z0 = y0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. (z0:B) IN (W:num->B->bool) m` (X_CHOOSE_TAC `m:num`) THENL
   [UNDISCH_TAC `UNIONS {(W:num->B->bool) k | k IN (:num)} = topspace top` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `z0:B`) THEN
    SUBGOAL_THEN `(z0:B) IN topspace top` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `FST(c:(B->bool)#(B->real^3)) SUBSET topspace top` THEN
      UNDISCH_TAC `(z0:B) IN FST(c:(B->bool)#(B->real^3))` THEN SET_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `m:num`; `a:real`; `&0`; `sub:num->num`] P2CR_SEQHYP_SUB) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "sh")) THEN
  ABBREV_TAC `Vm = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
  SUBGOAL_THEN `open (Vm:real^3->bool) /\ (y0:real^3) IN Vm /\
                Vm SUBSET IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Vm" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `z0:B` THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Vm:real^3->bool`; `a:real`; `&0`;
                 `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s)`]
                P2CB_CTX_SEQHYP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Vm" THEN
    USE_THEN "sh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                       `cc:num->real^3`; `rr:num->real`; `sub':num->num`;
                       `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`Vm:real^3->bool`;
    `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
             (p2cv_P V t Q atlas (phi:num->B->A) ((sub:num->num) (N + n)) s)`;
    `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
    `cc:num->real^3`; `rr:num->real`; `sub':num->num`;
    `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "Vm" THEN
  MATCH_MP_TAC P2BU_IDENT_AB THEN
  MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `top:B topology`; `g0:B->real^3^3`;
                        `xl:B`; `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`;
                        `ee:num->real`; `cc:num->real^3`; `rr:num->real`;
                        `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[]);;


(* Copy-adapted from P2CO_FROM_SLICE_V (pc_p2c_fl515), with two more        *)
(* conjuncts: the limit flow is smooth up to time 0 (P2BU_CHART_UPTO_TOP in *)
(* every chart) and every point of the limit is joinable to xl.              *)

let P2BU_FROM_SLICE_UPTO = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q J (top:B topology) atlas g0 xl W phi.
     is_realinterval J /\ (&0) IN J /\
     (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
     (!n. p2c_regular_view (V n)) /\ (!n. x n IN topspace(rfs_vtop (V n) (t n))) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
              ==> ?CA N. !n. N <= n
                      ==> (!s. a <= s /\ s <= b
                               ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                   topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                          rfs_persists (V n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n + a / Q n) (t n + b / Q n) /\
                          !s y. a <= s /\ s <= b /\
                                y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n)
     ==> ?sub (top':B topology) atlas' g.
            p3_subseq sub /\
            p3_flow_limit_on (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) J (top',atlas') g xl /\
            (!s. s IN J ==> riemannian_metric atlas' (g s)) /\
            mfd_complete (top',atlas') (g (&0)) /\
            (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top',atlas') a b g) /\
            (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                      (!A. &0 < A
                           ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                           y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                           ==> p3_vrm (V n) (t n + s / Q n) y <= CI * Q n)
                      ==> !s. a <= s /\ s <= b ==> mfd_complete (top',atlas') (g s)) /\
            (!a. a < &0 /\ real_interval[a,&0] SUBSET J
                 ==> rfs_flow_upto (top',atlas') a (&0) g) /\
            (!y. y IN topspace top' ==> mfd_joinable (top',atlas') xl y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2CO_HYP_FROM_SLICE) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hyp") (CONJUNCTS_THEN2 (LABEL_TAC "rlim")
    (CONJUNCTS_THEN2 (LABEL_TAC "rcompl") (LABEL_TAC "rjoin")))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  USE_THEN "hyp" (MP_TAC o MATCH_MP P2CR_CORE) THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "flw") (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (LABEL_TAC "lck")))))))) THEN
  MAP_EVERY EXISTS_TAC
   [`sub:num->num`;
    `subtopology (top:B topology)
       {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
       {y | mfd_joinable (top:B topology,atlas) xl y}`;
    `g:real->B->real^3^3`] THEN
  SUBGOAL_THEN
   `!a. a < &0 /\ real_interval[a,&0] SUBSET J
        ==> rfs_flow_upto
              (subtopology (top:B topology)
                 {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y},
               restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                 {y | mfd_joinable (top:B topology,atlas) xl y}) a (&0) (g:real->B->real^3^3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real` THEN STRIP_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2BU_CHART_UPTO_TOP THEN
      MAP_EVERY EXISTS_TAC
       [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
        `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
        `subtopology (top:B topology)
           {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
        `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
           {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
        `xl:B`;
        `\k. (W:num->B->bool) k INTER
             {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
        `phi:num->B->A`; `sub:num->num`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
    MAP_EVERY EXISTS_TAC
     [`\k. (W:num->B->bool) k INTER
           {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
      `(phi:num->B->A) o (sub:num->num)`] THEN
    USE_THEN "flw" ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `CI:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CIh")))) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`;
                 `x:num->A`; `t:num->real`; `Q:num->real`;
                 `subtopology (top:B topology)
                    {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                 `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                    {y | mfd_joinable (top:B topology,atlas) xl y}`;
                 `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
                    {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
                 `xl:B`;
                 `\k. (W:num->B->bool) k INTER
                      {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
                 `phi:num->B->A`; `a:real`; `b:real`; `CI:real`] P2CO_CI_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_TAC] THEN
  MATCH_MP_TAC P2CO_COMPLETE_ON THEN
  MAP_EVERY EXISTS_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `J:real->bool`;
    `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
       {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
    `xl:B`;
    `\k. (W:num->B->bool) k INTER
         {y | mfd_joinable (top:B topology,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `phi:num->B->A`; `sub:num->num`; `CI:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The same for the rescaled histories of Thm 5.15 along a subsequence      *)
(* carrying a slice limit at the base time.                                  *)


(* ------------------------------------------------------------------------- *)
(* Pinching (rfs_pinched, Hamilton-Ivey) bounds |Rm| by the scalar           *)
(* curvature: |Rm| <= 2|R| + 2 exp 4 (RFA_PINCH_RM, pc_rfa_pinchrm), and R   *)
(* >= -6 at times t >= 0; so R <= K Q with Q >= 1 gives |Rm| <= (2 K + 12 +  *)
(* 2 exp 4) Q.                                                               *)
(* ------------------------------------------------------------------------- *)

let P2BU_VIEW_PINCH_RM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     p2c_regular_view V /\ rfs_pinched V /\ &0 <= t /\ x IN topspace(rfs_vtop V t)
     ==> p3_vrm V t x <= &2 * abs(rfs_vscalar V t x) + &2 * exp(&4) /\
         --(&6) <= rfs_vscalar V t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t (x:A)` MP_TAC THENL
   [UNDISCH_TAC `rfs_pinched (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3))` THEN
    REWRITE_TAC[P2CP_PINCHED_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[p3_vrm; P2B9_RFS_VSCALAR] THEN MATCH_MP_TAC RFA_PINCH_RM THEN
    MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) t`; `t:real`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `rfs_pinched_at (rfs_vatlas V t) (rfs_vmetric V t) t (x:A)` THEN
    REWRITE_TAC[rfs_pinched_at; P2B9_RFS_VSCALAR] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REAL_ARITH `--(&6) <= a ==> a <= r ==> --(&6) <= r`) THEN
    REWRITE_TAC[REAL_ARITH `--(&6) <= --(&6) / y <=> &6 / y <= &6`] THEN
    SUBGOAL_THEN `&1 <= &4 * t + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= y ==> &0 < y`] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BU_VIEW_PINCH_RM_Q = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x K Q.
     p2c_regular_view V /\ rfs_pinched V /\ &0 <= t /\ x IN topspace(rfs_vtop V t) /\
     &0 <= K /\ &1 <= Q /\ rfs_vscalar V t x <= K * Q
     ==> p3_vrm V t x <= (&2 * K + &12 + &2 * exp(&4)) * Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t:real`; `x:A`] P2BU_VIEW_PINCH_RM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * abs(rfs_vscalar V t (x:A)) + &2 * exp(&4)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < exp(&4)` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(rfs_vscalar V t (x:A)) <= K * Q + &6` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= K * Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&4) <= exp(&4) * Q` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Cor 11.3 at one point.  If the derivative bounds of canonical          *)
(* neighbourhoods hold wherever R >= 4 Q at times <= t0 and an open set W    *)
(* around y persists over (t0 - tau, t0], then (Lemma 11.2,                  *)
(* P2C_LEMMA_11_2_DB with r0^-2 = 4 Q) R(y,s) <= 2 (max(0,R(y,t0)) + 4 Q)    *)
(* for t0 - Delta < s <= t0, Delta = min tau (1/(16 C (max(0,R) + 4Q))).     *)
(* ------------------------------------------------------------------------- *)

let P2BU_COR_11_3_POINT = prove
 (`!(u:A->bool) V C Q t0 y W tau.
     P2C_LEMMA_11_2_DB_STATEMENT u /\
     p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) /\
     &0 < C /\ &0 < Q /\ &0 < tau /\
     (!x s. s <= t0 /\ x IN topspace(rfs_vtop V s) /\ &4 * Q <= rfs_vscalar V s x
            ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V s) (rfs_vmetric V s) x) <=
                C * rfs_vscalar V s x * sqrt(rfs_vscalar V s x) /\
                abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) x) <=
                C * rfs_vscalar V s x pow 2) /\
     y IN W /\ open_in (rfs_vtop V t0) W /\ rfs_persists V W (t0 - tau) t0
     ==> !s. t0 - min tau (inv(&16 * C * (max (&0) (rfs_vscalar V t0 y) + &4 * Q))) < s /\
             s <= t0
             ==> rfs_vscalar V s y <= &2 * (max (&0) (rfs_vscalar V t0 y) + &4 * Q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "db") STRIP_ASSUME_TAC)))))) THEN
  REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN DISCH_THEN(LABEL_TAC "l112") THEN
  ABBREV_TAC `R0 = max (&0) (rfs_vscalar V t0 (y:A))` THEN
  ABBREV_TAC `D = min tau (inv(&16 * C * (R0 + &4 * Q)))` THEN
  SUBGOAL_THEN `&0 < R0 + &4 * Q` ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D /\ D <= tau /\ D <= inv(&16 * C * (R0 + &4 * Q))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the slice at t0 and a small ball about y inside W *)
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop V t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:A). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t0`;
                 `W:A->bool`; `y:A`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rw:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r' = min rw (inv(&2 * C * sqrt(max (rfs_vscalar V t0 (y:A)) (&4 * Q))))` THEN
  SUBGOAL_THEN `inv((inv(&2 * sqrt Q)) pow 2) = &4 * Q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r'` ASSUME_TAC THENL
   [EXPAND_TAC "r'" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vball V t0 (y:A) r' SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball V t0 (y:A) rw` THEN
    ASM_REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN
    EXPAND_TAC "r'" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists V (rfs_vball V t0 (y:A) r') (t0 - D) t0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN EXISTS_TAC `W:A->bool` THEN
    EXISTS_TAC `t0:real` THEN ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `rfs_persists V (W:A->bool) (t0 - tau) t0` THEN
      REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "l112" (MP_TAC o SPECL
    [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `C:real`; `inv(&2 * sqrt Q)`; `y:A`; `t0:real`; `t0 - D`; `r':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`z:A`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "db" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s <= max t0 (t0 - D)` THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "r'" THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ARITH `abs(t0 - D - t0) = abs D`] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < D ==> abs D = D`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `min t0 (t0 - D) = t0 - D /\ max t0 (t0 - D) = t0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `min t0 (t0 - D) = t0 - D /\ max t0 (t0 - D) = t0`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t0`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) t0`;
                   `y:A`; `r':real`] MFD_CENTRE_IN_BALL) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

(* Strong canonical neighbourhoods are canonical neighbourhoods of the slice; *)
(* with P2C_CANON_DERIV they give the derivative bounds of Lemma 11.2.       *)

let P2BU_STRONG_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U.
     rfs_strong_canonical V C eps x t U
     ==> rfs_canonical_nbhd (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps x U`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[rfs_strong_canonical; rfs_canonical_nbhd; rfs_vtop; rfs_vatlas; rfs_vmetric;
              rfs_strong_neck; rfs_evolving_neck] THEN
  MESON_TAC[]);;

let P2BU_CANON_DB = prove
 (`!u:A->bool.
     P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !V C eps y s.
              p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ y IN topspace(rfs_vtop V s) /\
              p3_canon_at V C eps y s
              ==> &0 < rfs_vscalar V s y /\
                  sqrt(rfs_scalar_grad2 (rfs_vatlas V s) (rfs_vmetric V s) y) <=
                  max C (&2) * rfs_vscalar V s y * sqrt(rfs_vscalar V s y) /\
                  abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) y +
                      &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) y) <=
                  max C (&2) * rfs_vscalar V s y pow 2`,
  GEN_TAC THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `C:real`; `eps:real`; `y:A`; `s:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `s:real`; `y:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p3_canon_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) C eps y s` THEN
  REWRITE_TAC[p3_canon_at] THEN DISCH_THEN(X_CHOOSE_THEN `U:A->bool` MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP P2BU_STRONG_SLICE) THEN
  REWRITE_TAC[P2B9_RFS_VSCALAR] THEN
  USE_THEN "cd" MATCH_MP_TAC THEN EXISTS_TAC `rfs_vtop (V:(real->A topology)#
    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s` THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `U:A->bool`] THEN ASM_REWRITE_TAC[]);;

(* A union of persisting open sets persists: an open B all of whose points  *)
(* lie in open sets persisting over (a,t0] persists over (a,t0].            *)

let P2BU_BALL_PERSIST_UNION = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) B a t0.
     p2c_regular_view V /\ open_in (rfs_vtop V t0) B /\ ~(B = {}) /\ a < t0 /\
     (!y. y IN B ==> ?W. y IN W /\ open_in (rfs_vtop V t0) W /\ rfs_persists V W a t0)
     ==> rfs_persists V B a t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2cz_from_smooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CR_REGULAR_FROM_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
      is_neg(concl th))) THEN
    DISCH_THEN(X_CHOOSE_TAC `y0:A`) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y0:A) IN B`) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `B:A->bool`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W a t0` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:A) IN B`) o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `B:A->bool`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(B:A->bool) INTER W` THEN
  ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC P2CO_OPEN_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `t0:real`; `t0:real`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W a t0` THEN
  REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  ASM_SIMP_TAC[]);;

(* One point of the ball (the per-point part of P2BU_REGION_BOUND). *)

let P2BU_REGION_POINT = prove
 (`!(u:A->bool) V C t0 y Q D mu dl.
     P2C_LEMMA_11_2_DB_STATEMENT u /\
     p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) /\
     &0 < C /\ &0 <= D /\ &0 < mu /\ &0 < Q /\
     dl = min (mu / max (&1) D) (inv(&16 * C * (D + &4))) /\
     (!y s. s <= t0 /\ y IN topspace(rfs_vtop V s) /\ &4 * Q <= rfs_vscalar V s y
            ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V s) (rfs_vmetric V s) y) <=
                C * rfs_vscalar V s y * sqrt(rfs_vscalar V s y) /\
                abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) y +
                    &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) y) <=
                C * rfs_vscalar V s y pow 2) /\
     rfs_vscalar V t0 y <= D * Q /\
     p2c_local_persist V y (t0 - mu * inv(max Q (rfs_vscalar V t0 y))) t0
     ==> ?W. y IN W /\ open_in (rfs_vtop V t0) W /\ rfs_persists V W (t0 - dl / Q) t0 /\
             !s. t0 - dl / Q < s /\ s <= t0
                 ==> rfs_vscalar V s y <= &2 * (D + &4) * Q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "db") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))) THEN
  SUBGOAL_THEN `&0 < dl /\ dl <= mu / max (&1) D /\ dl <= inv(&16 * C * (D + &4))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl / Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `dl:real`)) THEN
  REWRITE_TAC[p2c_local_persist] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tau = mu * inv(max Q (rfs_vscalar V t0 (y:A)))` THEN
  SUBGOAL_THEN `&0 < max Q (rfs_vscalar V t0 (y:A)) /\
                max Q (rfs_vscalar V t0 (y:A)) <= max (&1) D * Q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MAX_LE] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * Q` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tau /\ dl / Q <= tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(mu / max (&1) D) / Q` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop V t0) (W:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) (t0 - tau) t0` THEN
    REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CD_PERSISTS_MONO THEN EXISTS_TAC `t0 - tau` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)`;
                 `C:real`; `Q:real`; `t0:real`; `y:A`; `W:A->bool`; `tau:real`]
                P2BU_COR_11_3_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:A`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "db" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (max (&0) (rfs_vscalar V t0 (y:A)) + &4 * Q)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `!dq. dq <= m /\ t0 - dq < s ==> t0 - m < s`) THEN
    EXISTS_TAC `dl / Q` THEN REWRITE_TAC[REAL_LE_MIN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&16 * C * (D + &4)) / Q` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ]; ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < max (&0) (rfs_vscalar V t0 (y:A)) + &4 * Q` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `max (&0) (rfs_vscalar V t0 (y:A)) <= D * Q` MP_TAC THENL
     [REWRITE_TAC[REAL_MAX_LE] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN `max (&0) (rfs_vscalar V t0 (y:A)) <= D * Q` MP_TAC THENL
     [REWRITE_TAC[REAL_MAX_LE] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* MT Cor 11.3 on a ball: if R <= D Q on B(x,t0,A Q^-1/2) (Q = R(x,t0)) and  *)
(* every point of the ball has a neighbourhood persisting back for          *)
(* mu / max(Q,R(y)) (MT 11.1 (5)), then the ball persists back for dl / Q   *)
(* and R <= 2 (D + 4) Q on it, dl = min (mu / max 1 D) (1/(16 C (D + 4))).    *)

let P2BU_REGION_BOUND = prove
 (`!(u:A->bool) V C t0 x A D mu.
     P2C_LEMMA_11_2_DB_STATEMENT u /\
     p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) /\
     &0 < C /\ &0 < A /\ &0 <= D /\ &0 < mu /\ &0 < rfs_vscalar V t0 x /\
     x IN topspace(rfs_vtop V t0) /\
     (!y s. s <= t0 /\ y IN topspace(rfs_vtop V s) /\
            &4 * rfs_vscalar V t0 x <= rfs_vscalar V s y
            ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V s) (rfs_vmetric V s) y) <=
                C * rfs_vscalar V s y * sqrt(rfs_vscalar V s y) /\
                abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) y +
                    &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) y) <=
                C * rfs_vscalar V s y pow 2) /\
     (!y. y IN rfs_vball V t0 x (A * inv(sqrt(rfs_vscalar V t0 x)))
          ==> rfs_vscalar V t0 y <= D * rfs_vscalar V t0 x /\
              p2c_local_persist V y
                (t0 - mu * inv(max (rfs_vscalar V t0 x) (rfs_vscalar V t0 y))) t0)
     ==> rfs_persists V (rfs_vball V t0 x (A * inv(sqrt(rfs_vscalar V t0 x))))
           (t0 - min (mu / max (&1) D) (inv(&16 * C * (D + &4))) / rfs_vscalar V t0 x) t0 /\
         !s y. t0 - min (mu / max (&1) D) (inv(&16 * C * (D + &4))) / rfs_vscalar V t0 x < s /\
               s <= t0 /\ y IN rfs_vball V t0 x (A * inv(sqrt(rfs_vscalar V t0 x)))
               ==> rfs_vscalar V s y <= &2 * (D + &4) * rfs_vscalar V t0 x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "db") (LABEL_TAC "ball")))))))))) THEN
  ABBREV_TAC `Q = rfs_vscalar V t0 (x:A)` THEN
  ABBREV_TAC `B = rfs_vball V t0 (x:A) (A * inv(sqrt Q))` THEN
  ABBREV_TAC `dl = min (mu / max (&1) D) (inv(&16 * C * (D + &4)))` THEN
  SUBGOAL_THEN `&0 < dl /\ dl <= mu / max (&1) D /\ dl <= inv(&16 * C * (D + &4))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dl / Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the per-point bound *)
  SUBGOAL_THEN
   `!y. y IN B
        ==> ?W. y IN W /\ open_in (rfs_vtop V t0) W /\ rfs_persists V W (t0 - dl / Q) t0 /\
                !s. t0 - dl / Q < s /\ s <= t0
                    ==> rfs_vscalar V s (y:A) <= &2 * (D + &4) * Q`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "ball" (MP_TAC o C MATCH_MP (ASSUME `(y:A) IN B`) o REWRITE_RULE
      [ASSUME `rfs_vscalar V t0 (x:A) = Q`; ASSUME `rfs_vball V t0 (x:A) (A * inv(sqrt Q)) = B`]) THEN
    STRIP_TAC THEN MATCH_MP_TAC P2BU_REGION_POINT THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `C:real`; `mu:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "dl" THEN REWRITE_TAC[];
      USE_THEN "db" (fun th -> REWRITE_TAC[REWRITE_RULE[ASSUME `rfs_vscalar V t0 (x:A) = Q`] th])];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BU_BALL_PERSIST_UNION THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `t0:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[P2CO_VBALL] THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `t0:real`; `x:A`] P2C_REGULAR_SLICE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(y:A) IN B`)) THEN MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(y:A) IN B`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Copy-adapted from P2CW_REGION_BALL_COMPACT (pc_p2c_fl511): compact       *)
(* closure of W in place of a compact slice.                                 *)

let P2BU_REGION_BALL_COMPACT_CC = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W y r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top (top closure_of W) /\
     open_in top W /\ &0 < r /\ mfd_ball (top,atlas) g y (&2 * r) SUBSET W
     ==> compact_in (subtopology top W)
           (subtopology top W closure_of
            mfd_ball (subtopology top W,restrict_atlas atlas W) (restrict_metric atlas W g) y r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = mfd_ball (subtopology top W,
                            restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) W)
                           (restrict_metric atlas W (g:A->real^3^3)) (y:A) r` THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) y r` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2CW_RESTRICT_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (S:A->bool) SUBSET mfd_ball (top,atlas) (g:A->real^3^3) y (&2 * r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) y r` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) y r` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET W` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) W`;
                   `restrict_metric (atlas:((A->bool)#(A->real^3))->bool) W g`; `y:A`; `r:real`]
           P2CU_BALL_SUBSET) THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(W:A->bool) INTER S = S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) INTER (top closure_of S) = top closure_of S` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `(top:A topology) closure_of W` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W:A->bool` THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
      ASM_REWRITE_TAC[]];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shi's estimate on regular views (the region flow of the persisting ball   *)
(* B(x0,4 R / sqrt q) over (a,b], at the points of B(x0,R / sqrt q), compact *)
(* slice), and MT Thm 5.11.                                                  *)
(* ------------------------------------------------------------------------- *)


(* Copy-adapted from P2CW_SHI_VIEW (pc_p2c_fl511): compact closure of the    *)
(* ball B(x0,4 R / sqrt q) at time b in place of a compact slice.             *)

let P2BU_SHI_VIEW_CC = prove
 (`!l K R tau.
     &0 < K /\ &0 < R /\ &0 < tau
     ==> ?C. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) x0 a b q y.
               p2c_regular_view V /\
               compact_in (rfs_vtop V b)
                 (rfs_vtop V b closure_of rfs_vball V b x0 ((&4 * R) * inv(sqrt q))) /\
               x0 IN topspace(rfs_vtop V b) /\ &0 < q /\ a < b /\ tau <= q * (b - a) /\
               rfs_persists V (rfs_vball V b x0 ((&4 * R) * inv(sqrt q))) a b /\
               (!s z. a < s /\ s <= b /\ z IN rfs_vball V b x0 ((&4 * R) * inv(sqrt q))
                      ==> p3_vrm V s z <= K * q) /\
               y IN rfs_vball V b x0 (R * inv(sqrt q))
               ==> p3_vderiv2 V l b y <= C * q pow (l + 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `K:real`; `R:real`; `tau:real`] P2CW_SHI_SCALED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "shi")) THEN
  EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x0:A`; `a:real`; `b:real`; `q:real`; `y:A`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `b:real`; `x0:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R * inv(sqrt q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * R) * inv(sqrt q) = &4 * (R * inv(sqrt q))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `r = R * inv(sqrt q)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[P2C_VIEW_EXPAND]) THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(&4 * R) * inv(sqrt q) = &4 * r`]) THEN
  ABBREV_TAC `W = mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) (&4 * r)` THEN
  SUBGOAL_THEN `p2c_vflow (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W a b`
  MP_TAC THENL
   [MATCH_MP_TAC P2C_REGULAR_VFLOW THEN ASM_REWRITE_TAC[P2C_VIEW_EXPAND]; ALL_TAC] THEN
  REWRITE_TAC[p2c_vflow; P2C_VIEW_EXPAND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) b) W`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) r SUBSET W /\
    mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (y:A) (&2 * r) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_ball (rfs_vtop V b,rfs_vatlas V b) (rfs_vmetric V b) (x0:A) (r + &2 * r)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CU_BALL_SHIFT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) W b b =
                restrict_metric (rfs_vatlas V b) W (rfs_vmetric V b)`
  ASSUME_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `l:num`; `y:A`]
         P2CW_VFAM_DERIV_LAST) THEN
  ASM_REWRITE_TAC[P2C_VIEW_EXPAND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "shi" (MP_TAC o SPECL
   [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b) W`;
    `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b) W`;
    `a:real`; `b:real`;
    `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) W b`;
    `y:A`; `q:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    MATCH_MP_TAC P2BU_REGION_BALL_COMPACT_CC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN W` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_metric (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
                        (rfs_vmetric V b)`; `y:A`; `r:real`] P2CU_BALL_SUBSET) THEN
      ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) s z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CW_VFAM_RM_NORM_LE THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[P2C_VIEW_EXPAND];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:A) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[]]]);;

(* MT Thm 5.11 on the carrier real^3 from the regularity of history views. *)


(* ------------------------------------------------------------------------- *)
(* The blow-up sequence: Thm 10.2 (A2) bounds R by D Q n on the rescaled    *)
(* balls at t n; then Cor 11.3 (P2BU_REGION_BOUND, with the derivative     *)
(* bounds of P2BU_CANON_DB above 4 Q n) and pinching give persistence back *)
(* for dl / Q n and |Rm| <= K Q n on them.                                  *)
(* ------------------------------------------------------------------------- *)

let P2BU_SEQ_D = prove
 (`!u:A->bool.
     P2C_REQ_THM_10_2_VIEW_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t A.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\ &0 < A
              ==> ?D N. &0 < D /\
                        !n y. N <= n /\
                              y IN rfs_vball (V n) (t n) (x n)
                                     (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                              ==> rfs_vscalar (V n) (t n) y <=
                                  D * rfs_vscalar (V n) (t n) (x n)`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_THM_10_2_VIEW_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a2"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `A:real`] THEN
  REWRITE_TAC[p2c_vblowup_seq] THEN STRIP_TAC THEN
  USE_THEN "a2" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real` (X_CHOOSE_THEN `D:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `D0:real` o check (fun th ->
    can (term_match [] `!B. ?N. !n. N <= n ==> B < (f:num->real) n`) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`D:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "dd" (MP_TAC o SPECL
    [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
          (real->A->real^3^3)) n`; `(x:num->A) n`; `(t:num->real) n`]) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
      can (term_match [] `!n:num. p2c_regular_view ((V:num->(real->A topology)#
             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\ P n`)
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `D0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Persistence of a nonempty set over (a,b] in a view whose slices are empty *)
(* before 0 forces a >= 0 on (a,b], i.e. every time s in (a,b] is >= 0.     *)

let P2BU_PERSIST_NONNEG = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) B a b s z.
     rfs_persists V B a b /\ z IN B /\ a < s /\ s <= b /\
     (!s. s < &0 ==> rfs_vtop V s = discrete_topology {})
     ==> &0 <= s /\ B SUBSET topspace(rfs_vtop V s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2CO_PERSISTS_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(B:A->bool) SUBSET topspace(rfs_vtop V s)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `open_in:(A)topology->(A->bool)->bool`))
                               (concl th))) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `(B:A->bool) SUBSET topspace(rfs_vtop V s)` THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `s < &0`) o SPEC `s:real` o check (fun th ->
    can (find_term ((=) `discrete_topology:(A->bool)->A topology`)) (concl th))) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN
  UNDISCH_TAC `(z:A) IN B` THEN SET_TAC[]);;

(* MT Cor 11.3 along the blow-up sequence: for each A, given R <= D Q n on  *)
(* the A-balls at t n (from A2, or uniformly after Claim 11.7), eventually  *)
(* the A-ball persists back for dl / Q n and R, |Rm| are bounded there.    *)

let P2BU_SEQ_REGION = prove
 (`!u:A->bool.
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t A D.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              &0 < A /\ &0 <= D /\
              (?N. !n y. N <= n /\
                         y IN rfs_vball (V n) (t n) (x n)
                                (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                         ==> rfs_vscalar (V n) (t n) y <= D * rfs_vscalar (V n) (t n) (x n))
              ==> ?N. !n. N <= n
                     ==> &1 <= rfs_vscalar (V n) (t n) (x n) /\
                         rfs_persists (V n)
                           (rfs_vball (V n) (t n) (x n)
                              (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                           (t n - min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4))) /
                                  rfs_vscalar (V n) (t n) (x n)) (t n) /\
                         !s y. t n - min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4))) /
                                     rfs_vscalar (V n) (t n) (x n) < s /\
                               s <= t n /\
                               y IN rfs_vball (V n) (t n) (x n)
                                      (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                               ==> &0 <= s /\ y IN topspace(rfs_vtop (V n) s) /\
                                   rfs_vscalar (V n) s y <=
                                   &2 * (D + &4) * rfs_vscalar (V n) (t n) (x n) /\
                                   p3_vrm (V n) s y <=
                                   (&2 * (&2 * (D + &4)) + &12 + &2 * exp(&4)) *
                                   rfs_vscalar (V n) (t n) (x n)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2BU_CANON_DB) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cdb"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `A:real`; `D:real`] THEN
  REWRITE_TAC[p2c_vblowup_seq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `N1:num` (LABEL_TAC "D")))))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (LABEL_TAC "noncoll"))))))) THEN
  USE_THEN "Qinf" (X_CHOOSE_TAC `N2:num` o SPEC `&1`) THEN
  USE_THEN "noncoll" (X_CHOOSE_THEN `N3:num` (LABEL_TAC "nc") o SPEC `A:real`) THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `Q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (t n) (x n)` THEN
  SUBGOAL_THEN `&1 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MP_TAC(ISPECL [`u:A->bool`;
                 `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) n`;
                 `max C (&2)`; `(t:num->real) n`; `(x:num->A) n`; `A:real`; `D:real`; `mu:real`]
                P2BU_REGION_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:A`; `s:real`] THEN STRIP_TAC THEN
      USE_THEN "cdb" (MP_TAC o SPECL
        [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) n`; `C:real`; `eps:real`; `y:A`; `s:real`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "canon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [EXPAND_TAC "Q" THEN USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC;
        EXPAND_TAC "Q" THEN USE_THEN "nc" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `N1 + N2 + N3 <= n:num` THEN ARITH_TAC;
          SIMP_TAC[]]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rb")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) n`;
                 `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) n) (t n) (x n) (A * inv(sqrt Q))`;
                 `(t:num->real) n - min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4))) / Q`;
                 `(t:num->real) n`; `s:real`; `y:A`] P2BU_PERSIST_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_vscalar ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s y <=
                &2 * (D + &4) * Q` ASSUME_TAC THENL
   [USE_THEN "rb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) n`; `s:real`; `y:A`; `&2 * (D + &4)`; `Q:real`]
                P2BU_VIEW_PINCH_RM_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Curvature at a point of a flow limit is the limit of the rescaled         *)
(* curvature of the approximants at phi k y0 (scalar curvature, and          *)
(* sectional curvature plane by plane), from the C^2 closeness at y0         *)
(* (APX_SCALAR_STABILITY_LIP, APX_SECTIONAL_STABILITY_LIP) and the chart     *)
(* formulas P2CP_APPROX_CURV of pc_p2c_t533.                                 *)
(* ------------------------------------------------------------------------- *)

let P2BU_POINT_CURV = prove
 (`!V x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s0 y0 e.
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3))) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     s0 IN J /\ y0 IN topspace top /\ &0 < e
     ==> ?N. !k. N <= k
                 ==> phi k y0 IN topspace(rfs_vtop (V k) (t k + s0 / Q k)) /\
                     abs(mfd_scalar atlas (g s0) y0 -
                         mfd_scalar (rfs_vatlas (V k) (t k + s0 / Q k))
                                    (rfs_vmetric (V k) (t k + s0 / Q k)) (phi k y0) / Q k) < e /\
                     !u v. ~collinear {vec 0,u,v}
                           ==> ?u' v'. ~collinear {vec 0,u',v'} /\
                                       abs(mfd_sectional atlas (g s0) y0 u v -
                                           mfd_sectional (rfs_vatlas (V k) (t k + s0 / Q k))
                                             (rfs_vmetric (V k) (t k + s0 / Q k))
                                             (phi k y0) u' v' / Q k) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv"))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0)` ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S0 = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                         (FST(chart_at atlas y0))` THEN
  ABBREV_TAC `G0 = metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas (y0:B))
                     ((g:real->B->real^3^3) s0)` THEN
  ABBREV_TAC `yc = SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)) y0` THEN
  SUBGOAL_THEN `metric_field (S0:real^3->bool) (G0:real^3->real^3^3) /\ (yc:real^3) IN S0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "G0"; "yc"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->B->real^3^3) s0)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) s0) y0 = lscalar (G0:real^3->real^3^3) yc /\
                !u v. mfd_sectional atlas ((g:real->B->real^3^3) s0) y0 u v =
                      lsectional (G0:real^3->real^3^3) yc u v`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["G0"; "yc"] THEN REWRITE_TAC[mfd_scalar; mfd_sectional]; ALL_TAC] THEN
  (* a frame and a bound for the curvature of the limit at yc *)
  MP_TAC(ISPECL [`S0:real^3->bool`; `G0:real^3->real^3^3`; `yc:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K1 = max (&1) (lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc)` THEN
  SUBGOAL_THEN `&1 <= K1 /\ lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc <= K1 pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max (&1) (lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC P2CP_LE_POW2 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 4 (S0:real^3->bool) (lrm4 (G0:real^3->real^3^3))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S0:real^3->bool`; `G0:real^3->real^3^3`] LRM4_TENSOR_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. abs(lrm4 (G0:real^3->real^3^3) yc a) <=
        abs K1 * norm((M:real^3^3) ** a 1) * norm(M ** a 2) * norm(M ** a 3) * norm(M ** a 4)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:num->real^3` THEN
    MP_TAC(ISPECL [`4`; `S0:real^3->bool`; `G0:real^3->real^3^3`; `lrm4 (G0:real^3->real^3^3)`;
                   `yc:real^3`; `M:real^3^3`; `a:num->real^3`; `K1 pow 2`]
                  LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4; POW_2_SQRT_ABS] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc <= K1 pow 2` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S0:real^3->bool`; `G0:real^3->real^3^3`; `yc:real^3`; `M:real^3^3`;
                 `abs(K1:real)`] LRG_RM0_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_THEN(LABEL_TAC "RM0") THEN
  (* the closeness needed *)
  ABBREV_TAC `delta = min (&1 / &10) (e / (&73 * (&1 + abs K1)))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ &8 * (&1 + abs K1) * delta < e /\
                &8 * &9 * (&1 + abs K1) * delta < e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + abs K1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `delta <= e / (&73 * (&1 + abs K1))` MP_TAC THENL
     [EXPAND_TAC "delta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / (&73 * (&1 + abs K1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &73`] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "delta" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
       [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (&1 + abs K1) * delta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `delta * &73 * (&1 + abs K1) <= e` THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
       [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (&1 + abs K1) * delta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `delta * &73 * (&1 + abs K1) <= e` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`s0:real`; `s0:real`; `{y0:B}`; `2`; `delta pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET; COMPACT_IN_SING] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[SING_SUBSET]) (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `psi:A->B` o
     C MP (CONJ (SPEC `s0:real` REAL_LE_REFL) (SPEC `s0:real` REAL_LE_REFL)) o SPEC `s0:real`)
    (MP_TAC o SPECL [`s0:real`; `y0:B`]))) THEN
  REWRITE_TAC[REAL_LE_REFL; IN_SING] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `tau = (t:num->real) k + s0 / Q k` THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the slice at tau *)
  SUBGOAL_THEN `(phi:num->B->A) k y0 IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)
                   ((W:num->B->bool) k) (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                   (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi` THEN
    REWRITE_TAC[mfd_diffeo] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE ((phi:num->B->A) k) (W k) SUBSET topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)`
    MP_TAC THENL [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `tau:real`; `(phi:num->B->A) k y0`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the approximant at yc *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `(Q:num->real) k`;
                 `y0:B`] P2CP_APPROX_CURV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Gk = \z. (Q:num->real) k %%
                   rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau)
                     ((phi:num->B->A) k o chart_inv (chart_at (atlas:((B->bool)#(B->real^3))->bool)
                                                         (y0:B)))
                     (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) tau) z` THEN
  ABBREV_TAC `S = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                        (FST(chart_at atlas y0) INTER (W:num->B->bool) k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "scal") (LABEL_TAC "sect")))) THEN
  (* C^2 closeness at yc *)
  SUBGOAL_THEN `metric_field (S:real^3->bool) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `S0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["S"; "S0"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) < delta /\
                &0 <= sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 * (&1 + abs K1) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) <=
                &8 * (&1 + abs K1) * delta /\
                &8 * &9 * (&1 + abs K1) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) <=
                &8 * &9 * (&1 + abs K1) * delta` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`K1:real`; `S:real^3->bool`; `G0:real^3->real^3^3`; `Gk:real^3->real^3^3`;
                   `yc:real^3`] APX_SCALAR_STABILITY_LIP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    USE_THEN "scal" (fun th -> REWRITE_TAC[SYM th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  USE_THEN "sect" (MP_TAC o C MP (ASSUME `~collinear {vec 0,u:real^3,v}`) o
                   SPECL [`u:real^3`; `v:real^3`]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u':real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v':real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G0:real^3->real^3^3`; `Gk:real^3->real^3^3`; `yc:real^3`;
                 `M:real^3^3`; `abs(K1:real)`] APX_SECTIONAL_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `lsectional (Gk:real^3->real^3^3)`)) (rhs(concl th)))) THEN
  ASM_REAL_ARITH_TAC);;

(* Separation of 2-spheres passes to slice limits: P2B_SEP_EMBED_CORE       *)
(* (pc_p2b_lim) applied to the exhaustion and the time-0 diffeomorphisms.   *)

let P2BU_SEP_SLICE = prove
 (`!V x t Q (top:B topology) atlas g xl W (phi:num->B->A).
     p2c_slice_limit_with (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) x t Q (top,atlas) g xl W phi /\
     (!k. smooth_manifold_atlas (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k)) /\
          apx_sphere_sep (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k)))
     ==> apx_sphere_sep top atlas`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_slice_limit_with] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B_SEP_EMBED_CORE THEN
  MAP_EVERY EXISTS_TAC
   [`W:num->B->bool`; `phi:num->B->A`;
    `\k. rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k) (t k)`;
    `\k. rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) k) (t k)`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o check (fun th ->
    can (term_match [] `!k:num. open_in (top:B topology) ((W:num->B->bool) k) /\ P k`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(top:B topology) closure_of (W:num->B->bool) k` THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBSET; OPEN_IN_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The region facts for every radius (A2 + Cor 11.3), Shi's derivative       *)
(* bounds at t n (Cor 11.4) and the volume bound at x n (Claim 11.5), the    *)
(* hypotheses of the Cheeger-Gromov compactness T1.                          *)
(* ------------------------------------------------------------------------- *)

let P2BU_SEQ_REGION_ALL = prove
 (`!u:A->bool.
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s))
              ==> !A. &0 < A
                      ==> ?dl K N. &0 < dl /\ &0 < K /\
                            !n. N <= n
                                ==> &1 <= rfs_vscalar (V n) (t n) (x n) /\
                                    rfs_persists (V n)
                                      (rfs_vball (V n) (t n) (x n)
                                         (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                                      (t n - dl / rfs_vscalar (V n) (t n) (x n)) (t n) /\
                                    !s y. t n - dl / rfs_vscalar (V n) (t n) (x n) < s /\
                                          s <= t n /\
                                          y IN rfs_vball (V n) (t n) (x n)
                                                 (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                                          ==> &0 <= s /\ y IN topspace(rfs_vtop (V n) s) /\
                                              p3_vrm (V n) s y <=
                                              K * rfs_vscalar (V n) (t n) (x n)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_SEQ_D) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sd"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_SEQ_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sr"))) THEN
  EXISTS_TAC `min e1 e2` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LE_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`] THEN STRIP_TAC THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  USE_THEN "sd" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `A:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC)) THEN
  USE_THEN "sr" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `A:real`; `D:real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXISTS_TAC `N1:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  MAP_EVERY EXISTS_TAC
   [`min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4)))`;
    `&2 * (&2 * (D + &4)) + &12 + &2 * exp(&4)`; `N:num`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN
      UNDISCH_TAC `p2c_vblowup_seq (C,eps,kappa,r0,mu)
                     (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) x t` THEN
      REWRITE_TAC[p2c_vblowup_seq] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N" (MP_TAC o C MATCH_MP (ASSUME `N <= n:num`)) THEN MESON_TAC[]]);;

(* Shi's derivative bounds at t n on the rescaled balls (MT Cor 11.4), from *)
(* the region facts at radius 4 A and the compact closure of the 4A-ball.  *)

let P2BU_SEQ_SHI = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
           (real->A->real^3^3)) x t.
     (!n. p2c_regular_view (V n) /\
          x n IN topspace(rfs_vtop (V n) (t n))) /\
     (!A. &0 < A
          ==> ?dl K N. &0 < dl /\ &0 < K /\
                !n. N <= n
                    ==> &1 <= rfs_vscalar (V n) (t n) (x n) /\
                        rfs_persists (V n)
                          (rfs_vball (V n) (t n) (x n)
                             (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                          (t n - dl / rfs_vscalar (V n) (t n) (x n)) (t n) /\
                        !s y. t n - dl / rfs_vscalar (V n) (t n) (x n) < s /\ s <= t n /\
                              y IN rfs_vball (V n) (t n) (x n)
                                     (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                              ==> &0 <= s /\ y IN topspace(rfs_vtop (V n) s) /\
                                  p3_vrm (V n) s y <= K * rfs_vscalar (V n) (t n) (x n)) /\
     (!A. ?N. !n. N <= n
                  ==> compact_in (rfs_vtop (V n) (t n))
                        (rfs_vtop (V n) (t n) closure_of
                         rfs_vball (V n) (t n) (x n)
                           (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))))
     ==> !A l. &0 < A
               ==> ?CAl N. !n y. N <= n /\
                                 y IN rfs_vball (V n) (t n) (x n)
                                        (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                                 ==> p3_vderiv2 (V n) l (t n) y <=
                                     CAl * rfs_vscalar (V n) (t n) (x n) pow (l + 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "reg")
    (LABEL_TAC "cc"))) THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
  USE_THEN "reg" (MP_TAC o SPEC `&4 * A`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N1")))))) THEN
  USE_THEN "cc" (X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2") o SPEC `&4 * A`) THEN
  MP_TAC(ISPECL [`l:num`; `K:real`; `A:real`; `dl:real`] P2BU_SHI_VIEW_CC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CA:real` (LABEL_TAC "shi")) THEN
  MAP_EVERY EXISTS_TAC [`CA:real`; `N1 + N2:num`] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vrm"))) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "shi" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(x:num->A) n`; `(t:num->real) n - dl / rfs_vscalar
    ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
    (t n) (x n)`] THEN
  SUBGOAL_THEN `&0 < rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) n) (t n) (x n)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "N2" MATCH_MP_TAC THEN UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `t - d < t <=> &0 < d`] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_ARITH `t - (t - d) = d`] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL];
    MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    USE_THEN "vrm" (MP_TAC o SPECL [`s:real`; `z:A`]) THEN ASM_SIMP_TAC[]]);;

(* The volume bound at x n (MT Claim 11.5) from kappa-noncollapsing at x n  *)
(* on the scale eta / sqrt(Q n), eta = min 1 (min (sqrt dl) (1 / sqrt K)).   *)

let P2BU_SEQ_VOL = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
           (real->A->real^3^3)) x t kappa r0 dl K N.
     (!n. p2c_regular_view (V n) /\
          x n IN topspace(rfs_vtop (V n) (t n))) /\
     &0 < kappa /\ &0 < r0 /\ &0 < dl /\ &0 < K /\
     (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n)) /\
     (!n. N <= n
          ==> &1 <= rfs_vscalar (V n) (t n) (x n) /\
              p3_noncoll_at (V n) kappa r0 (x n) (t n) /\
              rfs_persists (V n)
                (rfs_vball (V n) (t n) (x n) (&1 * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                (t n - dl / rfs_vscalar (V n) (t n) (x n)) (t n) /\
              !s y. t n - dl / rfs_vscalar (V n) (t n) (x n) < s /\ s <= t n /\
                    y IN rfs_vball (V n) (t n) (x n)
                           (&1 * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                    ==> &0 <= s /\ y IN topspace(rfs_vtop (V n) s) /\
                        p3_vrm (V n) s y <= K * rfs_vscalar (V n) (t n) (x n))
     ==> ?eta N'. &0 < eta /\
           !n. N' <= n
               ==> ?v. mfd_has_volume (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                         (rfs_vmetric (V n) (t n))
                         (rfs_vball (V n) (t n) (x n)
                            (eta * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))) v /\
                       kappa * (eta * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))) pow 3 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (LABEL_TAC "N"))))))) THEN
  ABBREV_TAC `eta = min (&1) (min (sqrt dl) (inv(sqrt K)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 /\ eta pow 2 <= dl /\ K * eta pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < sqrt dl /\ &0 < inv(sqrt K) /\ sqrt dl pow 2 = dl /\
                  inv(sqrt K) pow 2 = inv K` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_INV];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `eta <= sqrt dl /\ eta <= inv(sqrt K)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "eta" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt dl pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * inv(sqrt K) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LT_IMP_LE];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  USE_THEN "Qinf" (X_CHOOSE_TAC `N2:num` o SPEC `(eta / r0) pow 2`) THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `N + N2:num`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "N" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `N + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vrm")))) THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `Q = rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) n) (t n) (x n)` THEN
  SUBGOAL_THEN `(eta / r0) pow 2 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `N + N2 <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = eta * inv(sqrt Q)` THEN
  SUBGOAL_THEN `&0 < Q /\ &0 < sqrt Q /\ sqrt Q pow 2 = Q` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ r <= &1 * inv(sqrt Q) /\ r pow 2 <= dl / Q /\
                K * Q <= inv(r pow 2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `r pow 2 = eta pow 2 / Q` ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
      ASM_REWRITE_TAC[real_div];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV];
      EXPAND_TAC "r" THEN REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `eta / r0 < sqrt Q` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_DIV2_EQ];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_INV_DIV] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
      SUBGOAL_THEN `(K * Q) * eta pow 2 = (K * eta pow 2) * Q` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[p3_noncoll_at] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_parabolic_exists] THEN MATCH_MP_TAC P2CD_PERSISTS_MONO THEN
    EXISTS_TAC `(t:num->real) n - dl / Q` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    EXISTS_TAC `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) n) (t n) (x n) (&1 * inv(sqrt Q))` THEN
    EXISTS_TAC `(t:num->real) n` THEN ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d <= t`) THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_LE_REFL];
      UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
         (rfs_vball (V n) (t n) (x n) (&1 * inv(sqrt Q))) (t n - dl / Q) (t n)` THEN
      REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(MP_TAC o SPEC `(t:num->real) n`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < d ==> t - d < t /\ t <= t`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n`; `(t:num->real) n`; `(x:num->A) n`]
                    P2C_REGULAR_SLICE) THEN
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM p3_vrm] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * Q` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "vrm" (MP_TAC o SPECL [`s:real`; `y:A`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:A) IN rfs_vball ((V:num->(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n) r` THEN
      REWRITE_TAC[P2CO_VBALL] THEN
      SUBGOAL_THEN `mfd_ball (rfs_vtop ((V:num->(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n),
         rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) (x n) r SUBSET
                    mfd_ball (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                      (rfs_vmetric (V n) (t n)) (x n) (&1 * inv(sqrt Q))` MP_TAC THENL
       [MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[]; SET_TAC[]]]]);;

(* The time-0 limit (MT Thm 11.1, up to Claim 11.5 and Cor 5.10): T1      *)
(* (P2C_CG_COMPACT) applied to the tail of the sequence from an index where *)
(* the scalar curvature at the base point is positive.                     *)

let P2BU_TIME0_LIMIT = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))))
              ==> ?sub (top:B topology) atlas g0 xl.
                     p3_subseq sub /\
                     p3_slice_limit (\n. V (sub n)) (x o sub) (t o sub)
                       (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                       (top,atlas) g0 xl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_SEQ_REGION_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sra"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc")))))) THEN
  USE_THEN "sra" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "reg")] THEN
  UNDISCH_TAC `p2c_vblowup_seq (C,eps,kappa,r0,mu)
                 (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) x t` THEN
  REWRITE_TAC[p2c_vblowup_seq] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (LABEL_TAC "noncoll"))))))) THEN
  SUBGOAL_THEN `!n. p2c_regular_view ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\
                    x n IN topspace(rfs_vtop (V n) (t n))` (LABEL_TAC "vx") THENL
   [GEN_TAC THEN USE_THEN "views" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  (* Shi and volume *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`] P2BU_SEQ_SHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "shi")] THEN
  USE_THEN "reg" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))))) THEN
  USE_THEN "noncoll" (X_CHOOSE_THEN `N2:num` (LABEL_TAC "nc1") o SPEC `&1`) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `kappa:real`;
                 `r0:real`; `dl:real`; `K:real`; `N1 + N2:num`] P2BU_SEQ_VOL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "r1" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "nc1" (MP_TAC o SPECL [`n:num`; `(x:num->A) n`]) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [UNDISCH_TAC `N1 + N2 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "vx" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n`; `(t:num->real) n`; `(x:num->A) n`]
                    P2C_REGULAR_SLICE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[P2CO_VBALL; MFD_CENTRE_IN_BALL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `N3:num` STRIP_ASSUME_TAC)) THEN
  (* the tail and T1 *)
  USE_THEN "Qinf" (X_CHOOSE_TAC `N0:num` o SPEC `&0`) THEN
  UNDISCH_TAC `P2C_CG_COMPACT_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2C_CG_COMPACT_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) (n + N0)`;
    `\n. (x:num->A) (n + N0)`; `\n. (t:num->real) (n + N0)`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) (n + N0)) (t (n + N0)) (x (n + N0))`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN USE_THEN "vx" (STRIP_ASSUME_TAC o SPEC `n + N0:num`) THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) (n + N0)`; `(t:num->real) (n + N0)`;
                     `(x:num->A) (n + N0)`] P2C_REGULAR_SLICE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `N0:num`)) (concl th))) THEN
      ARITH_TAC;
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "cc" (X_CHOOSE_TAC `M:num` o SPEC `A:real`) THEN EXISTS_TAC `M:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `M <= n:num` THEN ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`A:real`; `l:num`] THEN DISCH_TAC THEN
      USE_THEN "shi" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `l:num`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `CAl:real` (X_CHOOSE_TAC `M:num`)) THEN
      MAP_EVERY EXISTS_TAC [`CAl:real`; `M:num`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `M <= n:num` THEN ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`eta:real`; `kappa:real`; `N3:num`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `N3 <= n:num` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g0:B->real^3^3`
    (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`\n. (sub:num->num) n + N0`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `p3_subseq (sub:num->num)` THEN REWRITE_TAC[p3_subseq] THEN
    MESON_TAC[LT_ADD2; LE_REFL; LT_ADD_RCANCEL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun u -> try fst(dest_const(fst(strip_comb u))) = "p3_slice_limit"
                             with _ -> false)) (concl th))) THEN
  REWRITE_TAC[o_DEF]);;

(* ------------------------------------------------------------------------- *)
(* With a slice limit as a flow limit on J = {0} (P2B11_SLICE_TO_FLOW0,      *)
(* pc_p2b_limbridge), Thm 5.33 gives sec >= 0 for the time-0 limit;          *)
(* divergence of Q along subsequences; uniform convergence of the rescaled   *)
(* scalar curvature on compact sets; and the uniform bound R <= (6 Kl + 1) Q *)
(* on the rescaled balls of every radius (6 Kl from P2BS_MFD_SCALAR_SECT,    *)
(* pc_p2b_slice) (the step of MT Thm 11.1 after Claim 11.7).                 *)
(* ------------------------------------------------------------------------- *)

let P2BU_QINF_SUBSEQ = prove
 (`!(Q:num->real) sub.
     (!B. ?N. !n. N <= n ==> B < Q n) /\ p3_subseq sub
     ==> !B. ?N. !n. N <= n ==> B < Q(sub n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `B:real` THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
  ASM_MESON_TAC[]);;

let P2BU_TIME0_SEC = prove
 (`!(u:A->bool) (w:B->bool) V x t (top:B topology) atlas g0 xl W phi.
     P2C_THM_5_33_STATEMENT u w /\
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) /\
          rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {})) /\
     (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n)) /\
     p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) (top,atlas) g0 xl W phi
     ==> !y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g0 y u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `P2C_THM_5_33_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2C_THM_5_33_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `\n. rfs_vscalar ((V:num->(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)`;
    `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `\s:real. (g0:B->real^3^3)`; `xl:B`]) THEN
  REWRITE_TAC[IN_SING] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[P2C_FLOW_LIMIT_ON_WITH] THEN
      MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN
      MATCH_MP_TAC P2B11_SLICE_TO_FLOW0 THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with"
                                 with _ -> false)) (concl th))) THEN
      REWRITE_TAC[p2c_slice_limit_with] THEN SIMP_TAC[]];
    MESON_TAC[]]);;

(* Uniform convergence of the rescaled scalar curvature on a compact set,  *)
(* given a sectional bound Kl of the limit at s0 (it bounds |Rm|^2 by       *)
(* RFA_LRM_SECTIONAL_BOUND, the constant of APX_SCALAR_STABILITY_LIP).      *)

let P2BU_UNIF_SCALAR = prove
 (`!V x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s0 K Kl e.
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3))) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     s0 IN J /\ compact_in top K /\ &0 <= Kl /\
     (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
              ==> abs(mfd_sectional atlas (g s0) y u v) <= Kl) /\ &0 < e
     ==> ?N. !k y. N <= k /\ y IN K
                   ==> phi k y IN topspace(rfs_vtop (V k) (t k + s0 / Q k)) /\
                       abs(mfd_scalar atlas (g s0) y -
                           mfd_scalar (rfs_vatlas (V k) (t k + s0 / Q k))
                                      (rfs_vmetric (V k) (t k + s0 / Q k)) (phi k y) / Q k) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "kl") ASSUME_TAC))))))) THEN
  REWRITE_TAC[p2c_flow_limit_with] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv"))))))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0)` ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:3`,`:N`] RFA_LRM_SECTIONAL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cr:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K0 = sqrt(Cr * Kl pow 2)` THEN
  SUBGOAL_THEN `&0 <= K0 /\ Cr * Kl pow 2 = K0 pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    SUBGOAL_THEN `&0 <= Cr * Kl pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `delta = min (&1 / &10) (e / (&73 * (&1 + abs K0)))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ &8 * &9 * (&1 + abs K0) * delta < e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + abs K0` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / (&73 * (&1 + abs K0))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
     [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `delta * &73 * (&1 + abs K0) <= e` ASSUME_TAC THENL
     [SUBGOAL_THEN `delta <= e / (&73 * (&1 + abs K0))` MP_TAC THENL
       [EXPAND_TAC "delta" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &73`];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "delta" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < (&1 + abs K0) * delta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `delta * &73 * (&1 + abs K0) <= e` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`s0:real`; `s0:real`; `K:B->bool`; `2`; `delta pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTERVAL_SING; SING_SUBSET] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "k0")) THEN
  EXISTS_TAC `k0:num` THEN MAP_EVERY X_GEN_TAC [`k:num`; `y0:B`] THEN STRIP_TAC THEN
  USE_THEN "k0" (MP_TAC o C MP (ASSUME `k0 <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `psi:A->B` o
     C MP (CONJ (SPEC `s0:real` REAL_LE_REFL) (SPEC `s0:real` REAL_LE_REFL)) o SPEC `s0:real`)
    (MP_TAC o SPECL [`s0:real`; `y0:B`]))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y0:B) IN (W:num->B->bool) k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:B) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `(W:num->B->bool) k` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S0 = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                         (FST(chart_at atlas y0))` THEN
  ABBREV_TAC `G0 = metric_local (atlas:((B->bool)#(B->real^3))->bool) (chart_at atlas (y0:B))
                     ((g:real->B->real^3^3) s0)` THEN
  ABBREV_TAC `yc = SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)) y0` THEN
  SUBGOAL_THEN `metric_field (S0:real^3->bool) (G0:real^3->real^3^3) /\ (yc:real^3) IN S0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "G0"; "yc"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->B->real^3^3) s0)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrm_deriv_norm2 0 (G0:real^3->real^3^3) yc <= K0 pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `Cr * Kl pow 2 = K0 pow 2`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "lrm_deriv_norm2" with _ -> false))
          (concl th) && is_forall(concl th))) THEN
    EXISTS_TAC `S0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "kl" (MP_TAC o C MP (CONJ (ASSUME `(y0:B) IN topspace top`)
                                       (ASSUME `~collinear {vec 0,u:real^3,v}`)) o
                   SPECL [`y0:B`; `u:real^3`; `v:real^3`]) THEN
    REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:num->B->A) k y0 IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) k`;
                   `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k)`;
                   `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k)`;
                   `(phi:num->B->A) k`; `psi:A->B`; `y0:B`] P2B_DIFFEO_IMAGE_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `t (k:num) + s0 / Q k`; `(phi:num->B->A) k y0`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k)`; `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k)`;
                 `(W:num->B->bool) k`; `(phi:num->B->A) k`; `psi:A->B`; `(Q:num->real) k`;
                 `y0:B`] P2CP_APPROX_CURV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Gk = \z. (Q:num->real) k %%
                   rfs_pullback (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k))
                     ((phi:num->B->A) k o chart_inv (chart_at (atlas:((B->bool)#(B->real^3))->bool)
                                                         (y0:B)))
                     (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k + s0 / Q k)) z` THEN
  ABBREV_TAC `S = IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)))
                        (FST(chart_at atlas y0) INTER (W:num->B->bool) k)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "scal") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `metric_field (S:real^3->bool) (G0:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `S0:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["S"; "S0"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) < delta /\
                &0 <= sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K0:real`; `S:real^3->bool`; `G0:real^3->real^3^3`; `Gk:real^3->real^3^3`;
                 `yc:real^3`] APX_SCALAR_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  USE_THEN "scal" (fun th -> REWRITE_TAC[SYM th]) THEN
  SUBGOAL_THEN `mfd_scalar atlas ((g:real->B->real^3^3) s0) y0 = lscalar (G0:real^3->real^3^3) yc`
  SUBST1_TAC THENL [MAP_EVERY EXPAND_TAC ["G0"; "yc"] THEN REWRITE_TAC[mfd_scalar]; ALL_TAC] THEN
  SUBGOAL_THEN `&8 * &9 * (&1 + abs K0) * sqrt(lck_dist2 2 (G0:real^3->real^3^3) Gk yc) <=
                &8 * &9 * (&1 + abs K0) * delta` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The uniform scalar bound on the rescaled balls of every radius from a    *)
(* global sectional bound Kl of the (complete) time-0 limit: MT's step      *)
(* after Claim 11.7, with LIM_BALL_IN and P2BU_UNIF_SCALAR on the compact   *)
(* closure of B(xl,2A).                                                       *)

let P2BU_UNIF_D = prove
 (`!V x t Q (top:B topology) atlas g0 xl W (phi:num->B->A) Kl.
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) /\
          hausdorff_space (rfs_vtop (V n) (t n))) /\
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\ mfd_complete (top,atlas) g0 /\
     &0 <= Kl /\
     (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
              ==> abs(mfd_sectional atlas g0 y u v) <= Kl)
     ==> !A. &0 < A
             ==> ?N. !n y. N <= n /\ y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                           ==> rfs_vscalar (V n) (t n) y <= (&6 * Kl + &1) * Q n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kl"))))) THEN
  X_GEN_TAC `A:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B11_SLICE_TO_FLOW0) THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with" with _ -> false))
        (concl th))) THEN
  REWRITE_TAC[p2c_slice_limit_with] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. (t:num->real) k + &0 / Q k = t k` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\s:real. (g0:B->real^3^3)`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `A:real`; `&2 * A`] LIM_BALL_IN) THEN
  ASM_REWRITE_TAC[IN_SING] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "bin")) THEN
  ABBREV_TAC `KK = (top:B topology) closure_of
                   mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 xl (&2 * A)` THEN
  SUBGOAL_THEN `compact_in (top:B topology) KK` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `xl:B`; `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 xl (&2 * A)`;
                   `&2 * A`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\s:real. (g0:B->real^3^3)`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `KK:B->bool`; `Kl:real`; `&1`] P2BU_UNIF_SCALAR) THEN
  SUBGOAL_THEN `!n. p2c_regular_view ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)` ASSUME_TAC THENL
   [USE_THEN "views" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_SING; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "us")) THEN
  EXISTS_TAC `k0 + N1:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:A`] THEN STRIP_TAC THEN
  USE_THEN "bin" (MP_TAC o SPECL [`n:num`; `z:A`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `k0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(z:A) IN rfs_vball ((V:num->(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)
       (A * inv(sqrt((Q:num->real) n)))` THEN
    ASM_REWRITE_TAC[P2CO_VBALL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:B) IN KK` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 xl (&2 * A)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC CLOSURE_OF_SUBSET] THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  USE_THEN "us" (MP_TAC o SPECL [`n:num`; `y:B`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `k0 + N1 <= n:num` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:B) IN mfd_ball (top,atlas) (g0:B->real^3^3) xl (&2 * A)` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g0:B->real^3^3) y <= &6 * Kl` MP_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                   `y:B`; `Kl:real`] P2BS_MFD_SCALAR_SECT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `abs x <= k ==> x <= k`) THEN
    USE_THEN "kl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2B9_RFS_VSCALAR] THEN
  SUBGOAL_THEN `&0 < (Q:num->real) n` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `abs(a - b) < c <=> b < a + c /\ a - c < b`] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g0:B->real^3^3) y * Q n <= (&6 * Kl) * (Q:num->real) n`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 11.7 (bounded curvature of the time-0 limit from the slice form  *)
(* of A4, hence R <= D Q n on all rescaled balls), subsequences of blow-up   *)
(* sequences, transfer of |Rm| bounds to flow limits, and MT's last          *)
(* paragraph of the proof of Thm 11.1 (P2BU_S9).                             *)
(* ------------------------------------------------------------------------- *)

(* MT Claim 11.7 and the step after it: a connected complete time-0 slice    *)
(* limit with canonical neighbourhoods for R > 4 has bounded curvature (the  *)
(* slice form of A4, given here as an instance at (C',eps')), hence R is     *)
(* bounded by D Q n on the rescaled balls of every radius (P2BU_UNIF_D).     *)

let P2BU_CLAIM_11_7 = prove
 (`!(u:A->bool) (w:B->bool) C' eps' V x t (top:B topology) atlas g0 xl W (phi:num->B->A).
     P2C_THM_5_33_STATEMENT u w /\
     (!top1 atlas1 g1.
        hausdorff_space (top1:B topology) /\ smooth_manifold_atlas top1 atlas1 /\
        riemannian_metric atlas1 (g1:B->real^3^3) /\ connected_space top1 /\
        mfd_complete (top1,atlas1) g1 /\ apx_sphere_sep top1 atlas1 /\
        (!y u v. y IN topspace top1 /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas1 g1 y u v) /\
        (!y. y IN topspace top1 /\ &4 < mfd_scalar atlas1 g1 y
             ==> ?U. rfs_canonical_nbhd (top1,atlas1) g1 C' eps' y U)
        ==> ?K. !y. y IN topspace top1 ==> mfd_rm_norm atlas1 g1 y <= K) /\
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) /\
          rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
          x n IN topspace(rfs_vtop (V n) (t n)) /\
          apx_sphere_sep (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))) /\
     (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n)) /\
     p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n)) (top,atlas) g0 xl W phi /\
     connected_space top /\ mfd_complete (top,atlas) g0 /\
     (!y. y IN topspace top /\ &4 < mfd_scalar atlas g0 y
          ==> ?U. rfs_canonical_nbhd (top,atlas) g0 C' eps' y U)
     ==> ?D. &0 < D /\
             !A. &0 < A
                 ==> ?N. !n y. N <= n /\
                               y IN rfs_vball (V n) (t n) (x n)
                                      (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                               ==> rfs_vscalar (V n) (t n) y <=
                                   D * rfs_vscalar (V n) (t n) (x n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "a4")
    (CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "canon")))))))) THEN
  SUBGOAL_THEN `!n. p2c_regular_view ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\
                    hausdorff_space (rfs_vtop (V n) (t n)) /\
                    smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n))`
  (LABEL_TAC "vs") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) n`; `(t:num->real) n`; `(x:num->A) n`]
                  P2C_REGULAR_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`;
                 `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`] P2BU_TIME0_SEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
    DISCH_THEN(LABEL_TAC "sec")] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        (t n) ((x:num->A) n)`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`] P2BU_SEP_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "views" (fun th -> USE_THEN "vs" (fun th' ->
      MESON_TAC[th; th']));
    DISCH_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (top:B topology) /\
                smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas (g0:B->real^3^3)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with" with _ -> false))
          (concl th))) THEN
    REWRITE_TAC[p2c_slice_limit_with] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "a4" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                 `g0:B->real^3^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "sec" ACCEPT_TAC; USE_THEN "canon" ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `K:real`)] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `\n. rfs_vscalar ((V:num->(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                        (t n) ((x:num->A) n)`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `max (&0) K`] P2BU_UNIF_D) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&0 <= max (&0) K`] THEN
    MAP_EVERY X_GEN_TAC [`y:B`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_rm_norm atlas (g0:B->real^3^3) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_SECTIONAL_LE_RM_NORM THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `a <= K ==> a <= max (&0) K`) THEN ASM_SIMP_TAC[]];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  EXISTS_TAC `&6 * max (&0) K + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Blow-up sequences pass to subsequences.                                   *)

let P2BU_VBLOWUP_SUBSEQ = prove
 (`!C eps kappa r0 mu (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) x t sub.
     p2c_vblowup_seq (C,eps,kappa,r0,mu) V x t /\ p3_subseq sub
     ==> p2c_vblowup_seq (C,eps,kappa,r0,mu) (\n. V (sub n)) (x o sub) (t o sub)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_vblowup_seq; o_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (LABEL_TAC "noncoll"))))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN USE_THEN "views" (ACCEPT_TAC o SPEC `(sub:num->num) n`);
    X_GEN_TAC `B:real` THEN USE_THEN "Qinf" (X_CHOOSE_TAC `N:num` o SPEC `B:real`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ge" (ACCEPT_TAC o SPEC `n:num`);
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`; `s:real`] THEN
    USE_THEN "canon" (ACCEPT_TAC o SPECL [`(sub:num->num) n`; `y:A`; `s:real`]);
    X_GEN_TAC `A:real` THEN USE_THEN "noncoll" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN
    EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN USE_THEN "ge" (ACCEPT_TAC o SPEC `n:num`)]);;

(* Transfer of a curvature bound p3_vrm <= K Q n on all rescaled balls at    *)
(* time t n + s0 / Q n to the flow limit at time s0 (sectional curvatures    *)
(* converge pointwise, P2BU_POINT_CURV; the images of limit balls lie in     *)
(* rescaled view balls, LIM_BALL_OUT).                                        *)

let P2BU_RM_TRANSFER = prove
 (`!V x t Q J (top:B topology) atlas g xl W (phi:num->B->A) s0 y0 K.
     (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3))) /\
     p2c_flow_limit_with V x t Q J (top,atlas) g xl W phi /\
     (!s. s IN J ==> riemannian_metric atlas (g s)) /\
     (&0) IN J /\ mfd_complete (top,atlas) (g (&0)) /\
     s0 IN J /\ y0 IN topspace top /\ mfd_joinable (top,atlas) xl y0 /\
     (!A. &0 < A
          ==> ?N. !n y. N <= n /\ y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                        ==> p3_vrm (V n) (t n + s0 / Q n) y <= K * Q n)
     ==> mfd_rm_norm atlas (g s0) y0 <= K`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "views") (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vrm"))))))))) THEN
  MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `sc = mfd_sectional atlas ((g:real->B->real^3^3) s0) y0 u v` THEN
  ABBREV_TAC `e = (abs sc - K) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ K + e < abs sc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the point phi k y0 lies in a rescaled ball about x k *)
  ABBREV_TAC `r = abs(mfd_dist (top,atlas) ((g:real->B->real^3^3) (&0)) xl y0) + &1` THEN
  SUBGOAL_THEN `&0 < r /\ (y0:B) IN mfd_ball (top,atlas) ((g:real->B->real^3^3) (&0)) xl r`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "r" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(xl:B) IN topspace top /\ (!k. (phi:num->B->A) k xl = x k) /\
                (!k. &0 < (Q:num->real) k)` STRIP_ASSUME_TAC THENL
   [USE_THEN "fl" MP_TAC THEN REWRITE_TAC[p2c_flow_limit_with] THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `r:real`; `r + &1`] LIM_BALL_OUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `r < r + &1`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN ASM_REWRITE_TAC[];
      USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (MP_TAC o SPEC `y0:B` o ONCE_REWRITE_RULE[SWAP_FORALL_THM])) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "out") THEN
  USE_THEN "vrm" (MP_TAC o SPEC `r + &1`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2"))] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `s0:real`; `y0:B`; `e:real`] P2BU_POINT_CURV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "pc")) THEN
  ABBREV_TAC `k = k0 + N1 + N2:num` THEN
  USE_THEN "pc" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "out" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "N2" (MP_TAC o SPECL [`k:num`; `(phi:num->B->A) k y0`]) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[P2CO_VBALL; GSYM real_div] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "mfd_ball" with _ -> false)) (concl th) &&
      can (find_term ((=) `(phi:num->B->A) k y0`)) (concl th))) THEN
    ASM_REWRITE_TAC[real_div];
    ALL_TAC] THEN
  REWRITE_TAC[p3_vrm] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k`; `(t:num->real) k + s0 / Q k`;
                 `(phi:num->B->A) k y0`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k) (t k + s0 / Q k)`;
                 `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k) (t k + s0 / Q k)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) k) (t k + s0 / Q k)`;
                 `(phi:num->B->A) k y0`; `u':real^3`; `v':real^3`] MFD_SECTIONAL_LE_RM_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `sk = mfd_sectional (rfs_vatlas ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
                     (t k + s0 / Q k)) (rfs_vmetric (V k) (t k + s0 / Q k))
                     ((phi:num->B->A) k y0) u' v'` THEN
  SUBGOAL_THEN `abs(sk / (Q:num->real) k) <= K` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < q ==> abs q = q`; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The region facts of Cor 11.3 with a persistence time dl uniform in A    *)
(* give the hypotheses of P2BU_FROM_SLICE_UPTO on J = (-dl,0] (MT's last    *)
(* paragraph of the proof of Thm 11.1).                                      *)

let P2BU_REGION_TO_J = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q dl K.
     &0 < dl /\ (!n. &0 < Q n) /\
     (!A. &0 < A
          ==> ?N. !n. N <= n
                 ==> rfs_persists (V n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                       (t n - dl / Q n) (t n) /\
                     !s y. t n - dl / Q n < s /\ s <= t n /\
                           y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                           ==> y IN topspace(rfs_vtop (V n) s) /\ p3_vrm (V n) s y <= K * Q n)
     ==> (!A a b. &0 < A /\ real_interval[a,b] SUBSET {s | --dl < s /\ s <= &0}
                  ==> ?CA N. !n. N <= n
                         ==> (!s. a <= s /\ s <= b
                                  ==> rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))) SUBSET
                                      topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                             rfs_persists (V n)
                               (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                               (t n + a / Q n) (t n + b / Q n) /\
                             !s y. a <= s /\ s <= b /\
                                   y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                   ==> p3_vrm (V n) (t n + s / Q n) y <= CA * Q n) /\
         (!a b A. --dl < a /\ b <= &0 /\ &0 < A
                  ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                  y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                  ==> p3_vrm (V n) (t n + s / Q n) y <= K * Q n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Qpos")
    (LABEL_TAC "reg"))) THEN
  SUBGOAL_THEN `!n s. --dl < s /\ s <= &0
                      ==> (t:num->real) n - dl / Q n < t n + s / Q n /\ t n + s / Q n <= t n`
  (LABEL_TAC "tm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (Q:num->real) n` ASSUME_TAC THENL
     [USE_THEN "Qpos" (ACCEPT_TAC o SPEC `n:num`); ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `t - a < t + b <=> --a < b`;
                REAL_ARITH `t + b <= t <=> b <= &0`] THEN
    SUBGOAL_THEN `--(dl / Q n) = --dl / (Q:num->real) n` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LNEG]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`A:real`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!s. a <= s /\ s <= b ==> --dl < s /\ s <= &0` (LABEL_TAC "ab") THENL
     [UNDISCH_TAC `real_interval[a,b] SUBSET {s | --dl < s /\ s <= &0}` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "reg" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `N:num`] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (Q:num->real) n` ASSUME_TAC THENL
     [USE_THEN "Qpos" (ACCEPT_TAC o SPEC `n:num`); ALL_TAC] THEN
    USE_THEN "N" (MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "in")) THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "ab" (MP_TAC o C MP (ASSUME `a <= s /\ s <= b`) o SPEC `s:real`) THEN
      DISCH_TAC THEN
      USE_THEN "tm" (MP_TAC o C MP (ASSUME `--dl < s /\ s <= &0`) o SPECL [`n:num`; `s:real`]) THEN
      STRIP_TAC THEN
      USE_THEN "in" (MP_TAC o SPECL [`(t:num->real) n + s / Q n`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      UNDISCH_TAC `rfs_persists ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) n) (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))
                     (t n - dl / Q n) (t n)` THEN
      REWRITE_TAC[P2CO_PERSISTS_ALT] THEN DISCH_THEN(LABEL_TAC "p") THEN
      X_GEN_TAC `s':real` THEN STRIP_TAC THEN USE_THEN "p" MATCH_MP_TAC THEN
      SUBGOAL_THEN `a / (Q:num->real) n < b / Q n` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN DISCH_TAC THEN
      USE_THEN "ab" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "ab" (MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      USE_THEN "tm" (MP_TAC o C MP (ASSUME `--dl < a /\ a <= &0`) o SPECL [`n:num`; `a:real`]) THEN
      USE_THEN "tm" (MP_TAC o C MP (ASSUME `--dl < b /\ b <= &0`) o SPECL [`n:num`; `b:real`]) THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "ab" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "tm" (MP_TAC o C MP (ASSUME `--dl < s /\ s <= &0`) o SPECL [`n:num`; `s:real`]) THEN
      STRIP_TAC THEN
      USE_THEN "in" (MP_TAC o SPECL [`(t:num->real) n + s / Q n`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `A:real`] THEN STRIP_TAC THEN
    USE_THEN "reg" (MP_TAC o C MP (ASSUME `&0 < A`) o SPEC `A:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
    DISCH_THEN(MP_TAC o SPECL [`(t:num->real) n + s / Q n`; `y:A`] o CONJUNCT2) THEN
    USE_THEN "tm" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* MT's last paragraph of the proof of Thm 11.1: with R <= D Q n on the     *)
(* rescaled balls of every radius, Cor 11.3 gives a persistence time dl and *)
(* a bound |Rm| <= K' Q n uniform in A; the slice limit extends to a flow   *)
(* limit on (-dl,0] (P2BU_FROM_SLICE_UPTO), complete with sec >= 0          *)
(* (Thm 5.33) and |Rm| <= K' (P2BU_RM_TRANSFER) on (-dl/2,0], and a further *)
(* subsequence gives p3_flow_limit with T1 = dl/2.                           *)

let P2BU_S9 = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
     P2C_THM_5_33_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t (top:B topology) atlas g0 xl W (phi:num->B->A) D.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                (top,atlas) g0 xl W phi /\
              mfd_complete (top,atlas) g0 /\ &0 < D /\
              (!A. &0 < A
                   ==> ?N. !n y. N <= n /\
                                 y IN rfs_vball (V n) (t n) (x n)
                                        (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                                 ==> rfs_vscalar (V n) (t n) y <=
                                     D * rfs_vscalar (V n) (t n) (x n))
              ==> ?sub (top':B topology) atlas' g T1 K.
                     &0 < T1 /\ p3_subseq sub /\
                     p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                       (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                       (top',atlas') g xl T1 /\
                     (!s. --T1 < s /\ s <= &0
                          ==> mfd_complete (top',atlas') (g s) /\
                              (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                                       ==> &0 <= mfd_sectional atlas' (g s) y u v) /\
                              (!y. y IN topspace top' ==> mfd_rm_norm atlas' (g s) y <= K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BU_SEQ_REGION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sreg"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `D:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bseq")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dbd")))))))) THEN
  USE_THEN "bseq" (MP_TAC o REWRITE_RULE[p2c_vblowup_seq]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `!n. &0 < rfs_vscalar ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) (x n)`
  (LABEL_TAC "Qpos") THENL
   [USE_THEN "sl" (MP_TAC o REWRITE_RULE[p2c_slice_limit_with]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `dl = min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4)))` THEN
  ABBREV_TAC `K' = &2 * (&2 * (D + &4)) + &12 + &2 * exp(&4)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K'` ASSUME_TAC THENL
   [EXPAND_TAC "K'" THEN MP_TAC(SPEC `&4` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Cor 11.3 with D uniform in A *)
  SUBGOAL_THEN
   `!A. &0 < A
        ==> ?N. !n. N <= n
               ==> rfs_persists ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                     (rfs_vball (V n) (t n) (x n) (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                     (t n - dl / rfs_vscalar (V n) (t n) (x n)) (t n) /\
                   !s y. t n - dl / rfs_vscalar (V n) (t n) (x n) < s /\ s <= t n /\
                         y IN rfs_vball (V n) (t n) (x n)
                                (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                         ==> y IN topspace(rfs_vtop (V n) s) /\
                             p3_vrm (V n) s y <= K' * rfs_vscalar (V n) (t n) (x n)`
  (LABEL_TAC "reg") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "sreg" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
      `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `x:num->A`; `t:num->real`; `A:real`; `D:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        USE_THEN "Dbd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[ASSUME `min (mu / max (&1) D) (inv(&16 * max C (&2) * (D + &4))) = dl`;
                ASSUME `&2 * (&2 * (D + &4)) + &12 + &2 * exp(&4) = K'`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `x:num->A`; `t:num->real`;
     `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
     `dl:real`; `K':real`] P2BU_REGION_TO_J)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rj1") (LABEL_TAC "rj2")) THEN
  (* the flow limit on J = (-dl,0] *)
  SUBGOAL_THEN `is_realinterval {s:real | --dl < s /\ s <= &0} /\
                (&0) IN {s:real | --dl < s /\ s <= &0} /\
                (!a0. a0 IN {s:real | --dl < s /\ s <= &0} /\
                      (!s. s IN {s:real | --dl < s /\ s <= &0} ==> a0 <= s) ==> a0 = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `a0:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a0 - dl) / &2`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `x:num->A`; `t:num->real`;
     `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
     `{s:real | --dl < s /\ s <= &0}`; `top:B topology`;
     `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
     `phi:num->B->A`] P2BU_FROM_SLICE_UPTO)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fl")
    (CONJUNCTS_THEN2 (LABEL_TAC "riem") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "compl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "join")))))))))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub2 n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub2:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* completeness on J *)
  SUBGOAL_THEN `!s. --dl < s /\ s <= &0 ==> mfd_complete (top',atlas') ((g:real->B->real^3^3) s)`
  (LABEL_TAC "cs") THENL
   [X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    USE_THEN "compl" (MP_TAC o SPECL [`s0:real`; `&0`; `K':real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `A:real` THEN DISCH_TAC THEN USE_THEN "rj2" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[REAL_LE_REFL]];
      DISCH_THEN(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* sec >= 0 on J (Thm 5.33) *)
  SUBGOAL_THEN `!s y u v. s IN {s:real | --dl < s /\ s <= &0} /\ y IN topspace top' /\
                          ~collinear {vec 0,u,v}
                          ==> &0 <= mfd_sectional atlas' ((g:real->B->real^3^3) s) y u v`
  (LABEL_TAC "sec") THENL
   [UNDISCH_TAC `P2C_THM_5_33_STATEMENT (u:A->bool) (w:B->bool)` THEN
    REWRITE_TAC[P2C_THM_5_33_STATEMENT] THEN
    DISCH_THEN(MP_TAC o ISPECL
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
              (real->A->real^3^3)) ((sub2:num->num) n)`;
      `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
      `(\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) n) (t n) ((x:num->A) n)) o (sub2:num->num)`;
      `{s:real | --dl < s /\ s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
       `sub2:num->num`] P2BU_QINF_SUBSEQ)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* |Rm| <= K' on J *)
  SUBGOAL_THEN `!s y. --dl < s /\ s <= &0 /\ y IN topspace top'
                      ==> mfd_rm_norm atlas' ((g:real->B->real^3^3) s) y <= K'`
  (LABEL_TAC "rmb") THENL
   [MAP_EVERY X_GEN_TAC [`s0:real`; `y0:B`] THEN STRIP_TAC THEN
    USE_THEN "fl" (MP_TAC o REWRITE_RULE[P2C_FLOW_LIMIT_ON_WITH]) THEN
    DISCH_THEN(X_CHOOSE_THEN `W':num->B->bool` (X_CHOOSE_THEN `phi':num->B->A` ASSUME_TAC)) THEN
    MP_TAC(ISPECL
     [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
              (real->A->real^3^3)) ((sub2:num->num) n)`;
      `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
      `(\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) n) (t n) ((x:num->A) n)) o (sub2:num->num)`;
      `{s:real | --dl < s /\ s <= &0}`; `top':B topology`;
      `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
      `W':num->B->bool`; `phi':num->B->A`; `s0:real`; `y0:B`; `K':real`] P2BU_RM_TRANSFER) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      USE_THEN "join" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `A:real` THEN DISCH_TAC THEN
      USE_THEN "rj2" (MP_TAC o C MP (CONJ (ASSUME `--dl < s0`)
        (CONJ (ASSUME `s0 <= &0`) (ASSUME `&0 < A`))) o SPECL [`s0:real`; `s0:real`; `A:real`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN EXISTS_TAC `N:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
      USE_THEN "N" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the flow limit with T1 = dl / 2 *)
  MP_TAC(ISPECL
   [`\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) ((sub2:num->num) n)`;
    `(x:num->A) o (sub2:num->num)`; `(t:num->real) o (sub2:num->num)`;
    `(\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n) (t n) ((x:num->A) n)) o (sub2:num->num)`;
    `{s:real | --dl < s /\ s <= &0}`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`;
    `\k:num. dl / &2`] P2BU_FLOW_LIMIT_OF_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub3:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `dl / &2`))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `a:real` THEN DISCH_TAC THEN TRY(EXISTS_TAC `0`) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `a:real` THEN STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  EXISTS_TAC `(sub2:num->num) o (sub3:num->num)` THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                        `g:real->B->real^3^3`; `dl / &2`; `K':real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `p3_subseq (sub2:num->num)` THEN UNDISCH_TAC `p3_subseq (sub3:num->num)` THEN
    REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[];
    REWRITE_TAC[o_DEF] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[o_DEF] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p3_flow_limit" with _ -> false))
          (concl th)));
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `--dl < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "cs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`y:B`; `u':real^3`; `v':real^3`] THEN STRIP_TAC THEN
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN USE_THEN "rmb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for MT Claim 11.6.  Chart forms of pullback fields, the reverse     *)
(* closeness (P2BU_REV_CLOSE: exchange of the reference metric with          *)
(* pc_lck_swap, naturality, scaling), components under the limit maps, and   *)
(* the hypotheses of SLICE_FIX at one approximant (P2BU_SLICE_FIX_HYPS).     *)
(* The diameter bounds of canonical neighbourhoods are in pc_canon_diam.     *)
(* ------------------------------------------------------------------------- *)

(* Chart form of a pullback metric by a diffeomorphism f: W -> W': on the    *)
(* chart image of FST c INTER W it is a metric field, in both forms.        *)

let P2BU_PB_LOCAL_FIELD = prove
 (`!top atlas top' atlas' W W' (f:A->B) f' (g':B->real^N^N) c.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\ mfd_diffeo top atlas W top' atlas' W' f f' /\
     c IN atlas
     ==> open (IMAGE (SND c) (FST c INTER W)) /\
         metric_field (IMAGE (SND c) (FST c INTER W)) (rfs_pullback atlas' (f o chart_inv c) g') /\
         metric_field (IMAGE (SND c) (FST c INTER W))
           (metric_local atlas c (mfd_pullback_metric atlas atlas' f g'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top (atlas:((A->bool)#(A->real^N))->bool)
                  (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)) (chart_inv c)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                    MFD_PARAM_CHART_INV) THEN
      ASM_REWRITE_TAC[PAIR];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (chart_inv (c:(A->bool)#(A->real^N)))
                  (IMAGE (SND c) (FST c INTER W)) SUBSET W` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W))
                  (rfs_pullback atlas' ((f:A->B) o chart_inv c) (g':B->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `W:A->bool`; `W':B->bool`; `f':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `rfs_pullback atlas' ((f:A->B) o chart_inv (c:(A->bool)#(A->real^N)))
                (g':B->real^N^N)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2BL_PB_CHART THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `W:A->bool`; `W':B->bool`;
                        `f':B->A`] THEN
  ASM_REWRITE_TAC[]);;

(* Reverse closeness (the exchange of the reference metric in Claim 11.6):  *)
(* if the limit metric g0 and Q phi^* gA are eta-close at psi y' with g0 as *)
(* reference, then at y' the metrics c Q gA and c psi^* g0 are close with   *)
(* the approximant as reference: the exchange (an instance of               *)
(* LCK_CK_BASE_REV with constant M), naturality under psi                   *)
(* (P2B9S_LCK_NATURAL) and the scaling by c (P2BL_LCK_CHART_CONVERT).       *)

let P2BU_REV_CLOSE = prove
 (`!topL atlasL topA atlasA (W:B->bool) W' (phi:B->A) psi (g0:B->real^N^N) gA Q c m M
    eta y'.
     smooth_manifold_atlas topL atlasL /\ smooth_manifold_atlas topA atlasA /\
     riemannian_metric atlasL g0 /\ riemannian_metric atlasA gA /\
     mfd_diffeo topL atlasL W topA atlasA W' phi psi /\ y' IN W' /\
     &0 < Q /\ &0 < c /\ &0 <= M /\ eta <= &1 / &4 /\
     (!s (G0:real^N->real^N^N) G1 G2 y.
        metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
        lck_dist2 m G0 G1 y <= &1 / &4
        ==> lck_dist2 m G1 G2 y <= M * lck_dist2 m G0 (\z. G0 z + G2 z - G1 z) y) /\
     lck_dist2 m (metric_local atlasL (chart_at atlasL (psi y')) g0)
                 (\w. Q %% rfs_pullback atlasA (phi o chart_inv (chart_at atlasL (psi y'))) gA w)
                 (SND(chart_at atlasL (psi y')) (psi y')) <= eta
     ==> lck_dist2 m (metric_local atlasA (chart_at atlasA y') (\z. c %% (Q %% gA z)))
                     (metric_local atlasA (chart_at atlasA y')
                        (\z. c %% mfd_pullback_metric atlasA atlasL psi g0 z))
                     (SND(chart_at atlasA y') y') <= (&1 + inv c) pow m * M * eta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rev") (LABEL_TAC "cl")))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
  SUBGOAL_THEN `open_in topL (W:B->bool) /\ open_in topA (W':A->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) y' IN W /\ (phi:B->A) (psi y') = y'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) y' IN topspace topL /\ (y':A) IN topspace topA`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlasA (\z:A. Q %% (gA:A->real^N^N) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* step 1: the scaling by c and the rfs_pullback form on the approximant side *)
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                 `topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                 `W':A->bool`; `W:B->bool`; `psi:A->B`; `phi:B->A`;
                 `\z:A. Q %% (gA:A->real^N^N) z`; `g0:B->real^N^N`; `c:real`; `&1`;
                 `m:num`; `y':A`] P2BL_LCK_CHART_CONVERT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID; MATRIX_CMUL_LID; ETA_AX] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (rand(concl th)) THEN
                       CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `cA = chart_at (atlasA:((A->bool)#(A->real^N))->bool) y'` THEN
  ABBREV_TAC `z0 = (psi:A->B) y'` THEN
  ABBREV_TAC `cL = chart_at (atlasL:((B->bool)#(B->real^N))->bool) z0` THEN
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`; `y':A`] CHART_AT) THEN
  MP_TAC(ISPECL [`topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`; `z0:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* step 2: back to pullback fields on the approximant side *)
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                 `topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                 `W':A->bool`; `W:B->bool`; `psi:A->B`; `phi:B->A`; `g0:B->real^N^N`;
                 `cA:(A->bool)#(A->real^N)`] P2BU_PB_LOCAL_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                 `cA:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lck_dist2 m (metric_local atlasA cA (\z. Q %% (gA:A->real^N^N) z))
                (rfs_pullback atlasL ((psi:A->B) o chart_inv cA) (g0:B->real^N^N))
                (SND (cA:(A->bool)#(A->real^N)) y') =
    lck_dist2 m (metric_local atlasA cA
                   (mfd_pullback_metric atlasA atlasL psi
                      (mfd_pullback_metric atlasL atlasA (phi:B->A) (\z. Q %% gA z))))
                (metric_local atlasA cA (mfd_pullback_metric atlasA atlasL psi g0))
                (SND cA y')`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (cA:(A->bool)#(A->real^N))) (FST cA INTER W')` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                     `topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                     `W:B->bool`; `W':A->bool`; `phi:B->A`; `psi:A->B`;
                     `\z:A. Q %% (gA:A->real^N^N) z`; `w:A`] P2B9S_PB_PB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BL_PB_CHART THEN
      MAP_EVERY EXISTS_TAC [`topA:A topology`; `topL:B topology`; `W':A->bool`;
                            `W:B->bool`; `phi:B->A`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  (* step 3: naturality under psi *)
  MP_TAC(ISPECL [`topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                 `topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                 `W:B->bool`; `W':A->bool`; `phi:B->A`; `psi:A->B`; `gA:A->real^N^N`;
                 `cL:(B->bool)#(B->real^N)`] P2BU_PB_LOCAL_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W))
      (\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv cL) (gA:A->real^N^N) w) /\
    metric_field (IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W))
      (metric_local atlasL cL (mfd_pullback_metric atlasL atlasA (phi:B->A)
                                 (\z. Q %% (gA:A->real^N^N) z))) /\
    metric_field (IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W))
      (metric_local atlasL cL (g0:B->real^N^N)) /\
    (!w. w IN IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W)
         ==> metric_local atlasL cL (mfd_pullback_metric atlasL atlasA (phi:B->A)
                                       (\z. Q %% (gA:A->real^N^N) z)) w =
             Q %% rfs_pullback atlasA (phi o chart_inv cL) gA w)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!w. w IN IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W)
          ==> metric_local atlasL cL (mfd_pullback_metric atlasL atlasA (phi:B->A)
                                        (\z. Q %% (gA:A->real^N^N) z)) w =
              Q %% rfs_pullback atlasA (phi o chart_inv cL) gA w`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                     `topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                     `W:B->bool`; `W':A->bool`; `phi:B->A`; `psi:A->B`;
                     `\z:A. Q %% (gA:A->real^N^N) z`; `cL:(B->bool)#(B->real^N)`; `w:real^N`]
                    P2BL_PB_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[P2B9_RFS_PULLBACK_CMUL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W))
        (\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv cL) (gA:A->real^N^N) w)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
      EXISTS_TAC `\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv cL)
                          (gA:A->real^N^N) w` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlasL (g0:B->real^N^N)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                 `topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                 `W':A->bool`; `W:B->bool`; `psi:A->B`; `phi:B->A`;
                 `mfd_pullback_metric atlasL atlasA (phi:B->A) (\z. Q %% (gA:A->real^N^N) z)`;
                 `g0:B->real^N^N`; `m:num`; `y':A`;
                 `IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W)`]
                P2B9S_LCK_NATURAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  (* step 4: the rfs_pullback form on the limit side and the exchange *)
  SUBGOAL_THEN
   `lck_dist2 m (metric_local atlasL cL (mfd_pullback_metric atlasL atlasA (phi:B->A)
                                          (\z. Q %% (gA:A->real^N^N) z)))
                (metric_local atlasL cL (g0:B->real^N^N)) (SND (cL:(B->bool)#(B->real^N)) z0) =
    lck_dist2 m (\w. Q %% rfs_pullback atlasA (phi o chart_inv cL) gA w)
                (metric_local atlasL cL g0) (SND cL z0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (cL:(B->bool)#(B->real^N)) z0 IN IMAGE (SND cL) (FST cL INTER W)`
  ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  USE_THEN "cl" (MP_TAC o REWRITE_RULE[ASSUME `(psi:A->B) y' = z0`;
                                       ASSUME `chart_at (atlasL:((B->bool)#(B->real^N))->bool)
                                                 (z0:B) = cL`]) THEN
  DISCH_TAC THEN
  USE_THEN "rev" (MP_TAC o SPECL
    [`IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W)`;
     `metric_local atlasL (cL:(B->bool)#(B->real^N)) (g0:B->real^N^N)`;
     `\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv (cL:(B->bool)#(B->real^N)))
                 (gA:A->real^N^N) w`;
     `metric_local atlasL (cL:(B->bool)#(B->real^N)) (g0:B->real^N^N)`;
     `SND (cL:(B->bool)#(B->real^N)) z0`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `IMAGE (SND (cL:(B->bool)#(B->real^N))) (FST cL INTER W)`;
                 `metric_local atlasL (cL:(B->bool)#(B->real^N)) (g0:B->real^N^N)`;
                 `\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv (cL:(B->bool)#(B->real^N)))
                             (gA:A->real^N^N) w`;
                 `SND (cL:(B->bool)#(B->real^N)) z0`] LCK_DIST2_REFLECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `M * lck_dist2 m (metric_local atlasL (cL:(B->bool)#(B->real^N)) (g0:B->real^N^N))
                (\w. Q %% rfs_pullback atlasA ((phi:B->A) o chart_inv cL) (gA:A->real^N^N) w)
                (SND cL z0)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* A component of the approximant inside the image of a diffeomorphism,     *)
(* whose preimage lies in a compact subset of the domain, maps onto a        *)
(* component of the (Hausdorff) limit.                                       *)

let P2BU_COMPONENT_TRANSFER = prove
 (`!(topL:B topology) (atlasL:((B->bool)#(B->real^N))->bool) topA
    (atlasA:((A->bool)#(A->real^N))->bool)
    W W' (phi:B->A) psi U K.
     hausdorff_space topL /\ smooth_manifold_atlas topA atlasA /\
     mfd_diffeo topL atlasL W topA atlasA W' phi psi /\
     U IN connected_components_of topA /\ U SUBSET W' /\
     compact_in topL K /\ K SUBSET W /\ IMAGE psi U SUBSET K
     ==> IMAGE psi U IN connected_components_of topL`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in topL (W:B->bool) /\ open_in topA (W':A->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:A->B) U = {z | z IN topspace (subtopology topL K) /\
                                        (phi:B->A) z IN U}` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(K:B->bool) SUBSET topspace topL` MP_TAC THENL
     [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (psi:A->B) U SUBSET K` THEN UNDISCH_TAC `(K:B->bool) SUBSET W` THEN
    UNDISCH_TAC `(U:A->bool) SUBSET W'` THEN
    UNDISCH_TAC `!x:B. x IN W ==> (psi:A->B) ((phi:B->A) x) = x` THEN
    UNDISCH_TAC `!y:A. y IN W' ==> (phi:B->A) ((psi:A->B) y) = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_CLOPEN_COMPONENT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology topA (W':A->bool)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF];
    SUBGOAL_THEN `open_in topA (U:A->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`]
                     APX_COMPONENT_OPEN) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`; `W':A->bool`;
                   `topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`; `W:B->bool`;
                   `psi:A->B`; `phi:B->A`; `U:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN MESON_TAC[mfd_diffeo];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `compact_in (subtopology topL K) (IMAGE (psi:A->B) U)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY] THEN
      ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `topA:A topology` THEN
      ASM_SIMP_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    ASM_MESON_TAC[NONEMPTY_CONNECTED_COMPONENTS_OF]]);;

(* The hypotheses of SLICE_FIX for a canonical neighbourhood U of xA in the  *)
(* approximant (metric Q gA) inside the image of phi, from limit-referenced *)
(* closeness on a compact K containing psi U.                               *)

let P2BU_SLICE_FIX_HYPS = prove
 (`!(topA:A topology) atlasA (gA:A->real^N^N) (topL:B topology) atlasL (g0:B->real^N^N)
    W W' (phi:B->A) psi Q K U xA m M eta.
     hausdorff_space topL /\ smooth_manifold_atlas topA atlasA /\
     smooth_manifold_atlas topL atlasL /\
     riemannian_metric atlasA gA /\ riemannian_metric atlasL g0 /\
     mfd_diffeo topL atlasL W topA atlasA W' phi psi /\ &0 < Q /\
     open_in topA U /\ xA IN U /\ U SUBSET W' /\
     compact_in topL K /\ K SUBSET W /\ IMAGE psi U SUBSET K /\
     &1 <= mfd_scalar atlasA (\z. Q %% gA z) xA /\
     &0 <= M /\ &0 <= eta /\ eta <= &1 / &4 /\
     (!s (G0:real^N->real^N^N) G1 G2 y.
        metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
        lck_dist2 m G0 G1 y <= &1 / &4
        ==> lck_dist2 m G1 G2 y <= M * lck_dist2 m G0 (\z. G0 z + G2 z - G1 z) y) /\
     (!z. z IN K
          ==> lck_dist2 m (metric_local atlasL (chart_at atlasL z) g0)
                (\w. Q %% rfs_pullback atlasA (phi o chart_inv (chart_at atlasL z)) gA w)
                (SND(chart_at atlasL z) z) <= eta)
     ==> mfd_diffeo topA atlasA U topL atlasL (IMAGE psi U) psi phi /\
         (U IN connected_components_of topA ==> IMAGE psi U IN connected_components_of topL) /\
         !y'. y' IN U
              ==> lck_dist2 m
                    (metric_local atlasA (chart_at atlasA y')
                       (\y. mfd_scalar atlasA (\z. Q %% gA z) xA %% (Q %% gA y)))
                    (metric_local atlasA (chart_at atlasA y')
                       (\y. mfd_scalar atlasA (\z. Q %% gA z) xA %%
                            mfd_pullback_metric atlasA atlasL psi g0 y))
                    (SND(chart_at atlasA y') y') <= &2 pow m * M * eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `W':A->bool` THEN
    EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC P2BU_COMPONENT_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`atlasL:((B->bool)#(B->real^N))->bool`; `topA:A topology`;
                          `atlasA:((A->bool)#(A->real^N))->bool`; `W:B->bool`; `W':A->bool`;
                          `phi:B->A`; `K:B->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y':A` THEN DISCH_TAC THEN
    ABBREV_TAC `c = mfd_scalar atlasA (\z. Q %% (gA:A->real^N^N) z) (xA:A)` THEN
    SUBGOAL_THEN `(y':A) IN W'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`topL:B topology`; `atlasL:((B->bool)#(B->real^N))->bool`;
                   `topA:A topology`; `atlasA:((A->bool)#(A->real^N))->bool`;
                   `W:B->bool`; `W':A->bool`; `phi:B->A`; `psi:A->B`; `g0:B->real^N^N`;
                   `gA:A->real^N^N`; `Q:real`; `c:real`; `m:num`; `M:real`; `eta:real`;
                   `y':A`] P2BU_REV_CLOSE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "rfs_pullback" with _ -> false))
            (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `bb <= cc ==> aa <= bb ==> aa <= cc`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &1 + x <= &2`) THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]]);;

(* Derivative bounds of the canonical rescaling: |nabla^l Rm|^2 <= CA Q^(l+2) *)
(* for gA gives |nabla^l Rm|^2 <= CA for (c Q) gA when c >= 1.               *)

let P2BU_KR_BOUND = prove
 (`!top atlas (gA:A->real^N^N) Q c CA y'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas gA /\ y' IN topspace top /\
     &0 < Q /\ &1 <= c /\ &0 <= CA /\
     (!l. l <= 2
          ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y') gA)
                (SND(chart_at atlas y') y') <= CA * Q pow (l + 2))
     ==> !l. l <= 2
             ==> lrm_deriv_norm2 l
                   (metric_local atlas (chart_at atlas y') (\z. c %% (Q %% gA z)))
                   (SND(chart_at atlas y') y') <= CA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y':A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC; METRIC_LOCAL_CMUL] THEN
  SUBGOAL_THEN `&0 < c * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y':A)))
                        (FST(chart_at atlas y'))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y':A))
                    (gA:A->real^N^N)`;
                 `c * Q`; `l:num`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y':A)) y'`]
                RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (gA:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "lrm_deriv_norm2" with _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= inv(c * Q) pow (l + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(c * Q) pow (l + 2) * (CA * Q pow (l + 2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(c * Q) pow (l + 2) * (CA * Q pow (l + 2)) = CA * inv c pow (l + 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; REAL_POW_MUL; REAL_POW_INV] THEN
    SUBGOAL_THEN `~(Q pow (l + 2) = &0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 11.6, the assembly of MT Thm 11.1 (B5) from the route            *)
(* hypotheses, and the main theorem P2BU_THM_11_1_VIEW_ROUTE.                *)
(* ------------------------------------------------------------------------- *)


(* The base points of a slice limit lie in their slices.                   *)

let P2BU_SLICE_BASE_IN = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl W phi n.
     p2c_slice_limit_with V x t Q (top,atlas) g xl W phi
     ==> x n IN topspace(rfs_vtop (V n) (t n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_slice_limit_with] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `psi:A->B` o SPEC `n:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "mfd_diffeo" with _ -> false))
        (concl th))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  MATCH_MP_TAC(SET_RULE `(z:A) IN s ==> s SUBSET t ==> z IN t`) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `xl:B` THEN ASM_MESON_TAC[]);;

(* MT Claim 11.6, general form: a slice limit at times t n with scales Q n,  *)
(* approximants with (C,eps)-canonical neighbourhoods above 4 Q n at t n and *)
(* Shi bounds on the rescaled balls about x n.  Used at time 0 (Thm 11.1)   *)
(* and at the times s of the long-time limits (Thm 11.8).                   *)

let P2BU_CLAIM_11_6_GEN = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_SLICE_FIX_STATEMENT u w
     ==> ?K1 eps1. &1 <= K1 /\ &0 < eps1 /\
           !C eps V x t Q (top:B topology) atlas g0 xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps1 /\
              (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3))) /\
              (!n y. y IN topspace(rfs_vtop (V n) (t n)) /\ &4 * Q n <= rfs_vscalar (V n) (t n) y
                     ==> p3_canon_at (V n) C eps y (t n)) /\
              (!A l. &0 < A
                     ==> ?CAl N. !n y. N <= n /\
                                       y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                       ==> p3_vderiv2 (V n) l (t n) y <= CAl * Q n pow (l + 2)) /\
              p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
              mfd_complete (top,atlas) g0 /\ connected_space top
              ==> !y. y IN topspace top /\ &4 < mfd_scalar atlas g0 y
                      ==> ?U. rfs_canonical_nbhd (top,atlas) g0 (&2 * C) (K1 * eps) y U`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `P2C_REQ_SLICE_FIX_STATEMENT (u:A->bool) (w:B->bool)` THEN
  REWRITE_TAC[P2C_REQ_SLICE_FIX_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `ef:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))))) THEN
  X_CHOOSE_THEN `eb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cib"))
    (INST_TYPE [`:A`,`:A`] CANON_NBHD_IN_BALL) THEN
  MAP_EVERY EXISTS_TAC [`K1:real`; `min (ef / K1) eb`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `Q:num->real`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
    `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "reg0")
    (CONJUNCTS_THEN2 (LABEL_TAC "canon") (CONJUNCTS_THEN2 (LABEL_TAC "shi")
    STRIP_ASSUME_TAC)))))) THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\
                    (x:num->A) n IN topspace(rfs_vtop (V n) ((t:num->real) n))`
  (LABEL_TAC "views") THENL
   [GEN_TAC THEN USE_THEN "reg0" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC P2BU_SLICE_BASE_IN THEN
    MAP_EVERY EXISTS_TAC [`Q:num->real`; `top:B topology`;
      `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
      `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `K1 * eps <= ef` ASSUME_TAC THENL
   [UNDISCH_TAC `eps <= ef / K1` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= k ==> &0 < k`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the slice limit *)
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B11_SLICE_TO_FLOW0 o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with" with _ -> false))
        (concl th))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_slice_limit_with] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_slice_limit_with" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Qpos") (CONJUNCTS_THEN2 (LABEL_TAC "Wk")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "phx")
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "conv")))))))))) THEN
  SUBGOAL_THEN `!n s. ~(topspace(rfs_vtop ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) s) = {})
                  ==> smooth_manifold_atlas (rfs_vtop (V n) s) (rfs_vatlas (V n) s) /\
                      riemannian_metric (rfs_vatlas (V n) s) (rfs_vmetric (V n) s)`
  (LABEL_TAC "slices") THENL
   [MATCH_MP_TAC P2CO_REGULAR_SLICES THEN USE_THEN "views" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  (* radii *)
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (xl:B) y` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `d0 = mfd_dist (top,atlas) (g0:B->real^3^3) xl y` THEN
  SUBGOAL_THEN `&0 <= d0` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Dc = max (sqrt(&1 + eps) * (inv eps + sqrt(&2) * pi)) (max (C * sqrt C) (&12))` THEN
  SUBGOAL_THEN `&12 <= Dc` ASSUME_TAC THENL [EXPAND_TAC "Dc" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = d0 + Dc / &2 + &5` THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [EXPAND_TAC "A" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "shi" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `0`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CA0:real` (X_CHOOSE_THEN `N0:num` (LABEL_TAC "s0"))) THEN
  USE_THEN "shi" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `1`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CA1:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "s1"))) THEN
  USE_THEN "shi" (MP_TAC o C MP (ASSUME `&0 < A`) o SPECL [`A:real`; `2`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CA2:real` (X_CHOOSE_THEN `N2:num` (LABEL_TAC "s2"))) THEN
  ABBREV_TAC `Kr = max (&0) (max CA0 (max CA1 CA2))` THEN
  (* SLICE_FIX: delta, then m, M, eta *)
  USE_THEN "fix" (MP_TAC o SPECL [`C:real`; `eps:real`; `&2 * C`; `K1 * eps`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fixD"))) THEN
  ABBREV_TAC `m = rfs_kreg delta` THEN
  MP_TAC(SPEC `m:num` (INST_TYPE [`:3`,`:N`] LCK_CK_BASE_REV)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))) THEN
  ABBREV_TAC `eta = min (&1 / &4) (delta pow 2 / (&2 * &2 pow m * (M + &1)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 / &4 /\ &2 pow m * M * eta < delta pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * &2 pow m * (M + &1) /\ &0 < delta pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `eta * (&2 * &2 pow m * (M + &1)) <= delta pow 2 /\ &0 < eta`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN EXPAND_TAC "eta" THEN REAL_ARITH_TAC;
        EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      EXPAND_TAC "eta" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= &2 pow m * eta` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      UNDISCH_TAC `eta * (&2 * &2 pow m * (M + &1)) <= delta pow 2` THEN
      UNDISCH_TAC `&0 < delta pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* convergence at y and inclusions of balls *)
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `Q:num->real`;
                 `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\s:real. (g0:B->real^3^3)`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `y:B`; `(mfd_scalar atlas (g0:B->real^3^3) y - &4) / &2`]
                P2BU_POINT_CURV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SING] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC; USE_THEN "views" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `Np:num` (LABEL_TAC "pc")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `Q:num->real`;
                 `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\s:real. (g0:B->real^3^3)`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `y:B`; `Dc / &2 + &1`; `Dc / &2 + &2`] LIM_BALL_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SING; REAL_ARITH `x + &1 < x + &2`] THEN
    REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) k`; `(t:num->real) k`; `(x:num->A) k`]
                    P2C_REGULAR_SLICE) THEN
      ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nin:num` (LABEL_TAC "bin")) THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`;
                 `Q:num->real`;
                 `{&0}`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\s:real. (g0:B->real^3^3)`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `&0`; `xl:B`; `d0 + Dc / &2 + &3`; `d0 + Dc / &2 + &4`] LIM_BALL_OUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SING] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `!q. &0 / q = &0`; REAL_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nout:num` (LABEL_TAC "bout")) THEN
  ABBREV_TAC `Kc = (top:B topology) closure_of
                   mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 y (Dc / &2 + &2)` THEN
  SUBGOAL_THEN `compact_in (top:B topology) Kc /\ (y:B) IN Kc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g0:B->real^3^3`; `y:B`;
                     `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 y (Dc / &2 + &2)`;
                     `Dc / &2 + &2`] P2BL_BOUNDED_CLOSURE_COMPACT) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
      EXISTS_TAC `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 y (Dc / &2 + &2)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
        MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]]];
    ALL_TAC] THEN
  USE_THEN "conv" (MP_TAC o SPECL [`Kc:B->bool`; `m:num`; `eta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nc:num` (LABEL_TAC "cv")) THEN
  (* the index k *)
  ABBREV_TAC `k = Np + Nin + Nout + Nc + N0 + N1 + N2:num` THEN
  SUBGOAL_THEN `Np <= k /\ Nin <= k /\ Nout <= k /\ Nc <= k /\ N0 <= k /\ N1 <= k /\
                N2 <= k:num` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN ARITH_TAC; ALL_TAC] THEN
  (* the canonical neighbourhood of phi k y in the slice at t k *)
  USE_THEN "pc" (MP_TAC o C MP (ASSUME `Np <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `&0 < (Q:num->real) k` ASSUME_TAC THENL
   [USE_THEN "Qpos" (ACCEPT_TAC o SPEC `k:num`); ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (Q:num->real) k <
                rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) ((phi:num->B->A) k y)` ASSUME_TAC THENL
   [REWRITE_TAC[P2B9_RFS_VSCALAR] THEN
    SUBGOAL_THEN `&4 < mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                         ((phi:num->B->A) k y) / (Q:num->real) k`
    MP_TAC THENL
     [UNDISCH_TAC `abs(mfd_scalar atlas (g0:B->real^3^3) y -
                       mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)) (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                         ((phi:num->B->A) k y) / (Q:num->real) k) <
                   (mfd_scalar atlas g0 y - &4) / &2` THEN
      UNDISCH_TAC `&4 < mfd_scalar atlas (g0:B->real^3^3) y` THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[P2B9_RFS_VSCALAR] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "views" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)`; `(t:num->real) k`; `(x:num->A) k`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "canon" (MP_TAC o SPECL [`k:num`; `(phi:num->B->A) k y`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[p3_canon_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (ASSUME_TAC o MATCH_MP P2BU_STRONG_SLICE)) THEN
  USE_THEN "cib" (MP_TAC o SPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
    `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `C:real`; `eps:real`; `(phi:num->B->A) k y`; `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inb"))) THEN
  (* U lies in the image of phi k *)
  USE_THEN "dif" (X_CHOOSE_TAC `psi:A->B` o SPEC `k:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term ((=) `psi:A->B`)) (concl th) &&
    can (find_term (fun u -> try fst(dest_const u) = "mfd_diffeo" with _ -> false)) (concl th))) THEN
  USE_THEN "cv" (MP_TAC o C MP (ASSUME `Nc <= k:num`) o SPEC `k:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cvk")) THEN
  SUBGOAL_THEN `!z. z IN U
                    ==> ?w. w IN mfd_ball (top,atlas) (g0:B->real^3^3) y (Dc / &2 + &2) /\
                            w IN W (k:num) /\ z = (phi:num->B->A) k w`
  (LABEL_TAC "Uw") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "bin" (MP_TAC o SPECL [`k:num`; `z:A`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "inb" (MP_TAC o C MP (ASSUME `(z:A) IN U`) o SPEC `z:A`) THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN
      MATCH_MP_TAC(REAL_ARITH `bb < cc ==> aa <= bb ==> aa < cc`) THEN
      SUBGOAL_THEN `inv(sqrt(rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) ((phi:num->B->A) k y))) <=
                    inv(&2) * inv(sqrt((Q:num->real) k))`
      MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `&2 = sqrt(&4)` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          ALL_TAC] THEN
        ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 < inv(sqrt((Q:num->real) k))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `Dc * inv(&2) * inv(sqrt((Q:num->real) k))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM ACCEPT_TAC];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET IMAGE ((phi:num->B->A) k) (W k) /\
                IMAGE (psi:A->B) U SUBSET Kc` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:A` THEN
    DISCH_TAC THEN USE_THEN "Uw" (MP_TAC o C MP (ASSUME `(z:A) IN U`) o SPEC `z:A`) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:B` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[] THEN EXPAND_TAC "Kc" THEN
      MATCH_MP_TAC(SET_RULE `!s t (z:B). z IN s /\ s SUBSET t ==> z IN t`) THEN
      EXISTS_TAC `mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) g0 y (Dc / &2 + &2)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC CLOSURE_OF_SUBSET] THEN
      REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  (* Shi bounds on U, through the ball about x k *)
  SUBGOAL_THEN `!z. z IN U
                    ==> z IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) ((x:num->A) k)
                               (A * inv(sqrt((Q:num->real) k)))`
  (LABEL_TAC "Ub") THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "Uw" (MP_TAC o C MP (ASSUME `(z:A) IN U`) o SPEC `z:A`) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:B) IN mfd_ball (top,atlas) (g0:B->real^3^3) xl (d0 + Dc / &2 + &3)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(w:B) IN mfd_ball (top,atlas) (g0:B->real^3^3) y (Dc / &2 + &2)` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g0:B->real^3^3) xl y + mfd_dist (top,atlas) g0 y w` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "bout" (MP_TAC o SPECL [`k:num`; `w:B`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "phx" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[P2CO_VBALL] THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:A). s SUBSET t ==> z IN s ==> z IN t`) THEN
    MATCH_MP_TAC P2CU_BALL_MONO THEN EXPAND_TAC "A" THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `CA0 <= Kr /\ CA1 <= Kr /\ CA2 <= Kr /\ &0 <= Kr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kr" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `C:real`; `eps:real`;
                   `(phi:num->B->A) k y`; `U:A->bool`] CANON_NBHD_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cc = mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k))
                     (\z. (Q:num->real) k %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) z)
                     ((phi:num->B->A) k y)` THEN
  SUBGOAL_THEN `&1 <= cc` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `(Q:num->real) k`;
                   `(phi:num->B->A) k y`] P2BCS_SCALAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `&4 * (Q:num->real) k <
                 rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) ((phi:num->B->A) k y)` THEN
    REWRITE_TAC[P2B9_RFS_VSCALAR] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y' l. y' IN U /\ l <= 2
           ==> lrm_deriv_norm2 l
                 (metric_local (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)) (chart_at (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)) y')
                    (\z. cc %% ((Q:num->real) k %%
                               rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) z)))
                 (SND(chart_at (rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)) y') y') <= Kr`
  (LABEL_TAC "Kr") THENL
   [MAP_EVERY X_GEN_TAC [`y':A`; `l:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
                   `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `(Q:num->real) k`;
                   `cc:real`; `Kr:real`; `y':A`] P2BU_KR_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2` MP_TAC THENL
       [UNDISCH_TAC `j <= 2` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "Ub" (MP_TAC o C MP (ASSUME `(y':A) IN U`) o SPEC `y':A`) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (Q:num->real) k pow (j + 2)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[GSYM p3_vderiv2] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
       [USE_THEN "s0" (MP_TAC o SPECL [`k:num`; `y':A`]);
        USE_THEN "s1" (MP_TAC o SPECL [`k:num`; `y':A`]);
        USE_THEN "s2" (MP_TAC o SPECL [`k:num`; `y':A`])] THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      MATCH_MP_TAC(REAL_ARITH `qq <= rr ==> pp <= qq ==> pp <= rr`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the hypotheses of SLICE_FIX and SLICE_FIX itself *)
  MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
                 `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `(W:num->B->bool) k`; `IMAGE ((phi:num->B->A) k) (W k)`;
                 `(phi:num->B->A) k`; `psi:A->B`; `(Q:num->real) k`;
                 `Kc:B->bool`; `U:A->bool`; `(phi:num->B->A) k y`; `m:num`; `M:real`;
                 `eta:real`] P2BU_SLICE_FIX_HYPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN NO_TAC;
      MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
                     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `C:real`; `eps:real`;
                     `(phi:num->B->A) k y`; `U:A->bool`] CANON_NBHD_OPEN) THEN
      ASM_SIMP_TAC[] THEN NO_TAC;
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "cvk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lckU"))) THEN
  SUBGOAL_THEN `(psi:A->B) ((phi:num->B->A) k y) = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `psi:A->B`)) (concl th) &&
      can (find_term ((=) `(W:num->B->bool) k`)) (concl th) &&
      not (can (find_term (fun u -> try fst(dest_const u) = "mfd_diffeo" with _ -> false))
               (concl th)))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "fixD" (MP_TAC o SPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
    `\z. (Q:num->real) k %% rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k) z`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
    `(phi:num->B->A) k y`; `U:A->bool`; `psi:A->B`; `(phi:num->B->A) k`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN NO_TAC;
      MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`;
                     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (t k)`; `C:real`; `eps:real`; `(phi:num->B->A) k y`;
                     `U:A->bool`; `(Q:num->real) k`] P2BCS_CANON_CMUL) THEN
      ASM_SIMP_TAC[] THEN NO_TAC;
      REWRITE_TAC[rfs_mclose] THEN EXISTS_TAC `&2 pow m * M * eta` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      USE_THEN "lckU" (MP_TAC o C MP (ASSUME `(z:A) IN U`) o SPEC `z:A`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* MT Claim 11.6 for blow-up sequences at time 0 (from the general form,   *)
(* with Shi bounds from P2BU_SEQ_SHI).                                        *)

let P2BU_CLAIM_11_6 = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u
     ==> ?K1 eps1. &1 <= K1 /\ &0 < eps1 /\
           !C eps kappa r0 mu V x t (top:B topology) atlas g0 xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps1 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                (top,atlas) g0 xl W phi /\
              mfd_complete (top,atlas) g0 /\ connected_space top
              ==> !y. y IN topspace top /\ &4 < mfd_scalar atlas g0 y
                      ==> ?U. rfs_canonical_nbhd (top,atlas) g0 (&2 * C) (K1 * eps) y U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CLAIM_11_6_GEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `eg:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen"))))) THEN
  MP_TAC(SPEC `u:A->bool` P2BU_SEQ_REGION_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `er:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sra"))) THEN
  MAP_EVERY EXISTS_TAC [`K1:real`; `min eg er`] THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qinf") (CONJUNCTS_THEN2 (LABEL_TAC "canon")
    (K ALL_TAC))))))) THEN
  USE_THEN "sra" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "reg")] THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`] P2BU_SEQ_SHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "shi")] THEN
  USE_THEN "gen" (MP_TAC o SPECL [`C:real`; `eps:real`; `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `x:num->A`; `t:num->real`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (t n) ((x:num->A) n)`; `top:B topology`;
    `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`;
    `phi:num->B->A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "canon" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    SIMP_TAC[]]);;


(* Claims 11.6, 11.7 and the last paragraph on a connected complete time-0  *)
(* slice limit.                                                              *)

let P2BU_STAGE3 = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t (top:B topology) atlas g0 xl W (phi:num->B->A).
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              p2c_slice_limit_with V x t (\n. rfs_vscalar (V n) (t n) (x n))
                (top,atlas) g0 xl W phi /\
              mfd_complete (top,atlas) g0 /\ connected_space top
              ==> ?sub (top':B topology) atlas' g T1 K.
                     &0 < T1 /\ p3_subseq sub /\
                     p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                       (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                       (top',atlas') g xl T1 /\
                     (!s. --T1 < s /\ s <= &0
                          ==> mfd_complete (top',atlas') (g s) /\
                              (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                                       ==> &0 <= mfd_sectional atlas' (g s) y u v) /\
                              (!y. y IN topspace top' ==> mfd_rm_norm atlas' (g s) y <= K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_S9) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s9"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_CLAIM_11_6) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K1:real` (X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c116"))))) THEN
  UNDISCH_TAC `P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a4"))) THEN
  EXISTS_TAC `min e2 (min e3 (e4 / K1))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `K1 * eps <= e4 /\ &1 < &2 * C /\ &0 < K1 * eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `eps <= e4 / K1` THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= k ==> &0 < k`] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
    can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
        (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "views")
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
  (* Claim 11.6 *)
  USE_THEN "c116" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* Claim 11.7 *)
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`; `&2 * C`; `K1 * eps`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] P2BU_CLAIM_11_7) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`top1:B topology`; `atlas1:((B->bool)#(B->real^3))->bool`;
                         `g1:B->real^3^3`] THEN STRIP_TAC THEN
    USE_THEN "a4" (MP_TAC o SPECL [`&2 * C`; `K1 * eps`; `top1:B topology`;
      `atlas1:((B->bool)#(B->real^3))->bool`; `g1:B->real^3^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC)] THEN
  (* the last paragraph *)
  USE_THEN "s9" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* Restriction of the time-0 limit to the component of its base point.      *)

let P2BU_STAGE2 = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_THM_5_33_STATEMENT u w /\
     P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> ?eps0. &0 < eps0 /\
           !C eps kappa r0 mu V x t (top:B topology) atlas g0 xl.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\
              p2c_vblowup_seq (C,eps,kappa,r0,mu)
                (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) x t /\
              (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
              (!A. ?N. !n. N <= n
                           ==> compact_in (rfs_vtop (V n) (t n))
                                 (rfs_vtop (V n) (t n) closure_of
                                  rfs_vball (V n) (t n) (x n)
                                    (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))) /\
              p3_slice_limit V x t (\n. rfs_vscalar (V n) (t n) (x n)) (top,atlas) g0 xl
              ==> ?sub (top':B topology) atlas' g T1 K.
                     &0 < T1 /\ p3_subseq sub /\
                     p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                       (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                       (top',atlas') g xl T1 /\
                     (!s. --T1 < s /\ s <= &0
                          ==> mfd_complete (top',atlas') (g s) /\
                              (!y u v. y IN topspace top' /\ ~collinear {vec 0,u,v}
                                       ==> &0 <= mfd_sectional atlas' (g s) y u v) /\
                              (!y. y IN topspace top' ==> mfd_rm_norm atlas' (g s) y <= K))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BU_STAGE3) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st3")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g0:B->real^3^3`; `xl:B`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`;
    `\n. rfs_vscalar ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`]
   P2CO_P3_SLICE_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CO_REGULAR_SLICES THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p2c_vblowup_seq] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p2c_vblowup_seq" with _ -> false))
          (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2C_SLICE_LIMIT_WITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_TAC `phi:num->B->A`))) ASSUME_TAC) THEN
  USE_THEN "st3" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`;
    `subtopology (top:B topology)
       {y | mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) xl y}`;
    `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
       {y | mfd_joinable (top:B topology,atlas) xl y}`;
    `restrict_metric (atlas:((B->bool)#(B->real^3))->bool)
       {y | mfd_joinable (top:B topology,atlas) xl y} (g0:B->real^3^3)`;
    `xl:B`; `W:num->B->bool`; `phi:num->B->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* MT Thm 11.1 in view form from the route hypotheses (the route of B5).    *)

let P2BU_THM_11_1_CORE = prove
 (`!(u:A->bool) (w:B->bool).
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CG_COMPACT_STATEMENT u w /\
     P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
     ==> P2C_THM_11_1_VIEW_STATEMENT u w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_TIME0_LIMIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t0l"))) THEN
  MP_TAC(SPECL [`u:A->bool`; `w:B->bool`] P2BU_STAGE2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st2"))) THEN
  REWRITE_TAC[P2C_THM_11_1_VIEW_STATEMENT] THEN EXISTS_TAC `min e1 e2` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc")))))) THEN
  USE_THEN "t0l" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub1:num->num` (X_CHOOSE_THEN `top:B topology`
    (X_CHOOSE_THEN `atlas:((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g0:B->real^3^3`
    (X_CHOOSE_THEN `xl:B` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `!n:num. n <= sub1 n` (LABEL_TAC "ge") THENL
   [MP_TAC(ISPEC `sub1:num->num` MONOTONE_BIGGER) THEN REWRITE_TAC[GSYM p3_subseq] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "st2" (MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
    `\n. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) ((sub1:num->num) n)`;
    `(x:num->A) o (sub1:num->num)`; `(t:num->real) o (sub1:num->num)`;
    `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `xl:B`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST
     [MATCH_MP_TAC P2BU_VBLOWUP_SUBSEQ THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[o_THM] THEN X_GEN_TAC `A:real` THEN
      USE_THEN "cc" (X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub2:num->num` (X_CHOOSE_THEN `top':B topology`
    (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool` (X_CHOOSE_THEN `g:real->B->real^3^3`
    (X_CHOOSE_THEN `T1:real` (X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`(sub1:num->num) o (sub2:num->num)`; `top':B topology`;
    `atlas':((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `xl:B`; `T1:real`;
    `K:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p3_subseq (sub1:num->num)` THEN UNDISCH_TAC `p3_subseq (sub2:num->num)` THEN
    REWRITE_TAC[p3_subseq; o_THM] THEN MESON_TAC[];
    REWRITE_TAC[o_DEF] THEN
    FIRST_X_ASSUM(ACCEPT_TAC o REWRITE_RULE[o_DEF] o check (fun th ->
      can (find_term (fun u -> try fst(dest_const u) = "p3_flow_limit" with _ -> false))
          (concl th)))]);;

(* Headline: MT Thm 11.1 in view form along its route.                      *)

let P2BU_THM_11_1_VIEW_ROUTE = prove
 (`!u:A->bool. P2C_THM_11_1_VIEW_ROUTE_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P2C_THM_11_1_VIEW_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BU_THM_11_1_CORE THEN ASM_REWRITE_TAC[]);;

