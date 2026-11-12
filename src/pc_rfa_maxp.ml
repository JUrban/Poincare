(* ========================================================================= *)
(* Unit pc_rfa_maxp: scalar maximum principles on compact open sets of       *)
(* manifolds with a time-dependent metric: a Gronwall-type comparison lemma  *)
(* for left difference quotients, attainment and continuity of spatial       *)
(* maxima (tube lemma), the maximum and minimum principles in barrier form   *)
(* with ODE comparison (RFA_MAXP_BARRIER, RFA_MINP_BARRIER) and for          *)
(* functions smooth in charts (RFA_MAXP_SCALAR, RFA_MINP_SCALAR).            *)
(* ========================================================================= *)

needs "src/pc_rfa_lalg.ml";;
needs "src/pc_mfd_riem.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The real-variable comparison lemma.  A continuous e on                    *)
(* [a,b] with e(a) <= 0 whose left difference quotients at every positive    *)
(* value are, along arbitrarily small steps, at most L e(t) + eps, stays     *)
(* <= 0 (the max of e(t) exp(-(L+1) t) cannot be at a positive value).       *)
(* ========================================================================= *)

let RFA_EXP_STEP = prove
 (`!L h. &0 <= L /\ &0 < h /\ h * (&2 * (L + &1) pow 2 + &1) < &1
         ==> &1 < (&1 - h * (L + inv(&2))) * exp((L + &1) * h) /\
             &0 < &1 - h * (L + inv(&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `be = L + &1` THEN
  SUBGOAL_THEN `&1 <= be` ASSUME_TAC THENL
   [EXPAND_TAC "be" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L + inv(&2) = be - inv(&2)` SUBST1_TAC THENL
   [EXPAND_TAC "be" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `be <= be pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h * be < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `h * (&2 * be pow 2 + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `be:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * h * be pow 2 < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `h * (&2 * be pow 2 + &1) < &1` THEN
    UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - h * (be - inv(&2))` ASSUME_TAC THENL
   [UNDISCH_TAC `h * be < &1` THEN UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `(&1 - h * (be - inv(&2))) * (&1 + be * h)` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(&1 - h * (be - inv(&2))) * (&1 + be * h) =
      &1 + h * inv(&2) - h * (h * (be pow 2 - be * inv(&2)))`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `h * (be pow 2 - be * inv(&2)) < inv(&2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `h * be pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&2 * h * be pow 2 < &1` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`h:real`; `h * (be pow 2 - be * inv(&2))`; `inv(&2)`]
           REAL_LT_LMUL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(SPEC `be * h` REAL_EXP_LE_X) THEN REWRITE_TAC[]]);;

let RFA_DINI_GRONWALL = prove
 (`!e a b L.
        a < b /\ &0 <= L /\ e real_continuous_on real_interval[a,b] /\
        e a <= &0 /\
        (!t. a < t /\ t <= b /\ &0 < e t
             ==> !eps d. &0 < eps /\ &0 < d
                         ==> ?h. &0 < h /\ h < d /\ a <= t - h /\
                                 e t - e(t - h) <= h * (L * e t + eps))
        ==> !t. a <= t /\ t <= b ==> e t <= &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dini"))))) THEN
  X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `q = \t. (e:real->real) t * exp(--((L + &1) * t))` THEN
  SUBGOAL_THEN `q real_continuous_on real_interval[a,t1]` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EXP] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (q:real->real) (real_interval[a,t1])`
         REAL_COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_COMPACT_CONTINUOUS_IMAGE; REAL_COMPACT_INTERVAL] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; REAL_INTERVAL_NE_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "max"))) THEN
  SUBGOAL_THEN `&0 < (e:real->real) ts` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (e:real->real) ts * exp(--((L + &1) * ts))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(e:real->real) t1 * exp(--((L + &1) * t1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
        USE_THEN "max" (MP_TAC o SPEC `t1:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "q" THEN REWRITE_TAC[]];
      MP_TAC(SPECL [`&0`; `(e:real->real) ts`; `exp(--((L + &1) * ts))`]
             REAL_LT_RMUL_EQ) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_POS_LT] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < ts` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "dini" (MP_TAC o SPEC `ts:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * (L + &1) pow 2 + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &2 * x + &1`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(e:real->real) ts / &2`;
    `min (ts - a) (&1 / (&2 * (L + &1) pow 2 + &1))`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_HALF; REAL_LT_MIN; REAL_SUB_LT; REAL_LT_DIV; REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`L:real`; `h:real`] RFA_EXP_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `h < &1 / (&2 * (L + &1) pow 2 + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "max" (MP_TAC o SPEC `ts - h:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "q" THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  SUBGOAL_THEN
   `exp(--((L + &1) * (ts - h))) = exp(--((L + &1) * ts)) * exp((L + &1) * h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(e:real->real) ts * (&1 - h * (L + inv(&2))) <= e(ts - h)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(e:real->real) ts - e(ts - h) <= h * (L * e ts + e ts / &2)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `--((L + &1) * ts)` REAL_EXP_POS_LT) THEN
  ABBREV_TAC `E = exp(--((L + &1) * ts))` THEN
  ABBREV_TAC `X = exp((L + &1) * h)` THEN
  ABBREV_TAC `c = &1 - h * (L + inv(&2))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (e:real->real) ts * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((e:real->real) ts * E) * &1 < (e ts * E) * (c * X)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((e:real->real) ts * c) * (E * X) <= e(ts - h) * (E * X)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The spatial maximum of a jointly continuous function over a               *)
(* compact set is attained, and it depends continuously on the parameter     *)
(* (tube lemma for the upper bound, a fixed maximum point for the lower).    *)
(* ========================================================================= *)

(* Copy of REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP from                         *)
(* Autoformalization/sarkovskii.ml of HOL Light (same statement and proof),  *)
(* which is too heavy to load for this one lemma.                            *)

let RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP = prove
 (`!f s.
        f real_continuous_on s <=>
        continuous_map
         (subtopology euclideanreal s,euclideanreal) f`,
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
              GSYM MTOPOLOGY_SUBMETRIC] THEN
  REWRITE_TAC[METRIC_CONTINUOUS_MAP; real_continuous_on] THEN
  REWRITE_TAC[SUBMETRIC; REAL_EUCLIDEAN_METRIC; IN_UNIV; IN_INTER] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_ABS_SUB] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:real`; `e:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[REAL_ABS_SUB];
    DISCH_TAC THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `e:real`]) THEN
    ASM_REWRITE_TAC[REAL_ABS_SUB]]);;

let RFA_SLICE_CONTINUOUS = prove
 (`!(top:A topology) (top':B topology) (f:A->B->real) x.
        x IN topspace top /\
        continuous_map (prod_topology top top',euclideanreal)
                       (\z. f (FST z) (SND z))
        ==> continuous_map (top',euclideanreal) (f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B->real) x = (\z. f (FST z) (SND z)) o (\y:B. (x:A),y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (top:A topology) (top':B topology)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_CONST;
                  CONTINUOUS_MAP_ID]);;

let RFA_SLICE_CONTINUOUS_LEFT = prove
 (`!(top:A topology) (top':B topology) (f:A->B->real) y.
        y IN topspace top' /\
        continuous_map (prod_topology top top',euclideanreal)
                       (\z. f (FST z) (SND z))
        ==> continuous_map (top,euclideanreal) (\x. f x y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:A->B->real) x y) = (\z. f (FST z) (SND z)) o (\x:A. x,(y:B))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (top:A topology) (top':B topology)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_CONST;
                  CONTINUOUS_MAP_ID]);;

let RFA_SUP_COMPACT_ATTAINED = prove
 (`!(top:A topology) (top':B topology) k (f:A->B->real) x.
        compact_in top' k /\ ~(k = {}) /\ x IN topspace top /\
        continuous_map (prod_topology top (subtopology top' k),euclideanreal)
                       (\z. f (FST z) (SND z))
        ==> ?y. y IN k /\ sup(IMAGE (f x) k) = f x y /\
                !y'. y' IN k ==> f x y' <= f x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `subtopology (top':B topology) k`;
                 `f:A->B->real`; `x:A`] RFA_SLICE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_compact (IMAGE ((f:A->B->real) x) k)` ASSUME_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology (top':B topology) k` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. !w. w IN IMAGE ((f:A->B->real) x) k ==> w <= B`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[real_bounded] THEN
    MESON_TAC[REAL_ARITH `abs w <= B ==> w <= B`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE ((f:A->B->real) x) k` REAL_COMPACT_CONTAINS_SUP) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` (CONJUNCTS_THEN2 (LABEL_TAC "eq") ASSUME_TAC)) THEN
  EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y':B` THEN DISCH_TAC THEN
  USE_THEN "eq" (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  MATCH_MP_TAC ELEMENT_LE_SUP THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let RFA_SUP_COMPACT_CONTINUOUS = prove
 (`!(top:A topology) (top':B topology) k (f:A->B->real).
        compact_in top' k /\ ~(k = {}) /\
        continuous_map (prod_topology top (subtopology top' k),euclideanreal)
                       (\z. f (FST z) (SND z))
        ==> continuous_map (top,euclideanreal) (\x. sup(IMAGE (f x) k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont"))) THEN
  SUBGOAL_THEN `(k:B->bool) SUBSET topspace top'` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT] THEN
  CONJ_TAC THEN X_GEN_TAC `r:real` THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x0:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `top':B topology`; `k:B->bool`;
                 `f:A->B->real`; `x0:A`] RFA_SUP_COMPACT_ATTAINED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:B` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `{x | x IN topspace top /\ (f:A->B->real) x y0 > r}` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `subtopology (top':B topology) k`;
                     `f:A->B->real`; `y0:B`] RFA_SLICE_CONTINUOUS_LEFT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT1 o
        GEN_REWRITE_RULE I [CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT]) THEN
      REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `top':B topology`; `k:B->bool`;
                     `f:A->B->real`; `x:A`] RFA_SUP_COMPACT_ATTAINED) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y1:B` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:A->B->real) x y0 <= f x y1` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `subtopology (top':B topology) k`; `x0:A`;
                 `k:B->bool`;
                 `{z | z IN topspace(prod_topology (top:A topology)
                                    (subtopology (top':B topology) k)) /\
                       (f:A->B->real) (FST z) (SND z) < r}`]
         TUBE_LEMMA_RIGHT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "cont" (MP_TAC o SPEC `r:real` o CONJUNCT2 o
        GEN_REWRITE_RULE I [CONTINUOUS_MAP_UPPER_LOWER_SEMICONTINUOUS_LT]) THEN
      REWRITE_TAC[];
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_SING; IN_ELIM_THM;
                  TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      MAP_EVERY X_GEN_TAC [`p1:A`; `p2:B`] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(f:A->B->real) x0 p2 <= f x0 y0` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (X_CHOOSE_THEN `v:B->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "tube"))))))) THEN
  EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `top':B topology`; `k:B->bool`;
                 `f:A->B->real`; `x:A`] RFA_SUP_COMPACT_ATTAINED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:B` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y1:B) IN v` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  USE_THEN "tube" (MP_TAC o SPEC `(x:A,y1:B)` o GEN_REWRITE_RULE I [SUBSET]) THEN
  ASM_REWRITE_TAC[IN_CROSS; IN_ELIM_THM; FST; SND] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The two local steps of the barrier maximum principle: the                 *)
(* one-sided difference estimate (time) and the second-derivative test at a  *)
(* spatial maximum in a chart (space).                                       *)
(* ========================================================================= *)

let RFA_LEFT_DERIV_BOUND = prove
 (`!(f:real->real) f' t0 s eps.
        (f has_real_derivative f') (atreal t0 within s) /\ &0 < eps
        ==> ?d. &0 < d /\
                !h. &0 < h /\ h < d /\ (t0 - h) IN s
                    ==> abs(f t0 - f(t0 - h) - h * f') <= eps * h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; REALLIM_WITHINREAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `eps:real`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  USE_THEN "d" (MP_TAC o SPEC `t0 - h:real`) THEN
  SUBGOAL_THEN `abs((t0 - h) - t0) = h` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Q = ((f:real->real)(t0 - h) - f t0) / ((t0 - h) - t0)` THEN
  SUBGOAL_THEN `(f:real->real) t0 - f(t0 - h) - h * f' = h * (Q - f')`
  SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN
    SUBGOAL_THEN `~((t0 - h) - t0 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < h ==> abs h = h`] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* The Dini step: at a time t0 where the spatial maximum M exceeds H, a     *)
(* lower barrier p for M at t0 with left derivative D, and the derivative V  *)
(* of H, with D - V <= L (M - H), give the hypothesis of RFA_DINI_GRONWALL. *)

let RFA_DINI_STEP = prove
 (`!(M:real->real) (H:real->real) (p:real->real) a b t0 d0 D V L.
        a < t0 /\ t0 < b /\ &0 < d0 /\ p t0 = M t0 /\
        (!t. t0 - d0 < t /\ t <= t0 /\ a <= t ==> p t <= M t) /\
        (p has_real_derivative D)
          (atreal t0 within {s | t0 - d0 <= s /\ s <= t0}) /\
        (H has_real_derivative V) (atreal t0 within {s | a <= s /\ s < b}) /\
        D - V <= L * (M t0 - H t0)
        ==> !eps d. &0 < eps /\ &0 < d
                    ==> ?h. &0 < h /\ h < d /\ a <= t0 - h /\
                            (M t0 - H t0) - (M(t0 - h) - H(t0 - h)) <=
                            h * (L * (M t0 - H t0) + eps)`,
  INTRO_TAC "!M H p a b t0 d0 D V L; at0 t0b d0pos peq pb pder hder dv" THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `d:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real->real`; `D:real`; `t0:real`;
                 `{s | t0 - d0 <= s /\ s <= t0}`; `eps / &2`]
         RFA_LEFT_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
  MP_TAC(ISPECL [`H:real->real`; `V:real`; `t0:real`;
                 `{s | a <= s /\ s < b}`; `eps / &2`]
         RFA_LEFT_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
  EXISTS_TAC `min (min d d0) (min (min d1 d2) (t0 - a)) / &2` THEN
  ABBREV_TAC `h = min (min d d0) (min (min d1 d2) (t0 - a)) / &2` THEN
  SUBGOAL_THEN `&0 < h /\ h < d /\ h < d0 /\ h < d1 /\ h < d2 /\ h < t0 - a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "d1" (MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "d2" (MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "pb" (MP_TAC o SPEC `t0 - h:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `h * (D - V) <= h * (L * ((M:real->real) t0 - (H:real->real) t0))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `abs((M:real->real) t0 - (p:real->real)(t0 - h) - h * D) <= eps / &2 * h` THEN
  UNDISCH_TAC `abs((H:real->real) t0 - H(t0 - h) - h * V) <= eps / &2 * h` THEN
  UNDISCH_TAC `(p:real->real)(t0 - h) <= (M:real->real)(t0 - h)` THEN
  UNDISCH_TAC `(p:real->real) t0 = (M:real->real) t0` THEN
  REAL_ARITH_TAC);;

(* The spatial step: a function phi below f on a chart neighbourhood W, with *)
(* equality at the chart image of a maximum point x0 of f on U, has zero     *)
(* gradient and nonpositive Laplacian there.                                 *)

let RFA_BARRIER_SPATIAL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U (g:A->real^N^N)
    (f:A->real) (phi:real^N->real) x0 W.
      smooth_manifold_atlas top atlas /\ open_in top U /\
      riemannian_metric atlas g /\
      x0 IN U /\ (!x. x IN U ==> f x <= f x0) /\
      open W /\ SND(chart_at atlas x0) x0 IN W /\
      W SUBSET IMAGE (SND(chart_at atlas x0)) (FST(chart_at atlas x0) INTER U) /\
      (!y. y IN W ==> phi y <= f (chart_inv (chart_at atlas x0) y)) /\
      phi (SND(chart_at atlas x0) x0) = f x0 /\
      smooth_map_on W (\y. lift(phi y))
      ==> ((\y. lift(phi y)) has_derivative (\v. vec 0))
            (at (SND(chart_at atlas x0) x0)) /\
          llap (metric_local atlas (chart_at atlas x0) g) phi
               (SND(chart_at atlas x0) x0) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) x0` THEN
  ABBREV_TAC `y0 = SND(c:(A->bool)#(A->real^N)) x0` THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN W ==> chart_inv (c:(A->bool)#(A->real^N)) y IN U`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`;
                   `SND(c:(A->bool)#(A->real^N))`] CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER U)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN W ==> (phi:real^N->real) y <= phi y0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(f:A->real) (chart_inv (c:(A->bool)#(A->real^N)) y)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((phi:real^N->real) y)) differentiable (at y0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. lift((phi:real^N->real) y)) (at y0) = (\v. vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIAL_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC [`\y. lift((phi:real^N->real) y)`; `y0:real^N`;
                          `W:real^N->bool`] THEN
    REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_LLAP_LOCAL_MAX THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                        `W:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN ASM_SIMP_TAC[];
    EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The scalar maximum principle in barrier form                              *)
(* (RFA_MAXP_BARRIER): the spatial maximum M of F is continuous,             *)
(* attained, and satisfies the Dini hypothesis of RFA_DINI_GRONWALL for     *)
(* M - H on every [a,t1], t1 < b.                                            *)
(* ========================================================================= *)

let RFA_MAXP_BARRIER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U a b
    (g:real->A->real^N^N) (ff:real->A->real) (psi:real->real->real)
    (H:real->real).
      smooth_manifold_atlas top atlas /\ compact_in top U /\ open_in top U /\
      a < b /\
      (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
      continuous_map (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                                    (subtopology top U),
                      euclideanreal) (\z. ff (FST z) (SND z)) /\
      (!c B. c < b
             ==> ?L. !t u v. a <= t /\ t <= c /\ abs u <= B /\ abs v <= B
                             ==> abs(psi t u - psi t v) <= L * abs(u - v)) /\
      (!t. a <= t /\ t < b
           ==> (H has_real_derivative psi t (H t)) (atreal t within {s | a <= s /\ s < b})) /\
      (!x. x IN U ==> ff a x <= H a) /\
      (!t0 x0. a < t0 /\ t0 < b /\ x0 IN U /\ H t0 < ff t0 x0 /\
               (!x. x IN U ==> ff t0 x <= ff t0 x0)
               ==> ?d W (phi:real->real^N->real) D.
                     &0 < d /\ open W /\ SND(chart_at atlas x0) x0 IN W /\
                     W SUBSET IMAGE (SND(chart_at atlas x0))
                                    (FST(chart_at atlas x0) INTER U) /\
                     (!y. y IN W
                          ==> phi t0 y <= ff t0 (chart_inv (chart_at atlas x0) y)) /\
                     phi t0 (SND(chart_at atlas x0) x0) = ff t0 x0 /\
                     (!t. t0 - d < t /\ t <= t0
                          ==> phi t (SND(chart_at atlas x0) x0) <= ff t x0) /\
                     smooth_map_on W (\y. lift(phi t0 y)) /\
                     ((\t. phi t (SND(chart_at atlas x0) x0)) has_real_derivative D)
                       (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
                     (((\y. lift(phi t0 y)) has_derivative (\v. vec 0))
                        (at (SND(chart_at atlas x0) x0))
                      ==> D <= llap (metric_local atlas (chart_at atlas x0) (g t0))
                                    (phi t0) (SND(chart_at atlas x0) x0) +
                               psi t0 (ff t0 x0)))
      ==> !t x. a <= t /\ t < b /\ x IN U ==> ff t x <= H t`,
  INTRO_TAC "!top atlas U a b g ff psi H; mfd cpt opn ab rm cont lip hder init bar" THEN
  ASM_CASES_TAC `U:A->bool = {}` THENL [ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  ABBREV_TAC `M = \t. sup(IMAGE ((ff:real->A->real) t) U)` THEN
  SUBGOAL_THEN `(M:real->real) real_continuous_on {t | a <= t /\ t < b}`
  (LABEL_TAC "mcont") THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP] THEN
    MATCH_MP_TAC RFA_SUP_COMPACT_CONTINUOUS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> ?x0. x0 IN U /\ (M:real->real) t = (ff:real->A->real) t x0 /\
                 !x. x IN U ==> ff t x <= ff t x0`
  (LABEL_TAC "att") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "M" THEN
    MATCH_MP_TAC RFA_SUP_COMPACT_ATTAINED THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                          `top:A topology`] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t x. a <= t /\ t < b /\ x IN U ==> (ff:real->A->real) t x <= M t`
  (LABEL_TAC "fm") THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    USE_THEN "att" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b ==> (M:real->real) t <= (H:real->real) t`
  (LABEL_TAC "mh") THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(M:real->real) t` THEN
    CONJ_TAC THENL
     [USE_THEN "fm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "mh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]] THEN
  X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
  USE_THEN "att" (MP_TAC o SPEC `a:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xa:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(M:real->real) a <= (H:real->real) a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "init" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t1:real = a` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a < t1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(M:real->real) real_continuous_on real_interval[a,t1] /\
                (H:real->real) real_continuous_on real_interval[a,t1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{t | a <= t /\ t < b}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_SUBSET THEN
      EXISTS_TAC `{s | a <= s /\ s < b}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
        EXISTS_TAC `(psi:real->real->real) t ((H:real->real) t)` THEN
        USE_THEN "hder" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?B. !t. a <= t /\ t <= t1
            ==> abs((M:real->real) t) <= B /\ abs((H:real->real) t) <= B`
  (X_CHOOSE_THEN `B:real` (LABEL_TAC "bd")) THENL
   [MP_TAC(ISPECL [`M:real->real`; `real_interval[a,t1]`]
           REAL_COMPACT_CONTINUOUS_IMAGE) THEN
    MP_TAC(ISPECL [`H:real->real`; `real_interval[a,t1]`]
           REAL_COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real` (LABEL_TAC "b1")) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real` (LABEL_TAC "b2")) THEN
    EXISTS_TAC `abs B1 + abs B2` THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "b1" (MP_TAC o SPEC `t:real`) THEN
    USE_THEN "b2" (MP_TAC o SPEC `t:real`) THEN
    UNDISCH_TAC `a <= t` THEN UNDISCH_TAC `t <= t1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "lip" (MP_TAC o SPECL [`t1:real`; `B:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (LABEL_TAC "L")) THEN
  MP_TAC(ISPECL [`\t. (M:real->real) t - (H:real->real) t`; `a:real`; `t1:real`;
                 `abs L`] RFA_DINI_GRONWALL) THEN
  REWRITE_TAC[REAL_ABS_POS] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      ALL_TAC];
    DISCH_THEN(MP_TAC o SPEC `t1:real`) THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "att" (MP_TAC o SPEC `t0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
  USE_THEN "bar" (MP_TAC o SPECL [`t0:real`; `x0:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < (M:real->real) t0 - (H:real->real) t0` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DESTRUCT_TAC
    "@dd W phi D. dpos wo y0w wsub phile phieq tle sm pd imp") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `(g:real->A->real^N^N) t0`;
                 `(ff:real->A->real) t0`; `(phi:real->real^N->real) t0`;
                 `x0:A`; `W:real^N->bool`] RFA_BARRIER_SPATIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dz") (LABEL_TAC "lapneg"))] THEN
  SUBGOAL_THEN `D <= (psi:real->real->real) t0 ((M:real->real) t0)`
  ASSUME_TAC THENL
   [USE_THEN "imp" MP_TAC THEN USE_THEN "dz" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "lapneg" MP_TAC THEN
    SUBGOAL_THEN `(M:real->real) t0 = (ff:real->A->real) t0 x0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `D - (psi:real->real->real) t0 ((H:real->real) t0) <=
    abs L * ((M:real->real) t0 - H t0)`
  ASSUME_TAC THENL
   [USE_THEN "L" (MP_TAC o SPECL [`t0:real`; `(M:real->real) t0`;
                                  `(H:real->real) t0`]) THEN
    USE_THEN "bd" (MP_TAC o SPEC `t0:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `L * abs((M:real->real) t0 - (H:real->real) t0) <= abs L * (M t0 - H t0)`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 < x - y ==> abs(x - y) = x - y`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `D <= (psi:real->real->real) t0 ((M:real->real) t0)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t0 - dd < t /\ t <= t0 /\ a <= t
        ==> (phi:real->real^N->real) t
              (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)) x0) <=
            (M:real->real) t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(ff:real->A->real) t x0` THEN CONJ_TAC THENL
     [USE_THEN "tle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "fm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((H:real->real) has_real_derivative (psi:real->real->real) t0 (H t0))
      (atreal t0 within {s | a <= s /\ s < b})`
  ASSUME_TAC THENL
   [USE_THEN "hder" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real->real`; `H:real->real`;
                 `\t. (phi:real->real^N->real) t
                        (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                      (x0:A)) x0)`;
                 `a:real`; `b:real`; `t0:real`; `dd:real`; `D:real`;
                 `(psi:real->real->real) t0 ((H:real->real) t0)`; `abs L`]
         RFA_DINI_STEP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The minimum principle in barrier form, from                               *)
(* RFA_MAXP_BARRIER applied to --F, --H, the barriers --phi and the         *)
(* reflected reaction term (t,u) |-> --psi(t,--u).                          *)
(* ========================================================================= *)

let RFA_MINP_BARRIER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U a b
    (g:real->A->real^N^N) (ff:real->A->real) (psi:real->real->real)
    (H:real->real).
      smooth_manifold_atlas top atlas /\ compact_in top U /\ open_in top U /\
      a < b /\
      (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
      continuous_map (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                                    (subtopology top U),
                      euclideanreal) (\z. ff (FST z) (SND z)) /\
      (!c B. c < b
             ==> ?L. !t u v. a <= t /\ t <= c /\ abs u <= B /\ abs v <= B
                             ==> abs(psi t u - psi t v) <= L * abs(u - v)) /\
      (!t. a <= t /\ t < b
           ==> (H has_real_derivative psi t (H t)) (atreal t within {s | a <= s /\ s < b})) /\
      (!x. x IN U ==> H a <= ff a x) /\
      (!t0 x0. a < t0 /\ t0 < b /\ x0 IN U /\ ff t0 x0 < H t0 /\
               (!x. x IN U ==> ff t0 x0 <= ff t0 x)
               ==> ?d W (phi:real->real^N->real) D.
                     &0 < d /\ open W /\ SND(chart_at atlas x0) x0 IN W /\
                     W SUBSET IMAGE (SND(chart_at atlas x0))
                                    (FST(chart_at atlas x0) INTER U) /\
                     (!y. y IN W
                          ==> ff t0 (chart_inv (chart_at atlas x0) y) <= phi t0 y) /\
                     phi t0 (SND(chart_at atlas x0) x0) = ff t0 x0 /\
                     (!t. t0 - d < t /\ t <= t0
                          ==> ff t x0 <= phi t (SND(chart_at atlas x0) x0)) /\
                     smooth_map_on W (\y. lift(phi t0 y)) /\
                     ((\t. phi t (SND(chart_at atlas x0) x0)) has_real_derivative D)
                       (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
                     (((\y. lift(phi t0 y)) has_derivative (\v. vec 0))
                        (at (SND(chart_at atlas x0) x0))
                      ==> llap (metric_local atlas (chart_at atlas x0) (g t0))
                               (phi t0) (SND(chart_at atlas x0) x0) +
                          psi t0 (ff t0 x0) <= D))
      ==> !t x. a <= t /\ t < b /\ x IN U ==> H t <= ff t x`,
  INTRO_TAC "!top atlas U a b g ff psi H; mfd cpt opn ab rm cont lip hder init bar" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `a:real`; `b:real`; `g:real->A->real^N^N`;
                 `\t x. --((ff:real->A->real) t x)`;
                 `\t u. --((psi:real->real->real) t (--u))`;
                 `\t. --((H:real->real) t)`] RFA_MAXP_BARRIER) THEN
  REWRITE_TAC[REAL_LE_NEG2; REAL_LT_NEG2; REAL_NEG_NEG] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN USE_THEN "cont" ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`c:real`; `B:real`] THEN DISCH_TAC THEN
    USE_THEN "lip" (MP_TAC o SPECL [`c:real`; `B:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real` (LABEL_TAC "L")) THEN
    EXISTS_TAC `L:real` THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `u:real`; `v:real`] THEN STRIP_TAC THEN
    REMOVE_THEN "L" (MP_TAC o SPECL [`t:real`; `--u:real`; `--v:real`]) THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ARITH `--x - --y = --(x - y)`];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
    USE_THEN "hder" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN STRIP_TAC THEN
  USE_THEN "bar" (MP_TAC o SPECL [`t0:real`; `x0:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DESTRUCT_TAC
    "@dd W phi D. dpos wo y0w wsub phile phieq tle sm pd imp") THEN
  MAP_EVERY EXISTS_TAC [`dd:real`; `W:real^N->bool`;
                        `\t y. --((phi:real->real^N->real) t y)`; `--D:real`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_EQ_NEG2] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "dz0") THEN
    MP_TAC(ISPECL [`W:real^N->bool`;
                   `metric_local (atlas:((A->bool)#(A->real^N))->bool)
                      (chart_at atlas (x0:A)) ((g:real->A->real^N^N) t0)`;
                   `(phi:real->real^N->real) t0`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)) x0`]
           RFA_LLAP_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "imp" MP_TAC THEN ANTS_TAC THENL
     [USE_THEN "dz0" (MP_TAC o MATCH_MP HAS_DERIVATIVE_NEG) THEN
      REWRITE_TAC[LIFT_NEG; VECTOR_NEG_NEG; VECTOR_NEG_0];
      REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The scalar maximum and minimum principles for functions                   *)
(* smooth in space-time charts (RFA_MAXP_SCALAR, RFA_MINP_SCALAR), from the  *)
(* barrier forms with the function itself as barrier.                        *)
(* ========================================================================= *)

(* The Laplacian of a function on the manifold at x, in the preferred chart *)
(* at x.                                                                     *)

let rfa_lap = new_definition
 `rfa_lap (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real)
          (x:A) =
    llap (metric_local atlas (chart_at atlas x) g)
         (\y. f (chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x)`;;

let RFA_CHART_AT_FACTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) x U.
     smooth_manifold_atlas top atlas /\ open_in top U /\ x IN U
     ==> chart_at atlas x IN atlas /\ x IN FST(chart_at atlas x) /\
         chart_inv (chart_at atlas x) (SND(chart_at atlas x) x) = x /\
         open (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x) INTER U)) /\
         (!y. y IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x) INTER U)
              ==> chart_inv (chart_at atlas x) y IN U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
         CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
         SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N)) INTER U`] CHART_IMAGE_OPEN) THEN
    ASM_SIMP_TAC[PAIR; OPEN_IN_INTER; INTER_SUBSET];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]]);;

let RFA_SMOOTH_MAP_ON_SLICE = prove
 (`!(Fm:real^(1,N)finite_sum->real^P) a b W t0.
        smooth_map_on (interval(lift a,lift b) PCROSS W) Fm /\ open W /\
        a < t0 /\ t0 < b
        ==> smooth_map_on W (\y. Fm(pastecart (lift t0) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (Fm:real^(1,N)finite_sum->real^P) (pastecart (lift t0) y)) =
                Fm o (\y:real^N. pastecart (lift t0) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (W:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                LIFT_DROP] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let RFA_MAXP_SCALAR = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U a b
    (g:real->A->real^N^N) (ff:real->A->real) (psi:real->real->real)
    (H:real->real).
      smooth_manifold_atlas top atlas /\ compact_in top U /\ open_in top U /\
      a < b /\
      (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
      continuous_map (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                                    (subtopology top U),
                      euclideanreal) (\z. ff (FST z) (SND z)) /\
      (!c. c IN atlas
           ==> smooth_map_on
                 (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c INTER U))
                 (\z. lift(ff (drop(fstcart z)) (chart_inv c (sndcart z))))) /\
      (!t x. a < t /\ t < b /\ x IN U
             ==> ?D. ((\s. ff s x) has_real_derivative D) (atreal t) /\
                     (((\y. lift(ff t (chart_inv (chart_at atlas x) y))) has_derivative
                       (\v. vec 0)) (at (SND(chart_at atlas x) x))
                      ==> D <= rfa_lap atlas (g t) (ff t) x + psi t (ff t x))) /\
      (!c B. c < b
             ==> ?L. !t u v. a <= t /\ t <= c /\ abs u <= B /\ abs v <= B
                             ==> abs(psi t u - psi t v) <= L * abs(u - v)) /\
      (!t. a <= t /\ t < b
           ==> (H has_real_derivative psi t (H t)) (atreal t within {s | a <= s /\ s < b})) /\
      (!x. x IN U ==> ff a x <= H a)
      ==> !t x. a <= t /\ t < b /\ x IN U ==> ff t x <= H t`,
  INTRO_TAC "!top atlas U a b g ff psi H; mfd cpt opn ab rm cont sm deriv lip hder init" THEN
  MATCH_MP_TAC RFA_MAXP_BARRIER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:real->A->real^N^N`; `psi:real->real->real`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x0:A`; `U:A->bool`] RFA_CHART_AT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "deriv" (MP_TAC o SPECL [`t0:real`; `x0:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dimp"))) THEN
  MAP_EVERY EXISTS_TAC
   [`&1`;
    `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)))
           (FST(chart_at atlas x0) INTER U)`;
    `\t y. (ff:real->A->real) t
             (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)) y)`;
    `D:real`] THEN
  REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REAL_LT_01; SUBSET_REFL; REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    MP_TAC(ISPECL
     [`\z. lift((ff:real->A->real) (drop(fstcart z))
             (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A))
                        (sndcart z)))`;
      `a:real`; `b:real`;
      `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)))
             (FST(chart_at atlas x0) INTER U)`;
      `t0:real`] RFA_SMOOTH_MAP_ON_SLICE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[ETA_AX];
    USE_THEN "dimp" (fun th -> ACCEPT_TAC(REWRITE_RULE[rfa_lap] th))]);;

let RFA_MINP_SCALAR = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U a b
    (g:real->A->real^N^N) (ff:real->A->real) (psi:real->real->real)
    (H:real->real).
      smooth_manifold_atlas top atlas /\ compact_in top U /\ open_in top U /\
      a < b /\
      (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
      continuous_map (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                                    (subtopology top U),
                      euclideanreal) (\z. ff (FST z) (SND z)) /\
      (!c. c IN atlas
           ==> smooth_map_on
                 (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c INTER U))
                 (\z. lift(ff (drop(fstcart z)) (chart_inv c (sndcart z))))) /\
      (!t x. a < t /\ t < b /\ x IN U
             ==> ?D. ((\s. ff s x) has_real_derivative D) (atreal t) /\
                     (((\y. lift(ff t (chart_inv (chart_at atlas x) y))) has_derivative
                       (\v. vec 0)) (at (SND(chart_at atlas x) x))
                      ==> rfa_lap atlas (g t) (ff t) x + psi t (ff t x) <= D)) /\
      (!c B. c < b
             ==> ?L. !t u v. a <= t /\ t <= c /\ abs u <= B /\ abs v <= B
                             ==> abs(psi t u - psi t v) <= L * abs(u - v)) /\
      (!t. a <= t /\ t < b
           ==> (H has_real_derivative psi t (H t)) (atreal t within {s | a <= s /\ s < b})) /\
      (!x. x IN U ==> H a <= ff a x)
      ==> !t x. a <= t /\ t < b /\ x IN U ==> H t <= ff t x`,
  INTRO_TAC "!top atlas U a b g ff psi H; mfd cpt opn ab rm cont sm deriv lip hder init" THEN
  MATCH_MP_TAC RFA_MINP_BARRIER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:real->A->real^N^N`; `psi:real->real->real`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x0:A`; `U:A->bool`] RFA_CHART_AT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "deriv" (MP_TAC o SPECL [`t0:real`; `x0:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dimp"))) THEN
  MAP_EVERY EXISTS_TAC
   [`&1`;
    `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)))
           (FST(chart_at atlas x0) INTER U)`;
    `\t y. (ff:real->A->real) t
             (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)) y)`;
    `D:real`] THEN
  REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[REAL_LT_01; SUBSET_REFL; REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    MP_TAC(ISPECL
     [`\z. lift((ff:real->A->real) (drop(fstcart z))
             (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A))
                        (sndcart z)))`;
      `a:real`; `b:real`;
      `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)))
             (FST(chart_at atlas x0) INTER U)`;
      `t0:real`] RFA_SMOOTH_MAP_ON_SLICE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[ETA_AX];
    USE_THEN "dimp" (fun th -> ACCEPT_TAC(REWRITE_RULE[rfa_lap] th))]);;


