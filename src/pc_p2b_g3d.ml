(* ========================================================================= *)
(* Unit pc_p2b_g3d: partitions of unity subordinate to chart boxes of the    *)
(* limit and the global weak functional of G3 (sum of the chart weak forms   *)
(* weighted by the partition); its sign on nonnegative tests and its value   *)
(* on tests in one chart box.                                                *)
(* ========================================================================= *)

needs "src/pc_p2b_g3c.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Nonnegative partitions of unity on compact sets, subordinate to chart     *)
(* balls.                                                                    *)
(*                                                                           *)
(* P2BX_PARTITION_OF_UNITY_POS is a copy of RFU_PARTITION_OF_UNITY_ON (unit  *)
(* pc_rf_unique_ncint) with one extra conjunct, 0 <= rho j x (the            *)
(* construction product(1..j-1) (1 - b i) * b j already gives it).           *)
(* ========================================================================= *)

let P2BX_PARTITION_OF_UNITY_POS = prove
 (`!top atlas (K:A->bool).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_in top K
        ==> ?k (U:num->A->bool) (phi:num->A->real^N) (y0:num->real^N) (r:num->real)
              (rho:num->A->real).
              (!j. j IN 1..k
                   ==> (U j,phi j) IN atlas /\ &0 < r j /\
                       cball(y0 j,&2 * r j) SUBSET IMAGE (phi j) (U j) /\
                       mfd_smooth atlas (\x. lift(rho j x)) /\
                       (!x. &0 <= rho j x) /\
                       (!x. ~(x IN U j /\ phi j x IN cball(y0 j,&2 * r j))
                            ==> rho j x = &0)) /\
              (!x. x IN K ==> sum(1..k) (\j. rho j x) = &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `{{p:A | p IN U /\ phi p IN ball(y,r)} |
     (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\ &0 < r /\
     cball(y:real^N,&2 * r) SUBSET IMAGE phi U}` o
   CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN ASM_MESON_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `topspace top:A->bool`; `x:A`] MFDC_LOCAL_BALL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
        (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `{p:A | p IN V /\ (psi:A->real^N) p IN ball(psi x,s)}` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC
         [`V:A->bool`; `psi:A->real^N`; `(psi:A->real^N) x`; `s:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `k = CARD(F0:(A->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> ?U phi y r. (U,phi) IN atlas /\ &0 < r /\
                        cball(y:real^N,&2 * r) SUBSET IMAGE (phi:A->real^N) U /\
                        (w:num->A->bool) j = {p | p IN U /\ phi p IN ball(y,r)}`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:num->A->bool) j IN F0` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `(F0:(A->bool)->bool) SUBSET
      {{p:A | p IN U /\ phi p IN ball(y,r)} |
       (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool) /\ &0 < r /\
       cball(y:real^N,&2 * r) SUBSET IMAGE phi U}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:num->A->bool` (X_CHOOSE_THEN `phi:num->A->real^N`
   (X_CHOOSE_THEN `y0:num->real^N` (X_CHOOSE_THEN `r:num->real`
     (LABEL_TAC "W"))))) THEN
  ABBREV_TAC
   `b = \j (x:A). if x IN U j
                  then smooth_bump ((r:num->real) j) (&2 * r j)
                                   ((phi:num->A->real^N) j x - y0 j)
                  else &0` THEN
  SUBGOAL_THEN
   `!j (x:A). j IN 1..k
              ==> &0 <= (b:num->A->real) j x /\ b j x <= &1 /\
                  (x IN (U:num->A->bool) j /\ (phi:num->A->real^N) j x IN ball(y0 j,r j)
                   ==> b j x = &1) /\
                  (~(x IN U j /\ phi j x IN cball(y0 j,&2 * r j)) ==> b j x = &0)`
  (LABEL_TAC "BV") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(U:num->A->bool) j`; `(phi:num->A->real^N) j`;
                   `(y0:num->real^N) j`; `(r:num->real) j`; `x:A`]
                  MFDC_BUMP_VALUES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
                       (\x. lift((b:num->A->real) j x))`
  (LABEL_TAC "BS") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    MATCH_MP_TAC MFDC_BUMP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `U:num->A->bool`; `phi:num->A->real^N`; `y0:num->real^N`;
    `r:num->real`;
    `\j (x:A). product(1..j-1) (\i. &1 - (b:num->A->real) i x) * b j x`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "W" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_smooth; o_DEF] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
       [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
      SUBGOAL_THEN
       `!i. i IN 1..k
            ==> smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                  (\y. lift((b:num->A->real) i (chart_inv c y)))`
      ASSUME_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        USE_THEN "BS" (MP_TAC o C MATCH_MP (ASSUME `i IN 1..k`)) THEN
        REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\y. lift(product(1..j-1)
                   (\i. &1 - (b:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) y)))`;
        `\y. lift((b:num->A->real) j (chart_inv (c:(A->bool)#(A->real^N)) y))`]
       SMOOTH_MAP_ON_LIFT_MUL) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\i y. lift(&1 - (b:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) y))`;
        `1..j-1`] SMOOTH_MAP_ON_LIFT_PRODUCT) THEN
      REWRITE_TAC[LIFT_DROP; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
        `\y:real^N. lift(&1)`;
        `\y. lift((b:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) y))`]
       SMOOTH_MAP_ON_LIFT_SUB) THEN
      REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `j IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        REWRITE_TAC[REAL_SUB_LE] THEN
        USE_THEN "BV" (MP_TAC o SPECL [`i:num`; `x:A`]) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `j IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
          SIMP_TAC[]];
        USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o
                       SPECL [`j:num`; `x:A`]) THEN
        SIMP_TAC[]];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o
                     SPECL [`j:num`; `x:A`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\i. (b:num->A->real) i x`; `k:num`] RFU_TELESCOPE) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `p = &0 ==> &1 - p = &1`) THEN
  SIMP_TAC[PRODUCT_EQ_0_NUMSEG] THEN
  SUBGOAL_THEN `?j. j IN 1..k /\ (x:A) IN (w:num->A->bool) j` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (F0:(A->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `j:num` THEN
  SUBGOAL_THEN `1 <= j /\ j <= k` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
  USE_THEN "BV" (MP_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPECL [`j:num`; `x:A`]) THEN
  USE_THEN "W" (MP_TAC o last o CONJUNCTS o C MATCH_MP (ASSUME `j IN 1..k`)) THEN
  DISCH_THEN(fun th -> UNDISCH_TAC `(x:A) IN (w:num->A->bool) j` THEN
                       REWRITE_TAC[th; IN_ELIM_THM]) THEN
  SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Product boxes and closed balls with room inside an open set.              *)
(* ========================================================================= *)

let P2BX_IN_PCROSS = prove
 (`!(s:real^M->bool) (t:real^N->bool) z.
     z IN s PCROSS t <=> fstcart z IN s /\ sndcart z IN t`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS]);;

let P2BX_CBALL_ENLARGE = prove
 (`!(s:real^N->bool) y r.
     open s /\ &0 <= r /\ cball(y,r) SUBSET s ==> ?r'. r < r' /\ cball(y,r') SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cball(y:real^N,r)`; `(:real^N) DIFF s`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r + d / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `dist(y:real^N,x) <= r` THENL
   [UNDISCH_TAC `cball(y:real^N,r) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = dist(y:real^N,x)` THEN
  SUBGOAL_THEN `&0 < D /\ r < D` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(x - y:real^N) = D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[dist] THEN MATCH_ACCEPT_TAC NORM_SUB; ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y + (r / D) % (x - y):real^N`; `x:real^N`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
  REWRITE_TAC[IN_CBALL; IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `y - (y + c % (x - y)):real^N = --(c % (x - y))`;
              VECTOR_ARITH `(y + c % (x - y)) - x:real^N = (c - &1) % (x - y)`;
              NORM_NEG; NORM_MUL] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(r / D) = r / D /\ abs(r / D - &1) = &1 - r / D` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> abs(x - &1) = &1 - x`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r / D * D = r` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - r / D) * D = D - r` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Nonnegative partitions of unity on a compact set of the limit, each       *)
(* member read in a chart with a product box ball x (a/2, 2b) containing     *)
(* its support times [a, b] in a compact set.                                *)
(* ========================================================================= *)

let P2BX_BOX_PART = prove
 (`!(top':B topology) (atlas':((B->bool)#(B->real^3))->bool) K a b.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ compact_in top' K /\
     &0 < a /\ a <= b
     ==> ?k (c:num->(B->bool)#(B->real^3)) (om:num->real^(3,1)finite_sum->bool)
           (Kb:num->real^(3,1)finite_sum->bool) (rho:num->B->real).
           (!j. j IN 1..k
                ==> c j IN atlas' /\ p2bg_cbox (c j) (om j) /\
                    compact (Kb j) /\ Kb j SUBSET om j /\
                    mfd_smooth atlas' (\x. lift(rho j x)) /\ (!x. &0 <= rho j x) /\
                    (!x t. ~(rho j x = &0) /\ a <= t /\ t <= b
                           ==> x IN FST(c j) /\ pastecart (SND(c j) x) (lift t) IN Kb j)) /\
           (!x. x IN K ==> sum(1..k) (\j. rho j x) = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`]
                P2BX_PARTITION_OF_UNITY_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `U:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->real^3` (X_CHOOSE_THEN `y0:num->real^3`
    (X_CHOOSE_THEN `r:num->real` (X_CHOOSE_THEN `rho:num->B->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "P") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> ?r'. &2 * (r:num->real) j < r' /\
                 cball((y0:num->real^3) j,r') SUBSET IMAGE ((phi:num->B->real^3) j) ((U:num->B->bool) j)`
  (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "P" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
    MATCH_MP_TAC P2BX_CBALL_ENLARGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `((U:num->B->bool) j,(phi:num->B->real^3) j)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':num->real` (LABEL_TAC "R")) THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `\j:num. ((U:num->B->bool) j,(phi:num->B->real^3) j)`;
    `\j:num. ball((y0:num->real^3) j,(r':num->real) j) PCROSS
             interval(lift(a / &2),lift(&2 * b))`;
    `\j:num. cball((y0:num->real^3) j,&2 * (r:num->real) j) PCROSS interval[lift a,lift b]`;
    `rho:num->B->real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "P" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
  USE_THEN "R" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
  SUBGOAL_THEN `&0 < (r':num->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2bg_cbox] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_BALL; OPEN_INTERVAL];
      MATCH_MP_TAC BOUNDED_PCROSS THEN REWRITE_TAC[BOUNDED_BALL; BOUNDED_INTERVAL];
      REWRITE_TAC[CLOSURE_PCROSS] THEN ASM_SIMP_TAC[CLOSURE_BALL] THEN
      SUBGOAL_THEN `closure(interval(lift(a / &2),lift(&2 * b))) =
                    interval[lift(a / &2),lift(&2 * b)]` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
        REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; P2BX_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `cball((y0:num->real^3) j,(r':num->real) j) SUBSET
                     IMAGE ((phi:num->B->real^3) j) ((U:num->B->bool) j)` THEN
        ASM SET_TAC[];
        ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_CBALL; COMPACT_INTERVAL];
    REWRITE_TAC[SUBSET; P2BX_IN_PCROSS; IN_CBALL; IN_BALL; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:B`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:B) IN (U:num->B->bool) j /\ (phi:num->B->real^3) j x IN cball((y0:num->real^3) j,&2 * (r:num->real) j)`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cball:real^3#real->real^3->bool`)) (concl th) &&
        can (find_term ((=) `rho:num->B->real`)) (concl th))) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]]);;

(* ========================================================================= *)
(* U as a function on the limit, the weak integrand of the conjugate heat    *)
(* equation in a chart (p2bx_wint), the subsolution property on boxes in     *)
(* this form, and the product rule.                                          *)
(* ========================================================================= *)

let p2bx_uf = new_definition
 `p2bx_uf (linf:real->B->real) (t:real) (x:B) = exp(--(linf t x + &3 / &2 * log t))`;;

let p2bx_wint = new_definition
 `p2bx_wint (atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
            (c:(B->bool)#(B->real^3)) (uu:real->B->real)
            (ff:real^(3,1)finite_sum->real) (z:real^(3,1)finite_sum) =
    ff z * (wan_tder (p2bw_cfun c uu) z + p2bw_cscal atlas' c (&1) g' z * p2bw_cfun c uu z) *
           sqrt(det(p2bw_cmet atlas' c (&1) g' z)) +
    p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' c (&1) g' z)) %% matrix_inv(p2bw_cmet atlas' c (&1) g' z))
             (p2bw_cfun c uu) ff z`;;

let P2BX_UOF_UF = prove
 (`!(c:(B->bool)#(B->real^3)) (linf:real->B->real).
     p2bw_uof (p2bw_cfun c linf) = p2bw_cfun c (p2bx_uf linf)`,
  REWRITE_TAC[FUN_EQ_THM; p2bw_uof; p2bw_cfun; p2bx_uf; DIMINDEX_3]);;

let P2BX_BOX_WSUB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om psi.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om /\ p2bw_ltest om psi
     ==> drop(integral om (\z. lift(p2bx_wint atlas' g' c (p2bx_uf linf) psi z))) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_CSUB) THEN
  ASM_REWRITE_TAC[p2bw_csub; P2BX_UOF_UF] THEN
  DISCH_THEN(MP_TAC o SPEC `psi:real^(3,1)finite_sum->real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[p2bx_wint]);;

let P2BX_BIL_MUL_RIGHT = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u rr ff z.
     (\w. lift(rr w)) differentiable at z /\ (\w. lift(ff w)) differentiable at z
     ==> p2bw_bil A u (\w. rr w * ff w) z =
         rr z * p2bw_bil A u ff z + ff z * p2bw_bil A u rr z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. wan_xder j (\w. (rr:real^(N,1)finite_sum->real) w * ff w) z =
                    rr z * wan_xder j ff z + ff z * wan_xder j rr z` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wan_xder] THEN
    MP_TAC(ISPECL [`rr:real^(N,1)finite_sum->real`; `ff:real^(N,1)finite_sum->real`;
                   `z:real^(N,1)finite_sum`; `pastecart (basis j:real^N) (vec 0:real^1)`]
                  P2BW_DER_MUL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bw_bil] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2BX_WINT_MUL = prove
 (`!atlas' g' (c:(B->bool)#(B->real^3)) uu rr ff z.
     (\w. lift(rr w)) differentiable at z /\ (\w. lift(ff w)) differentiable at z
     ==> p2bx_wint atlas' g' c uu (\w. rr w * ff w) z =
         rr z * p2bx_wint atlas' g' c uu ff z +
         ff z * p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' c (&1) g' z)) %%
                              matrix_inv(p2bw_cmet atlas' c (&1) g' z))
                         (p2bw_cfun c uu) rr z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx_wint] THEN
  ASM_SIMP_TAC[P2BX_BIL_MUL_RIGHT] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Locality of derivatives and of the weak integrand; Lipschitz tests times  *)
(* locally bounded measurable functions.                                     *)
(* ========================================================================= *)

let P2BX_DERIV_LOCAL = prove
 (`!(f:real^M->real) g O z.
     open O /\ z IN O /\ (!w. w IN O ==> f w = g w) /\ (\w. lift(g w)) differentiable at z
     ==> (\w. lift(f w)) differentiable at z /\
         frechet_derivative (\w. lift(f w)) (at z) = frechet_derivative (\w. lift(g w)) (at z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN DISCH_TAC THEN
  UNDISCH_TAC `open(O:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `((\w. lift((f:real^M->real) w)) has_derivative
                 frechet_derivative (\w. lift((g:real^M->real) w)) (at z)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\w. lift((g:real^M->real) w)`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_EQ] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `O:real^M->bool`)) (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

let P2BX_WINT_LOCAL = prove
 (`!atlas' g' (c:(B->bool)#(B->real^3)) uu ff hh O z.
     open O /\ z IN O /\ (!w. w IN O ==> ff w = hh w) /\ (\w. lift(hh w)) differentiable at z
     ==> p2bx_wint atlas' g' c uu ff z = p2bx_wint atlas' g' c uu hh z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ff:real^(3,1)finite_sum->real`; `hh:real^(3,1)finite_sum->real`;
                 `O:real^(3,1)finite_sum->bool`; `z:real^(3,1)finite_sum`] P2BX_DERIV_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bx_wint; p2bw_bil; wan_xder] THEN ASM_SIMP_TAC[]);;

let P2BX_LTEST_CONT = prove
 (`!(om:real^M->bool) psi k.
     open om /\ wan_loclip om psi /\ compact k /\ k SUBSET om /\
     (!z. ~(z IN k) ==> psi z = &0)
     ==> (\z. lift(psi z)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^M) IN om` THENL
   [MP_TAC(ISPECL [`\z. lift((psi:real^M->real) z)`; `om:real^M->bool`]
                  CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^M) IN k)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\z:real^M. lift(&0)` THEN
  SUBGOAL_THEN `open((:real^M) DIFF k)` MP_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[CONTINUOUS_CONST] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let P2BX_LTEST_LEBM_ABSINT = prove
 (`!(om:real^(N,1)finite_sum->bool) psi h.
     open om /\ p2bw_ltest om psi /\ p2bw_lebm om h
     ==> (\z. lift(psi z * h z)) absolutely_integrable_on om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2bw_ltest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `h:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2BW_LEBM_L1BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` (MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o SPEC `psi:real^(N,1)finite_sum->real`) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `k:real^(N,1)finite_sum->bool` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `aa:real^(N,1)finite_sum` (X_CHOOSE_TAC `bb:real^(N,1)finite_sum`)) THEN
  SUBGOAL_THEN `(\x. lift((psi:real^(N,1)finite_sum->real) x)) =
                (\x. if x IN interval[aa,bb] then lift(psi x) else vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^(N,1)finite_sum->real) x = &0` (fun th -> REWRITE_TAC[th; LIFT_NUM]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_LTEST_CONT THEN
  MAP_EVERY EXISTS_TAC [`om:real^(N,1)finite_sum->bool`; `k:real^(N,1)finite_sum->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Smooth functions are locally Lipschitz; chart readings of smooth          *)
(* functions on the limit as space-time functions.                           *)
(* ========================================================================= *)

let P2BX_SMOOTH_LOCLIP = prove
 (`!(U:real^M->bool) g. open U /\ smooth_map_on U (\x. lift(g x)) ==> wan_loclip U g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_loclip] THEN X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `k:real^M->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `th:real^M->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `th:real^M->real`; `g:real^M->real`] WAN_TEST_MUL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[wan_test] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k':real^M->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\x:real^M. if x IN U then (th:real^M->real) x * g x else &0`;
                 `k':real^M->bool`] WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B:real` THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  SUBGOAL_THEN `(x:real^M) IN U /\ y IN U` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_LID]);;

let P2BX_OPEN_CHART_CYL = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)).
     smooth_manifold_atlas top' atlas' /\ c IN atlas'
     ==> open {z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND c) (FST c)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[]]);;

let P2BX_MSMOOTH_CFUN = prove
 (`!(top':B topology) atlas' rh (c:(B->bool)#(B->real^3)).
     smooth_manifold_atlas top' atlas' /\ mfd_smooth atlas' (\x. lift(rh x)) /\ c IN atlas'
     ==> smooth_map_on {z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND c) (FST c)}
                       (\z. lift(p2bw_cfun c (\t:real. rh) z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_cfun] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(B->bool)#(B->real^3)` o GEN_REWRITE_RULE I [mfd_smooth] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_smooth"))
      (concl th))) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\z:real^(3,1)finite_sum. lift((rh:B->real)(chart_inv (c:(B->bool)#(B->real^3)) (fstcart z)))) =
                (\y. lift(rh(chart_inv c y))) o (fstcart o (\z:real^(3,1)finite_sum. z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] P2BX_OPEN_CHART_CYL) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]]);;

let P2BX_MSMOOTH_CFUN_FACTS = prove
 (`!(top':B topology) atlas' rh (c:(B->bool)#(B->real^3)) om.
     smooth_manifold_atlas top' atlas' /\ mfd_smooth atlas' (\x. lift(rh x)) /\ c IN atlas' /\
     p2bg_cbox c om
     ==> wan_loclip om (p2bw_cfun c (\t:real. rh)) /\
         (!z. fstcart z IN IMAGE (SND c) (FST c)
              ==> (\w. lift(p2bw_cfun c (\t:real. rh) w)) differentiable at z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `rh:B->real`;
                 `c:(B->bool)#(B->real^3)`] P2BX_MSMOOTH_CFUN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] P2BX_OPEN_CHART_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN
    EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN REWRITE_TAC[p2bg_cbox] THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      MP_TAC(ISPEC `om:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN SET_TAC[]];
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* ========================================================================= *)
(* Partition data (p2bx_pdata) with spatial compact supports; supports read  *)
(* in other charts; coefficient continuity on boxes.                         *)
(* ========================================================================= *)

let p2bx_pdata = new_definition
 `p2bx_pdata (atlas':((B->bool)#(B->real^3))->bool) (K:B->bool) (a:real) (b:real) (k:num)
             (c:num->(B->bool)#(B->real^3)) (om:num->real^(3,1)finite_sum->bool)
             (Ks:num->real^3->bool) (rho:num->B->real) <=>
    (!j. j IN 1..k
         ==> c j IN atlas' /\ p2bg_cbox (c j) (om j) /\ compact (Ks j) /\
             Ks j SUBSET IMAGE (SND(c j)) (FST(c j)) /\
             Ks j PCROSS interval[lift a,lift b] SUBSET om j /\
             mfd_smooth atlas' (\x. lift(rho j x)) /\ (!x. &0 <= rho j x) /\
             (!x. ~(rho j x = &0) ==> x IN FST(c j) /\ SND(c j) x IN Ks j)) /\
    (!x. x IN K ==> sum(1..k) (\j. rho j x) = &1)`;;

let P2BX_PDATA_EXISTS = prove
 (`!(top':B topology) (atlas':((B->bool)#(B->real^3))->bool) K a b.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ compact_in top' K /\
     &0 < a /\ a <= b
     ==> ?k c om Ks rho. p2bx_pdata atlas' K a b k c om Ks rho`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx_pdata] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`]
                P2BX_PARTITION_OF_UNITY_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `U:num->B->bool`
    (X_CHOOSE_THEN `phi:num->B->real^3` (X_CHOOSE_THEN `y0:num->real^3`
    (X_CHOOSE_THEN `r:num->real` (X_CHOOSE_THEN `rho:num->B->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "P") ASSUME_TAC))))))) THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> ?r'. &2 * (r:num->real) j < r' /\
                 cball((y0:num->real^3) j,r') SUBSET IMAGE ((phi:num->B->real^3) j) ((U:num->B->bool) j)`
  (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "P" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
    MATCH_MP_TAC P2BX_CBALL_ENLARGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `((U:num->B->bool) j,(phi:num->B->real^3) j)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':num->real` (LABEL_TAC "R")) THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `\j:num. ((U:num->B->bool) j,(phi:num->B->real^3) j)`;
    `\j:num. ball((y0:num->real^3) j,(r':num->real) j) PCROSS
             interval(lift(a / &2),lift(&2 * b))`;
    `\j:num. cball((y0:num->real^3) j,&2 * (r:num->real) j)`;
    `rho:num->B->real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  USE_THEN "P" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
  USE_THEN "R" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
  SUBGOAL_THEN `&0 < (r':num->real) j` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2bg_cbox] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_BALL; OPEN_INTERVAL];
      MATCH_MP_TAC BOUNDED_PCROSS THEN REWRITE_TAC[BOUNDED_BALL; BOUNDED_INTERVAL];
      REWRITE_TAC[CLOSURE_PCROSS] THEN ASM_SIMP_TAC[CLOSURE_BALL] THEN
      SUBGOAL_THEN `closure(interval(lift(a / &2),lift(&2 * b))) =
                    interval[lift(a / &2),lift(&2 * b)]` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
        REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; P2BX_IN_PCROSS; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `cball((y0:num->real^3) j,(r':num->real) j) SUBSET
                     IMAGE ((phi:num->B->real^3) j) ((U:num->B->bool) j)` THEN
        ASM SET_TAC[];
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[SUBSET; P2BX_IN_PCROSS; IN_CBALL; IN_BALL; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cball:real^3#real->real^3->bool`)) (concl th) &&
      can (find_term ((=) `rho:num->B->real`)) (concl th))) THEN
    ASM_MESON_TAC[]]);;

(* The support of a member, as a compact set of the limit. *)

let P2BX_PDATA_SUPPORT = prove
 (`!(top':B topology) atlas' K a b k c om Ks rho j.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k
     ==> compact_in top' (IMAGE (chart_inv (c j)) (Ks j)) /\
         (!x. ~(rho j x = &0) ==> x IN IMAGE (chart_inv (c j)) (Ks j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_pdata] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1) ASSUME_TAC))) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num`) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `FST((c:num->(B->bool)#(B->real^3)) j)`; `SND((c:num->(B->bool)#(B->real^3)) j)`]
                MFDC_CHART_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `compact_in (subtopology top' (FST((c:num->(B->bool)#(B->real^3)) j)))
                    (IMAGE (chart_inv (c j)) (Ks j))` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j)))` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
      SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `SND((c:num->(B->bool)#(B->real^3)) j) x` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:B` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `rho:num->B->real`)) (concl th) &&
      can (find_term ((=) `Ks:num->real^3->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

(* A space-time function read in a chart has zero derivatives at a point   *)
(* whose base point lies off a closed set off which the function vanishes. *)

let P2BX_CFUN_ZERO_NEAR = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) C (f:real->B->real) z.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ closed_in top' C /\
     (!t x. ~(x IN C) ==> f t x = &0) /\
     fstcart z IN IMAGE (SND c) (FST c) /\ ~(chart_inv c (fstcart z) IN C)
     ==> (!i. wan_xder i (p2bw_cfun c f) z = &0) /\ wan_tder (p2bw_cfun c f) z = &0 /\
         p2bw_cfun c f z = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bw_cfun (c:(B->bool)#(B->real^3)) (f:real->B->real) z = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_cfun] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX_XDER_ZERO_OPEN THEN
  EXISTS_TAC `{z':real^(3,1)finite_sum | fstcart z' IN
                IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c DIFF C)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
      MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_DIFF] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))` THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[p2bw_cfun] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[]]);;

(* Coefficient continuity on a box. *)

let P2BX_BOX_A_CONT = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) c om.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\ c IN atlas' /\
     p2bg_cbox c om
     ==> (!i j. 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
                ==> (\z. lift((sqrt(det(p2bw_cmet atlas' c (&1) g' z)) %%
                               matrix_inv(p2bw_cmet atlas' c (&1) g' z))$i$j)) continuous_on om) /\
         (\z. lift(sqrt(det(p2bw_cmet atlas' c (&1) g' z)))) continuous_on om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded(om:real^(3,1)finite_sum->bool) /\
                om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN
    REWRITE_TAC[p2bg_cbox] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_LIMIT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(3,1)finite_sum->bool`;
                 `p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`] P2BW_COEFF_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
      can (find_term ((=) `vectorize:real^3^3->real^(3,3)finite_prod`)) (concl th) &&
      is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "smooth_map_on")) THEN
    REWRITE_TAC[o_DEF];
    REWRITE_TAC[p2bw_coeff; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Absolute integrability of products that vanish off a compact subset of a  *)
(* box; the pieces of the S = 0 identity.                                    *)
(* ========================================================================= *)

let P2BX_ABSINT_SUPPORT = prove
 (`!(om:real^(N,1)finite_sum->bool) kk psi0 h.
     open om /\ compact kk /\ kk SUBSET om /\ wan_loclip om psi0 /\ (!z. &0 <= psi0 z) /\
     p2bw_lebm om h /\ (!z. z IN om /\ ~(z IN kk) ==> psi0 z * h z = &0)
     ==> (\z. lift(psi0 z * h z)) absolutely_integrable_on om`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(N,1)finite_sum->bool`; `kk:real^(N,1)finite_sum->bool`]
                WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `th:real^(N,1)finite_sum->real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
  EXISTS_TAC `\z. lift(((th:real^(N,1)finite_sum->real) z * psi0 z) * h z)` THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
    ASM_CASES_TAC `(z:real^(N,1)finite_sum) IN kk` THEN ASM_SIMP_TAC[REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX_LTEST_LEBM_ABSINT THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k':real^(N,1)finite_sum->bool`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[p2bw_ltest] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `k':real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO]]);;

(* Facts about one member of the partition data. *)

let P2BX_PDATA_MEMBER = prove
 (`!(top':B topology) atlas' K a b k c om Ks rho j.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k
     ==> c j IN atlas' /\ p2bg_cbox (c j) (om j) /\ open(om j) /\ compact (Ks j) /\
         Ks j SUBSET IMAGE (SND(c j)) (FST(c j)) /\
         Ks j PCROSS interval[lift a,lift b] SUBSET om j /\
         compact (Ks j PCROSS interval[lift a,lift b]) /\
         om j SUBSET {z | fstcart z IN IMAGE (SND(c j)) (FST(c j))} /\
         mfd_smooth atlas' (\x. lift(rho j x)) /\ (!x. &0 <= rho j x) /\
         closed_in top' (IMAGE (chart_inv (c j)) (Ks j)) /\
         (!t x. ~(x IN IMAGE (chart_inv (c j)) (Ks j)) ==> (\t:real. rho j) t x = &0) /\
         (!x. ~(rho j x = &0) ==> x IN FST(c j) /\ SND(c j) x IN Ks j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2bx_pdata atlas' K a b k (c:num->(B->bool)#(B->real^3)) om Ks (rho:num->B->real)` THEN
  REWRITE_TAC[p2bx_pdata] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `j IN 1..k`) o SPEC `j:num` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p2bg_cbox ((c:num->(B->bool)#(B->real^3)) j) (om j)` THEN SIMP_TAC[p2bg_cbox];
    MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
    UNDISCH_TAC `p2bg_cbox ((c:num->(B->bool)#(B->real^3)) j) (om j)` THEN
    REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `(om:num->real^(3,1)finite_sum->bool) j` CLOSURE_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* A point of a chart cylinder and its base point. *)

let P2BX_CHART_POINT = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) y.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ y IN IMAGE (SND c) (FST c)
     ==> chart_inv c y IN FST c /\ SND c (chart_inv c y) = y /\
         chart_inv c y IN topspace top'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
    concl th = `open_in (top':B topology) (FST (c:(B->bool)#(B->real^3)))`)) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* One term of the S = 0 identity transferred from chart j to chart i.       *)
(* ========================================================================= *)

let P2BX_CFUN_MUL = prove
 (`!(c:(B->bool)#(B->real^3)) (f:real->B->real) (h:real->B->real).
     p2bw_cfun c (\t x. f t x * h t x) = (\z. p2bw_cfun c f z * p2bw_cfun c h z)`,
  REWRITE_TAC[FUN_EQ_THM; p2bw_cfun]);;

let P2BX_BOX_UF = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om
     ==> wan_loclip om (p2bw_cfun c linf) /\ wan_loclip om (p2bw_cfun c (p2bx_uf linf)) /\
         (!i j. 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
                ==> (\z. lift((sqrt(det(p2bw_cmet atlas' c (&1) g' z)) %%
                               matrix_inv(p2bw_cmet atlas' c (&1) g' z))$i$j)) continuous_on om)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_CSUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM P2BX_UOF_UF] THEN MATCH_MP_TAC P2BW_UOF_LOCLIP THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN REWRITE_TAC[p2bg_cbox] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `om:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `closure om SUBSET
                 {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                      &0 < drop(sndcart z)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                   `om:real^(3,1)finite_sum->bool`] P2BX_BOX_A_CONT) THEN
    ASM_SIMP_TAC[]]);;

(* Vanishing of the S-terms off the compact pieces of the boxes. *)

let P2BX_S0_VANISH_J = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) K Wo a b k c om Ks rho
    (tf:real->B->real) (uu:real->B->real) i j z.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\
     j IN 1..k /\ z IN om j /\ ~(z IN Ks j PCROSS interval[lift a,lift b])
     ==> p2bw_cfun (c j) (\t x. rho i x * tf t x) z *
         p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                       matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                  (p2bw_cfun (c j) uu) (p2bw_cfun (c j) (\t:real. rho j)) z = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
    UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                 {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(z:real^(3,1)finite_sum)`]
                P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(tf:real->B->real) (drop(sndcart z))
                   (chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart z)) = &0` THENL
   [ASM_REWRITE_TAC[p2bw_cfun; REAL_MUL_RZERO; REAL_MUL_LZERO]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                             `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(fstcart(z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])` THEN
    REWRITE_TAC[P2BX_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum)) IN
                  IMAGE (chart_inv (c j)) ((Ks:num->real^3->bool) j))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(fstcart(z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `y':real^3`] P2BX_CHART_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y':real^3) IN (Ks:num->real^3->bool) j` THEN
      UNDISCH_TAC `(Ks:num->real^3->bool) j SUBSET
                   IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` THEN SET_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) = y'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `SND((c:num->(B->bool)#(B->real^3)) j) (chart_inv (c j) (fstcart(z:real^(3,1)finite_sum)))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`;
                 `IMAGE (chart_inv ((c:num->(B->bool)#(B->real^3)) j)) ((Ks:num->real^3->bool) j)`;
                 `\t:real. (rho:num->B->real) j`; `z:real^(3,1)finite_sum`] P2BX_CFUN_ZERO_NEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) j) (&1)
                              (g':real->B->real^3^3) z)) %%
                  matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
             (p2bw_cfun (c j) (uu:real->B->real))
             (p2bw_cfun (c j) (\t:real. (rho:num->B->real) j)) z = &0`
  (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN ASM_REWRITE_TAC[]);;

let P2BX_S0_VANISH_I = prove
 (`!(top':B topology) atlas' K Wo a b k c om Ks rho (tf:real->B->real) i z.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\
     i IN 1..k /\ z IN om i /\ ~(z IN Ks i PCROSS interval[lift a,lift b])
     ==> p2bw_cfun (c i) (\t x. rho i x * tf t x) z = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `i:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) i` THEN
    UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) i SUBSET
                 {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) i`; `fstcart(z:real^(3,1)finite_sum)`]
                P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bw_cfun; REAL_ENTIRE] THEN
  ASM_CASES_TAC `(rho:num->B->real) i (chart_inv ((c:num->(B->bool)#(B->real^3)) i)
                   (fstcart(z:real^(3,1)finite_sum))) = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(tf:real->B->real) (drop(sndcart(z:real^(3,1)finite_sum)))
                   (chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart z)) = &0` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND((c:num->(B->bool)#(B->real^3)) i)
                  (chart_inv (c i) (fstcart(z:real^(3,1)finite_sum))) IN (Ks:num->real^3->bool) i`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `chart_inv ((c:num->(B->bool)#(B->real^3)) i)
                                (fstcart(z:real^(3,1)finite_sum))` o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(Ks:num->real^3->bool) i`)) (concl th) &&
        can (find_term ((=) `(rho:num->B->real) i`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                             `chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart(z:real^(3,1)finite_sum))`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) i PCROSS interval[lift a,lift b])` THEN
  ASM_REWRITE_TAC[P2BX_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]);;

(* Absolute integrability of the S-terms in the two charts. *)

let P2BX_S0_ABSINT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf i j m.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf)) /\
     i IN 1..k /\ j IN 1..k /\ (m = i \/ m = j)
     ==> (\z. lift(p2bw_cfun (c m) (\t x. rho i x * tf t x) z *
                   p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c m) (&1) g' z)) %%
                                 matrix_inv(p2bw_cmet atlas' (c m) (&1) g' z))
                            (p2bw_cfun (c m) (p2bx_uf linf)) (p2bw_cfun (c m) (\t:real. rho j)) z))
           absolutely_integrable_on (om m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `(m:num) IN 1..k` ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `m:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) m`; `(om:num->real^(3,1)finite_sum->bool) m`]
                P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:num. r IN 1..k
                ==> wan_loclip ((om:num->real^(3,1)finite_sum->bool) m)
                      (p2bw_cfun ((c:num->(B->bool)#(B->real^3)) m) (\t:real. (rho:num->B->real) r))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                   `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                   `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                   `rho:num->B->real`; `r:num`] P2BX_PDATA_MEMBER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(rho:num->B->real) r`; `(c:num->(B->bool)#(B->real^3)) m`;
                   `(om:num->real^(3,1)finite_sum->bool) m`] P2BX_MSMOOTH_CFUN_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX_ABSINT_SUPPORT THEN
  EXISTS_TAC `(Ks:num->real^3->bool) m PCROSS interval[lift a,lift b]` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[P2BX_CFUN_MUL; ETA_AX] THEN MATCH_MP_TAC P2BW_LOCLIP_MUL THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
    GEN_TAC THEN REWRITE_TAC[p2bw_cfun] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                   `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                   `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                   `rho:num->B->real`; `i:num`] P2BX_PDATA_MEMBER) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_SIMP_TAC[];
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> is_disj(concl th))) THENL
     [SUBGOAL_THEN `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i)
                      (\t x. (rho:num->B->real) i x * tf t x) z = &0`
        (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
      MATCH_MP_TAC P2BX_S0_VANISH_I THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                            `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BX_S0_VANISH_J THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`;
                            `k:num`; `om:num->real^(3,1)finite_sum->bool`;
                            `Ks:num->real^3->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

(* The transfer of an S-term from chart j to chart i. *)

let P2BX_S0_TRANSFER = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf i j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf)) /\
     i IN 1..k /\ j IN 1..k
     ==> integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t x. rho i x * tf t x) z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                              (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z)) =
         integral (om i)
           (\z. lift(p2bw_cfun (c i) (\t x. rho i x * tf t x) z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c i) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c i) (&1) g' z))
                              (p2bw_cfun (c i) (p2bx_uf linf)) (p2bw_cfun (c i) (\t:real. rho j)) z))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `i:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) i`; `(om:num->real^(3,1)finite_sum->bool) i`]
                P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) i`;
                 `(om:num->real^(3,1)finite_sum->bool) i`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `tf:real->B->real`;
                 `i:num`; `j:num`; `i:num`] P2BX_S0_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`;
                 `FST((c:num->(B->bool)#(B->real^3)) j)`; `SND((c:num->(B->bool)#(B->real^3)) j)`;
                 `FST((c:num->(B->bool)#(B->real^3)) i)`; `SND((c:num->(B->bool)#(B->real^3)) i)`;
                 `(om:num->real^(3,1)finite_sum->bool) j`; `(om:num->real^(3,1)finite_sum->bool) i`;
                 `\t x. (rho:num->B->real) i x * (tf:real->B->real) t x`;
                 `\z:real^(3,1)finite_sum. &0`; `\z:real^(3,1)finite_sum. &0`;
                 `{}:real^(3,1)finite_sum->bool`; `p2bx_uf (linf:real->B->real)`;
                 `\t:real. (rho:num->B->real) j`] P2BX_CHART_WTRANSFER) THEN
  REWRITE_TAC[PAIR; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; NEGLIGIBLE_EMPTY; NOT_IN_EMPTY] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(z:real^(3,1)finite_sum)`]
                  P2BX_CHART_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                    (\t x. (rho:num->B->real) i x * tf t x) z = &0`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    REWRITE_TAC[p2bw_cfun; REAL_ENTIRE] THEN
    ASM_CASES_TAC `(rho:num->B->real) i (chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                     (fstcart(z:real^(3,1)finite_sum))) = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(tf:real->B->real) (drop(sndcart(z:real^(3,1)finite_sum)))
                     (chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart z)) = &0` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                                (fstcart(z:real^(3,1)finite_sum))` o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(Ks:num->real^3->bool) i`)) (concl th) &&
        can (find_term ((=) `(rho:num->B->real) i`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                               `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_trans")) (concl th))) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[chart_trans] THEN
      UNDISCH_TAC `(Ks:num->real^3->bool) i PCROSS interval[lift a,lift b] SUBSET
                   (om:num->real^(3,1)finite_sum->bool) i` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]];
    X_GEN_TAC `y:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN `fstcart(y:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i))` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) i` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) i SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) i`; `fstcart(y:real^(3,1)finite_sum)`]
                  P2BX_CHART_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i)
                     (\t x. (rho:num->B->real) i x * tf t x) y = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `~((rho:num->B->real) i (chart_inv ((c:num->(B->bool)#(B->real^3)) i)
                      (fstcart(y:real^(3,1)finite_sum))) = &0) /\
                  ~((tf:real->B->real) (drop(sndcart y)) (chart_inv (c i) (fstcart y)) = &0)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i)
                      (\t x. (rho:num->B->real) i x * tf t x) y = &0)` THEN
      REWRITE_TAC[p2bw_cfun; REAL_ENTIRE; DE_MORGAN_THM];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(y:real^(3,1)finite_sum))`;
                               `chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart(y:real^(3,1)finite_sum))`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    ASM_CASES_TAC `chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart(y:real^(3,1)finite_sum)) IN
                   IMAGE (chart_inv (c j)) ((Ks:num->real^3->bool) j)` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(c:num->(B->bool)#(B->real^3)) j`; `y2:real^3`] P2BX_CHART_POINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y2:real^3) IN (Ks:num->real^3->bool) j` THEN
        UNDISCH_TAC `(Ks:num->real^3->bool) j SUBSET
                     IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` THEN SET_TAC[];
        STRIP_TAC] THEN
      SUBGOAL_THEN `chart_trans ((c:num->(B->bool)#(B->real^3)) j) (c i) y2 = fstcart(y:real^(3,1)finite_sum)`
      ASSUME_TAC THENL
       [REWRITE_TAC[chart_trans] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `chart_inv ((c:num->(B->bool)#(B->real^3)) j) y2`)) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_trans")) (concl th))) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `pastecart (y2:real^3) (sndcart(y:real^(3,1)finite_sum))` THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b] SUBSET
                     (om:num->real^(3,1)finite_sum->bool) j` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
        EXISTS_TAC `chart_inv ((c:num->(B->bool)#(B->real^3)) j) y2` THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `chart_inv ((c:num->(B->bool)#(B->real^3)) j) y2`)) THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(c:num->(B->bool)#(B->real^3)) i`;
                     `IMAGE (chart_inv ((c:num->(B->bool)#(B->real^3)) j)) ((Ks:num->real^3->bool) j)`;
                     `\t:real. (rho:num->B->real) j`; `y:real^(3,1)finite_sum`] P2BX_CFUN_ZERO_NEAR) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) i) (&1)
                                  (g':real->B->real^3^3) y)) %%
                      matrix_inv(p2bw_cmet atlas' (c i) (&1) g' y))
                 (p2bw_cfun (c i) (p2bx_uf (linf:real->B->real)))
                 (p2bw_cfun (c i) (\t:real. (rho:num->B->real) j)) y = &0`
      (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
      MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The S = 0 identity: the gradient terms of the partition functions cancel  *)
(* in the sum of the chart weak forms.                                       *)
(* ========================================================================= *)

let P2BX_SUM_DROP = prove
 (`!s (f:num->real^1). sum s (\i. drop(f i)) = drop(vsum s f)`,
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let P2BX_VSUM_LIFT = prove
 (`!s (f:num->real). vsum s (\i. lift(f i)) = lift(sum s f)`,
  REWRITE_TAC[LIFT_SUM; o_DEF]);;

let P2BX_S0_SPLIT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ Wo SUBSET K /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf)) /\ j IN 1..k
     ==> drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) tf z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                              (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z))) =
         sum(1..k) (\i. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t x. rho i x * tf t x) z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                              (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REWRITE_TAC[P2BX_SUM_DROP] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`\i:num. \z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                        (\t x. (rho:num->B->real) i x * (tf:real->B->real) t x) z *
                      p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z)) %%
                                    matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                               (p2bw_cfun (c j) (p2bx_uf (linf:real->B->real)))
                               (p2bw_cfun (c j) (\t:real. rho j)) z)`;
    `(om:num->real^(3,1)finite_sum->bool) j`; `1..k`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC P2BX_S0_ABSINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`;
                          `k:num`; `Ks:num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN REWRITE_TAC[P2BX_VSUM_LIFT; LIFT_EQ] THEN
  REWRITE_TAC[SUM_RMUL] THEN REWRITE_TAC[p2bw_cfun] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REWRITE_TAC[SUM_RMUL] THEN
  ASM_CASES_TAC `(tf:real->B->real) (drop(sndcart(z:real^(3,1)finite_sum)))
                   (chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart z)) = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `sum(1..k) (\i. (rho:num->B->real) i (chart_inv ((c:num->(B->bool)#(B->real^3)) j)
                  (fstcart(z:real^(3,1)finite_sum)))) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
  UNDISCH_TAC `p2bx_pdata atlas' K a b k (c:num->(B->bool)#(B->real^3)) om Ks (rho:num->B->real)` THEN
  REWRITE_TAC[p2bx_pdata] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                             `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `(Wo:B->bool) SUBSET K` THEN ASM SET_TAC[]);;

(* In one chart, the gradients of the partition functions sum to zero on  *)
(* the support of the test.                                                *)

let P2BX_S0_SUMZERO = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf i.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ open_in top' Wo /\ Wo SUBSET K /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf)) /\ i IN 1..k
     ==> sum(1..k) (\j. drop(integral (om i)
           (\z. lift(p2bw_cfun (c i) (\t x. rho i x * tf t x) z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c i) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c i) (&1) g' z))
                              (p2bw_cfun (c i) (p2bx_uf linf)) (p2bw_cfun (c i) (\t:real. rho j)) z)))) =
         &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `i:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BX_SUM_DROP] THEN
  MP_TAC(ISPECL
   [`\j:num. \z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i)
                        (\t x. (rho:num->B->real) i x * (tf:real->B->real) t x) z *
                      p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c i) (&1) (g':real->B->real^3^3) z)) %%
                                    matrix_inv(p2bw_cmet atlas' (c i) (&1) g' z))
                               (p2bw_cfun (c i) (p2bx_uf (linf:real->B->real)))
                               (p2bw_cfun (c i) (\t:real. rho j)) z)`;
    `(om:num->real^(3,1)finite_sum->bool) i`; `1..k`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC P2BX_S0_ABSINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`;
                          `k:num`; `Ks:num->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM DROP_VEC] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `integral ((om:num->real^(3,1)finite_sum->bool) i) (\z. vec 0:real^1)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  REWRITE_TAC[P2BX_VSUM_LIFT; GSYM LIFT_NUM; LIFT_EQ; SUM_LMUL] THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) i` THEN
    UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) i SUBSET
                 {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) i`; `fstcart(z:real^(3,1)finite_sum)`]
                P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(tf:real->B->real) (drop(sndcart(z:real^(3,1)finite_sum)))
                   (chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart z)) = &0` THENL
   [ASM_REWRITE_TAC[p2bw_cfun; REAL_MUL_RZERO; REAL_MUL_LZERO]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                             `chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart(z:real^(3,1)finite_sum))`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  (* the derivatives of the partition sum vanish *)
  SUBGOAL_THEN `!j. 1 <= j /\ j <= k
                    ==> (\w. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i) (\t:real. (rho:num->B->real) j) w))
                        differentiable at z`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                   `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                   `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                   `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) i`;
                   `(om:num->real^(3,1)finite_sum->bool) i`] P2BX_MSMOOTH_CFUN_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) i) (&1)
                               (g':real->B->real^3^3) z)) %%
                      matrix_inv(p2bw_cmet atlas' (c i) (&1) g' z)`;
                 `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i) (p2bx_uf (linf:real->B->real))`;
                 `\j:num. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i) (\t:real. (rho:num->B->real) j)`;
                 `k:num`; `z:real^(3,1)finite_sum`] P2BX_BIL_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' ((c:num->(B->bool)#(B->real^3)) i) (&1)
                              (g':real->B->real^3^3) z)) %%
                  matrix_inv(p2bw_cmet atlas' (c i) (&1) g' z))
             (p2bw_cfun (c i) (p2bx_uf (linf:real->B->real)))
             (\w. sum(1..k) (\j. p2bw_cfun (c i) (\t:real. (rho:num->B->real) j) w)) z = &0`
  (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
  MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN X_GEN_TAC `jj:num` THEN DISCH_TAC THEN
  REWRITE_TAC[wan_xder] THEN
  MP_TAC(ISPECL [`\w:real^(3,1)finite_sum. sum(1..k)
                   (\j. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i) (\t:real. (rho:num->B->real) j) w)`;
                 `\w:real^(3,1)finite_sum. &1`;
                 `{w:real^(3,1)finite_sum | fstcart w IN
                     IMAGE (SND((c:num->(B->bool)#(B->real^3)) i)) (FST(c i) INTER Wo)}`;
                 `z:real^(3,1)finite_sum`] P2BX_DERIV_LOCAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIFFERENTIABLE_CONST] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
        ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `(c:num->(B->bool)#(B->real^3)) i`] MFDM_CHART) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv ((c:num->(B->bool)#(B->real^3)) i) (fstcart(z:real^(3,1)finite_sum))` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[p2bw_cfun] THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(c:num->(B->bool)#(B->real^3)) i`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `p2bx_pdata atlas' K a b k (c:num->(B->bool)#(B->real^3)) om Ks (rho:num->B->real)` THEN
      REWRITE_TAC[p2bx_pdata] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      UNDISCH_TAC `(Wo:B->bool) SUBSET K` THEN ASM SET_TAC[]];
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC]]);;

(* The S = 0 identity. *)

let P2BX_GFUN_S0 = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ open_in top' Wo /\ Wo SUBSET K /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf))
     ==> sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) tf z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                              (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z)))) =
         &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..k) (\j. sum(1..k) (\i. drop(integral ((om:num->real^(3,1)finite_sum->bool) i)
       (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) i)
                   (\t x. (rho:num->B->real) i x * (tf:real->B->real) t x) z *
                 p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c i) (&1) (g':real->B->real^3^3) z)) %%
                               matrix_inv(p2bw_cmet atlas' (c i) (&1) g' z))
                          (p2bw_cfun (c i) (p2bx_uf (linf:real->B->real)))
                          (p2bw_cfun (c i) (\t:real. rho j)) z)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                   `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                   `Ks:num->real^3->bool`; `rho:num->B->real`; `tf:real->B->real`; `j:num`]
                  P2BX_S0_SPLIT) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC P2BX_S0_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`;
                          `k:num`; `Ks:num->real^3->bool`] THEN
    ASM_REWRITE_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX_S0_SUMZERO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                        `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                        `sub:num->num`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`;
                        `Ks:num->real^3->bool`] THEN
  ASM_REWRITE_TAC[IN_NUMSEG]);;

(* ========================================================================= *)
(* The global functional is nonpositive on nonnegative admissible functions  *)
(* (P1).  In each chart the product rule splits the weighted term into a box *)
(* subsolution term (a nonnegative Lipschitz test) minus an S-term; the      *)
(* S-terms sum to 0 (P2BX_GFUN_S0).                                          *)
(* ========================================================================= *)

let P2BX_LOCLIP_EQ = prove
 (`!(s:real^M->bool) u v.
     wan_loclip s u /\ (!x. x IN s ==> u x = v x) ==> wan_loclip s v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_loclip] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^M->real) x = u x /\ v y = u y` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]]);;

let P2BX_LOCLIP_CONST = prove
 (`!(s:real^M->bool) c. wan_loclip s (\x. c)`,
  REWRITE_TAC[wan_loclip; REAL_SUB_REFL; REAL_ABS_0] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]);;

(* The weak integrand of a nonnegative Lipschitz test on a box is           *)
(* absolutely integrable.                                                    *)

let P2BX_WINT_ABSINT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om psi.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om /\ p2bw_ltest om psi
     ==> (\z. lift(p2bx_wint atlas' g' c (p2bx_uf linf) psi z)) absolutely_integrable_on om`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_LIMIT_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_BOX_A_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(om:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bg_cbox]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bw_ltest]) THEN
  REWRITE_TAC[p2bx_wint; LIFT_ADD] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_LTEST_LEBM_ABSINT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[wan_tder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN
        ASM_REWRITE_TAC[ETA_AX];
        MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THEN MATCH_MP_TAC P2BW_LEBM_CONT THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX]]];
      MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`om:real^(3,1)finite_sum->bool`; `k:real^(3,1)finite_sum->bool`;
                 `\z:real^(3,1)finite_sum. &1`;
                 `p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) z)) %%
                                matrix_inv(p2bw_cmet atlas' c (&1) g' z))
                           (p2bw_cfun (c:(B->bool)#(B->real^3)) (p2bx_uf (linf:real->B->real)))
                           (psi:real^(3,1)finite_sum->real)`] P2BX_ABSINT_SUPPORT) THEN
  REWRITE_TAC[REAL_MUL_LID; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_POS; P2BX_LOCLIP_CONST] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN
  MP_TAC(ISPECL [`psi:real^(3,1)finite_sum->real`; `(:real^(3,1)finite_sum) DIFF k`;
                 `z:real^(3,1)finite_sum`] P2BX_XDER_ZERO_OPEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM closed; IN_DIFF; IN_UNIV] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    SIMP_TAC[]]);;

(* The gradient of a partition member vanishes off its compact piece. *)

let P2BX_BIL_RHO_ZERO = prove
 (`!(top':B topology) atlas' (A:real^(3,1)finite_sum->real^3^3) K a b k c om Ks rho
    (uu:real->B->real) j z.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     j IN 1..k /\ z IN om j /\ ~(fstcart z IN Ks j)
     ==> p2bw_bil A (p2bw_cfun (c j) uu) (p2bw_cfun (c j) (\t:real. rho j)) z = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
    UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                 {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(z:real^(3,1)finite_sum)`]
                P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum)) IN
                  IMAGE (chart_inv (c j)) ((Ks:num->real^3->bool) j))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(fstcart(z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `y':real^3`] P2BX_CHART_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y':real^3) IN (Ks:num->real^3->bool) j` THEN
      UNDISCH_TAC `(Ks:num->real^3->bool) j SUBSET
                   IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` THEN SET_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) = y'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `SND((c:num->(B->bool)#(B->real^3)) j) (chart_inv (c j) (fstcart(z:real^(3,1)finite_sum)))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(c:num->(B->bool)#(B->real^3)) j`;
                 `IMAGE (chart_inv ((c:num->(B->bool)#(B->real^3)) j)) ((Ks:num->real^3->bool) j)`;
                 `\t:real. (rho:num->B->real) j`; `z:real^(3,1)finite_sum`] P2BX_CFUN_ZERO_NEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN ASM_REWRITE_TAC[]);;

(* The S-term without the outer partition weight is absolutely integrable. *)

let P2BX_TF_BIL_ABSINT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     wan_loclip (om j) (p2bw_cfun (c j) tf) /\ j IN 1..k
     ==> (\z. lift(p2bw_cfun (c j) tf z *
                   p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                                 matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                            (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z))
           absolutely_integrable_on (om j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`]
                P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX_ABSINT_SUPPORT THEN
  EXISTS_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
  ASM_CASES_TAC `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf:real->B->real) z = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  MATCH_MP_TAC(REAL_RING `y = &0 ==> x * y = &0`) THEN
  MATCH_MP_TAC P2BX_BIL_RHO_ZERO THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                        `K:B->bool`; `a:real`; `b:real`; `k:num`;
                        `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf:real->B->real) z = &0)` THEN
  REWRITE_TAC[p2bw_cfun] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`drop(sndcart(z:real^(3,1)finite_sum))`;
                             `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))`] o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `Wo:B->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `~((z:real^(3,1)finite_sum) IN (Ks:num->real^3->bool) j PCROSS interval[lift a,lift b])` THEN
  ASM_REWRITE_TAC[P2BX_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]);;

(* One chart term of the global functional is at most minus its S-term. *)

let P2BX_GFUN_TERM = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     wan_loclip (om j) (p2bw_cfun (c j) tf) /\ j IN 1..k
     ==> drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf) (p2bw_cfun (c j) tf) z))) <=
         --drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) tf z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                              (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `(c:num->(B->bool)#(B->real^3)) j`;
                 `(om:num->real^(3,1)finite_sum->bool) j`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `psi = \z:real^(3,1)finite_sum.
                 if z IN (om:num->real^(3,1)finite_sum->bool) j
                 then p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                        (\t x. (rho:num->B->real) j x * (tf:real->B->real) t x) z
                 else &0` THEN
  SUBGOAL_THEN `!z. z IN (om:num->real^(3,1)finite_sum->bool) j
                    ==> (psi:real^(3,1)finite_sum->real) z =
                        p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                        p2bw_cfun (c j) (tf:real->B->real) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[p2bw_cfun];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bw_ltest ((om:num->real^(3,1)finite_sum->bool) j) psi` ASSUME_TAC THENL
   [REWRITE_TAC[p2bw_ltest] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_LOCLIP_EQ THEN
      EXISTS_TAC `\z. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                      p2bw_cfun (c j) (tf:real->B->real) z` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_LE_REFL; p2bw_cfun] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b]` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
      EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC P2BX_S0_VANISH_I THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                            `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`;
                 `psi:real^(3,1)finite_sum->real`] P2BX_BOX_WSUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`;
                 `psi:real^(3,1)finite_sum->real`] P2BX_WINT_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `tf:real->B->real`; `j:num`]
                P2BX_TF_BIL_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `integral ((om:num->real^(3,1)finite_sum->bool) j)
      (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                p2bx_wint atlas' (g':real->B->real^3^3) (c j) (p2bx_uf (linf:real->B->real))
                          (p2bw_cfun (c j) (tf:real->B->real)) z)) =
    integral (om j)
      (\z. lift(p2bx_wint atlas' g' (c j) (p2bx_uf linf) psi z) -
           lift(p2bw_cfun (c j) tf z *
                p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                              matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                         (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (\t:real. rho j)) z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{z | z IN (om:num->real^(3,1)finite_sum->bool) j /\
                     ~((\y. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                                   (tf:real->B->real) y)) differentiable at z)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_LOCLIP_AE_OPEN THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(\y. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                             (tf:real->B->real) y)) differentiable at z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\y. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j)
                             (\t:real. (rho:num->B->real) j) y)) differentiable at z` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j)`;
                   `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf:real->B->real)`;
                   `z:real^(3,1)finite_sum`; `vec 0:real^(3,1)finite_sum`] P2BW_DER_MUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `p2bx_uf (linf:real->B->real)`;
                   `psi:real^(3,1)finite_sum->real`;
                   `\w. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) w *
                        p2bw_cfun (c j) (tf:real->B->real) w`;
                   `(om:num->real^(3,1)finite_sum->bool) j`; `z:real^(3,1)finite_sum`]
                  P2BX_WINT_LOCAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `p2bx_uf (linf:real->B->real)`;
                   `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j)`;
                   `p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf:real->B->real)`;
                   `z:real^(3,1)finite_sum`] P2BX_WINT_MUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM LIFT_SUB; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_SUB] THEN
  ASM_REAL_ARITH_TAC);;

(* P1: the global functional is nonpositive. *)

let P2BX_GFUN_NONPOS = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K Wo a b k c om Ks rho tf.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ open_in top' Wo /\ Wo SUBSET K /\
     (!t x. ~(tf t x = &0) ==> x IN Wo /\ a <= t /\ t <= b) /\ (!t x. &0 <= tf t x) /\
     (!j. j IN 1..k ==> wan_loclip (om j) (p2bw_cfun (c j) tf))
     ==> sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf) (p2bw_cfun (c j) tf) z)))) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..k) (\j. --drop(integral ((om:num->real^(3,1)finite_sum->bool) j)
           (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (tf:real->B->real) z *
                     p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) (g':real->B->real^3^3) z)) %%
                                   matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                              (p2bw_cfun (c j) (p2bx_uf (linf:real->B->real)))
                              (p2bw_cfun (c j) (\t:real. (rho:num->B->real) j)) z))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BX_GFUN_TERM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`; `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`;
                          `k:num`; `Ks:num->real^3->bool`] THEN
    ASM_SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_NEG] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `Wo:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `tf:real->B->real`] P2BX_GFUN_S0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A chart test as a function on the limit (p2bx_mfun), its chart readings   *)
(* (smooth in every chart), the chart invariance of time derivatives.        *)
(* ========================================================================= *)

let p2bx_mfun = new_definition
 `p2bx_mfun (c:(B->bool)#(B->real^3)) (psi:real^(3,1)finite_sum->real) (t:real) (x:B) =
    if x IN FST c then psi(pastecart (SND c x) (lift t)) else &0`;;

let P2BX_MFUN_CFUN_SELF = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) psi z.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ fstcart z IN IMAGE (SND c) (FST c)
     ==> p2bw_cfun c (p2bx_mfun c psi) z = psi z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`; `fstcart(z:real^(3,1)finite_sum)`] P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[p2bw_cfun; p2bx_mfun; LIFT_DROP; PASTECART_FST_SND]);;

let P2BX_MFUN_SUPPORT = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) psi kp.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ (!z. ~(z IN kp) ==> psi z = &0)
     ==> !t x. ~(x IN IMAGE (chart_inv c) (IMAGE fstcart kp)) ==> p2bx_mfun c psi t x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx_mfun] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~((x:B) IN IMAGE (chart_inv (c:(B->bool)#(B->real^3)))
                   (IMAGE fstcart (kp:real^(3,1)finite_sum->bool)))` THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `SND(c:(B->bool)#(B->real^3)) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `pastecart (SND(c:(B->bool)#(B->real^3)) x) (lift t)` THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART]]);;

(* The base points of the support of a chart test form a compact set. *)

let P2BX_MFUN_SUPPSET = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) kp.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ c IN atlas' /\
     compact (kp:real^(3,1)finite_sum->bool) /\ IMAGE fstcart kp SUBSET IMAGE (SND c) (FST c)
     ==> compact_in top' (IMAGE (chart_inv c) (IMAGE fstcart kp)) /\
         closed_in top' (IMAGE (chart_inv c) (IMAGE fstcart kp)) /\
         IMAGE (chart_inv c) (IMAGE fstcart kp) SUBSET FST c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`]
                MFDC_CHART_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_in (subtopology top' (FST(c:(B->bool)#(B->real^3))))
                  (IMAGE (chart_inv c) (IMAGE fstcart (kp:real^(3,1)finite_sum->bool)))`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[LINEAR_FSTCART];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]);;

(* A chart test read in any chart of the limit is smooth on the chart       *)
(* cylinder.                                                                  *)

let P2BX_MFUN_SMOOTH = prove
 (`!(top':B topology) atlas' (c0:(B->bool)#(B->real^3)) c psi kp.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ c0 IN atlas' /\ c IN atlas' /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     compact kp /\ IMAGE fstcart kp SUBSET IMAGE (SND c0) (FST c0) /\
     (!z. ~(z IN kp) ==> psi z = &0)
     ==> smooth_map_on {z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND c) (FST c)}
                       (\z. lift(p2bw_cfun c (p2bx_mfun c0 psi) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`; `kp:real^(3,1)finite_sum->bool`] P2BX_MFUN_SUPPSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`; `psi:real^(3,1)finite_sum->real`;
                 `kp:real^(3,1)finite_sum->bool`] P2BX_MFUN_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_OPEN_CHART_CYL THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`; `fstcart(z:real^(3,1)finite_sum)`] P2BX_CHART_POINT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN
                 FST(c0:(B->bool)#(B->real^3))` THENL
   [EXISTS_TAC `{w:real^(3,1)finite_sum | fstcart w IN
                   IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER FST(c0:(B->bool)#(B->real^3)))}` THEN
    SUBGOAL_THEN `open {w:real^(3,1)finite_sum | fstcart w IN
                   IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER FST(c0:(B->bool)#(B->real^3)))} /\
                  open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER FST(c0:(B->bool)#(B->real^3))))`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
        ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
        DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
        GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(\y. lift((psi:real^(3,1)finite_sum->real) y)) o
                (\w. pastecart (chart_trans (c:(B->bool)#(B->real^3)) c0 (fstcart w)) (sndcart w))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(3,1)finite_sum` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_INTER; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[p2bw_cfun; p2bx_mfun; chart_trans; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\w:real^(3,1)finite_sum. chart_trans (c:(B->bool)#(B->real^3)) c0 (fstcart w)) =
                    chart_trans c c0 o (fstcart o (\w:real^(3,1)finite_sum. w))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER FST(c0:(B->bool)#(B->real^3)))` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
        MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                       `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                       `FST(c0:(B->bool)#(B->real^3))`; `SND(c0:(B->bool)#(B->real^3))`]
                      CHART_TRANS_SMOOTH) THEN
        ASM_REWRITE_TAC[PAIR]];
      REWRITE_TAC[ETA_AX] THEN
      SUBGOAL_THEN `(sndcart:real^(3,1)finite_sum->real^1) = sndcart o (\w:real^(3,1)finite_sum. w)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN
                  IMAGE (chart_inv c0) (IMAGE fstcart (kp:real^(3,1)finite_sum->bool)))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Cp = IMAGE (chart_inv (c0:(B->bool)#(B->real^3)))
                         (IMAGE fstcart (kp:real^(3,1)finite_sum->bool))` THEN
  EXISTS_TAC `{w:real^(3,1)finite_sum | fstcart w IN
                 IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c DIFF (Cp:B->bool))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
      MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF; SUBSET_DIFF]];
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\w:real^(3,1)finite_sum. lift(&0)` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[LIFT_EQ] THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[p2bw_cfun] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* Time derivatives of chart readings are chart invariant. *)

let P2BX_TDER_TRANS = prove
 (`!(top':B topology) atlas' U1 (phi1:B->real^3) U2 phi2 (f:real->B->real) z.
     smooth_manifold_atlas top' atlas' /\ (U1,phi1) IN atlas' /\ (U2,phi2) IN atlas' /\
     fstcart z IN IMAGE phi1 (U1 INTER U2) /\
     (\y. lift(p2bw_cfun (U2,phi2) f y)) differentiable at
       (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z))
     ==> (\y. lift(p2bw_cfun (U1,phi1) f y)) differentiable at z /\
         wan_tder (p2bw_cfun (U1,phi1) f) z =
         wan_tder (p2bw_cfun (U2,phi2) f)
           (pastecart (chart_trans (U1,phi1) (U2,phi2) (fstcart z)) (sndcart z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[REAL_MUL_LID; LIFT_DROP; REAL_LT_01]
   (ISPECL [`IMAGE (phi1:B->real^3) (U1 INTER U2)`; `IMAGE (phi2:B->real^3) (U1 INTER U2)`;
            `chart_trans (U1:B->bool,phi1:B->real^3) (U2,phi2)`;
            `chart_trans (U2:B->bool,phi2:B->real^3) (U1,phi1)`; `&1`;
            `p2bw_cfun (U2:B->bool,phi2:B->real^3) (f:real->B->real)`;
            `p2bw_cfun (U1:B->bool,phi1:B->real^3) (f:real->B->real)`;
            `{w:real^(3,1)finite_sum | fstcart w IN IMAGE (phi1:B->real^3) (U1 INTER U2)}`;
            `z:real^(3,1)finite_sum`] P2BX_PHI_CHAIN)) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
      MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `phi2:B->real^3`] THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`; `U1:B->bool`; `phi1:B->real^3`;
                   `U2:B->bool`; `phi2:B->real^3`; `w:real^(3,1)finite_sum`] P2BX_CHART_DATA_TRANS) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The weighted weak integrand vanishes where the test vanishes nearby. *)

let P2BX_WFORM_ZERO = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) u s O z rr Q D.
     open O /\ z IN O /\ (!w. w IN O ==> s w = &0)
     ==> rr * (s z * Q) * D + rr * p2bw_bil A u s z = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^(N,1)finite_sum->real) z = &0` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bw_bil (A:real^(N,1)finite_sum->real^N^N) u s z = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN
    MP_TAC(ISPECL [`s:real^(N,1)finite_sum->real`; `O:real^(N,1)finite_sum->bool`;
                   `z:real^(N,1)finite_sum`] P2BX_XDER_ZERO_OPEN) THEN
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC]);;

(* A chart test read in a chart vanishes near points whose base point lies  *)
(* off the (closed) set of base points of its support.                       *)

let P2BX_MFUN_ZERO_BASE = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) c0 psi kp z.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ c0 IN atlas' /\
     (!z. ~(z IN kp) ==> psi z = &0) /\
     closed_in top' (IMAGE (chart_inv c0) (IMAGE fstcart kp)) /\
     fstcart z IN IMAGE (SND c) (FST c) /\
     ~(chart_inv c (fstcart z) IN IMAGE (chart_inv c0) (IMAGE fstcart kp))
     ==> ?O. open O /\ z IN O /\ !w. w IN O ==> p2bw_cfun c (p2bx_mfun c0 psi) w = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`; `psi:real^(3,1)finite_sum->real`;
                 `kp:real^(3,1)finite_sum->bool`] P2BX_MFUN_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Cp = IMAGE (chart_inv (c0:(B->bool)#(B->real^3)))
                         (IMAGE fstcart (kp:real^(3,1)finite_sum->bool))` THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{w:real^(3,1)finite_sum | fstcart w IN
                 IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c DIFF (Cp:B->bool))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART];
      MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF; SUBSET_DIFF]];
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c:(B->bool)#(B->real^3)) (fstcart(z:real^(3,1)finite_sum))` THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[p2bw_cfun] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* ... and near points whose transition image lies off the support. *)

let P2BX_MFUN_ZERO_TRANS = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) c0 psi kp z.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ c0 IN atlas' /\
     closed kp /\ (!z. ~(z IN kp) ==> psi z = &0) /\
     fstcart z IN IMAGE (SND c) (FST c INTER FST c0) /\
     ~(pastecart (chart_trans c c0 (fstcart z)) (sndcart z) IN kp)
     ==> ?O. open O /\ z IN O /\ !w. w IN O ==> p2bw_cfun c (p2bx_mfun c0 psi) w = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER FST(c0:(B->bool)#(B->real^3))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `{w:real^(3,1)finite_sum |
                 w IN {w | fstcart w IN IMAGE (SND(c:(B->bool)#(B->real^3)))
                                          (FST c INTER FST(c0:(B->bool)#(B->real^3)))} /\
                 (\w. pastecart (chart_trans c c0 (fstcart w)) (sndcart w)) w IN
                 (:real^(3,1)finite_sum) DIFF kp}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[GSYM closed] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\w:real^(3,1)finite_sum. chart_trans (c:(B->bool)#(B->real^3)) c0 (fstcart w)) =
                      chart_trans c c0 o fstcart`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER FST(c0:(B->bool)#(B->real^3)))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
          MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `FST(c:(B->bool)#(B->real^3))`; `SND(c:(B->bool)#(B->real^3))`;
                         `FST(c0:(B->bool)#(B->real^3))`; `SND(c0:(B->bool)#(B->real^3))`]
                        CHART_TRANS_SMOOTH) THEN
          ASM_REWRITE_TAC[PAIR];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[LINEAR_FSTCART]];
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV];
    X_GEN_TAC `w:real^(3,1)finite_sum` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (SND c x) = x`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(pastecart (chart_trans (c:(B->bool)#(B->real^3)) c0 (fstcart(w:real^(3,1)finite_sum)))
                             (sndcart w) IN kp)` THEN
    ASM_REWRITE_TAC[chart_trans; p2bw_cfun; p2bx_mfun; LIFT_DROP] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* One partition term of the global functional at a chart test, moved to   *)
(* the chart of the test.                                                     *)

let P2BX_MFUN_TRANSFER = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho c0 om0 psi kp j.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ j IN 1..k /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     compact kp /\ kp SUBSET om0 /\ (!z. ~(z IN kp) ==> psi z = &0) /\
     (!z. z IN kp ==> a <= drop(sndcart z) /\ drop(sndcart z) <= b)
     ==> integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf) (p2bw_cfun (c j) (p2bx_mfun c0 psi)) z)) =
         integral om0
           (\y. lift(p2bw_cfun c0 (\t:real. rho j) y * p2bx_wint atlas' g' c0 (p2bx_uf linf) psi y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                 `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                 `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                 `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(om0:real^(3,1)finite_sum->bool) /\
                om0 SUBSET {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c0:(B->bool)#(B->real^3)) om0` THEN REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `om0:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`] P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`] P2BX_BOX_LIMIT_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c0:(B->bool)#(B->real^3)`;
                 `om0:real^(3,1)finite_sum->bool`] P2BX_BOX_A_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(rho:num->B->real) j`; `c0:(B->bool)#(B->real^3)`;
                 `om0:real^(3,1)finite_sum->bool`] P2BX_MSMOOTH_CFUN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE fstcart (kp:real^(3,1)finite_sum->bool) SUBSET
                IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(kp:real^(3,1)finite_sum->bool) SUBSET om0` THEN
    UNDISCH_TAC `(om0:real^(3,1)finite_sum->bool) SUBSET
                 {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`; `kp:real^(3,1)finite_sum->bool`] P2BX_MFUN_SUPPSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`] P2BX_OPEN_CHART_CYL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c0:(B->bool)#(B->real^3)`; `c0:(B->bool)#(B->real^3)`;
                 `psi:real^(3,1)finite_sum->real`; `kp:real^(3,1)finite_sum->bool`] P2BX_MFUN_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}
                    ==> p2bw_cfun c0 (p2bx_mfun c0 psi) y = (psi:real^(3,1)finite_sum->real) y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_MFUN_CFUN_SELF THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip om0 (p2bw_cfun (c0:(B->bool)#(B->real^3)) (p2bx_mfun c0 psi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN
    EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the integrals in the form of the weighted transfer *)
  SUBGOAL_THEN
   `integral om0
      (\y. lift(p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y *
                p2bx_wint atlas' (g':real->B->real^3^3) c0 (p2bx_uf (linf:real->B->real)) psi y)) =
    integral om0
      (\y. lift(p2bw_cfun c0 (\t:real. rho j) y *
                (p2bw_cfun c0 (p2bx_mfun c0 psi) y *
                 (wan_tder (p2bw_cfun c0 (p2bx_uf linf)) y +
                  p2bw_cscal atlas' c0 (&1) g' y * p2bw_cfun c0 (p2bx_uf linf) y)) *
                sqrt(det(p2bw_cmet atlas' c0 (&1) g' y)) +
                p2bw_cfun c0 (\t:real. rho j) y *
                p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' c0 (&1) g' z)) %%
                              matrix_inv(p2bw_cmet atlas' c0 (&1) g' z))
                         (p2bw_cfun c0 (p2bx_uf linf)) (p2bw_cfun c0 (p2bx_mfun c0 psi)) y))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_EQ] THEN
    SUBGOAL_THEN `(y:real^(3,1)finite_sum) IN
                  {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                   `c0:(B->bool)#(B->real^3)`; `p2bx_uf (linf:real->B->real)`;
                   `psi:real^(3,1)finite_sum->real`;
                   `p2bw_cfun (c0:(B->bool)#(B->real^3)) (p2bx_mfun c0 psi)`;
                   `{z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}`;
                   `y:real^(3,1)finite_sum`] P2BX_WINT_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[p2bx_wint] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral ((om:num->real^(3,1)finite_sum->bool) j)
      (\z. lift(p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (\t:real. (rho:num->B->real) j) z *
                p2bx_wint atlas' (g':real->B->real^3^3) (c j) (p2bx_uf (linf:real->B->real))
                          (p2bw_cfun (c j) (p2bx_mfun (c0:(B->bool)#(B->real^3)) psi)) z)) =
    integral (om j)
      (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                (p2bw_cfun (c j) (p2bx_mfun c0 psi) z *
                 (wan_tder (p2bw_cfun (c j) (p2bx_uf linf)) z +
                  p2bw_cscal atlas' (c j) (&1) g' z * p2bw_cfun (c j) (p2bx_uf linf) z)) *
                sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) +
                p2bw_cfun (c j) (\t:real. rho j) z *
                p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' (c j) (&1) g' z)) %%
                              matrix_inv(p2bw_cmet atlas' (c j) (&1) g' z))
                         (p2bw_cfun (c j) (p2bx_uf linf)) (p2bw_cfun (c j) (p2bx_mfun c0 psi)) z))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[p2bx_wint] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                 `FST((c:num->(B->bool)#(B->real^3)) j)`; `SND((c:num->(B->bool)#(B->real^3)) j)`;
                 `FST(c0:(B->bool)#(B->real^3))`; `SND(c0:(B->bool)#(B->real^3))`;
                 `(om:num->real^(3,1)finite_sum->bool) j`; `om0:real^(3,1)finite_sum->bool`;
                 `\t:real. (rho:num->B->real) j`;
                 `\z. p2bw_cfun ((c:num->(B->bool)#(B->real^3)) j) (p2bx_mfun c0 psi) z *
                      (wan_tder (p2bw_cfun (c j) (p2bx_uf (linf:real->B->real))) z +
                       p2bw_cscal atlas' (c j) (&1) (g':real->B->real^3^3) z *
                       p2bw_cfun (c j) (p2bx_uf linf) z)`;
                 `\y. p2bw_cfun (c0:(B->bool)#(B->real^3)) (p2bx_mfun c0 psi) y *
                      (wan_tder (p2bw_cfun c0 (p2bx_uf (linf:real->B->real))) y +
                       p2bw_cscal atlas' c0 (&1) (g':real->B->real^3^3) y *
                       p2bw_cfun c0 (p2bx_uf linf) y)`;
                 `{}:real^(3,1)finite_sum->bool`; `p2bx_uf (linf:real->B->real)`;
                 `p2bx_mfun (c0:(B->bool)#(B->real^3)) psi`] P2BX_CHART_WTRANSFER) THEN
  REWRITE_TAC[PAIR; NEGLIGIBLE_EMPTY; NOT_IN_EMPTY] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the q-relation *)
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':real->B->real^3^3`;
                   `FST((c:num->(B->bool)#(B->real^3)) j)`; `SND((c:num->(B->bool)#(B->real^3)) j)`;
                   `FST(c0:(B->bool)#(B->real^3))`; `SND(c0:(B->bool)#(B->real^3))`;
                   `z:real^(3,1)finite_sum`] P2BX_CHART_DATA_TRANS) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `FST((c:num->(B->bool)#(B->real^3)) j)`; `SND((c:num->(B->bool)#(B->real^3)) j)`;
                   `FST(c0:(B->bool)#(B->real^3))`; `SND(c0:(B->bool)#(B->real^3))`;
                   `p2bx_uf (linf:real->B->real)`; `z:real^(3,1)finite_sum`] P2BX_TDER_TRANS) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    (* the source integrand vanishes off the transfer domain *)
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX_WFORM_ZERO THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN
                  IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN (om:num->real^(3,1)finite_sum->bool) j` THEN
      UNDISCH_TAC `(om:num->real^(3,1)finite_sum->bool) j SUBSET
                   {z | fstcart z IN IMAGE (SND((c:num->(B->bool)#(B->real^3)) j)) (FST(c j))}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`; `fstcart(z:real^(3,1)finite_sum)`]
                  P2BX_CHART_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `fstcart(z:real^(3,1)finite_sum) IN
                   IMAGE (SND((c:num->(B->bool)#(B->real^3)) j))
                         (FST(c j) INTER FST(c0:(B->bool)#(B->real^3)))` THENL
     [MATCH_MP_TAC P2BX_MFUN_ZERO_TRANS THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `kp:real^(3,1)finite_sum->bool`] THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      UNDISCH_TAC `~(fstcart(z:real^(3,1)finite_sum) IN
                     IMAGE (SND((c:num->(B->bool)#(B->real^3)) j))
                           (FST(c j) INTER FST(c0:(B->bool)#(B->real^3))) /\
                     pastecart (chart_trans (c j) c0 (fstcart z)) (sndcart z) IN om0)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(kp:real^(3,1)finite_sum->bool) SUBSET om0` THEN SET_TAC[];
      MATCH_MP_TAC P2BX_MFUN_ZERO_BASE THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `kp:real^(3,1)finite_sum->bool`] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(fstcart(z:real^(3,1)finite_sum) IN
                     IMAGE (SND((c:num->(B->bool)#(B->real^3)) j))
                           (FST(c j) INTER FST(c0:(B->bool)#(B->real^3))))` THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (chart_inv (c0:(B->bool)#(B->real^3)))
                     (IMAGE fstcart (kp:real^(3,1)finite_sum->bool)) SUBSET FST c0` THEN
      UNDISCH_TAC `chart_inv ((c:num->(B->bool)#(B->real^3)) j) (fstcart(z:real^(3,1)finite_sum)) IN
                   IMAGE (chart_inv (c0:(B->bool)#(B->real^3)))
                     (IMAGE fstcart (kp:real^(3,1)finite_sum->bool))` THEN
      SET_TAC[]];
    (* the target integrand vanishes off the image of the transfer domain *)
    X_GEN_TAC `y:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    ASM_CASES_TAC `p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC P2BX_WFORM_ZERO THEN
    ASM_CASES_TAC `(y:real^(3,1)finite_sum) IN kp` THENL
     [ALL_TAC;
      EXISTS_TAC `(om0:real^(3,1)finite_sum->bool) DIFF kp` THEN
      ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF] THEN
      X_GEN_TAC `w:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(w:real^(3,1)finite_sum) IN
                    {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` ASSUME_TAC THENL
       [UNDISCH_TAC `(om0:real^(3,1)finite_sum->bool) SUBSET
                     {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `w:real^(3,1)finite_sum`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `fstcart(y:real^(3,1)finite_sum) IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(om0:real^(3,1)finite_sum->bool) SUBSET
                   {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^(3,1)finite_sum`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c0:(B->bool)#(B->real^3)`; `fstcart(y:real^(3,1)finite_sum)`] P2BX_CHART_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `x = chart_inv (c0:(B->bool)#(B->real^3)) (fstcart(y:real^(3,1)finite_sum))` THEN
    SUBGOAL_THEN `(x:B) IN FST((c:num->(B->bool)#(B->real^3)) j) /\
                  SND(c j) x IN (Ks:num->real^3->bool) j` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(Ks:num->real^3->bool) j`)) (concl th) &&
        can (find_term ((=) `(rho:num->B->real) j`)) (concl th))) THEN
      UNDISCH_TAC `~(p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y = &0)` THEN
      ASM_REWRITE_TAC[p2bw_cfun];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(c:num->(B->bool)#(B->real^3)) j`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_trans")) (concl th))) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `pastecart (SND((c:num->(B->bool)#(B->real^3)) j) x) (sndcart(y:real^(3,1)finite_sum))` THEN
    SUBGOAL_THEN `chart_trans ((c:num->(B->bool)#(B->real^3)) j) c0 (SND(c j) x) =
                  fstcart(y:real^(3,1)finite_sum)` ASSUME_TAC THENL
     [REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(Ks:num->real^3->bool) j PCROSS interval[lift a,lift b] SUBSET
                   (om:num->real^(3,1)finite_sum->bool) j` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[];
      EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[IN_INTER]];
    (* the target integrand is absolutely integrable *)
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\y. lift(p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y *
                         ((p2bw_cfun c0 (p2bx_mfun c0 psi) y *
                           (wan_tder (p2bw_cfun c0 (p2bx_uf (linf:real->B->real))) y +
                            p2bw_cscal atlas' c0 (&1) (g':real->B->real^3^3) y *
                            p2bw_cfun c0 (p2bx_uf linf) y)) *
                          sqrt(det(p2bw_cmet atlas' c0 (&1) g' y)) +
                          p2bw_bil (\y. sqrt(det(p2bw_cmet atlas' c0 (&1) g' y)) %%
                                        matrix_inv(p2bw_cmet atlas' c0 (&1) g' y))
                                   (p2bw_cfun c0 (p2bx_uf linf)) (p2bw_cfun c0 (p2bx_mfun c0 psi)) y))` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BX_ABSINT_SUPPORT THEN EXISTS_TAC `kp:real^(3,1)finite_sum->bool` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC P2BW_LEBM_CONT THEN MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN
            ASM_REWRITE_TAC[ETA_AX];
            MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
             [REWRITE_TAC[wan_tder] THEN MATCH_MP_TAC P2BW_LEBM_LIPDER THEN
              ASM_REWRITE_TAC[ETA_AX];
              MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THEN MATCH_MP_TAC P2BW_LEBM_CONT THENL
               [ASM_REWRITE_TAC[];
                MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX]]]];
          MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_SIMP_TAC[ETA_AX]];
      X_GEN_TAC `y:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `r * (s * q) * d + r * b = &0 ==> r * ((s * q) * d + b) = &0`) THEN
      MATCH_MP_TAC P2BX_WFORM_ZERO THEN
      EXISTS_TAC `(om0:real^(3,1)finite_sum->bool) DIFF kp` THEN
      ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF] THEN
      X_GEN_TAC `w:real^(3,1)finite_sum` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(w:real^(3,1)finite_sum) IN
                    {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` ASSUME_TAC THENL
       [UNDISCH_TAC `(om0:real^(3,1)finite_sum->bool) SUBSET
                     {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `w:real^(3,1)finite_sum`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[]]]);;

(* The weak integrand vanishes where the test vanishes nearby; it is       *)
(* locally essentially bounded for Lipschitz tests.                          *)

let P2BX_WINT_ZERO = prove
 (`!atlas' g' (c:(B->bool)#(B->real^3)) uu psi O z.
     open O /\ z IN O /\ (!w. w IN O ==> psi w = &0)
     ==> p2bx_wint atlas' g' c uu psi z = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx_wint] THEN
  SUBGOAL_THEN `(psi:real^(3,1)finite_sum->real) z = &0` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bw_bil (\z. sqrt(det(p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) z)) %%
                  matrix_inv(p2bw_cmet atlas' c (&1) g' z))
             (p2bw_cfun c (uu:real->B->real)) psi z = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC P2BX_BIL_ZERO_RIGHT THEN
    MP_TAC(ISPECL [`psi:real^(3,1)finite_sum->real`; `O:real^(3,1)finite_sum->bool`;
                   `z:real^(3,1)finite_sum`] P2BX_XDER_ZERO_OPEN) THEN
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC]);;

let P2BX_WINT_LEBM = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om psi.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om /\ wan_loclip om psi
     ==> p2bw_lebm om (\z. p2bx_wint atlas' g' c (p2bx_uf linf) psi z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_UF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`;
                 `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] P2BX_BOX_LIMIT_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_BOX_A_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(om:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bg_cbox]; ALL_TAC] THEN
  REWRITE_TAC[p2bx_wint; wan_tder] THEN MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BW_LEBM_CONT THEN MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BW_LEBM_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2BW_LEBM_LIPDER THEN ASM_REWRITE_TAC[ETA_AX];
          MATCH_MP_TAC P2BW_LEBM_MUL THEN CONJ_TAC THEN MATCH_MP_TAC P2BW_LEBM_CONT THENL
           [ASM_REWRITE_TAC[];
            MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX]]];
        MATCH_MP_TAC P2BW_LEBM_CONT THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2BW_LEBM_BIL THEN ASM_SIMP_TAC[ETA_AX]]);;

(* P3: the global functional at (the function on the limit of) a test in a *)
(* chart box is the weak form of that test in the box.                       *)

let P2BX_GFUN_CHART = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf K a b k c om Ks rho c0 om0 psi kp.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bx_pdata atlas' K a b k c om Ks rho /\
     c0 IN atlas' /\ p2bg_cbox c0 om0 /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     compact kp /\ kp SUBSET om0 /\ (!z. ~(z IN kp) ==> psi z = &0) /\
     (!z. z IN kp ==> chart_inv c0 (fstcart z) IN K /\
                      a <= drop(sndcart z) /\ drop(sndcart z) <= b)
     ==> sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                               (p2bw_cfun (c j) (p2bx_mfun c0 psi)) z)))) =
         drop(integral om0 (\z. lift(p2bx_wint atlas' g' c0 (p2bx_uf linf) psi z)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `open(om0:real^(3,1)finite_sum->bool) /\
                om0 SUBSET {z | fstcart z IN IMAGE (SND(c0:(B->bool)#(B->real^3))) (FST c0)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c0:(B->bool)#(B->real^3)) om0` THEN REWRITE_TAC[p2bg_cbox] THEN
    MP_TAC(ISPEC `om0:real^(3,1)finite_sum->bool` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_loclip om0 (psi:real^(3,1)finite_sum->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. ~(y IN kp)
                    ==> p2bx_wint atlas' (g':real->B->real^3^3) (c0:(B->bool)#(B->real^3))
                          (p2bx_uf (linf:real->B->real)) psi y = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX_WINT_ZERO THEN
    EXISTS_TAC `(:real^(3,1)finite_sum) DIFF kp` THEN
    ASM_SIMP_TAC[IN_DIFF; IN_UNIV; GSYM closed; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c0:(B->bool)#(B->real^3)`; `om0:real^(3,1)finite_sum->bool`;
                 `psi:real^(3,1)finite_sum->real`] P2BX_WINT_LEBM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. j IN 1..k
        ==> (\y. lift(p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y *
                      p2bx_wint atlas' (g':real->B->real^3^3) c0 (p2bx_uf (linf:real->B->real)) psi y))
            absolutely_integrable_on om0`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                   `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                   `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                   `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `(rho:num->B->real) j`; `c0:(B->bool)#(B->real^3)`;
                   `om0:real^(3,1)finite_sum->bool`] P2BX_MSMOOTH_CFUN_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BX_ABSINT_SUPPORT THEN EXISTS_TAC `kp:real^(3,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum(1..k) (\j. drop(integral om0
      (\y. lift(p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y *
                p2bx_wint atlas' (g':real->B->real^3^3) c0 (p2bx_uf (linf:real->B->real)) psi y))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC P2BX_MFUN_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                          `sub:num->num`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                          `Ks:num->real^3->bool`; `kp:real^(3,1)finite_sum->bool`] THEN
    ASM_SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[P2BX_SUM_DROP] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`\j y. lift(p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y *
                p2bx_wint atlas' (g':real->B->real^3^3) c0 (p2bx_uf (linf:real->B->real)) psi y)`;
    `om0:real^(3,1)finite_sum->bool`; `1..k`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^(3,1)finite_sum` THEN DISCH_TAC THEN
  REWRITE_TAC[P2BX_VSUM_LIFT; LIFT_EQ; SUM_RMUL] THEN
  ASM_CASES_TAC `(y:real^(3,1)finite_sum) IN kp` THENL
   [ALL_TAC; ASM_SIMP_TAC[REAL_MUL_RZERO]] THEN
  SUBGOAL_THEN `sum(1..k) (\j. p2bw_cfun (c0:(B->bool)#(B->real^3)) (\t:real. (rho:num->B->real) j) y) = &1`
  (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
  REWRITE_TAC[p2bw_cfun] THEN
  UNDISCH_TAC `p2bx_pdata atlas' K a b k (c:num->(B->bool)#(B->real^3)) om Ks (rho:num->B->real)` THEN
  REWRITE_TAC[p2bx_pdata] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_SIMP_TAC[]);;

