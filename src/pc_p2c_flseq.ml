(* ========================================================================= *)
(* Unit pc_p2c_flseq (Part 2C, flowlim route): the setting p2ca_set of the   *)
(* abstract assembly pc_p2c_flasm for the sequence of MT Prop 5.14,          *)
(* P n s = Q n (phi n)^* g_n(t n + s / Q n) (p2cv_P of pc_p2c_flloc): the    *)
(* time-0 jets in charts, uniformly in n (pc_p2c_rmdjb and finite            *)
(* absorption), Shi's bounds on the derivatives of the curvature on a base  *)
(* region manifold, and the hypotheses p2ca_seqhyp of the local limit        *)
(* theorem on every chart image of the exhaustion and every compact          *)
(* interval of J around 0.                                                   *)
(* ========================================================================= *)

needs "src/pc_p2c_flloc.ml";;
needs "src/pc_p2c_rmdjb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The time-0 closeness read in a fixed chart (chart                         *)
(* independence of lck_dist2), finitely many exceptional indices, and the    *)
(* time-0 jets of the chart representatives, uniformly along the sequence.  *)
(* ------------------------------------------------------------------------- *)

let P2CQ_LCK0_CHART = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m c K.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ c IN atlas /\ compact K /\
     K SUBSET IMAGE (SND c) (FST c INTER W m)
     ==> !k e. &0 < e
               ==> ?N. !n z. N <= n /\ z IN K
                             ==> lck_dist2 k (metric_local atlas c g0)
                                   (metric_local atlas c (p2cv_P V t Q atlas phi n (&0))) z
                                 < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `e:real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL p2cv_hv P2CV_TIME0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top closure_of (W:num->B->bool) m`; `k:num`; `e:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  EXISTS_TAC `N1 + m:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y:B. y IN FST(c:(B->bool)#(B->real^3)) /\ y IN (W:num->B->bool) m /\
                      SND c y = z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:real^3->bool) SUBSET IMAGE (SND(c:(B->bool)#(B->real^3)))
                                              (FST c INTER (W:num->B->bool) m)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W n /\ W m SUBSET top closure_of W m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cv_hv @ [`n:num`]) P2CV_SLICE0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
  SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) n)
                         ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:B) IN (W:num->B->bool) n /\
    metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y) INTER W n))
                 (metric_local atlas (chart_at atlas y) (g0:B->real^3^3)) /\
    metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y) INTER W n))
                 (metric_local atlas (chart_at atlas y)
                    (p2cv_P V t Q atlas (phi:num->B->A) n (&0)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)))
                        (FST(chart_at atlas y))` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        CONJ_TAC THENL
         [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
          MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
          ASM_REWRITE_TAC[];
          SET_TAC[]]];
      REWRITE_TAC[P2CV_P_PB] THEN
      MP_TAC(ISPECL [`(V:num->p2cvv3) n`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) n`;
                     `(phi:num->B->A) n`; `(t:num->real) n`; `(Q:num->real) n`; `&0`;
                     `psi:A->B`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`]
                    P2CV_P_FIELD) THEN
      ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `p2cv_P V t Q atlas (phi:num->B->A) n (&0)`;
                 `c:(B->bool)#(B->real^3)`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`;
                 `(W:num->B->bool) n`; `y:B`; `k:num`] P2CA_LCK_CHART_INDEP_C) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "N1" (MP_TAC o SPECL [`n:num`; `y:B`]) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; SIMP_TAC[]]);;

(* Finitely many exceptional indices. *)

let P2CQ_FINITE_ABSORB = prove
 (`!(P:num->A->bool) (f:num->A->real) M.
     (!n. n < M ==> ?B. !x. P n x ==> f n x <= B) /\
     (?B. !n x. M <= n /\ P n x ==> f n x <= B)
     ==> ?B. !n x. P n x ==> f n x <= B`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LE_0] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fin") (X_CHOOSE_TAC `B1:real`)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "fin" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "fin" (MP_TAC o SPEC `M:num`) THEN REWRITE_TAC[ARITH_RULE `M < SUC M`] THEN
  DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN EXISTS_TAC `max B0 B1` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n:num = M` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b0 ==> a <= max b0 b1`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a <= b1 ==> a <= max b0 b1`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The time-0 jets of the chart representatives along the sequence. *)

let P2CQ_JETS0 = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m c K N.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ c IN atlas /\ compact K /\
     K SUBSET IMAGE (SND c) (FST c INTER W m) /\ m <= N
     ==> !k p q. 1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
                 ==> ?B. !n l y. l IN pde_index_lists k (:3) /\ y IN K
                                 ==> abs(drop(iterated_partial l
                                          (\z. lift(metric_local atlas c
                                                 (p2cv_P V t Q atlas phi (N + n) (&0)) z$p$q))
                                          y)) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. m <= n ==> metric_field S (metric_local atlas (c:(B->bool)#(B->real^3))
                                     (p2cv_P V t Q atlas (phi:num->B->A) n (&0)))`
  (LABEL_TAC "MFn") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL (p2cv_hv @ [`n:num`]) P2CV_SLICE0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
    SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) n)
                           ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2CV_HYP_ONE THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) n)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[P2CV_P_PB] THEN
      MP_TAC(ISPECL [`(V:num->p2cvv3) n`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) n`;
                     `(phi:num->B->A) n`; `(t:num->real) n`; `(Q:num->real) n`; `&0`;
                     `psi:A->B`; `c:(B->bool)#(B->real^3)`] P2CV_P_FIELD) THEN
      ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID];
      EXPAND_TAC "S" THEN
      SUBGOAL_THEN `(W:num->B->bool) m SUBSET W n` MP_TAC THENL
       [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `c:(B->bool)#(B->real^3)`; `K:real^3->bool`] P2CQ_LCK0_CHART) THEN
  ANTS_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `&1`]) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  ABBREV_TAC `M1 = N1 + N:num` THEN
  ABBREV_TAC `Js = {&n | (M1:num) <= n}` THEN
  ABBREV_TAC `GG = \s:real. metric_local atlas (c:(B->bool)#(B->real^3))
                              (p2cv_P V t Q atlas (phi:num->B->A) (@n. &n = s) (&0))` THEN
  SUBGOAL_THEN `!n. (GG:real->real^3->real^3^3) (&n) =
                    metric_local atlas (c:(B->bool)#(B->real^3))
                      (p2cv_P V t Q atlas (phi:num->B->A) n (&0))` (LABEL_TAC "GGn") THENL
   [GEN_TAC THEN EXPAND_TAC "GG" THEN REWRITE_TAC[REAL_OF_NUM_EQ; SELECT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN Js ==> ?n. (M1:num) <= n /\ s = &n` (LABEL_TAC "JS") THENL
   [EXPAND_TAC "Js" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Js:real->bool`; `S:real^3->bool`; `K:real^3->bool`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)`;
                 `GG:real->real^3->real^3^3`; `k:num`; `&1`] P2CJ_JB_FROM_LCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `s:real` THENL
     [DISCH_TAC THEN USE_THEN "JS" (MP_TAC o C MP (ASSUME `(s:real) IN Js`) o SPEC `s:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "MFn" MATCH_MP_TAC THEN
      MAP_EVERY EXPAND_TAC ["M1"] THEN ASM_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      USE_THEN "JS" (MP_TAC o C MP (ASSUME `(s:real) IN Js`) o SPEC `s:real`) THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "N1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["M1"] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:num`; `q:num`]) THEN ASM_REWRITE_TAC[rfa_jb] THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:real` o CONJUNCT2) THEN
  MP_TAC(ISPECL
   [`\n:num (ly:(num)list#real^3). FST ly IN pde_index_lists k (:3) /\ SND ly IN K`;
    `\n:num (ly:(num)list#real^3).
       abs(drop(iterated_partial (FST ly)
         (\z. lift(metric_local atlas (c:(B->bool)#(B->real^3))
                     (p2cv_P V t Q atlas (phi:num->B->A) (N + n:num) (&0)) z$p$q)) (SND ly)))`;
    `N1:num`] P2CQ_FINITE_ABSORB) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`S:real^3->bool`; `K:real^3->bool`;
                     `\z. lift(metric_local atlas (c:(B->bool)#(B->real^3))
                                 (p2cv_P V t Q atlas (phi:num->B->A) (N + n) (&0)) z$p$q)`;
                     `k:num`] P2CI_JETN_BOUNDED) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "MFn" (MP_TAC o SPEC `N + n:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL [`S:real^3->bool`;
                       `metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_P V t Q atlas (phi:num->B->A) (N + n) (&0))`]
                      LRG_SMOOTH_VECTORIZE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[ABS_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `B1:real` THEN MAP_EVERY X_GEN_TAC [`n:num`; `l:(num)list`; `y:real^3`] THEN
      STRIP_TAC THEN
      USE_THEN "GGn" (MP_TAC o SPEC `N + n:num`) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Js" THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `N + n:num` THEN
      REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["M1"] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Region manifolds (subtopology top Wr, restrict_atlas atlas               *)
(* Wr) with restricted metrics, built from chart representatives over the   *)
(* chart images of Wr only: chart representatives, Riemannian metrics,       *)
(* Ricci flows, flows up to and flows from a time, and the derivatives of   *)
(* the curvature read in an ambient chart.                                   *)
(* ------------------------------------------------------------------------- *)

let P2CQ_REGION_REP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr (g:A->real^N^N) c z.
     smooth_manifold_atlas top atlas /\ open_in top Wr /\ c IN atlas /\
     z IN IMAGE (SND c) (FST c INTER Wr)
     ==> metric_local (restrict_atlas atlas Wr) (FST c INTER Wr,SND c)
                      (restrict_metric atlas Wr g) z =
         metric_local atlas c g z`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC
      ASSUME_TAC))))) THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

let P2CQ_REGION_RIEM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ open_in top Wr /\
     (!c. c IN atlas
          ==> metric_field (IMAGE (SND c) (FST c INTER Wr)) (metric_local atlas c g))
     ==> riemannian_metric (restrict_atlas atlas Wr) (restrict_metric atlas Wr g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Wr:A->bool`;
                   `g:A->real^N^N`; `(U:A->bool,phi:A->real^N)`; `z:real^N`]
                  P2CQ_REGION_REP) THEN
    ASM_REWRITE_TAC[FST; SND]]);;

let P2CQ_REGION_RF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr (g:real->A->real^N^N) u v.
     smooth_manifold_atlas top atlas /\ open_in top Wr /\ u < v /\
     (!c. c IN atlas
          ==> lricci_flow (IMAGE (SND c) (FST c INTER Wr)) u v
                          (\s. metric_local atlas c (g s)))
     ==> ricci_flow_on (subtopology top Wr,restrict_atlas atlas Wr) u v
                       (\s. restrict_metric atlas Wr (g s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CA_RICCI_FLOW_ON_CHARTS THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC `\s. metric_local atlas (U:A->bool,phi:A->real^N) ((g:real->A->real^N^N) s)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Wr:A->bool`;
                   `(g:real->A->real^N^N) t`; `(U:A->bool,phi:A->real^N)`; `z:real^N`]
                  P2CQ_REGION_REP) THEN
    ASM_REWRITE_TAC[FST; SND]]);;

(* Flows up to a time, from chart representatives. *)

let P2CQ_REGION_UPTO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) Wr (g:real->A->real^3^3) u v.
     smooth_manifold_atlas top atlas /\ open_in top Wr /\ u < v /\
     (!c. c IN atlas
          ==> lricci_flow (IMAGE (SND c) (FST c INTER Wr)) u v
                          (\s. metric_local atlas c (g s)) /\
              metric_field (IMAGE (SND c) (FST c INTER Wr)) (metric_local atlas c (g v)) /\
              ?e Fx. &0 < e /\
                     smooth_map_on (interval(lift u,lift(v + e)) PCROSS
                                    IMAGE (SND c) (FST c INTER Wr)) Fx /\
                     !t y. u < t /\ t <= v /\ y IN IMAGE (SND c) (FST c INTER Wr)
                           ==> Fx(pastecart (lift t) y) =
                               (vectorize:real^3^3->real^(3,3)finite_prod)
                                 (metric_local atlas c (g t) y))
     ==> rfs_flow_upto (subtopology top Wr,restrict_atlas atlas Wr) u v
                       (\s. restrict_metric atlas Wr (g s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[rfs_flow_upto] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CQ_REGION_RF THEN ASM_SIMP_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC P2CQ_REGION_RIEM THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o
    C MP (ASSUME `(U:A->bool,phi:A->real^3) IN atlas`) o SPEC `(U:A->bool,phi:A->real^3)`) THEN
  REWRITE_TAC[FST; SND] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^3`] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Wr:A->bool`;
                 `(g:real->A->real^3^3) t`; `(U:A->bool,phi:A->real^3)`; `z:real^3`]
                P2CQ_REGION_REP) THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* Flows from a time, from chart representatives. *)

let P2CQ_REGION_FROM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr (g:real->A->real^N^N) u v.
     smooth_manifold_atlas top atlas /\ open_in top Wr /\ u < v /\
     (!c. c IN atlas
          ==> lricci_flow (IMAGE (SND c) (FST c INTER Wr)) u v
                          (\s. metric_local atlas c (g s)) /\
              metric_field (IMAGE (SND c) (FST c INTER Wr)) (metric_local atlas c (g u)) /\
              ?e F. &0 < e /\
                    smooth_map_on (interval(lift(u - e),lift v) PCROSS
                                   IMAGE (SND c) (FST c INTER Wr)) F /\
                    !t y. u <= t /\ t < v /\ y IN IMAGE (SND c) (FST c INTER Wr)
                          ==> F(pastecart (lift t) y) =
                              (vectorize:real^N^N->real^(N,N)finite_prod)
                                (metric_local atlas c (g t) y))
     ==> ricci_flow_from (subtopology top Wr,restrict_atlas atlas Wr) u v
                         (\s. restrict_metric atlas Wr (g s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[ricci_flow_from] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CQ_REGION_RF THEN ASM_SIMP_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC P2CQ_REGION_RIEM THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o
    C MP (ASSUME `(U:A->bool,phi:A->real^N) IN atlas`) o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  REWRITE_TAC[FST; SND] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Wr:A->bool`;
                 `(g:real->A->real^N^N) t`; `(U:A->bool,phi:A->real^N)`; `z:real^N`]
                P2CQ_REGION_REP) THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* Derivatives of the curvature of a region metric, read in an ambient chart. *)

let P2CQ_REGION_RMD2 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr (g:A->real^N^N) c x l.
     smooth_manifold_atlas top atlas /\ open_in top Wr /\
     riemannian_metric (restrict_atlas atlas Wr) (restrict_metric atlas Wr g) /\
     c IN atlas /\ x IN FST c /\ x IN Wr
     ==> rfa_rmd2 l (restrict_atlas atlas Wr) (restrict_metric atlas Wr g) x =
         lrm_deriv_norm2 l (metric_local atlas c g) (SND c x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `subtopology top (Wr:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Wr`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) Wr (g:A->real^N^N)`;
                 `(FST(c:(A->bool)#(A->real^N)) INTER Wr,SND c)`; `x:A`] RFA_RMD2_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_INTER] THEN
    REWRITE_TAC[restrict_atlas; IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`] THEN
    ASM_REWRITE_TAC[PAIR];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SND] THEN MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER Wr)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2CQ_REGION_REP THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A single flow p2cv_one on its base region manifold                       *)
(* (subtopology top Wb, restrict_atlas atlas Wb) with the restricted        *)
(* metrics of p2cv_pb: Riemannian metrics, flows up to a time (from the     *)
(* local flows and the top extension), flows from 0 at a bottom without     *)
(* margin (the bottom extension), and the curvature bound from the bound on *)
(* the view (pullback and rescaling of |Rm|^2, RFA_R1_RMD0).                 *)
(* ------------------------------------------------------------------------- *)

(* A copy of P3H_RM_NORM_LE_RMD2 (pc_p3_c17curv), whose closure is large. *)

let P2CQ_RM_NORM_LE_RMD2 = prove
 (`!top atlas (g:A->real^3^3) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> mfd_rm_norm atlas g x <= sqrt(rfa_rmd2 0 atlas g x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `2 <= 3`] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_RMD2 THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* Riemannian metrics on the base region manifold. *)

let P2CQ_PB_RIEM = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b s.
     p2cv_one V (top,atlas) Wb f t0 q /\ a' <= &0 /\ &0 <= b /\
     rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
     (a' < s \/ s = &0) /\ s <= b
     ==> riemannian_metric (restrict_atlas atlas Wb)
                           (restrict_metric atlas Wb (p2cv_pb V t0 q atlas f s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MATCH_MP_TAC P2CQ_REGION_RIEM THEN EXISTS_TAC `top:B topology` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CV_P_FIELD_AT THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b:real`] THEN ASM_REWRITE_TAC[]);;

(* Flows up to a time on the base region manifold. *)

let P2CQ_PB_UPTO = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b' u s.
     p2cv_one V (top,atlas) Wb f t0 q /\ a' <= &0 /\ &0 <= b' /\ a' <= u /\ u < s /\
     s <= b' /\ rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b' / q)
     ==> rfs_flow_upto (subtopology top Wb,restrict_atlas atlas Wb) u s
                       (\r. restrict_metric atlas Wb (p2cv_pb V t0 q atlas f r))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MATCH_MP_TAC P2CQ_REGION_UPTO THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b':real`; `c:(B->bool)#(B->real^3)`]) P2CV_LFLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_LRICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2CV_P_FIELD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s < b'` THENL
   [EXISTS_TAC `b' - s` THEN
    EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                      (metric_local atlas c
                         (p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) (drop(fstcart z)))
                         (sndcart z))` THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a',lift b') PCROSS
                IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `lricci_flow (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool)))
                     a' b' (\s. metric_local atlas c
                                  (p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) s))` THEN
      REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = b'` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a':real`; `b':real`;
                 `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
                 `\s y. (vectorize:real^3^3->real^(3,3)finite_prod)
                          (metric_local atlas c (p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) s) y)`]
                P2CV_UPTO_REVERSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b':real`; `c:(B->bool)#(B->real^3)`])
                  P2CV_TOP_EXT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `F0:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN EXISTS_TAC `F0:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a',lift(b' + e)) PCROSS
                IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Flows from 0 on the base region manifold, at a bottom without margin. *)

let P2CQ_PB_FROM = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q b' v.
     p2cv_one V (top,atlas) Wb f t0 q /\ &0 < v /\ v <= b' /\
     rfs_persists V (IMAGE f Wb) (t0 + &0 / q) (t0 + b' / q)
     ==> ricci_flow_from (subtopology top Wb,restrict_atlas atlas Wb) (&0) v
                         (\r. restrict_metric atlas Wb (p2cv_pb V t0 q atlas f r))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MATCH_MP_TAC P2CQ_REGION_FROM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cv_ov @ [`&0`; `b':real`; `c:(B->bool)#(B->real^3)`]) P2CV_LFLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CA_LRICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC P2CV_P_FIELD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cv_ov @ [`b':real`; `c:(B->bool)#(B->real^3)`]) P2CV_BOT_EXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[pde_upto]] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `F0:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real` THEN EXISTS_TAC `F0:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(&0 - e),lift b') PCROSS
                IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* The curvature bound on the base region manifold. *)

let P2CQ_PB_CURV = prove
 (`?C0. &0 <= C0 /\
        !(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q a' b s CM x.
          p2cv_one V (top,atlas) Wb f t0 q /\ a' <= &0 /\ &0 <= b /\ &0 <= CM /\
          rfs_persists V (IMAGE f Wb) (t0 + a' / q) (t0 + b / q) /\
          (a' < s \/ s = &0) /\ s <= b /\ x IN Wb /\
          p3_vrm V (t0 + s / q) (f x) <= CM * q
          ==> mfd_rm_norm (restrict_atlas atlas Wb)
                          (restrict_metric atlas Wb (p2cv_pb V t0 q atlas f s)) x
              <= sqrt C0 * CM`,
  X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`; `:3`,`:N`] RFA_R1_RMD0) THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  MP_TAC(ISPECL [`t0:real`; `q:real`] P2CV_TT_IFF) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas atlas (Wb:B->bool))
      (restrict_metric atlas Wb (p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CQ_PB_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)` THEN
  MP_TAC(ISPECL (p2cv_ov @ [`a':real`; `b:real`; `s:real`]) P2CV_PHI_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi:A->B`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop (V:p2cvv3) (t0 + s / q))
                                      (rfs_vatlas V (t0 + s / q))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `a' < s` THENL
     [MP_TAC(ISPECL [`V:p2cvv3`; `IMAGE (f:B->A) Wb`; `t0 + a' / q`; `t0 + b / q`;
                     `t0 + s / q`] P2CV_PERSISTS_AT) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (rfs_vatlas (V:p2cvv3) (t0 + s / q))
                                  (rfs_vmetric V (t0 + s / q))` ASSUME_TAC THENL
   [MP_TAC(SPEC `V:p2cvv3` P2CV_RV_SVS) THEN ASM_REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN
    DISCH_THEN(MP_TAC o SPEC `t0 + s / q`) THEN
    MATCH_MP_TAC(TAUT `p ==> (q /\ (p ==> r /\ s)) ==> s`) THEN
    UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (Wb:B->bool) (rfs_vtop (V:p2cvv3) (t0 + s / q))
                   (rfs_vatlas V (t0 + s / q)) (IMAGE (f:B->A) Wb) f (psi:A->B)` THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    UNDISCH_TAC `(x:B) IN Wb` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:B->A) x IN topspace(rfs_vtop (V:p2cvv3) (t0 + s / q))` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) (Wb:B->bool) (rfs_vtop (V:p2cvv3) (t0 + s / q))
                   (rfs_vatlas V (t0 + s / q)) (IMAGE (f:B->A) Wb) f (psi:A->B)` THEN
    REWRITE_TAC[mfd_diffeo] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
    UNDISCH_TAC `(x:B) IN Wb` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_rmd2 0 (restrict_atlas atlas (Wb:B->bool))
      (restrict_metric atlas Wb (p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) s)) x <=
    C0 * CM pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `Wb:B->bool`;
                   `p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) s`; `c:(B->bool)#(B->real^3)`;
                   `x:B`; `0`] P2CQ_REGION_RMD2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `SND(c:(B->bool)#(B->real^3)) (x:B) IN IMAGE (SND c) (FST c INTER (Wb:B->bool))`
    ASSUME_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param (rfs_vtop (V:p2cvv3) (t0 + s / q)) (rfs_vatlas V (t0 + s / q))
                (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool)))
                ((f:B->A) o chart_inv c)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2CV_CHART_PARAM THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `IMAGE (f:B->A) Wb`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lrm_deriv_norm2 0
                  (\z. q %% rfs_pullback (rfs_vatlas (V:p2cvv3) (t0 + s / q))
                                        ((f:B->A) o chart_inv (c:(B->bool)#(B->real^3)))
                                        (rfs_vmetric V (t0 + s / q)) z)
                  (SND c (x:B))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN
      EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC P2CV_P_CHART THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `Wb:B->bool`; `psi:A->B`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
                   `rfs_pullback (rfs_vatlas (V:p2cvv3) (t0 + s / q))
                                 ((f:B->A) o chart_inv (c:(B->bool)#(B->real^3)))
                                 (rfs_vmetric V (t0 + s / q))`;
                   `q:real`; `0`; `SND(c:(B->bool)#(B->real^3)) (x:B)`]
                  RFA_LRM_DERIV_NORM2_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `rfs_vtop (V:p2cvv3) (t0 + s / q)` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`0`; `rfs_vtop (V:p2cvv3) (t0 + s / q)`; `rfs_vatlas (V:p2cvv3) (t0 + s / q)`;
                   `rfs_vmetric (V:p2cvv3) (t0 + s / q)`;
                   `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (Wb:B->bool))`;
                   `(f:B->A) o chart_inv (c:(B->bool)#(B->real^3))`;
                   `SND(c:(B->bool)#(B->real^3)) (x:B)`] P2AP_PULLBACK_RMD_GEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `((f:B->A) o chart_inv (c:(B->bool)#(B->real^3))) (SND c x) = f x`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`rfs_vtop (V:p2cvv3) (t0 + s / q)`;
                                  `rfs_vatlas (V:p2cvv3) (t0 + s / q)`;
                                  `rfs_vmetric (V:p2cvv3) (t0 + s / q)`; `(f:B->A) x`;
                                  `CM * q:real`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfa_rmd2" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p3_vrm (V:p2cvv3) (t0 + s / q) ((f:B->A) x) <= CM * q` THEN
      REWRITE_TAC[p3_vrm];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(q pow (0 + 2)) * (C0 * (CM * q) pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[ADD_CLAUSES; REAL_POW_MUL] THEN
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(rfa_rmd2 0 (restrict_atlas atlas (Wb:B->bool))
                     (restrict_metric atlas Wb (p2cv_pb (V:p2cvv3) t0 q atlas (f:B->A) s)) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CQ_RM_NORM_LE_RMD2 THEN EXISTS_TAC `subtopology top (Wb:B->bool)` THEN
    ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; TOPSPACE_SUBTOPOLOGY; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(C0 * CM pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Balls.  A uniform radius for the balls around a compact set               *)
(* inside an open set; balls of a region manifold that stay in a smaller    *)
(* open set R, from balls of a comparison metric g0 and a quadratic-form    *)
(* comparison on R (RFA_BALL_INCLUSION); compact closures of such balls.    *)
(* ------------------------------------------------------------------------- *)

let P2CQ_FINITE_POS_MIN = prove
 (`!(f:A->real) s.
     FINITE s /\ (!x. x IN s ==> &0 < f x) ==> ?d. &0 < d /\ !x. x IN s ==> d <= f x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  EXISTS_TAC `inf(IMAGE (f:A->real) s)` THEN
  MP_TAC(ISPEC `IMAGE (f:A->real) s` INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let P2CQ_UNIF_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) K U.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ open_in top U /\ K SUBSET U
     ==> ?d. &0 < d /\ !x. x IN K ==> mfd_ball (top,atlas) g x d SUBSET U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN K ==> ?r. &0 < r /\ mfd_ball (top,atlas) (g:A->real^N^N) x (&2 * r) SUBSET U`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `U:A->bool`; `x:A`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    SUBGOAL_THEN `&2 * r / &2 = r` (fun th -> ASM_REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:A->real` (LABEL_TAC "rr")) THEN
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\x:A. mfd_ball (top,atlas) (g:A->real^N^N) x (rr x)) K` o
             CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `VV:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:A. mfd_ball (top,atlas) (g:A->real^N^N) x (rr x)`; `K:A->bool`;
                 `VV:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPECL [`rr:A->real`; `F0:A->bool`] P2CQ_FINITE_POS_MIN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:A. x IN F0 /\ y IN mfd_ball (top,atlas) (g:A->real^N^N) x (rr x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET
                 UNIONS (IMAGE (\x:A. mfd_ball (top,atlas) (g:A->real^N^N) x (rr x)) F0)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x (&2 * rr x)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^N^N) x (rr x)` THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x y + mfd_dist (top,atlas) g y z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a < r /\ b < d /\ d <= r ==> a + b < &2 * r`) THEN
    ASM_SIMP_TAC[]]);;

(* Balls of a region manifold that stay in a smaller open set. *)

let P2CQ_REGION_BALL_IN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr R (g0:A->real^N^N) (G:A->real^N^N) x d lam.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     open_in top Wr /\ open_in top R /\ R SUBSET Wr /\ x IN Wr /\ &0 < d /\ &0 < lam /\
     riemannian_metric (restrict_atlas atlas Wr) G /\
     mfd_ball (top,atlas) g0 x d SUBSET R /\
     (!z v. z IN R
            ==> v dot (restrict_metric atlas Wr g0 z ** v) <= lam pow 2 * (v dot (G z ** v)))
     ==> mfd_ball (subtopology top Wr,restrict_atlas atlas Wr) G x (d / lam) SUBSET R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN R` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. (x:A) IN s /\ s SUBSET R ==> x IN R`) THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g0:A->real^N^N) x d` THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology top (Wr:A->bool)) R` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `R:A->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (Wr:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Wr`;
                 `G:A->real^N^N`; `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) Wr g0`;
                 `R:A->bool`; `x:A`; `d:real`; `lam:real`] RFA_BALL_INCLUSION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Wr:A->bool`;
                   `g0:A->real^N^N`; `x:A`; `d:real`] P2AP_RESTRICT_BALL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_ball (top,atlas) (g0:A->real^N^N) x d SUBSET R` THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Compact closures of balls of a region manifold. *)

let P2CQ_REGION_BALL_COMPACT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Wr R (G:A->real^N^N) x r.
     open_in top Wr /\ compact_in top (top closure_of R) /\ top closure_of R SUBSET Wr /\
     mfd_ball (subtopology top Wr,restrict_atlas atlas Wr) G x r SUBSET R
     ==> compact_in (subtopology top Wr)
           (subtopology top Wr closure_of
            mfd_ball (subtopology top Wr,restrict_atlas atlas Wr) G x r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = mfd_ball (subtopology top Wr,restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) Wr)
                           (G:A->real^N^N) x r` THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(top:A topology) closure_of (Wr INTER B) SUBSET top closure_of R`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `Wr INTER (top:A topology) closure_of (Wr INTER B) =
                top closure_of (Wr INTER B)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `top closure_of (R:A->bool)` THEN
  ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]);;

(* ------------------------------------------------------------------------- *)
(* Quadratic-form comparison of the rescaled pulled back                    *)
(* metrics with g0 on the manifold and on a region manifold, and the balls  *)
(* of the region manifolds around points of W m: inside W (m + 1), with     *)
(* compact closures, for a radius independent of n and of the time.        *)
(* ------------------------------------------------------------------------- *)

(* A pointwise comparison of two metrics passes to their restrictions. *)

let P2CQ_RESTRICT_QF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g1:A->real^N^N) g2 C z.
     smooth_manifold_atlas top atlas /\ open_in top W /\ z IN W /\
     (!u. u dot (g1 z ** u) <= C * (u dot (g2 z ** u)))
     ==> !v. v dot (restrict_metric atlas W g1 z ** v) <=
             C * (v dot (restrict_metric atlas W g2 z ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `z:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[restrict_metric; SND] THEN
  SUBGOAL_THEN `(z:A) IN U INTER W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `W:A->bool`; `g1:A->real^N^N`; `z:A`]
                MFDR_METRIC_LOCAL_RESTRICT_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`; `W:A->bool`; `g2:A->real^N^N`; `z:A`]
                MFDR_METRIC_LOCAL_RESTRICT_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  GEN_TAC THEN MATCH_MP_TAC P2CV_ML_QF_MONO THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`;
                 `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* The manifold-level comparison with g0 over a working interval. *)

let P2CQ_QF_MANIFOLD = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m2 a' b' CM n s y u.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     a' <= &0 /\ &0 <= b' /\ a' < b' /\ &0 <= CM /\ m2 <= n /\
     rfs_persists (V n) (IMAGE (phi n) (W m2)) (t n + a' / Q n) (t n + b' / Q n) /\
     (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W m2)
            ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n) /\
     (!y u. y IN W m2
            ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                <= inv(&2) * (u dot (g0 y ** u))) /\
     (a' < s \/ s = &0) /\ s <= b' /\ y IN W m2
     ==> u dot (g0 y ** u) <=
         (&2 * exp(&8 * CM * (b' - a'))) * (u dot (p2cv_P V t Q atlas phi n s y ** u))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m2)
                         ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:num->p2cvv3) n`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(W:num->B->bool) m2`; `(phi:num->B->A) n`; `(t:num->real) n`;
                 `(Q:num->real) n`; `a':real`; `b':real`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)`; `CM:real`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)) y`;
                 `u:real^3`; `&0`; `s:real`] P2CV_QF_ALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] ORELSE ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  REWRITE_TAC[GSYM P2CV_P_PB] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `p2cv_P V t Q atlas (phi:num->B->A) n (&0)`; `y:B`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `p2cv_P V t Q atlas (phi:num->B->A) n s`; `y:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:B`; `u:real^3`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `inv(&2)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= exp(&8 * CM * (b' - a'))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * u dot (p2cv_P V t Q atlas (phi:num->B->A) n (&0) (y:B) ** u) <=
    &2 * (exp(&8 * CM * (b' - a')) * (u dot (p2cv_P V t Q atlas phi n s y ** u)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `abs(u dot (p2cv_P V t Q atlas (phi:num->B->A) n (&0) (y:B) ** u) -
        u dot ((g0:B->real^3^3) y ** u)) <= inv(&2) * (u dot (g0 y ** u))` THEN
  REAL_ARITH_TAC);;

(* The balls of the region manifold. *)

let P2CQ_BALLS = prove
 (`!(top:B topology) atlas (g0:B->real^3^3) (W:num->B->bool) m lam.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     (!k. open_in top (W k) /\ compact_in top (top closure_of W k) /\
          top closure_of W k SUBSET W (SUC k)) /\ &0 < lam
     ==> ?r. &0 < r /\
             !G x. riemannian_metric (restrict_atlas atlas (W(m + 2))) G /\ x IN W m /\
                   (!z v. z IN W (m + 1)
                          ==> v dot (restrict_metric atlas (W(m + 2)) g0 z ** v) <=
                              lam pow 2 * (v dot (G z ** v)))
                   ==> mfd_ball (subtopology top (W(m + 2)),restrict_atlas atlas (W(m + 2)))
                                G x r SUBSET W (m + 1) /\
                       compact_in (subtopology top (W(m + 2)))
                         (subtopology top (W(m + 2)) closure_of
                          mfd_ball (subtopology top (W(m + 2)),restrict_atlas atlas (W(m + 2)))
                                   G x r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET top closure_of W m /\
                top closure_of W m SUBSET W (m + 1) /\
                top closure_of W (m + 1) SUBSET W (m + 2) /\
                W (m + 1) SUBSET W (m + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `m + 1 = SUC m /\ m + 2 = SUC(SUC m)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (W:num->B->bool) (SUC m)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `top closure_of (W:num->B->bool) m`; `(W:num->B->bool) (m + 1)`]
                P2CQ_UNIF_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / lam` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MAP_EVERY X_GEN_TAC [`G:B->real^3^3`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:B) IN (W:num->B->bool) (m + 2) /\
                mfd_ball (top,atlas) (g0:B->real^3^3) y d SUBSET W (m + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CQ_REGION_BALL_IN THEN EXISTS_TAC `g0:B->real^3^3` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC P2CQ_REGION_BALL_COMPACT THEN
    EXISTS_TAC `(W:num->B->bool) (m + 1)` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Uniform bounds on the derivatives of the curvature at time 0              *)
(* along the sequence, on compact sets of a chart (P2CJ_RMD2_FROM_LCK on the *)
(* tail, continuity on the finitely many first members), and on W (m + 1)   *)
(* read in the region manifold of W (m + 2) (a finite cover by charts).      *)
(* ------------------------------------------------------------------------- *)

let P2CQ_CONT_BOUND = prove
 (`!(f:real^N->real) s. (\y. lift(f y)) continuous_on s /\ compact s
                        ==> ?B. !y. y IN s ==> f y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. lift((f:real^N->real) y)`; `s:real^N->bool`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[bounded; FORALL_IN_IMAGE; NORM_LIFT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS]);;

(* One order, one chart. *)

let P2CQ_INIT_CHART1 = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m2 c K N i.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ c IN atlas /\ compact K /\
     K SUBSET IMAGE (SND c) (FST c INTER W m2) /\ m2 <= N
     ==> ?C. !n z. N <= n /\ z IN K
                   ==> lrm_deriv_norm2 i
                         (metric_local atlas c (p2cv_P V t Q atlas phi n (&0))) z <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  ABBREV_TAC `S = IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m2)` THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g0:B->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. m2 <= n ==> metric_field S (metric_local atlas (c:(B->bool)#(B->real^3))
                                      (p2cv_P V t Q atlas (phi:num->B->A) n (&0)))`
  (LABEL_TAC "MFn") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "S" THEN
    MP_TAC(ISPECL (p2cv_hv @ [`n:num`]) P2CV_SLICE0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `psi:A->B`)) THEN
    SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) n)
                           ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2CV_HYP_ONE THEN
      MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) n)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[P2CV_P_PB] THEN
      MP_TAC(ISPECL [`(V:num->p2cvv3) n`; `top:B topology`;
                     `atlas:((B->bool)#(B->real^3))->bool`; `(W:num->B->bool) n`;
                     `(phi:num->B->A) n`; `(t:num->real) n`; `(Q:num->real) n`; `&0`;
                     `psi:A->B`; `c:(B->bool)#(B->real^3)`] P2CV_P_FIELD) THEN
      ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID];
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
        MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(W:num->B->bool) m2 SUBSET W n` MP_TAC THENL
         [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
          SET_TAC[]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `K:real^3->bool`;
                 `metric_local atlas (c:(B->bool)#(B->real^3)) (g0:B->real^3^3)`;
                 `i + 2`; `inv(&4)`; `i:num`] P2CJ_RMD2_FROM_LCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "C1")) THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m2:num`;
                 `c:(B->bool)#(B->real^3)`; `K:real^3->bool`] P2CQ_LCK0_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`i + 2`; `inv(&4)`]) THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  MP_TAC(ISPECL
   [`\n:num z:real^3. N <= n /\ z IN K`;
    `\n:num z:real^3. lrm_deriv_norm2 i
                        (metric_local atlas (c:(B->bool)#(B->real^3))
                           (p2cv_P V t Q atlas (phi:num->B->A) n (&0))) z`;
    `N1 + N:num`] P2CQ_FINITE_ABSORB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_CASES_TAC `N:num <= n` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\z. lrm_deriv_norm2 i
                           (metric_local atlas (c:(B->bool)#(B->real^3))
                              (p2cv_P V t Q atlas (phi:num->B->A) n (&0))) z`;
                     `K:real^3->bool`] P2CQ_CONT_BOUND) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC LRM_DERIV_NORM2_CONTINUOUS THEN USE_THEN "MFn" MATCH_MP_TAC THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      MESON_TAC[];
      EXISTS_TAC `C1:real` THEN MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
      USE_THEN "C1" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [USE_THEN "MFn" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "N1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    MESON_TAC[]]);;

(* All orders up to j, one chart. *)

let P2CQ_INIT_CHART = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m2 c K N j.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ c IN atlas /\ compact K /\
     K SUBSET IMAGE (SND c) (FST c INTER W m2) /\ m2 <= N
     ==> ?C. !n i z. N <= n /\ i <= j /\ z IN K
                     ==> lrm_deriv_norm2 i
                           (metric_local atlas c (p2cv_P V t Q atlas phi n (&0))) z <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`j:num`,`j:num`) THEN INDUCT_TAC THENL
   [MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                   `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m2:num`;
                   `c:(B->bool)#(B->real^3)`; `K:real^3->bool`; `N:num`; `0`]
                  P2CQ_INIT_CHART1) THEN
    ASM_REWRITE_TAC[LE] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `C0:real`) THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m2:num`;
                 `c:(B->bool)#(B->real^3)`; `K:real^3->bool`; `N:num`; `SUC j`]
                P2CQ_INIT_CHART1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C1:real`) THEN
  EXISTS_TAC `max C0 C1` THEN REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `a <= c1 ==> a <= max c0 c1`) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(REAL_ARITH `a <= c0 ==> a <= max c0 c1`) THEN ASM_SIMP_TAC[]]);;

(* The region metric at the base time. *)

let P2CQ_PB_RIEM0 = prove
 (`!(V:p2cvv3) (top:B topology) atlas Wb (f:B->A) t0 q.
     p2cv_one V (top,atlas) Wb f t0 q
     ==> riemannian_metric (restrict_atlas atlas Wb)
                           (restrict_metric atlas Wb (p2cv_pb V t0 q atlas f (&0)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_ONE_BASIC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `psi:A->B` o MATCH_MP P2CV_ONE_DIFFEO) THEN
  MATCH_MP_TAC P2CQ_REGION_RIEM THEN EXISTS_TAC `top:B topology` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cv_ov @ [`&0`; `psi:A->B`; `c:(B->bool)#(B->real^3)`]) P2CV_P_FIELD) THEN
  ASM_REWRITE_TAC[P2CV_DIV_LZERO; REAL_ADD_RID]);;

(* On W (m + 1), read in the region manifold of W (m + 2): a finite cover of *)
(* the compact closure of W (m + 1) by chart balls.                          *)

let P2CQ_INIT_BOUNDS = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m j N.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\ m + 2 <= N
     ==> ?K0. !n i y. N <= n /\ i <= j /\ y IN W (m + 1)
                      ==> rfa_rmd2 i (restrict_atlas atlas (W (m + 2)))
                            (restrict_metric atlas (W (m + 2))
                               (p2cv_P V t Q atlas phi n (&0))) y <= K0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `compact_in top (top closure_of (W:num->B->bool) (m + 1)) /\
                top closure_of W (m + 1) SUBSET W (m + 2) /\
                W (m + 1) SUBSET top closure_of W (m + 1) /\
                top closure_of W (m + 1) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[ARITH_RULE `m + 2 = SUC(m + 1)`];
      MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE]];
    ALL_TAC] THEN
  ABBREV_TAC `Km = top closure_of (W:num->B->bool) (m + 1)` THEN
  SUBGOAL_THEN
   `!y0:B. y0 IN Km
           ==> ?r. &0 < r /\
                   cball(SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) y0) y0,r) SUBSET
                   IMAGE (SND(chart_at atlas y0)) (FST(chart_at atlas y0) INTER
                                                  (W:num->B->bool) (m + 2))`
  MP_TAC THENL
   [X_GEN_TAC `y0:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`]
                  CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)`;
                   `(W:num->B->bool) (m + 2)`] P2CA_CHART_IMAGE_OPEN_C) THEN
    ASM_REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `rad:B->real` (LABEL_TAC "rad")) THEN
  UNDISCH_TAC `compact_in top (Km:B->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\y0:B. {y | y IN FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) y0) /\
                       SND(chart_at atlas y0) y IN
                       ball(SND(chart_at atlas y0) y0,(rad:B->real) y0)}) Km` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y0:B` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`]
                    CHART_AT) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPEC `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)` PAIR_SURJECTIVE) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`U:B->bool`; `psi:B->real^3`] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
      ASM_MESON_TAC[OPEN_BALL];
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`]
                      CHART_AT) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
        USE_THEN "rad" (MP_TAC o SPEC `y:B`) THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `VV:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\y0:B. {y | y IN FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) y0) /\
                 SND(chart_at atlas y0) y IN ball(SND(chart_at atlas y0) y0,(rad:B->real) y0)}`;
    `Km:B->bool`; `VV:(B->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN
   `!y0. y0 IN F0
         ==> ?C. !n i z. N <= n /\ i <= j /\
                         z IN cball(SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) y0) y0,
                                    (rad:B->real) y0)
                         ==> lrm_deriv_norm2 i
                               (metric_local atlas (chart_at atlas y0)
                                  (p2cv_P V t Q atlas (phi:num->B->A) n (&0))) z <= C`
  MP_TAC THENL
   [X_GEN_TAC `y0:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y0:B) IN Km` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`]
                  CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P2CQ_INIT_CHART THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `top:B topology`; `g0:B->real^3^3`;
                          `xl:B`; `W:num->B->bool`; `m + 2`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    USE_THEN "rad" (MP_TAC o SPEC `y0:B`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:B->real` (LABEL_TAC "CC")) THEN
  MP_TAC(ISPECL [`CC:B->real`; `F0:B->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `K0:real`) THEN
  EXISTS_TAC `K0:real` THEN MAP_EVERY X_GEN_TAC [`n:num`; `i:num`; `y:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?y0:B. y0 IN F0 /\ y IN FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) y0) /\
           SND(chart_at atlas y0) y IN ball(SND(chart_at atlas y0) y0,(rad:B->real) y0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `(Km:B->bool) SUBSET
      UNIONS (IMAGE (\y0:B. {y | y IN FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) y0) /\
                                 SND(chart_at atlas y0) y IN
                                 ball(SND(chart_at atlas y0) y0,(rad:B->real) y0)}) F0)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:B`) THEN ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:B) IN Km` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y0:B`] CHART_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2)))
      (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas (phi:num->B->A) n (&0)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CQ_PB_RIEM0 THEN
    EXISTS_TAC `top:B topology` THEN
    MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(W:num->B->bool) (m + 2)`; `p2cv_P V t Q atlas (phi:num->B->A) n (&0)`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (y0:B)`; `y:B`; `i:num`]
                P2CQ_REGION_RMD2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(CC:B->real) y0` THEN CONJ_TAC THENL
   [USE_THEN "CC" (MP_TAC o C MP (ASSUME `(y0:B) IN F0`) o SPEC `y0:B`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Shi's bounds on the derivatives of the curvature of the                   *)
(* chart representatives, uniformly along the sequence and over a compact   *)
(* interval of times: on the region manifold of W (m + 2), Thm 3.28 with the *)
(* margin a - a' below a, or at a bottom without margin Thm 3.29 from time 0 *)
(* with the initial bounds of P2CQ_INIT_BOUNDS (and Thm 3.28 at the top).   *)
(* ------------------------------------------------------------------------- *)

(* Uniform facts on the region manifold: metrics, balls, curvature. *)

let P2CQ_SEQ_FACTS = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m a' b' CM N.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     a' <= &0 /\ &0 <= b' /\ a' < b' /\ &0 <= CM /\ m + 2 <= N /\
     (!n. N <= n
          ==> rfs_persists (V n) (IMAGE (phi n) (W (m + 2))) (t n + a' / Q n) (t n + b' / Q n) /\
              (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W (m + 2))
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W (m + 2)
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u)))
     ==> ?r Kc. &0 < r /\ &0 < Kc /\
                !n s. N <= n /\ (a' < s \/ s = &0) /\ s <= b'
                      ==> riemannian_metric (restrict_atlas atlas (W (m + 2)))
                            (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas phi n s)) /\
                          (!xM. xM IN W m
                                ==> mfd_ball (subtopology top (W (m + 2)),
                                              restrict_atlas atlas (W (m + 2)))
                                      (restrict_metric atlas (W (m + 2))
                                         (p2cv_P V t Q atlas phi n s)) xM r
                                    SUBSET W (m + 1) /\
                                    compact_in (subtopology top (W (m + 2)))
                                      (subtopology top (W (m + 2)) closure_of
                                       mfd_ball (subtopology top (W (m + 2)),
                                                 restrict_atlas atlas (W (m + 2)))
                                         (restrict_metric atlas (W (m + 2))
                                            (p2cv_P V t Q atlas phi n s)) xM r)) /\
                          (!y. y IN W (m + 2)
                               ==> mfd_rm_norm (restrict_atlas atlas (W (m + 2)))
                                     (restrict_metric atlas (W (m + 2))
                                        (p2cv_P V t Q atlas phi n s)) y <= Kc)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "qf0")))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `&0 < exp(&8 * CM * (b' - a'))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `W:num->B->bool`; `m:num`; `sqrt(&2 * exp(&8 * CM * (b' - a')))`]
                P2CQ_BALLS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "balls"))) THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv")) P2CQ_PB_CURV THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `sqrt C0 * CM + &1`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  USE_THEN "per" (STRIP_ASSUME_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
  SUBGOAL_THEN `p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) (m + 2))
                         ((phi:num->B->A) n) (t n) (Q n)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (atlas:((B->bool)#(B->real^3))->bool)
                                      ((W:num->B->bool) (m + 2)))
      (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas (phi:num->B->A) n s))`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CQ_PB_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `xM:B` THEN DISCH_TAC THEN USE_THEN "balls" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:B`; `v:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:B) IN (W:num->B->bool) (m + 2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(W:num->B->bool) (m + 1) SUBSET W (m + 2)` MP_TAC THENL
       [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) (m + 2)`; `g0:B->real^3^3`;
                   `p2cv_P V t Q atlas (phi:num->B->A) n s`;
                   `sqrt(&2 * exp(&8 * CM * (b' - a'))) pow 2`; `z:B`] P2CQ_RESTRICT_QF) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `u:real^3` THEN
    SUBGOAL_THEN `sqrt(&2 * exp(&8 * CM * (b' - a'))) pow 2 = &2 * exp(&8 * CM * (b' - a'))`
    SUBST1_TAC THENL [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CQ_QF_MANIFOLD THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `top:B topology`; `xl:B`;
                          `W:num->B->bool`; `m + 2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "qf0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt C0 * CM` THEN REWRITE_TAC[REAL_ARITH `a <= a + &1`] THEN
  REWRITE_TAC[P2CV_P_PB] THEN USE_THEN "curv" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b':real`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "p3_vrm" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The assembly of Shi's bounds (P2CQ_SHI).                                  *)
(* ------------------------------------------------------------------------- *)

let P2CQ_SHI = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m a b a' b' CM N c K.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     a' <= a /\ a <= &0 /\ &0 <= b /\ a < b /\ b <= b' /\ (a' < a \/ a = &0 /\ a' = &0) /\
     &0 <= CM /\ m + 2 <= N /\
     (!n. N <= n
          ==> rfs_persists (V n) (IMAGE (phi n) (W (m + 2))) (t n + a' / Q n) (t n + b' / Q n) /\
              (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W (m + 2))
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W (m + 2)
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u))) /\
     c IN atlas /\ compact K /\ K SUBSET IMAGE (SND c) (FST c INTER W m)
     ==> !j. ?C. !n s y. N <= n /\ a <= s /\ s <= b /\ y IN K
                         ==> lrm_deriv_norm2 j
                               (metric_local atlas c (p2cv_P V t Q atlas phi n s)) y <= C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (CONJUNCTS_THEN2 (LABEL_TAC "qf0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN X_GEN_TAC `j:num` THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `a':real`; `b':real`; `CM:real`; `N:num`] P2CQ_SEQ_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `Kc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "facts"))))) THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `j:num`; `N:num`] P2CQ_INIT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K0:real` (LABEL_TAC "init")) THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W (m + 1) /\ W (m + 1) SUBSET W (m + 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `hausdorff_space (subtopology top ((W:num->B->bool) (m + 2)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace (subtopology top ((W:num->B->bool) (m + 2))) = W (m + 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(W:num->B->bool) (m + 2) SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
  (* Thm 3.28 *)
  SUBGOAL_THEN
   `!tau. &0 < tau
          ==> ?Cl. !n u s xM. N <= n /\ a' <= u /\ u < s /\ s <= b' /\ tau <= s - u /\
                              xM IN (W:num->B->bool) m
                              ==> rfa_rmd2 j (restrict_atlas atlas (W (m + 2)))
                                    (restrict_metric atlas (W (m + 2))
                                       (p2cv_P V t Q atlas (phi:num->B->A) n s)) xM <= Cl`
  (LABEL_TAC "s28") THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `(:B)` RFA_P2_THM_3_28) THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `Kc:real`; `r:real`; `tau:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "Cl")) THEN
    EXISTS_TAC `Cl:real` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `u:real`; `s:real`; `xM:B`] THEN STRIP_TAC THEN
    USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (MP_TAC o C MP (ASSUME `(xM:B) IN (W:num->B->bool) m`) o SPEC `xM:B`) ASSUME_TAC)) THEN
    STRIP_TAC THEN
    USE_THEN "Cl" (MP_TAC o SPECL
     [`subtopology top ((W:num->B->bool) (m + 2))`;
      `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))`;
      `u:real`; `s:real`;
      `\r. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))
             (p2cv_P V t Q atlas (phi:num->B->A) n r)`; `xM:B`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CQ_PB_UPTO THEN
        MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN
        USE_THEN "per" (STRIP_ASSUME_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC P2CV_HYP_ONE THEN
          MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
          ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM SET_TAC[];
        MAP_EVERY X_GEN_TAC [`tt:real`; `yy:B`] THEN STRIP_TAC THEN
        USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `tt:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM SET_TAC[]];
      DISCH_THEN(MP_TAC o SPEC `xM:B`) THEN REWRITE_TAC[rfa_rmd2] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`subtopology top ((W:num->B->bool) (m + 2))`;
                     `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))`;
                     `restrict_metric (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))
                        (p2cv_P V t Q atlas (phi:num->B->A) n s)`; `xM:B`; `r / &2`]
                    MFD_CENTRE_IN_BALL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* transfer to the chart c *)
  SUBGOAL_THEN
   `!n s y. N <= n /\ (a' < s \/ s = &0) /\ s <= b' /\ y IN K
            ==> chart_inv (c:(B->bool)#(B->real^3)) y IN (W:num->B->bool) m /\
                lrm_deriv_norm2 j (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) n s)) y =
                rfa_rmd2 j (restrict_atlas atlas (W (m + 2)))
                  (restrict_metric atlas (W (m + 2)) (p2cv_P V t Q atlas phi n s))
                  (chart_inv c y)`
  (LABEL_TAC "tr") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) y IN FST c /\
                  chart_inv c y IN (W:num->B->bool) m /\ SND c (chart_inv c y) = y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(K:real^3->bool) SUBSET IMAGE (SND(c:(B->bool)#(B->real^3)))
                                              (FST c INTER (W:num->B->bool) m)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `xx:B` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(W:num->B->bool) (m + 2)`; `p2cv_P V t Q atlas (phi:num->B->A) n s`;
                   `c:(B->bool)#(B->real^3)`; `chart_inv (c:(B->bool)#(B->real^3)) y`;
                   `j:num`] P2CQ_REGION_RMD2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `s:real`]) THEN ASM_SIMP_TAC[];
        ASM SET_TAC[]];
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  ASM_CASES_TAC `a' < a` THENL
   [USE_THEN "s28" (MP_TAC o SPEC `a - a':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "Cl")) THEN EXISTS_TAC `Cl:real` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "tr" (MP_TAC o SPECL [`n:num`; `s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    USE_THEN "Cl" MATCH_MP_TAC THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a = &0 /\ a' = &0 /\ &0 < b'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `a' < a \/ a = &0 /\ a' = &0` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Thm 3.29 from time 0 *)
  SUBGOAL_THEN
   `?Cl. !n s xM. N <= n /\ &0 <= s /\ s < b' /\ xM IN (W:num->B->bool) m
                  ==> rfa_rmd2 j (restrict_atlas atlas (W (m + 2)))
                        (restrict_metric atlas (W (m + 2))
                           (p2cv_P V t Q atlas (phi:num->B->A) n s)) xM <= Cl`
  (X_CHOOSE_THEN `Cl1:real` (LABEL_TAC "Cl1")) THENL
   [MP_TAC(ISPEC `(:B)` RFA_P2_THM_3_29) THEN REWRITE_TAC[P2_THM_3_29_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `Kc + abs K0`; `r:real`; `b':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "Cl")) THEN EXISTS_TAC `Cl:real` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `xM:B`] THEN STRIP_TAC THEN
    USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (MP_TAC o C MP (ASSUME `(xM:B) IN (W:num->B->bool) m`) o SPEC `xM:B`) ASSUME_TAC)) THEN
    STRIP_TAC THEN
    USE_THEN "Cl" (MP_TAC o SPECL
     [`subtopology top ((W:num->B->bool) (m + 2))`;
      `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))`;
      `&0`; `b':real`;
      `\r. restrict_metric (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))
             (p2cv_P V t Q atlas (phi:num->B->A) n r)`; `xM:B`]) THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_LE_REFL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CQ_PB_FROM THEN
        EXISTS_TAC `b':real` THEN
        USE_THEN "per" (STRIP_ASSUME_TAC o C MP (ASSUME `N <= n:num`) o SPEC `n:num`) THEN
        UNDISCH_TAC `rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n)
                       ((W:num->B->bool) (m + 2))) (t n + a' / Q n) (t n + b' / Q n)` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC P2CV_HYP_ONE THEN
        MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM SET_TAC[];
        MAP_EVERY X_GEN_TAC [`tt:real`; `yy:B`] THEN STRIP_TAC THEN
        USE_THEN "facts" (MP_TAC o SPECL [`n:num`; `tt:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
        DISCH_THEN(MP_TAC o SPEC `yy:B`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`i:num`; `yy:B`] THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM rfa_rmd2] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN
        CONJ_TAC THENL
         [USE_THEN "init" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(MP_TAC o SPECL [`j:num`; `s:real`; `xM:B`]) THEN REWRITE_TAC[rfa_rmd2] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
      MP_TAC(ISPECL [`subtopology top ((W:num->B->bool) (m + 2))`;
                     `restrict_atlas (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))`;
                     `restrict_metric (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) (m + 2))
                        (p2cv_P V t Q atlas (phi:num->B->A) n (&0))`; `xM:B`; `r / &2`]
                    MFD_CENTRE_IN_BALL) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "s28" (MP_TAC o C MP (ASSUME `&0 < b'`) o SPEC `b':real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl2:real` (LABEL_TAC "Cl2")) THEN
  EXISTS_TAC `max Cl1 Cl2` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:real`; `y:real^3`] THEN STRIP_TAC THEN
  USE_THEN "tr" (MP_TAC o SPECL [`n:num`; `s:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_CASES_TAC `s < b'` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= c1 ==> x <= max c1 c2`) THEN
    USE_THEN "Cl1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= c2 ==> x <= max c1 c2`) THEN
    USE_THEN "Cl2" MATCH_MP_TAC THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The working interval around a compact interval of J, the                  *)
(* hypotheses p2ca_seqhyp in one chart, for all charts after a common shift *)
(* of the sequence, and the setting p2ca_set (P2CQ_SETTING).                 *)
(* ------------------------------------------------------------------------- *)

let P2CQ_WORKING = prove
 (`!J a b. is_realinterval J /\ real_interval[a,b] SUBSET J /\ a <= b /\
           (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0)
           ==> ?a' b'. a' <= a /\ b <= b' /\ real_interval[a',b'] SUBSET J /\
                       (a' < a \/ a = &0 /\ a' = &0) /\ (b < b' \/ b' = b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) IN J /\ (b:real) IN J` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET J` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?a'. a' IN J /\ a' <= a /\ (a' < a \/ a = &0 /\ a' = &0)`
  (X_CHOOSE_THEN `a':real` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [ASM_CASES_TAC `?a1. a1 IN J /\ a1 < a` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `a1:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `a1:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_REFL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b'. b' IN J /\ b <= b' /\ (b < b' \/ b' = b)`
  (X_CHOOSE_THEN `b':real` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THENL
   [ASM_CASES_TAC `?b1. b1 IN J /\ b < b1` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `b1:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `b1:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  UNDISCH_TAC `is_realinterval J` THEN REWRITE_TAC[is_realinterval] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN
  ASM_REWRITE_TAC[]);;

(* The hypotheses of the local limit theorem in one chart. *)

let P2CQ_SEQHYP_C = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m a b a' b' CM N c.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     a' <= a /\ a <= &0 /\ &0 <= b /\ a < b /\ b <= b' /\ (a' < a \/ a = &0 /\ a' = &0) /\
     (b < b' \/ b' = b) /\ &0 <= CM /\ m + 2 <= N /\
     (!n. N <= n
          ==> rfs_persists (V n) (IMAGE (phi n) (W m)) (t n + a' / Q n) (t n + b' / Q n) /\
              (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W m)
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n. N <= n
          ==> rfs_persists (V n) (IMAGE (phi n) (W (m + 2))) (t n + a' / Q n) (t n + b' / Q n) /\
              (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W (m + 2))
                     ==> p3_vrm (V n) (t n + s / Q n) z <= CM * Q n)) /\
     (!n y u. N <= n /\ y IN W (m + 2)
              ==> abs(u dot (p2cv_P V t Q atlas phi n (&0) y ** u) - u dot (g0 y ** u))
                  <= inv(&2) * (u dot (g0 y ** u))) /\
     c IN atlas
     ==> p2ca_seqhyp (IMAGE (SND c) (FST c INTER W m)) a b
                     (\n s. metric_local atlas c (p2cv_P V t Q atlas phi (N + n) s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (CONJUNCTS_THEN2 (LABEL_TAC "per2")
    (CONJUNCTS_THEN2 (LABEL_TAC "qf0") ASSUME_TAC))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  SUBGOAL_THEN `a' < a \/ a = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `a' < a \/ a = &0 /\ a' = &0` THEN CONV_TAC TAUT; ALL_TAC] THEN
  SUBGOAL_THEN `m:num <= N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(W:num->B->bool) m SUBSET W (m + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CV_W_MONO THEN EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CA_CHART_IMAGE_OPEN_C THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N <= n ==> p2cv_one ((V:num->p2cvv3) n) (top,atlas) ((W:num->B->bool) m)
                            ((phi:num->B->A) n) (t n) (Q n)`
  (LABEL_TAC "one") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CV_HYP_ONE THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `g0:B->real^3^3`; `xl:B`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* metric fields, local flows, extensions *)
  SUBGOAL_THEN
   `!n s. a <= s /\ s <= b
          ==> metric_field (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m))
                (metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s))`
  (LABEL_TAC "mf") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_P_FIELD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b':real`] THEN
    USE_THEN "per" (STRIP_ASSUME_TAC o C MP (ARITH_RULE `N <= N + n:num`) o SPEC `N + n:num`) THEN
    USE_THEN "one" (ASSUME_TAC o C MP (ARITH_RULE `N <= N + n:num`) o SPEC `N + n:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lricci_flow (IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)) a b
          (\s. metric_local atlas c (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s))`
  (LABEL_TAC "lf") THENL
   [GEN_TAC THEN REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CA_LRICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a':real`; `b':real`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN MATCH_MP_TAC P2CV_LFLOW THEN
    EXISTS_TAC `top:B topology` THEN
    USE_THEN "per" (STRIP_ASSUME_TAC o C MP (ARITH_RULE `N <= N + n:num`) o SPEC `N + n:num`) THEN
    USE_THEN "one" (ASSUME_TAC o C MP (ARITH_RULE `N <= N + n:num`) o SPEC `N + n:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?e (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
          &0 < e /\
          smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS
                         IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)) FF /\
          (!s y. a <= s /\ s <= b /\ y IN IMAGE (SND c) (FST c INTER W m)
                 ==> FF(pastecart (lift s) y) =
                     vectorize(metric_local atlas c
                                 (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s) y))`
  (LABEL_TAC "ext") THENL
   [GEN_TAC THEN REWRITE_TAC[P2CV_P_PB] THEN MATCH_MP_TAC P2CV_EXT THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `a':real`; `b':real`] THEN
    USE_THEN "per" (STRIP_ASSUME_TAC o C MP (ARITH_RULE `N <= N + n:num`) o SPEC `N + n:num`) THEN
    USE_THEN "one" (ASSUME_TAC o C MP (ARITH_RULE `N <= N + n:num`) o SPEC `N + n:num`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2ca_seqhyp] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ c /\ (a /\ b /\ c ==> d /\ e) ==> a /\ b /\ c /\ d /\ e`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN USE_THEN "lf" ACCEPT_TAC;
    REWRITE_TAC[] THEN USE_THEN "ext" ACCEPT_TAC;
    STRIP_TAC] THEN
  (* positivity and derivative bounds on a compact set *)
  SUBGOAL_THEN
   `!n y u. N <= n /\ y IN (W:num->B->bool) m
            ==> abs(u dot (p2cv_P V t Q atlas (phi:num->B->A) n (&0) y ** u) -
                    u dot ((g0:B->real^3^3) y ** u)) <= inv(&2) * (u dot (g0 y ** u))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "qf0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(W:num->B->bool) m SUBSET W (m + 2)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K. compact K /\ K SUBSET IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)
        ==> ?Lm. &0 <= Lm /\
                 !n s y v. a <= s /\ s <= b /\ y IN K
                           ==> norm v pow 2 <=
                               Lm * (v dot (metric_local atlas c
                                     (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s) y ** v)) /\
                               v dot (metric_local atlas c
                                       (p2cv_P V t Q atlas phi (N + n) s) y ** v) <=
                               Lm * norm v pow 2`
  (LABEL_TAC "qfb") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                   `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                   `a:real`; `b:real`; `a':real`; `b':real`; `CM:real`; `N:num`;
                   `c:(B->bool)#(B->real^3)`; `K:real^3->bool`] P2CV_QF_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Lm:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `K:real^3->bool` THEN STRIP_TAC THEN
    USE_THEN "qfb" (MP_TAC o SPEC `K:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Lm:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Lm:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:real^3->bool`; `l:(num)list`; `p:num`; `q:num`] THEN STRIP_TAC THEN
  USE_THEN "qfb" (MP_TAC o SPEC `K:real^3->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Lm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lmb"))) THEN
  SUBGOAL_THEN
   `!n s y pp qq. a <= s /\ s <= b /\ y IN K /\ 1 <= pp /\ pp <= dimindex(:3) /\
                  1 <= qq /\ qq <= dimindex(:3)
                  ==> abs(metric_local atlas (c:(B->bool)#(B->real^3))
                            (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s) y$pp$qq) <= Lm`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CV_ENTRY_BOUNDS THEN
    EXISTS_TAC `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(K:real^3->bool) SUBSET
                   IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^3` THEN
      USE_THEN "lmb" (MP_TAC o SPECL [`n:num`; `s:real`; `y:real^3`; `v:real^3`]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n s y v. a <= s /\ s <= b /\ y IN K
              ==> norm v pow 2 <=
                  Lm * (v dot (metric_local atlas (c:(B->bool)#(B->real^3))
                                (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s) y ** v))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "lmb" (MP_TAC o SPECL [`n:num`; `s:real`; `y:real^3`; `v:real^3`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. ?C. !n s y. a <= s /\ s <= b /\ y IN K
                    ==> lrm_deriv_norm2 j (metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s)) y <= C`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                   `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                   `a:real`; `b:real`; `a':real`; `b':real`; `CM:real`; `N:num`;
                   `c:(B->bool)#(B->real^3)`; `K:real^3->bool`] P2CQ_SHI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `C:real` o SPEC `j:num`) THEN EXISTS_TAC `C:real` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `c:(B->bool)#(B->real^3)`; `K:real^3->bool`; `N:num`] P2CQ_JETS0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c INTER (W:num->B->bool) m)`;
                 `K:real^3->bool`; `a:real`; `b:real`;
                 `\n s. metric_local atlas (c:(B->bool)#(B->real^3))
                          (p2cv_P V t Q atlas (phi:num->B->A) (N + n) s)`;
                 `Lm:real`] P2CH_ST_JETS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:(num)list`; `p:num`; `q:num`]) THEN ASM_REWRITE_TAC[]);;

(* All charts at once, after a common shift of the sequence. *)

let P2CQ_SEQHYP = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A) m a b.
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi /\
     a <= &0 /\ &0 <= b /\ a < b /\ real_interval[a,b] SUBSET J
     ==> ?N. !c. c IN atlas
                 ==> p2ca_seqhyp (IMAGE (SND c) (FST c INTER W m)) a b
                                 (\n s. metric_local atlas c (p2cv_P V t Q atlas phi (N + n) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  FIRST_ASSUM(LABEL_TAC "int" o last o CONJUNCTS o MATCH_MP P2CV_HYP_BASIC) THEN
  MP_TAC(ISPECL [`J:real->bool`; `a:real`; `b:real`] P2CQ_WORKING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  USE_THEN "int" (MP_TAC o C MP (ASSUME `real_interval[a',b'] SUBSET J`) o
                  SPECL [`m:num`; `a':real`; `b':real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CM1:real` (X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1"))) THEN
  USE_THEN "int" (MP_TAC o C MP (ASSUME `real_interval[a',b'] SUBSET J`) o
                  SPECL [`m + 2`; `a':real`; `b':real`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `CM2:real` (X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2"))) THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
                 `top closure_of (W:num->B->bool) (m + 2)`] P2CV_QF_TIME0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  SUBGOAL_THEN `(W:num->B->bool) (m + 2) SUBSET top closure_of W (m + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= max (max CM1 CM2) (&0) /\ m + 2 <= N1 + N2 + N3 + m + 2`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N1 + N2 + N3 + m + 2 <= n
        ==> rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) m))
                         (t n + a' / Q n) (t n + b' / Q n) /\
            (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W m)
                   ==> p3_vrm (V n) (t n + s / Q n) z <= max (max CM1 CM2) (&0) * Q n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 + N3 + m + 2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vb"))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CM1 * (Q:num->real) n` THEN
    CONJ_TAC THENL
     [USE_THEN "vb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. N1 + N2 + N3 + m + 2 <= n
        ==> rfs_persists ((V:num->p2cvv3) n) (IMAGE ((phi:num->B->A) n) ((W:num->B->bool) (m + 2)))
                         (t n + a' / Q n) (t n + b' / Q n) /\
            (!s z. a' <= s /\ s <= b' /\ z IN IMAGE (phi n) (W (m + 2))
                   ==> p3_vrm (V n) (t n + s / Q n) z <= max (max CM1 CM2) (&0) * Q n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `N1 + N2 + N3 + m + 2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vb"))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CM2 * (Q:num->real) n` THEN
    CONJ_TAC THENL
     [USE_THEN "vb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n y u. N1 + N2 + N3 + m + 2 <= n /\ y IN (W:num->B->bool) (m + 2)
            ==> abs(u dot (p2cv_P V t Q atlas (phi:num->B->A) n (&0) y ** u) -
                    u dot ((g0:B->real^3^3) y ** u)) <= inv(&2) * (u dot (g0 y ** u))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "N3" (MP_TAC o SPECL [`n:num`; `y:B`; `u:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `N1 + N2 + N3 + m + 2 <= n` THEN ARITH_TAC;
        UNDISCH_TAC `(W:num->B->bool) (m + 2) SUBSET top closure_of W (m + 2)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `N1 + N2 + N3 + m + 2` THEN
  X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:num->p2cvv3`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `J:real->bool`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g0:B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `m:num`;
                 `a:real`; `b:real`; `a':real`; `b':real`; `max (max CM1 CM2) (&0)`;
                 `N1 + N2 + N3 + m + 2`; `c:(B->bool)#(B->real^3)`] P2CQ_SEQHYP_C) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The setting of the assembly theorem. *)

let P2CQ_SETTING = prove
 (`!V x t Q J (top:B topology) atlas g0 xl W (phi:num->B->A).
     p2cv_hyp V x t Q J (top,atlas) g0 xl W phi
     ==> p2ca_set top atlas W J (p2cv_P V t Q atlas phi) g0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CV_HYP_BASIC) THEN
  REWRITE_TAC[p2ca_set] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CQ_SEQHYP THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `top:B topology`; `g0:B->real^3^3`;
                          `xl:B`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CV_TIME0 THEN
    MAP_EVERY EXISTS_TAC [`x:num->A`; `J:real->bool`; `xl:B`; `W:num->B->bool`] THEN
    ASM_REWRITE_TAC[]]);;

