(* ========================================================================= *)
(* Unit pc_p2c_sing2: Lemma 11.23 and Lemma 11.23 MAXEXT (Morgan-Tian,       *)
(* Lemma 11.23 and Thm 11.19 (5)): strong canonical neighbourhoods at the    *)
(* limit time from those at earlier times.  Tools: the right-end tube, the   *)
(* reverse change of base, the slice transport, the drift, positivity of R.  *)
(* ========================================================================= *)

needs "src/pc_p2c_sing.ml";;
needs "src/pc_p3_c172c.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_rfs_evmono.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* T1: the right-end tube.  For a family smooth up to its end                *)
(* time b (rfs_flow_upto), the C^k distance (base: the metric at b, both     *)
(* scaled by R) to the metrics at times s in (b - d, b] is small uniformly   *)
(* on a compact set.  The Euclidean continuity at the right end comes from   *)
(* P3H_LCK_EXT_CONTINUOUS by reflecting time.                                 *)
(* ------------------------------------------------------------------------- *)

let SNGL_LCK_EXT_CONTINUOUS_UPTO = prove
 (`!V a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) k.
     open V /\ &0 < e /\ a < b /\
     (!t. a < t /\ t <= b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift a,lift(b + e)) PCROSS V) FF /\
     (!t y. a < t /\ t <= b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> (\w. lift(lck_dist2 k (Gc b) (Gc (drop(fstcart w))) (sndcart w))) continuous_on
         {w | a < drop(fstcart w) /\ drop(fstcart w) <= b /\ sndcart w IN V}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mf")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ff")))))) THEN
  ABBREV_TAC `rf = \w:real^(1,N)finite_sum. pastecart (--(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `linear (rf:real^(1,N)finite_sum->real^(1,N)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "rf" THEN MATCH_MP_TAC LINEAR_PASTECART THEN
    REWRITE_TAC[ETA_AX; LINEAR_SNDCART] THEN MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN
    REWRITE_TAC[ETA_AX; LINEAR_FSTCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^(1,N)finite_sum. drop(fstcart(rf w)) = --(drop(fstcart w)) /\
                                          sndcart(rf w) = sndcart w`
  (LABEL_TAC "rfw") THENL
   [EXPAND_TAC "rf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_NEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `--b:real`; `--a:real`; `e:real`;
                 `\t. (Gc:real->real^N->real^N^N) (--t)`;
                 `(FF:real^(1,N)finite_sum->real^(N,N)finite_prod) o
                  (rf:real^(1,N)finite_sum->real^(1,N)finite_sum)`; `k:num`]
                P3H_LCK_EXT_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "mf" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS (V:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
       [EXPAND_TAC "rf" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                    FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; DROP_NEG;
                    LIFT_DROP] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`interval(lift(--b - e),lift(--a)) PCROSS (V:real^N->bool)`;
                       `\x:real^(1,N)finite_sum. x`;
                       `rf:real^(1,N)finite_sum->real^(1,N)finite_sum`]
                      SMOOTH_MAP_ON_LINEAR_O) THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_ID; OPEN_PCROSS; OPEN_INTERVAL] THEN
        REWRITE_TAC[o_DEF; ETA_AX]];
      REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN EXPAND_TAC "rf" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; GSYM LIFT_NEG] THEN
      USE_THEN "ff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `(\w. lift(lck_dist2 k ((Gc:real->real^N->real^N^N) (--(--b)))
                                   (Gc (--(drop(fstcart w)))) (sndcart w))) o
              (rf:real^(1,N)finite_sum->real^(1,N)finite_sum)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_REWRITE_TAC[REAL_NEG_NEG];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{w:real^(1,N)finite_sum | --b <= drop(fstcart w) /\ drop(fstcart w) < --a /\
                                       sndcart w IN V}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The manifold tube at the right end, uniform on a compact set. *)

let SNGL_TUBE_UPTO = prove
 (`!top atlas (g:real->A->real^3^3) a b R k K th.
     rfs_flow_upto (top,atlas) a b g /\ &0 < R /\ compact_in top K /\ &0 < th
     ==> ?d. &0 < d /\
             !s p. b - d < s /\ s <= b /\ p IN K
                   ==> lck_dist2 k (metric_local atlas (chart_at atlas p) (\y. R %% g b y))
                                   (metric_local atlas (chart_at atlas p) (\y. R %% g s y))
                                   (SND(chart_at atlas p) p) < th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\ a < b /\
    (!t. a < t /\ t <= b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `K:A->bool`;
                 `\d (p:A). !s. b - d < s /\ s <= b
                     ==> lck_dist2 k (metric_local atlas (chart_at atlas p)
                                        (\y. R %% (g:real->A->real^3^3) b y))
                                     (metric_local atlas (chart_at atlas p) (\y. R %% g s y))
                                     (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) p) p)
                         < th`] SNGL_COMPACT_UNIFORM) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    MESON_TAC[]] THEN
  X_GEN_TAC `p0:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p0:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `compact_in top (K:A->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    UNDISCH_TAC `(p0:A) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p0:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (p0:A)` THEN
  STRIP_TAC THEN
  UNDISCH_TAC `rfs_flow_upto (top,atlas) a b (g:real->A->real^3^3)` THEN
  REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fx"))))) THEN
  ABBREV_TAC `Vc = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
  MP_TAC(ISPECL [`Vc:real^3->bool`; `a:real`; `b:real`; `e:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^3))
                        (\y. R %% (g:real->A->real^3^3) t y)`;
                 `\w. R % (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) w`; `k:num`]
                SNGL_LCK_EXT_CONTINUOUS_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `riemannian_metric atlas (\y. R %% (g:real->A->real^3^3) t y)` MP_TAC
      THENL
       [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Vc" THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; ETA_AX];
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "fx" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL; ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_on; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift b) ((SND(c:(A->bool)#(A->real^3))) p0)`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `th:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dl"))) THEN
  EXISTS_TAC `{y:A | y IN FST(c:(A->bool)#(A->real^3)) /\
                     SND c y IN ball(SND c p0,dl / &2)}` THEN
  EXISTS_TAC `min (dl / &2) (b - a)` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`;
                   `ball(SND(c:(A->bool)#(A->real^3)) p0,dl / &2)`]
                  GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; OPEN_BALL];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN STRIP_TAC THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    UNDISCH_TAC `(y:A) IN FST(c:(A->bool)#(A->real^3))` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas (\z. R %% (g:real->A->real^3^3) b z) /\
                riemannian_metric atlas (\z. R %% (g:real->A->real^3^3) s z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `\z. R %% (g:real->A->real^3^3) b z`; `\z. R %% (g:real->A->real^3^3) s z`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)`;
                 `c:(A->bool)#(A->real^3)`; `topspace top:A->bool`; `y:A`; `k:num`]
                P2CA_LCK_CHART_INDEP_C) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN CONJ_TAC THEN
    MATCH_MP_TAC SNGL_RIEM_FIELD_ON THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "dl" (MP_TAC o SPEC `pastecart (lift s) ((SND(c:(A->bool)#(A->real^3))) y)`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      EXPAND_TAC "Vc" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `dist(lift s,lift b) + dist((SND(c:(A->bool)#(A->real^3))) y,SND c p0)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[dist; PASTECART_SUB; NORM_PASTECART_LE];
        REWRITE_TAC[DIST_LIFT] THEN
        UNDISCH_TAC `dist(SND(c:(A->bool)#(A->real^3)) p0,SND c y) < dl / &2` THEN
        REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[P2BL_LCK_DIST2_REFL; DIST_LIFT; METRIC_LOCAL_CMUL; ETA_AX] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* T2: change of base in the other direction.  If G1 is                     *)
(* C^k-close to G0 (base G0), the C^k distance from G1 to G2 measured with   *)
(* base G1 is controlled by the same difference measured with base G0 (the  *)
(* converse of LRG_CK_BASE_CHANGE; from GEOB_R_DERIV and GEOB_NORM_COMPARE). *)
(* ------------------------------------------------------------------------- *)

let SNGL_CK_BASE_REV = prove
 (`!k. ?M. &0 <= M /\
      !s (G0:real^N->real^N^N) G1 G2 y.
         metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s /\
         lck_dist2 k G0 G1 y <= &1 / &4
         ==> lck_dist2 k G1 G2 y <= M * lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`k:num`; `k:num`] GEOB_R_DERIV) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `CR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CR"))) THEN
  EXISTS_TAC `&(k + 1) * CR * &2 pow (2 + k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                       `G2:real^N->real^N^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G0:real^N->real^N^N) z + G2 z - G1 z) z u - lmetric2 G0 z u) =
    geob_hd G1 G2`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; geob_hd; lmetric2] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RADD; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lck_dist2] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM geob_hd] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`]
         GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G1 (G2:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "it0") THEN
  SUBGOAL_THEN
   `sum(0..k) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                    (lnabla_iter 2 i G0 (geob_hd G1 G2)) y) <=
    &2 pow (2 + k) *
    sum(0..k) (\i. ltnorm2 (2 + i) (G0:real^N->real^N^N)
                    (lnabla_iter 2 i G0 (geob_hd G1 G2)) y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow (2 + i) * ltnorm2 (2 + i) (G0:real^N->real^N^N)
                                   (lnabla_iter 2 i G0 (geob_hd G1 G2)) y` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`;
                     `y:real^N`; `2 + i`;
                     `lnabla_iter 2 i G0 (geob_hd G1 (G2:real^N->real^N^N))`]
             GEOB_NORM_COMPARE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "it0" (fun th -> REWRITE_TAC[th]); SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
        MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "it0" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..k) (\b. CR * sum(0..k) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                                                 (lnabla_iter 2 i G0 (geob_hd G1 G2)) y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CR * sum(0..b) (\i. ltnorm2 (2 + i) (G1:real^N->real^N^N)
                                      (lnabla_iter 2 i G0 (geob_hd G1 G2)) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "CR" MATCH_MP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GEOB_SUM_MONO_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "it0" (fun th -> REWRITE_TAC[th])];
    REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Reflecting the second metric about the base leaves the distance unchanged. *)

let SNGL_LCK_DIST2_REFLECT = prove
 (`!k s (G0:real^N->real^N^N) G1 y.
     metric_field s G0 /\ metric_field s G1 /\ y IN s
     ==> lck_dist2 k G0 (\z. G0 z + G0 z - G1 z) y = lck_dist2 k G0 G1 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G0:real^N->real^N^N) z + G0 z - G1 z) z u - lmetric2 G0 z u) =
    (\z u. --(&1) * geob_hd G0 G1 z u + &0 * geob_hd G0 G1 z u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; geob_hd; lmetric2] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RADD; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z u. lmetric2 (G1:real^N->real^N^N) z u - lmetric2 G0 z u) = geob_hd G0 G1`
  SUBST1_TAC THENL [REWRITE_TAC[geob_hd]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
                GEOB_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `geob_hd G0 (G1:real^N->real^N^N)`; `geob_hd G0 (G1:real^N->real^N^N)`;
                 `--(&1)`; `&0`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`l:num`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[ltnorm2] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(--(&1) * a + &0 * a) * (--(&1) * b + &0 * b) * c = a * b * c`]);;

(* ------------------------------------------------------------------------- *)
(* Transport of C^k distances between the slice at time s                    *)
(* (preferred charts of the atlas at s, the target metric pulled back by the *)
(* identity) and the fixed manifold W at time b (restricted atlas, the view  *)
(* family p2c_vfam).  Through the parametrization chart_inv of a chart at b. *)
(* ------------------------------------------------------------------------- *)

let SNGL_SLICE_TRANSPORT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s p Q k.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ a < s /\ s <= b /\
     p IN W /\ &0 < Q
     ==> lck_dist2 k
           (metric_local (rfs_vatlas V s) (chart_at (rfs_vatlas V s) p)
              (\y. Q %% rfs_vmetric V s y))
           (metric_local (rfs_vatlas V s) (chart_at (rfs_vatlas V s) p)
              (\y. Q %% mfd_pullback_metric (rfs_vatlas V s) (rfs_vatlas V b) (\y. y)
                                            (rfs_vmetric V b) y))
           (SND(chart_at (rfs_vatlas V s) p) p) =
         lck_dist2 k
           (metric_local (restrict_atlas (rfs_vatlas V b) W)
              (chart_at (restrict_atlas (rfs_vatlas V b) W) p)
              (\y. Q %% p2c_vfam V W b s y))
           (metric_local (restrict_atlas (rfs_vatlas V b) W)
              (chart_at (restrict_atlas (rfs_vatlas V b) W) p)
              (\y. Q %% p2c_vfam V W b b y))
           (SND(chart_at (restrict_atlas (rfs_vatlas V b) W) p) p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* slices at s and b *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                P2CV_PERSISTS_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `b:real`]
                P2CV_PERSISTS_AT) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) /\
                p IN topspace(rfs_vtop V b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (W:A->bool)`));
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`))] THEN
    UNDISCH_TAC `(p:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `s:real`; `p:A`] SNGL_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `b:real`; `p:A`] SNGL_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the flow on W at b *)
  SUBGOAL_THEN
   `rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W) a b
      (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) W b)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[p2c_vflow] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop V b) W) (restrict_atlas (rfs_vatlas V b) W) /\
    (!u. a < u /\ u <= b
         ==> riemannian_metric (restrict_atlas (rfs_vatlas V b) W)
               (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) W b u))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
                  a b (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) W b)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `u:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the chart at b and the parametrization *)
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b`; `W:A->bool`; `p:A`]
                MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `S = IMAGE (phi:A->real^3) (U INTER W)` THEN
  SUBGOAL_THEN `open (S:real^3->bool) /\ (phi:A->real^3) p IN S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                            `rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b`;
                 `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "inv" o CONJUNCT1) THEN
  SUBGOAL_THEN
   `mfd_param (rfs_vtop V b) (rfs_vatlas V b) S (chart_inv (U:A->bool,phi:A->real^3)) /\
    IMAGE (chart_inv (U,phi)) S SUBSET (W:A->bool) /\
    chart_inv (U,phi) ((phi:A->real^3) p) = (p:A)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "S" THEN SET_TAC[]];
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      REPEAT STRIP_TAC THEN USE_THEN "inv" (fun th -> ASM_SIMP_TAC[th]);
      USE_THEN "inv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`;
                 `chart_inv (U:A->bool,phi:A->real^3)`; `S:real^3->bool`] P3H_VFLOW_NECK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vf"))) THEN
  USE_THEN "vf" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vfs"))) THEN
  USE_THEN "vf" (MP_TAC o SPEC `b:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vfb"))) THEN
  (* the left side through the parametrization at time s *)
  SUBGOAL_THEN
   `mfd_pullback_metric (rfs_vatlas V s) (rfs_vatlas V b) (\y:A. y)
      (\y. Q %% rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b y) =
    (\y. Q %% mfd_pullback_metric (rfs_vatlas V s) (rfs_vatlas V b) (\y. y)
                                  (rfs_vmetric V b) y)`
  (SUBST1_TAC o SYM) THENL [REWRITE_TAC[FUN_EQ_THM; P2B9S_PB_CMUL; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (\y. Q %% rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s y) /\
    riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (\y. Q %% rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) W (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W
               (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`; `s:real`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) s`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b`;
                 `S:real^3->bool`; `chart_inv (U:A->bool,phi:A->real^3)`;
                 `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`;
                 `\y. Q %% rfs_vmetric (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s y`;
                 `\y. Q %% rfs_vmetric (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b y`;
                 `k:num`; `(phi:A->real^3) p`] P2B9_LCK_PARAM_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  (* the right side through the same parametrization on W *)
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `\y. Q %% p2c_vfam (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s y`;
                 `\y. Q %% p2c_vfam (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b y`;
                 `S:real^3->bool`; `chart_inv (U:A->bool,phi:A->real^3)`; `k:num`;
                 `(phi:A->real^3) p`] P2B9_LCK_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `S:real^3->bool` THEN
  ASM_REWRITE_TAC[P2B9_RFS_PULLBACK_CMUL; o_DEF; ETA_AX] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  USE_THEN "vfs" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN S`))) THEN
  USE_THEN "vfb" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN S`))) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* T3: the drift.  In a regular view, for s close to the end                 *)
(* time b, the rescaled metric at s is C^k-close (measured in the atlas at s,*)
(* base the metric at s, scale R(x,s)) to the metric at b pulled back by the *)
(* identity, uniformly on a compact set of the persisting W.                 *)
(* ------------------------------------------------------------------------- *)

let SNGL_VIEW_DRIFT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K x k delta.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\
     compact_in (rfs_vtop V b) K /\ K SUBSET W /\ x IN W /\
     &0 < rfs_vscalar V b x /\ &0 < delta
     ==> ?d. &0 < d /\
             !s. b - d < s /\ s <= b
                 ==> rfs_vscalar V b x / &2 < rfs_vscalar V s x /\
                     rfs_mclose k delta (rfs_vatlas V s) K
                       (\y. rfs_vscalar V s x %% rfs_vmetric V s y)
                       (\y. rfs_vscalar V s x %%
                            mfd_pullback_metric (rfs_vatlas V s) (rfs_vatlas V b) (\y. y)
                                                (rfs_vmetric V b) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R0 = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b x` THEN
  (* the scalar curvature at x is continuous up to b *)
  SUBGOAL_THEN
   `?d1. &0 < d1 /\ d1 <= b - a /\
         !s. b - d1 < s /\ s <= b
             ==> abs(rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) s x - R0) < R0 / &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `x:A`;
                   `(a + b) / &2`] P2C_VIEW_SCALAR_CONT_UPTO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `R0 / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))) THEN
    EXISTS_TAC `min e1 ((b - a) / &2)` THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "c1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "R0" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "d1") THEN
  (* constants *)
  MP_TAC(SPEC `k:num` (INST_TYPE [`:3`,`:N`] SNGL_CK_BASE_REV)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M"))) THEN
  ABBREV_TAC `Cs = (&1 + &2 / R0) pow k` THEN
  SUBGOAL_THEN `&1 <= Cs` ASSUME_TAC THENL
   [EXPAND_TAC "Cs" THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    SUBGOAL_THEN `&0 < &2 / R0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `th = min (&1 / &4) (delta pow 2 / (&2 * Cs * (M + &1)))` THEN
  SUBGOAL_THEN `&0 < th /\ th <= &1 / &4 /\ Cs * M * th < delta pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < delta pow 2 /\ &0 < &2 * Cs * (M + &1)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < delta pow 2 / (&2 * Cs * (M + &1))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "th" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "th" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `Cs * (M + &1) * delta pow 2 / (&2 * Cs * (M + &1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `Cs * (M + &1) * delta pow 2 / (&2 * Cs * (M + &1)) = delta pow 2 / &2`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_FIELD
         `~(Cs = &0) /\ ~(M + &1 = &0)
          ==> Cs * (M + &1) * d / (&2 * Cs * (M + &1)) = d / &2`) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the tube on the fixed manifold W at b *)
  SUBGOAL_THEN
   `rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W) a b
      (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) W b)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[p2c_vflow] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W b`;
                 `a:real`; `b:real`; `&1`; `k:num`; `K:A->bool`; `th:real`]
                SNGL_TUBE_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; COMPACT_IN_SUBTOPOLOGY]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_LID; ETA_AX] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tube"))) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `R0 / &2 < rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
  ASSUME_TAC THENL
   [USE_THEN "d1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_mclose] THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) s x` THEN
  EXISTS_TAC `Cs * M * th` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`; `p:A`;
                 `Q:real`; `k:num`] SNGL_SLICE_TRANSPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  (* the chart of W at p *)
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                          (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) /\
    (!u. a < u /\ u <= b
         ==> riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b u))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W,restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)
                  a b (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b)` THEN
    REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `u:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `compact_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (K:A->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    UNDISCH_TAC `(p:A) IN K` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`; `p:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p:A)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
      (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s)) /\
    metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
      (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    SUBGOAL_THEN `!u. a < u /\ u <= b
                      ==> metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                            (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                                          (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b u))` MP_TAC THEN
    TRY(X_GEN_TAC `u:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `riemannian_metric (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b u)`
        MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        NO_TAC) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) p IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv Q) pow k *
              lck_dist2 k (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                             (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s))
                          (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                             (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b)) (SND(c:(A->bool)#(A->real^3)) p)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s)`;
                   `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b)`;
                   `Q:real`; `SND(c:(A->bool)#(A->real^3)) p`] P2B9S_LCK_SCALE_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "tube" (MP_TAC o SPECL [`s:real`; `p:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "M" (MP_TAC o ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                  `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b)`;
                  `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s)`;
                  `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b)`;
                  `SND(c:(A->bool)#(A->real^3)) p`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b)`;
                 `metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s)`;
                 `SND(c:(A->bool)#(A->real^3)) p`] SNGL_LCK_DIST2_REFLECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + inv Q) pow k <= Cs` ASSUME_TAC THENL
   [EXPAND_TAC "Cs" THEN MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(R0 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_INV_DIV] THEN REWRITE_TAC[real_div; REAL_MUL_SYM] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= lck_dist2 k (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s))
                      (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b))
                      (SND(c:(A->bool)#(A->real^3)) p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cs * lck_dist2 k (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                                  (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s))
                               (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                                  (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b)) (SND(c:(A->bool)#(A->real^3)) p)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `M * lck_dist2 k (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                                 (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b b))
                              (metric_local (restrict_atlas (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) c
                                 (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s)) (SND(c:(A->bool)#(A->real^3)) p)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* T4: positivity of R at the end time.  If R(x,s) > 0 and                   *)
(* |dR/ds| <= B R^2 along the flow line of x on (a,b) (the derivative bounds *)
(* of canonical neighbourhoods), then 1/R is Lipschitz, R stays away from 0  *)
(* and R(x,b) > 0.  Also: strong canonical neighbourhoods are canonical      *)
(* neighbourhoods of the slice.                                              *)
(* ------------------------------------------------------------------------- *)

let SNGL_STRONG_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U.
     rfs_strong_canonical V C eps x t U
     ==> rfs_canonical_nbhd (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps x U`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[rfs_strong_canonical; rfs_canonical_nbhd; rfs_strong_neck;
              rfs_evolving_neck; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MESON_TAC[]);;

let SNGL_SCALAR_POS_UPTO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b x B.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ x IN W /\ &0 <= B /\
     (!s. a < s /\ s < b
          ==> &0 < rfs_vscalar V s x /\
              abs(rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) x +
                  &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) x)
              <= B * rfs_vscalar V s x pow 2)
     ==> &0 < rfs_vscalar V b x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))))) THEN
  ABBREV_TAC `R = \u. rfs_vscalar (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u x` THEN
  ABBREV_TAC `s0 = (a + b) / &2` THEN
  SUBGOAL_THEN `a < s0 /\ s0 < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the derivative of R along the flow line *)
  SUBGOAL_THEN
   `!s. a < s /\ s < b
        ==> ((R:real->real) has_real_derivative
             (rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric (V:(real->A topology)#
                (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) x +
              &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) x)) (atreal s)`
  (LABEL_TAC "der") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R" THEN MATCH_MP_TAC P2C_VIEW_SCALAR_EVOL THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* 1/R is B-Lipschitz on [s0,s1] for s1 < b *)
  SUBGOAL_THEN
   `!s1. s0 <= s1 /\ s1 < b
         ==> inv((R:real->real) s1) <= inv(R s0) + B * (b - a)`
  (LABEL_TAC "lip") THENL
   [X_GEN_TAC `s1:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\u. inv((R:real->real) u)`;
                   `\u. --(rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric (V:(real->A topology)#
                          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) x +
                           &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x) /
                          (R:real->real) u pow 2`;
                   `real_interval[s0,s1]`; `B:real`] REAL_DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `a < u /\ u < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "bd" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "R" THEN BETA_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MP_TAC(ISPECL [`R:real->real`;
                       `rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric (V:(real->A topology)#
                          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) x +
                        &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x`; `u:real`]
                      HAS_REAL_DERIVATIVE_INV_ATREAL) THEN
        ANTS_TAC THENL
         [USE_THEN "der" (fun th -> ASM_SIMP_TAC[th]) THEN EXPAND_TAC "R" THEN
          BETA_TAC THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "R" THEN REWRITE_TAC[]];
        REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NEG; REAL_ABS_POW] THEN
        SUBGOAL_THEN `&0 < abs(rfs_vscalar (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u x) pow 2`
        ASSUME_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s1:real`; `s0:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `B * abs(s1 - s0) <= B * (b - a)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* R stays above 1/F near b, and R is continuous up to b *)
  ABBREV_TAC `F0 = inv((R:real->real) s0) + B * (b - a)` THEN
  SUBGOAL_THEN `&0 < F0` ASSUME_TAC THENL
   [USE_THEN "lip" (MP_TAC o SPEC `s0:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "bd" (MP_TAC o SPEC `s0:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "R" THEN BETA_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < inv(rfs_vscalar (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s0 x)`
    MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s1. s0 <= s1 /\ s1 < b ==> inv F0 <= (R:real->real) s1` (LABEL_TAC "low")
  THENL
   [X_GEN_TAC `s1:real` THEN STRIP_TAC THEN
    USE_THEN "lip" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "bd" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "R" THEN BETA_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(rfs_vscalar (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s1 x)`;
                   `F0:real`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; REWRITE_TAC[REAL_INV_INV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `x:A`; `s0:real`]
                P2C_VIEW_SCALAR_CONT_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> q ==> F) ==> q ==> p`) THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `inv F0`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))) THEN
  ABBREV_TAC `s2 = b - min (dd / &2) ((b - s0) / &2)` THEN
  SUBGOAL_THEN `s0 <= s2 /\ s2 < b /\ abs(s2 - b) < dd` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "low" (MP_TAC o SPEC `s2:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "dd" (MP_TAC o SPEC `s2:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "R" THEN BETA_TAC THEN
  UNDISCH_TAC `~(&0 < rfs_vscalar (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b x)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* T5: helpers on regular views (slices, the view family on W,               *)
(* parametrizations by inverse charts) and the uniform bound Kr on the       *)
(* derivatives of the rescaled curvature at times close to the end time.     *)
(* ------------------------------------------------------------------------- *)

let SNGL_VIEW_FACTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ a < u /\ u <= b /\
     ~(W = {})
     ==> smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
         open_in (rfs_vtop V u) W /\
         riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
         smooth_manifold_atlas (subtopology (rfs_vtop V b) W)
                               (restrict_atlas (rfs_vatlas V b) W) /\
         riemannian_metric (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b u) /\
         rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W) a b
                       (p2c_vfam V W b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`]
                P2CV_PERSISTS_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?y:A. y IN W` STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (W:A->bool)`)) THEN
    UNDISCH_TAC `(y:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `u:real`; `y:A`] SNGL_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W) a b
      (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) W b)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN
    REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[p2c_vflow] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
                 a b (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W b)` THEN
  REWRITE_TAC[rfs_flow_upto; ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u:real = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* A parametrization of a neighbourhood of y in W by an inverse chart of the *)
(* atlas at b, valid at all times of the window.                            *)

let SNGL_VIEW_PARAM_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b y.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ y IN W
     ==> ?S (e:real^3->A) z.
           open S /\ z IN S /\ e z = y /\ IMAGE e S SUBSET W /\
           mfd_param (subtopology (rfs_vtop V b) W) (restrict_atlas (rfs_vatlas V b) W) S e /\
           !u. a < u /\ u <= b
               ==> mfd_param (rfs_vtop V u) (rfs_vatlas V u) S e /\
                   !z'. z' IN S
                        ==> rfs_pullback (restrict_atlas (rfs_vatlas V b) W) e
                                         (p2c_vfam V W b u) z' =
                            rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `b:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b`; `W:A->bool`; `y:A`]
                MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b`;
                 `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "inv" o CONJUNCT1) THEN
  EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN
  EXISTS_TAC `chart_inv (U:A->bool,phi:A->real^3)` THEN
  EXISTS_TAC `(phi:A->real^3) y` THEN
  SUBGOAL_THEN
   `open (IMAGE (phi:A->real^3) (U INTER W)) /\
    mfd_param (rfs_vtop V b) (rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b)
      (IMAGE phi (U INTER W)) (chart_inv (U,phi)) /\
    IMAGE (chart_inv (U,phi)) (IMAGE phi (U INTER W)) SUBSET (W:A->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                            `rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN
      CONJ_TAC THENL [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
                              `rfs_vatlas (V:(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`] THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
      REPEAT STRIP_TAC THEN USE_THEN "inv" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`;
                 `chart_inv (U:A->bool,phi:A->real^3)`; `IMAGE (phi:A->real^3) (U INTER W)`]
                P3H_VFLOW_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vf"))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    USE_THEN "inv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real` THEN DISCH_TAC THEN
  USE_THEN "vf" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* The curvature derivative norms of the slice at s are those of the view    *)
(* family on W.                                                              *)

let SNGL_VFAM_RMD2 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s y l.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ a < s /\ s <= b /\ y IN W
     ==> rfa_rmd2 l (rfs_vatlas V s) (rfs_vmetric V s) y =
         rfa_rmd2 l (restrict_atlas (rfs_vatlas V b) W) (p2c_vfam V W b s) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `y:A`]
                SNGL_VIEW_PARAM_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pu"))))))))) THEN
  USE_THEN "pu" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq")) THEN
  MP_TAC(ISPECL [`l:num`; `rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                 `rfs_vmetric (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`;
                 `S:real^3->bool`; `e:real^3->A`; `z:real^3`] P2AP_PULLBACK_RMD_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`l:num`; `subtopology (rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `p2c_vfam (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W b s`;
                 `S:real^3->bool`; `e:real^3->A`; `z:real^3`] P2AP_PULLBACK_RMD_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `S:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* T5: a uniform bound on the derivatives (orders <= 2) of the curvature of   *)
(* the rescaled metrics R(x,s) g(s) on K for s close to b.                    *)

let SNGL_VIEW_KR = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K x.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\
     compact_in (rfs_vtop V b) K /\ K SUBSET W /\ x IN W /\ &0 < rfs_vscalar V b x
     ==> ?d Kr. &0 < d /\
                !s y l. b - d < s /\ s <= b /\ y IN K /\ l <= 2
                        ==> lrm_deriv_norm2 l
                              (metric_local (rfs_vatlas V s) (chart_at (rfs_vatlas V s) y)
                                 (\z. rfs_vscalar V s x %% rfs_vmetric V s z))
                              (SND(chart_at (rfs_vatlas V s) y) y) <= Kr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R0 = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b x` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `K:A->bool`; `x:A`;
                 `0`; `&1`] SNGL_VIEW_DRIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
  (* the unscaled bound, uniform on K *)
  SUBGOAL_THEN
   `?d2. &0 < d2 /\
         !y. y IN K
             ==> !s. b - d2 < s /\ s <= b
                     ==> !l. l <= 2
                             ==> rfa_rmd2 l (rfs_vatlas V s)
                                   (rfs_vmetric (V:(real->A topology)#
                                      (real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) s) y <= inv d2`
  (X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THENL
   [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) b`; `K:A->bool`;
                   `\d (y:A). !s. b - d < s /\ s <= b
                                  ==> !l. l <= 2
                                          ==> rfa_rmd2 l (rfs_vatlas V s)
                                                (rfs_vmetric (V:(real->A topology)#
                                                   (real->((A->bool)#(A->real^3))->bool)#
                                                   (real->A->real^3^3)) s) y <= inv d`]
                  SNGL_COMPACT_UNIFORM) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      MAP_EVERY X_GEN_TAC [`dd:real`; `dd':real`; `yy:A`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd"))) THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv dd:real` THEN
      CONJ_TAC THENL
       [USE_THEN "pd" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]] THEN
    X_GEN_TAC `p0:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p0:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `b:real`]
                  SNGL_VIEW_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(p0:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W)`
    ASSUME_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`)) THEN
      UNDISCH_TAC `(p0:A) IN W` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `p0:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c = chart_at (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (p0:A)` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `Vc = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
    SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) p0 IN Vc` ASSUME_TAC THENL
     [EXPAND_TAC "Vc" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* the smooth extension in the chart c *)
    UNDISCH_TAC `rfs_flow_upto (subtopology (rfs_vtop V b) W,restrict_atlas (rfs_vatlas V b) W)
                   a b (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) W b)` THEN
    REWRITE_TAC[rfs_flow_upto] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e0:real`
      (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fx"))))) THEN
    SUBGOAL_THEN
     `!t. a < t /\ t <= b
          ==> metric_field Vc (metric_local (restrict_atlas (rfs_vatlas V b) W) c
                 (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W b t))`
    (LABEL_TAC "mft") THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `t:real`]
                    SNGL_VIEW_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Vc:real^3->bool`; `a:real`; `b:real`; `e0:real`;
                   `\t. metric_local (restrict_atlas (rfs_vatlas V b) W) (c:(A->bool)#(A->real^3))
                          (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) W b t)`;
                   `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`; `4`]
                  SNGL_LCK_EXT_CONTINUOUS_UPTO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN USE_THEN "mft" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN BETA_TAC THEN USE_THEN "fx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_TAC THEN
    (* a compact ball in the chart and uniform continuity *)
    UNDISCH_TAC `open (Vc:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^3)) p0`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `tl = (a + b) / &2` THEN
    SUBGOAL_THEN `a < tl /\ tl < b` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "tl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\w. lift(lck_dist2 4
             (metric_local (restrict_atlas (rfs_vatlas V b) W) (c:(A->bool)#(A->real^3))
                (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) W b b))
             (metric_local (restrict_atlas (rfs_vatlas V b) W) c
                (p2c_vfam V W b (drop(fstcart w)))) (sndcart w)))
      uniformly_continuous_on
      (interval[lift tl,lift b] PCROSS cball(SND c p0,r))`
    MP_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
      SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN
    REWRITE_TAC[REAL_HALF; REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
    (* closeness in C^4 on the ball for t near b *)
    SUBGOAL_THEN
     `!t z. b - min del (b - tl) < t /\ t <= b /\ z IN cball(SND(c:(A->bool)#(A->real^3)) p0,r)
            ==> lck_dist2 4
                  (metric_local (restrict_atlas (rfs_vatlas V b) W) c
                     (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W b b))
                  (metric_local (restrict_atlas (rfs_vatlas V b) W) c (p2c_vfam V W b t)) z
                < &1 / &2`
    (LABEL_TAC "cl4") THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "uc" (MP_TAC o SPECL [`pastecart (lift b) (z:real^3)`;
                                     `pastecart (lift t) (z:real^3)`]) THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
        REWRITE_TAC[dist; PASTECART_SUB; VECTOR_SUB_REFL] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(lift t - lift b) + norm(vec 0:real^3)` THEN
        REWRITE_TAC[NORM_PASTECART_LE; NORM_0; REAL_ADD_RID; GSYM LIFT_SUB; NORM_LIFT] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[P2BL_LCK_DIST2_REFL; DIST_LIFT] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* the jet bounds from C^4 closeness *)
    SUBGOAL_THEN
     `?C. !l G y. l <= 2 /\ metric_field Vc G /\
                  (!z. z IN cball(SND(c:(A->bool)#(A->real^3)) p0,r)
                       ==> lck_dist2 4
                             (metric_local (restrict_atlas (rfs_vatlas V b) W) c
                                (p2c_vfam (V:(real->A topology)#
                                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                   W b b)) G z < &1 / &2) /\
                  y IN cball(SND c p0,r)
                  ==> lrm_deriv_norm2 l G y <= C`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `!l. l <= 2
            ==> ?C. !G y. metric_field Vc G /\
                          (!z. z IN cball(SND(c:(A->bool)#(A->real^3)) p0,r)
                               ==> lck_dist2 4
                                     (metric_local (restrict_atlas (rfs_vatlas V b) W) c
                                        (p2c_vfam (V:(real->A topology)#
                                           (real->((A->bool)#(A->real^3))->bool)#
                                           (real->A->real^3^3)) W b b)) G z < &1 / &2) /\
                          y IN cball(SND c p0,r)
                          ==> lrm_deriv_norm2 l G y <= C`
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CJ_RMD2_FROM_LCK THEN
        ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        CONJ_TAC THENL
         [USE_THEN "mft" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                           MP_TAC(SPEC `2` th)) THEN
      REWRITE_TAC[ARITH] THEN
      DISCH_THEN(X_CHOOSE_TAC `C2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `C1:real`) THEN
      DISCH_THEN(X_CHOOSE_TAC `C0:real`) THEN
      EXISTS_TAC `max C0 (max C1 C2)` THEN
      REWRITE_TAC[ARITH_RULE `l <= 2 <=> l = 0 \/ l = 1 \/ l = 2`] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `C0:real`; EXISTS_TAC `C1:real`; EXISTS_TAC `C2:real`] THEN
      (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);
      ALL_TAC] THEN
    (* the neighbourhood N of p0 and the local time window *)
    EXISTS_TAC `{q:A | q IN FST(c:(A->bool)#(A->real^3)) /\ SND c q IN ball(SND c p0,r)}` THEN
    EXISTS_TAC `min (min del (b - tl)) (inv(max C (&1)))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                     `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`;
                     `ball(SND(c:(A->bool)#(A->real^3)) p0,r)`] GRGD_CHART_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; OPEN_BALL];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (subtopology (rfs_vtop (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W) (FST(c:(A->bool)#(A->real^3)))`)) THEN
      UNDISCH_TAC `(y:A) IN FST(c:(A->bool)#(A->real^3))` THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`; `y:A`;
                   `l:num`] SNGL_VFAM_RMD2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`]
                  SNGL_VIEW_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
                    STRIP_TAC] THEN
    MP_TAC(ISPECL [`l:num`; `subtopology (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W b s`;
                   `c:(A->bool)#(A->real^3)`; `y:A`] RFA_RMD2_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C:real` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "mft" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN USE_THEN "cl4" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `SND(c:(A->bool)#(A->real^3)) y IN ball(SND c p0,r)` THEN
        REWRITE_TAC[IN_BALL; IN_CBALL] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `max C (&1)` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
        MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* combine with the scale R(x,s) *)
  EXISTS_TAC `min (min d1 d2) (b - a)` THEN EXISTS_TAC `(&1 + &2 / R0) pow 4 * inv d2` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`; `l:num`] THEN REWRITE_TAC[REAL_LT_MIN] THEN
  STRIP_TAC THEN
  USE_THEN "d1" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `Q = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x` THEN
  SUBGOAL_THEN `(y:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))`; `W:A->bool`; `a:real`; `b:real`; `s:real`] SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
                  STRIP_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (W:A->bool)`)) THEN
    UNDISCH_TAC `(y:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cs = chart_at (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (y:A)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(cs:(A->bool)#(A->real^3))) (FST cs))
                  (metric_local (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) cs (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "d2" (MP_TAC o SPEC `y:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[rfa_rmd2] THEN DISCH_TAC THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`IMAGE (SND(cs:(A->bool)#(A->real^3))) (FST cs)`;
                 `metric_local (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (cs:(A->bool)#(A->real^3)) (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s)`;
                 `Q:real`; `l:num`; `SND(cs:(A->bool)#(A->real^3)) y`]
                RFA_LRM_DERIV_NORM2_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv Q pow (l + 2) * inv d2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + &2 / R0) pow (l + 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(R0 / &2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_DIV] THEN
    SUBGOAL_THEN `&0 < &2 / R0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < &2 / R0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The cap, C-component and round-component cases of the limit transfer:     *)
(* canonical neighbourhoods of one type at times accumulating at T0 give one *)
(* of the same type at T0 (the typed uniform transfers of Part 2B, with the  *)
(* identity as the diffeomorphism, Kr from T5 and the closeness from T3).    *)
(* ------------------------------------------------------------------------- *)

let SNGL_MCLOSE_SUBSET = prove
 (`!k eps (atlas:((A->bool)#(A->real^N))->bool) K U g0 g.
     rfs_mclose k eps atlas K g0 g /\ U SUBSET K ==> rfs_mclose k eps atlas U g0 g`,
  REWRITE_TAC[rfs_mclose; SUBSET] THEN MESON_TAC[]);;

let SNGL_SOURCE_FACTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W eta T0 K x s U.
     p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\ K SUBSET W /\
     x IN K /\ T0 - eta < s /\ s < T0 /\ open_in (rfs_vtop V s) U /\ U SUBSET K
     ==> hausdorff_space (rfs_vtop V s) /\
         smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
         riemannian_metric (rfs_vatlas V s) (rfs_vmetric V s) /\
         hausdorff_space (rfs_vtop V T0) /\
         smooth_manifold_atlas (rfs_vtop V T0) (rfs_vatlas V T0) /\
         riemannian_metric (rfs_vatlas V T0) (rfs_vmetric V T0) /\
         mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) U (rfs_vtop V T0) (rfs_vatlas V T0)
                    (IMAGE (\y:A. y) U) (\y. y) (\y. y) /\
         rfs_vscalar V s x = mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
  SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`; `s:real`]
                P2CV_PERSISTS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`; `T0:real`]
                P2CV_PERSISTS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) s) /\
    x IN topspace(rfs_vtop V T0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (W:A->bool)`));
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in (rfs_vtop (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0) (W:A->bool)`))] THEN
    UNDISCH_TAC `(x:A) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `s:real`; `x:A`] SNGL_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `T0:real`; `x:A`] SNGL_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN MAP_EVERY EXISTS_TAC [`W:A->bool`; `W:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  UNDISCH_TAC `p2c_regular_view (V:(real->A topology)#
    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))` THEN
  REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `T0 - eta:real`; `T0:real`; `s:real`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* Caps at times accumulating at T0 give a (C', eps')-cap at T0 with x in    *)
(* the core.                                                                 *)

let SNGL_CAP_CASE = prove
 (`?Kcap eps0cap. &1 <= Kcap /\ &0 < eps0cap /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      C eps C' eps' T0 x eta W K.
       p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\
       compact_in (rfs_vtop V T0) K /\ K SUBSET W /\ x IN K /\ &0 < rfs_vscalar V T0 x /\
       &1 < C /\ &2 * C <= C' /\ &0 < eps /\ Kcap * eps <= eps' /\ eps' <= eps0cap /\
       (!d. &0 < d
            ==> ?s U Y. T0 - d < s /\ s < T0 /\
                        rfs_cap (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) C eps U Y /\
                        x IN Y /\ U SUBSET K)
       ==> ?U' Y'. rfs_cap (rfs_vtop V T0,rfs_vatlas V T0) (rfs_vmetric V T0) C' eps' U' Y' /\
                   x IN Y'`,
  MP_TAC(INST_TYPE [`:A`,`:B`] P2BF_CAP_FIX_GEN) THEN
  DISCH_THEN(X_CHOOSE_THEN `Kcap:real` (X_CHOOSE_THEN `eps0cap:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fix"))))) THEN
  MAP_EVERY EXISTS_TAC [`Kcap:real`; `eps0cap:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq"))))))))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`;
                 `K:A->bool`; `x:A`] SNGL_VIEW_KR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d5:real` (X_CHOOSE_THEN `Kr:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kr")))) THEN
  USE_THEN "fix" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`;
                 `K:A->bool`; `x:A`; `rfs_kreg delta`; `delta:real`] SNGL_VIEW_DRIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dr"))) THEN
  USE_THEN "freq" (MP_TAC o SPEC `min (min d5 d3) eta`) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `Y:A->bool`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `T0 - eta < s /\ T0 - d5 < s /\ T0 - d3 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (U:A->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_cap (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s)
      (rfs_vmetric V s) C eps U (Y:A->bool)` THEN SIMP_TAC[rfs_cap];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`; `K:A->bool`;
                 `x:A`; `s:real`; `U:A->bool`] SNGL_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "dr" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  USE_THEN "tr" (MP_TAC o SPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) s`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
     `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) T0`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) T0`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) T0`;
     `x:A`; `U:A->bool`; `Y:A->bool`; `\y:A. y`; `\y:A. y`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN REWRITE_TAC[IMAGE_ID] THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `K:A->bool` THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) (x:A) =
                    rfs_vscalar (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "kr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      MATCH_MP_TAC SNGL_MCLOSE_SUBSET THEN EXISTS_TAC `K:A->bool` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) (x:A) =
                    rfs_vscalar (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `Y':A->bool`
    (STRIP_ASSUME_TAC o BETA_RULE))) THEN
  MAP_EVERY EXISTS_TAC [`U':A->bool`; `Y':A->bool`] THEN ASM_REWRITE_TAC[]);;

(* C-components at times accumulating at T0 give a C'-component at T0.      *)

let SNGL_CCOMP_CASE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C C' T0 x eta W K.
     p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\
     compact_in (rfs_vtop V T0) K /\ K SUBSET W /\ x IN K /\ &0 < rfs_vscalar V T0 x /\
     &1 < C /\ &2 * C <= C' /\
     (!d. &0 < d
          ==> ?s U. T0 - d < s /\ s < T0 /\ x IN U /\
                    rfs_c_component (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s) C U /\
                    U SUBSET K)
     ==> ?U'. x IN U' /\
              rfs_c_component (rfs_vtop V T0,rfs_vatlas V T0) (rfs_vmetric V T0) C' U'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq")))))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`;
                 `K:A->bool`; `x:A`] SNGL_VIEW_KR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d5:real` (X_CHOOSE_THEN `Kr:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kr")))) THEN
  MP_TAC(MATCH_MP (INST_TYPE [`:A`,`:B`] P2BS_CCOMP_UNIF) P2B_REQ_LRG_DERIV) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:real`; `C':real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`;
                 `K:A->bool`; `x:A`; `rfs_kreg delta`; `delta:real`] SNGL_VIEW_DRIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dr"))) THEN
  USE_THEN "freq" (MP_TAC o SPEC `min (min d5 d3) eta`) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `T0 - eta < s /\ T0 - d5 < s /\ T0 - d3 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) /\
    U IN connected_components_of (rfs_vtop V s) /\ compact_in (rfs_vtop V s) (U:A->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_c_component (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s)
      (rfs_vmetric V s) C (U:A->bool)` THEN SIMP_TAC[rfs_c_component];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (U:A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`; `K:A->bool`;
                 `x:A`; `s:real`; `U:A->bool`] SNGL_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "dr" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `U = IMAGE (\y:A. y) U` SUBST1_TAC THENL [REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
  USE_THEN "tr" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) s`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
     `x:A`; `\y:A. y`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) (x:A) =
                  rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "kr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_COMPONENT_IMAGE) THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) s`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) T0`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SNGL_MCLOSE_SUBSET THEN EXISTS_TAC `K:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) (x:A) =
                  rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

(* eps-round components at times accumulating at T0 give an eps'-round       *)
(* component at T0.                                                          *)

let SNGL_ROUND_CASE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps eps' T0 x eta W K.
     p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\
     compact_in (rfs_vtop V T0) K /\ K SUBSET W /\ x IN K /\ &0 < rfs_vscalar V T0 x /\
     &0 < eps /\ &2 * eps <= eps' /\ eps' <= &1 / &40 /\
     (!d. &0 < d
          ==> ?s U. T0 - d < s /\ s < T0 /\ x IN U /\
                    rfs_round_component (rfs_vtop V s,rfs_vatlas V s) (rfs_vmetric V s)
                                        eps U /\
                    U SUBSET K)
     ==> ?U'. x IN U' /\
              rfs_round_component (rfs_vtop V T0,rfs_vatlas V T0) (rfs_vmetric V T0) eps' U'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq"))))))))))) THEN
  MP_TAC(ISPECL [`eps:real`; `eps':real`] (INST_TYPE [`:A`,`:B`] P2BS_ROUND_UNIF)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`;
                 `K:A->bool`; `x:A`; `rfs_kreg delta`; `delta:real`] SNGL_VIEW_DRIFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dr"))) THEN
  USE_THEN "freq" (MP_TAC o SPEC `min d3 eta`) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `T0 - eta < s /\ T0 - d3 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) /\
    U IN connected_components_of (rfs_vtop V s) /\ compact_in (rfs_vtop V s) (U:A->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_round_component (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,rfs_vatlas V s)
      (rfs_vmetric V s) eps (U:A->bool)` THEN SIMP_TAC[rfs_round_component];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (U:A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] APX_COMPONENT_OPEN) THEN
    EXISTS_TAC `rfs_vatlas (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`; `K:A->bool`;
                 `x:A`; `s:real`; `U:A->bool`] SNGL_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "dr" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `U = IMAGE (\y:A. y) U` SUBST1_TAC THENL [REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
  USE_THEN "tr" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) s`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) s`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
     `x:A`; `\y:A. y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] P2BL_COMPONENT_IMAGE) THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) s`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) T0`; `\y:A. y`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SNGL_MCLOSE_SUBSET THEN EXISTS_TAC `K:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar (rfs_vatlas V s) (rfs_vmetric V s) (x:A) =
                  rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* N1, part 1: at times u just before a strong eps-neck time s               *)
(* at x (normalized time sigma = (u - s) R(x,s) small), the pulled-back      *)
(* rescaled metric is C^4-close to the cylinder at time 0, hence             *)
(* Lap R + 2 |Ric|^2 > 0 at (x,u): R(x,.) is increasing there.               *)
(* ------------------------------------------------------------------------- *)

let SNGL_CYL0_RMD_SPHERE = prove
 (`!l. ?K0. !y:real^3. y IN sphere(vec 0,&1)
                       ==> lrm_deriv_norm2 l (cylinder_flow (&0)) y <= K0`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`l:num`; `(:real^3) DELETE vec 0`; `cylinder_flow (&0)`]
                LRM_DERIV_NORM2_CONTINUOUS) THEN
  SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. lift(lrm_deriv_norm2 l (cylinder_flow (&0)) y)`;
                 `sphere(vec 0:real^3,&1)`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_DELETE; IN_UNIV] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> x <= b`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* (1 + t)^n <= 2 when n t <= 1/2. *)

let SNGL_POW_FACTOR = prove
 (`!n t. &0 <= t /\ &n * t <= inv(&2) ==> (&1 + t) pow n <= &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(t) pow n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_N] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + &2 * (&n * t)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ASM_REAL_ARITH_TAC]);;

let SNGL_NECK_RDOT = prove
 (`?eps1. &0 < eps1 /\ eps1 <= &1 / &8 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      eps x s (e:real^3->A) u.
       p2c_regular_view V /\ &0 < eps /\ eps <= eps1 /\ rfs_strong_neck V eps x s e /\
       s - inv(&2 * &(rfs_kreg eps + 2)) / rfs_vscalar V s x < u /\ u <= s
       ==> &0 < rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) x +
                &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x`,
  (* constants *)
  MP_TAC(ISPECL [`&4`; `&1 / &16`] (INST_TYPE [`:3`,`:N`] P2C_PT_DERIV)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eta1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  MP_TAC(SPEC `0` SNGL_CYL0_RMD_SPHERE) THEN
  DISCH_THEN(X_CHOOSE_THEN `K00:real` (LABEL_TAC "k0")) THEN
  MP_TAC(SPEC `1` SNGL_CYL0_RMD_SPHERE) THEN
  DISCH_THEN(X_CHOOSE_THEN `K01:real` (LABEL_TAC "k1")) THEN
  MP_TAC(SPEC `2` SNGL_CYL0_RMD_SPHERE) THEN
  DISCH_THEN(X_CHOOSE_THEN `K02:real` (LABEL_TAC "k2")) THEN
  MP_TAC(MATCH_MP P2B9S_LRG_D P2B_REQ_LRG_DERIV) THEN
  DISCH_THEN(MP_TAC o SPECL [`max K00 (max K01 K02)`; `&1 / &16`]) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eta2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lrg"))) THEN
  ABBREV_TAC `eta = min eta1 (eta2 pow 2 / &2)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= eta1 /\ eta < eta2 pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < eta2 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < eta1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &8) (sqrt eta / &6)` THEN
  SUBGOAL_THEN `&0 < sqrt eta` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `eps:real`; `x:A`; `s:real`; `e:real^3->A`;
                       `u:real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  ABBREV_TAC `V = (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
                   G:real->A->real^3^3)` THEN
  ABBREV_TAC `R = rfs_vscalar (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x` THEN
  ABBREV_TAC `sg = (u - s) * R` THEN
  ABBREV_TAC `k = rfs_kreg eps` THEN
  SUBGOAL_THEN `4 <= k /\ &k <= inv eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_KREG_FOUR THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[RFS_KREG] THEN REWRITE_TAC[FLOOR]];
    ALL_TAC] THEN
  (* the neck at s *)
  UNDISCH_TAC `rfs_strong_neck (V:(real->A topology)#
    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) eps x s e` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  EXPAND_TAC "V" THEN
  REWRITE_TAC[rfs_strong_neck; rfs_evolving_neck; rfs_vatlas; rfs_vmetric] THEN
  SUBGOAL_THEN `mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) s)
                  ((G:real->A->real^3^3) s) x = R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN EXPAND_TAC "V" THEN REWRITE_TAC[rfs_vscalar]; ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl")))))) THEN
  SUBGOAL_THEN `&0 < R /\ ?y0. y0 IN sphere(vec 0,&1) /\ (e:real^3->A) y0 = x`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nk" (MP_TAC o REWRITE_RULE[rfs_neck; IN_IMAGE]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y1:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC))
      (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y1:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the normalized time *)
  SUBGOAL_THEN `&0 < &(k + 2) /\ inv(&2 * &(k + 2)) < eps / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `inv eps < &(k + 2)` ASSUME_TAC THENL
     [MP_TAC(SPEC `inv eps` FLOOR) THEN
      SUBGOAL_THEN `floor(inv eps) = &k` SUBST1_TAC THENL
       [EXPAND_TAC "k" THEN ASM_SIMP_TAC[RFS_KREG]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2 * &(k + 2)) = inv(&2) * inv(&(k + 2))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&(k + 2)) < eps` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_SIMP_TAC[REAL_LT_INV];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sg) < inv(&2 * &(k + 2)) /\ --(&1) < sg /\ sg <= &0 /\ s + sg / R = u`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `--(inv(&2 * &(k + 2))) < sg /\ sg <= &0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "sg" THEN CONJ_TAC THENL
       [SUBGOAL_THEN `--(inv(&2 * &(k + 2))) = --(inv(&2 * &(k + 2)) / R) * R`
        SUBST1_TAC THENL
         [MATCH_MP_TAC(REAL_FIELD `~(R = &0) ==> --c = --(c / R) * R`) THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC(REAL_ARITH `&0 <= (s - u) * R ==> (u - s) * R <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    EXPAND_TAC "sg" THEN MATCH_MP_TAC(REAL_FIELD `~(R = &0) ==> s + ((u - s) * R) / R = u`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* slice facts at u *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`; `e:real^3->A`;
                 `sg:real`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN REWRITE_TAC[rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Gp = rfs_pullback ((AT:real->((A->bool)#(A->real^3))->bool) u) (e:real^3->A)
                                ((G:real->A->real^3^3) u)` THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (Gp:real^3->real^3^3) /\
                metric_field (rfs_neck_dom eps) (\z. R %% (Gp:real^3->real^3^3) z)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "Gp" THEN MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `(TM:real->A topology) u` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  (* the closeness at sg, and at the cylinder at time 0 *)
  USE_THEN "cl" (MP_TAC o SPECL [`sg:real`; `y0:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `&0`; `sg:real`; `rfs_neck_dom eps`;
                 `\z. R %% (Gp:real^3->real^3^3) z`; `y0:real^3`] P2B9_CYL_BASE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[APX_NECK_DOM_NONZERO; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + abs(&0 - sg)) pow (k + 2) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_POW_FACTOR THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(k + 2) * inv(&2 * &(k + 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN
      MATCH_MP_TAC(REAL_FIELD `~(n = &0) ==> n * inv(&2 * n) = inv(&2)`) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 k (cylinder_flow sg) (\z. R %% (Gp:real^3->real^3^3) z) y0)
                < eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= y`) THEN MATCH_MP_TAC POW_2_SQRT THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (cylinder_flow (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    REWRITE_TAC[APX_NECK_DOM_NONZERO; APX_NECK_DOM_OPEN] THEN
    MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow (&0)) (\z. R %% (Gp:real^3->real^3^3) z) y0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lck_dist2 4 (cylinder_flow (&0)) (\z. R %% (Gp:real^3->real^3^3) z) y0 <= eta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 k (cylinder_flow (&0)) (\z. R %% (Gp:real^3->real^3^3) z) y0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(lck_dist2 k (cylinder_flow (&0)) (\z. R %% (Gp:real^3->real^3^3) z) y0)
      <= &4 * eps` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `a <= b ==> b <= c ==> a <= c`)) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (eps + eps)` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + &2 * b`) THEN
        REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC SQRT_POS_LE THEN
        MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        REWRITE_TAC[APX_NECK_DOM_NONZERO; APX_NECK_DOM_OPEN] THEN
        MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * eps) pow 2` THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `lck_dist2 k (cylinder_flow (&0)) (\z. R %% (Gp:real^3->real^3^3) z) y0`
                   SQRT_POW_2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * sqrt eta / &6) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the model values *)
  SUBGOAL_THEN `~((y0:real^3) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(y0:real^3) IN sphere(vec 0,&1)` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
                                 `\z. R %% (Gp:real^3->real^3^3) z`; `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT1 P2C_CYL_MODEL) THEN
      MP_TAC(SPEC `eps:real` APX_NECK_DOM_NONZERO) THEN ASM SET_TAC[];
      MATCH_MP_TAC(el 3 (CONJUNCTS P2C_CYL_MODEL)) THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  USE_THEN "lrg" (MP_TAC o SPECL [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
                                  `\z. R %% (Gp:real^3->real^3^3) z`; `y0:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K00:real` THEN CONJ_TAC THENL
       [USE_THEN "k0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K01:real` THEN CONJ_TAC THENL
       [USE_THEN "k1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K02:real` THEN CONJ_TAC THENL
       [USE_THEN "k2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(el 2 (CONJUNCTS P2C_CYL_MODEL)) THEN
  DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the reading of the manifold quantities at x and u *)
  MP_TAC(ISPECL [`(TM:real->A topology) u`; `(AT:real->((A->bool)#(A->real^3))->bool) u`;
                 `(G:real->A->real^3^3) u`; `rfs_neck_dom eps`; `e:real^3->A`; `y0:real^3`]
                P2C_PARAM_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_neck_dom eps`; `Gp:real^3->real^3^3`; `R:real`; `y0:real^3`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `abs(llap (\z. R %% (Gp:real^3->real^3^3) z) (lscalar (\z. R %% Gp z)) y0) <= &1 / &4`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`llap (\z. R %% (Gp:real^3->real^3^3) z) (lscalar (\z. R %% Gp z)) y0`;
                   `&1 / &4`] REAL_LE_SQUARE_ABS) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 < R pow 2 *
         (llap (\z. R %% (Gp:real^3->real^3^3) z) (lscalar (\z. R %% Gp z)) y0 +
          &2 * ltnorm2 2 (\z. R %% Gp z) (lric2 (\z. R %% Gp z)) y0)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* N1, part 2: if strong eps-necks at x occur at times accumulating at T0,   *)
(* then R(x,.) is nondecreasing on a left neighbourhood of T0.               *)

let SNGL_NECK_RMONO = prove
 (`?eps1. &0 < eps1 /\ eps1 <= &1 / &8 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      W eta T0 x eps.
       p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\ x IN W /\
       &0 < eps /\ eps <= eps1 /\
       (!d. &0 < d ==> ?s e. T0 - d < s /\ s < T0 /\ rfs_strong_neck V eps x s e)
       ==> ?d. &0 < d /\
               !s1 s2. T0 - d < s1 /\ s1 <= s2 /\ s2 <= T0
                       ==> rfs_vscalar V s1 x <= rfs_vscalar V s2 x`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "rd"))) (INST_TYPE [`:A`,`:A`] SNGL_NECK_RDOT) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "freq"))))))) THEN
  (* continuity and a bound for R(x,.) on [T0 - eta/2, T0] *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta:real`; `T0:real`; `x:A`;
                 `T0 - eta / &2`] P2C_VIEW_SCALAR_CONT_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\u. rfs_vscalar (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u x`;
                 `real_interval[T0 - eta / &2,T0]`] REAL_CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[REAL_COMPACT_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `um:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mx"))) THEN
  ABBREV_TAC `Rm = max (rfs_vscalar (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) um x) (&1)` THEN
  ABBREV_TAC `c = inv(&2 * &(rfs_kreg eps + 2))` THEN
  SUBGOAL_THEN `&0 < c /\ &0 < Rm` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "Rm"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
      ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* R increases on (T0 - d, T0) *)
  ABBREV_TAC `d = min (eta / &2) (c / Rm)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. T0 - d < u /\ u < T0
        ==> ((\u. rfs_vscalar (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u x)
             has_real_derivative
             (rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) x +
              &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x)) (atreal u) /\
            &0 < rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) x +
                 &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x`
  (LABEL_TAC "inc") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `T0 - eta / &2 < u /\ T0 - c / Rm < u` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `T0 - d < u` THEN EXPAND_TAC "d" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_VIEW_SCALAR_EVOL THEN
      MAP_EVERY EXISTS_TAC [`W:A->bool`; `T0 - eta:real`; `T0:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "freq" (MP_TAC o SPEC `T0 - u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC)) THEN
    USE_THEN "rd" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `s:real`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `&0 < rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x /\
                  rfs_vscalar V s x <= Rm` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`;
                       `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
        ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN ANTS_TAC THENL
         [REAL_ARITH_TAC; SIMP_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `rfs_vscalar (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) um x` THEN
        CONJ_TAC THENL
         [USE_THEN "mx" (MP_TAC o SPEC `s:real`) THEN BETA_TAC THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "Rm" THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `c / Rm <= c / rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s x`
    MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s1:real = s2` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. rfs_vscalar (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u x`;
                 `\u. rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) x +
                      &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x`;
                 `s1:real`; `s2:real`] REAL_MVT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[T0 - eta / &2,T0]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      UNDISCH_TAC `T0 - d < s1` THEN EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `w:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      USE_THEN "inc" (MP_TAC o SPEC `w:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  USE_THEN "inc" (MP_TAC o SPEC `w:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 <= (rfs_scalar_lap (rfs_vatlas V w) (rfs_vmetric (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) w) x +
                  &2 * rfs_ric_norm2 (rfs_vatlas V w) (rfs_vmetric V w) x) * (s2 - s1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* N2: the neck case.  If strong eps-necks at x accumulate at                *)
(* T0 from below inside K, one of them, e at time s close to T0, is a strong *)
(* (2 eps)-neck at (x, T0) with the same parametrization: before s the       *)
(* closeness comes from the neck itself (rescaling R(x,s) -> R(x,T0), shift  *)
(* of the cylinder time); after s it comes from the closeness of the metrics *)
(* at times near T0 to the metric at T0 (SNGL_TUBE_UPTO) and two base        *)
(* changes (P2B9S_CLOSE_TRIANGLE).                                           *)
(* ------------------------------------------------------------------------- *)

let SNGL_NECK_ARITH = prove
 (`!eps c P w.
     &0 < eps /\ eps <= &1 /\ &1 <= c /\ c <= &1 + eps / &32 /\
     &0 <= P /\ P <= &17 / &16 /\ &0 <= w /\ &32 * w <= eps
     ==> c * (P * (&17 / &16 * eps + &2 * w)) + abs(c - &1) * sqrt(&3) <= &3 / &2 * eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&3) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) * sqrt(&3) <= eps / &32 * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `P * (&17 / &16 * eps + &2 * w) <= &17 / &16 * (&18 / &16 * eps)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (P * (&17 / &16 * eps + &2 * w)) <=
                &17 / &16 * (&17 / &16 * (&18 / &16 * eps))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Rescaling and cylinder-time shift at one point of the neck domain.       *)

let SNGL_CYL_RESCALE = prove
 (`!k eps (G:real^3->real^3^3) s s' w c b y.
     metric_field (rfs_neck_dom eps) G /\ y IN rfs_neck_dom eps /\
     s <= &0 /\ s' <= &0 /\ abs(s - s') <= w /\ w <= &1 / &2 /\ &0 < c /\
     sqrt(lck_dist2 k (cylinder_flow s') G y) <= b
     ==> sqrt(lck_dist2 k (cylinder_flow s) (\z. c %% G z) y)
         <= c * ((&1 + w) pow (k + 2) * (b + &2 * w)) + abs(c - &1) * sqrt(&3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (rfs_neck_dom eps) (cylinder_flow s) /\
                metric_field (rfs_neck_dom eps) (cylinder_flow s')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `rfs_neck_dom eps`; `cylinder_flow s`; `G:real^3->real^3^3`;
                 `c:real`; `y:real^3`] LCK_DIST_RESCALE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real`; `s':real`; `rfs_neck_dom eps`; `G:real^3->real^3^3`;
                 `y:real^3`] P2B9_CYL_BASE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[P2BL_NECK_DOM_NZ] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= lck_dist2 k (cylinder_flow s') (G:real^3->real^3^3) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_LCK_DIST2_POS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + abs(s - s')) pow (k + 2) <= (&1 + w) pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + abs(s - s')) pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(lck_dist2 k (cylinder_flow s') (G:real^3->real^3^3) y)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + abs(s - s')) pow (k + 2) *
    (sqrt(lck_dist2 k (cylinder_flow s') (G:real^3->real^3^3) y) + &2 * abs(s - s'))
    <= (&1 + w) pow (k + 2) * (b + &2 * w)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c * sqrt(lck_dist2 k (cylinder_flow s) (G:real^3->real^3^3) y)
    <= c * ((&1 + w) pow (k + 2) * (b + &2 * w))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Two base changes: from the cylinder close to Rq Hs, Hs close to H0 and H0 *)
(* close to Hu (both measured with base R0 H0) to the cylinder close to      *)
(* Rq Hu.                                                                    *)

let SNGL_CHAIN2 = prove
 (`!k. ?Mb. &0 <= Mb /\
      !D (Lc:real^3->real^3^3) Hs H0 Hu Rq R0 dq th y.
        metric_field D Lc /\ metric_field D Hs /\ metric_field D H0 /\ metric_field D Hu /\
        y IN D /\ &0 < Rq /\ Rq <= R0 /\ R0 <= &2 * Rq /\ &0 <= dq /\ &0 <= th /\
        th <= &1 / &4 /\ (sqrt dq + Mb * sqrt th) pow 2 <= &1 / &4 /\
        lck_dist2 k Lc (\w. Rq %% Hs w) y <= dq /\
        lck_dist2 k (\w. R0 %% H0 w) (\w. R0 %% Hs w) y <= th /\
        lck_dist2 k (\w. R0 %% H0 w) (\w. R0 %% Hu w) y <= th
        ==> sqrt(lck_dist2 k Lc (\w. Rq %% Hu w) y) <= sqrt dq + Mb * sqrt th`,
  GEN_TAC THEN
  MP_TAC(SPEC `k:num` (INST_TYPE [`:3`,`:N`] SNGL_CK_BASE_REV)) THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M2"))) THEN
  MP_TAC(SPEC `k:num` LRG_CK_BASE_CHANGE) THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "M1"))) THEN
  ABBREV_TAC `A1 = sqrt(M1 * &3 pow k * M2)` THEN
  ABBREV_TAC `A2 = sqrt(M1 * &3 pow k)` THEN
  SUBGOAL_THEN `&0 <= A1 /\ &0 <= A2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  EXISTS_TAC `A1 + A2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt th /\ &0 <= sqrt dq` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field D (\w. Rq %% (Hs:real^3->real^3^3) w) /\
    metric_field D (\w. R0 %% (Hs:real^3->real^3^3) w) /\
    metric_field D (\w. Rq %% (H0:real^3->real^3^3) w) /\
    metric_field D (\w. R0 %% (H0:real^3->real^3^3) w) /\
    metric_field D (\w. Rq %% (Hu:real^3->real^3^3) w) /\
    metric_field D (\w. R0 %% (Hu:real^3->real^3^3) w)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + R0 / Rq) pow k <= &3 pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
    SUBGOAL_THEN `&0 <= R0 / Rq /\ R0 / Rq <= &2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `dq <= (sqrt dq + (A1 + A2) * sqrt th) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt dq pow 2 <= (sqrt dq + (A1 + A2) * sqrt th) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dq <= &1 / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* base change for Hs versus H0 *)
  SUBGOAL_THEN
   `lck_dist2 k (\w. R0 %% (Hs:real^3->real^3^3) w) (\w. R0 %% (H0:real^3->real^3^3) w) y
    <= M2 * th` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M2 * lck_dist2 k (\w. R0 %% (H0:real^3->real^3^3) w)
                                 (\w. R0 %% (Hs:real^3->real^3^3) w) y` THEN
    CONJ_TAC THENL
     [USE_THEN "M2" (MP_TAC o ISPECL [`D:real^3->bool`;
                                      `\w. R0 %% (H0:real^3->real^3^3) w`;
                                      `\w. R0 %% (Hs:real^3->real^3^3) w`;
                                      `\w. R0 %% (H0:real^3->real^3^3) w`; `y:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`k:num`; `D:real^3->bool`; `\w. R0 %% (H0:real^3->real^3^3) w`;
                     `\w. R0 %% (Hs:real^3->real^3^3) w`; `y:real^3`]
                    SNGL_LCK_DIST2_REFLECT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* first triangle: the cylinder against Rq H0 *)
  MP_TAC(ISPECL [`M1:real`; `k:num`; `k:num`; `D:real^3->bool`; `Lc:real^3->real^3^3`;
                 `Hs:real^3->real^3^3`; `H0:real^3->real^3^3`; `R0:real`; `Rq:real`;
                 `y:real^3`; `dq:real`; `M2 * th`] P2B9S_CLOSE_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(M1 * (&1 + R0 / Rq) pow k * M2 * th) <= A1 * sqrt th` ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L0 = lck_dist2 k Lc (\w. Rq %% (H0:real^3->real^3^3) w) y` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= L0` ASSUME_TAC THENL
   [EXPAND_TAC "L0" THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
    EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt L0 <= sqrt dq + A1 * sqrt th` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L0 <= (sqrt dq + A1 * sqrt th) pow 2 /\
                (sqrt dq + A1 * sqrt th) pow 2 <= &1 / &4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `sqrt L0 pow 2 <= (sqrt dq + A1 * sqrt th) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
        ASM_SIMP_TAC[SQRT_POW_2]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt dq + (A1 + A2) * sqrt th) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      SUBGOAL_THEN `&0 <= A1 * sqrt th /\ &0 <= A2 * sqrt th` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* second triangle: the cylinder against Rq Hu *)
  MP_TAC(ISPECL [`M1:real`; `k:num`; `k:num`; `D:real^3->bool`; `Lc:real^3->real^3^3`;
                 `H0:real^3->real^3^3`; `Hu:real^3->real^3^3`; `R0:real`; `Rq:real`;
                 `y:real^3`; `(sqrt dq + A1 * sqrt th) pow 2`; `th:real`]
                P2B9S_CLOSE_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt((sqrt dq + A1 * sqrt th) pow 2) = sqrt dq + A1 * sqrt th`
  SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(M1 * (&1 + R0 / Rq) pow k * th) <= A2 * sqrt th` ASSUME_TAC THENL
   [EXPAND_TAC "A2" THEN REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The tube at the end time b, read through parametrizations at time b      *)
(* with image in the compact set K.                                         *)

let SNGL_PB_TUBE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b K R k th.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\
     compact_in (rfs_vtop V b) K /\ K SUBSET W /\ &0 < R /\ &0 < th
     ==> ?d. &0 < d /\
             !u S (e:real^3->A) y.
               b - d < u /\ u <= b /\ open S /\
               mfd_param (rfs_vtop V b) (rfs_vatlas V b) S e /\ IMAGE e S SUBSET K /\ y IN S
               ==> lck_dist2 k (\w. R %% rfs_pullback (rfs_vatlas V b) e (rfs_vmetric V b) w)
                               (\w. R %% rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) w) y
                   < th`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `W:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) S SUBSET K` THEN UNDISCH_TAC `(y:real^3) IN S` THEN
    UNDISCH_TAC `(K:A->bool) SUBSET W` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `b:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W b`;
                 `a:real`; `b:real`; `R:real`; `k:num`; `K:A->bool`; `th:real`]
                SNGL_TUBE_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tube"))) THEN
  EXISTS_TAC `min d (b - a)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `S:real^3->bool`; `e:real^3->A`; `y:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `b - d < u /\ a < u` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `e:real^3->A`;
                 `S:real^3->bool`] P3H_VFLOW_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sl"))) THEN
  SUBGOAL_THEN
   `lck_dist2 k (\w. R %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) e
                                    (rfs_vmetric V b) w)
                (\w. R %% rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) w) y =
    lck_dist2 k (rfs_pullback (restrict_atlas (rfs_vatlas V b) W) e
                              (\x. R %% p2c_vfam V W b b x))
                (rfs_pullback (restrict_atlas (rfs_vatlas V b) W) e
                              (\x. R %% p2c_vfam V W b u x)) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[P2B9_RFS_PULLBACK_CMUL; ETA_AX] THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "sl" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "sl" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) W`;
                 `\x. R %% p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) W b b x`;
                 `\x. R %% p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) W b u x`;
                 `S:real^3->bool`; `e:real^3->A`; `k:num`; `y:real^3`] P2B9_LCK_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "tube" (MP_TAC o SPECL [`u:real`; `(e:real^3->A) y`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* A strong neck at s in the window of W is a parametrization at all later  *)
(* times of the window.                                                     *)

let SNGL_NECK_FWD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W eta T0 x eps s e.
     p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\
     T0 - eta < s /\ s < T0 /\ rfs_strong_neck V eps x s e /\
     IMAGE e (rfs_neck_dom eps) SUBSET W
     ==> mfd_param (rfs_vtop V T0) (rfs_vatlas V T0) (rfs_neck_dom eps) e /\
         !u. T0 - eta < u /\ u <= T0
             ==> smooth_manifold_atlas (rfs_vtop V u) (rfs_vatlas V u) /\
                 riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
                 mfd_param (rfs_vtop V u) (rfs_vatlas V u) (rfs_neck_dom eps) e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(W:A->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `T0 - eta < T0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `T0:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  MP_TAC(REWRITE_RULE[p2c_regular_view] (ASSUME
   `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3))`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `T0 - eta`; `T0:real`; `s:real`] o
             el 3 o CONJUNCTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) s`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) s`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) T0`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) T0`;
                 `rfs_neck_dom eps`; `e:real^3->A`; `W:A->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`] MFD_PARAM_COMPOSE_DIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:A. y) o (e:real^3->A) = e` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `e:real^3->A`;
                 `rfs_neck_dom eps`] P3H_VFLOW_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "sl" o CONJUNCT2 o CONJUNCT2) THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  USE_THEN "sl" (MP_TAC o SPEC `u:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `u:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[]);;

(* The target neck: a strong eps-neck e at (x, s) close to T0 with R(x, s)  *)
(* close to R(x, T0), and closeness of the rescaled metrics at later times   *)
(* to the cylinder (hypothesis ext), give a strong (2 eps)-neck at (x, T0).  *)

let SNGL_NECK_TARGET = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W eta T0 x eps s e w.
     p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\
     &0 < eps /\ eps <= &1 / &8 /\ T0 - eta < s /\ s < T0 /\
     rfs_strong_neck V eps x s e /\ IMAGE e (rfs_neck_dom eps) SUBSET W /\
     rfs_vscalar V s x <= rfs_vscalar V T0 x /\
     &32 * (rfs_vscalar V T0 x - rfs_vscalar V s x) <= eps * rfs_vscalar V s x /\
     (rfs_vscalar V T0 x - rfs_vscalar V s x) / rfs_vscalar V T0 x +
       rfs_vscalar V T0 x * (T0 - s) <= w /\
     &0 <= w /\ &32 * w <= eps /\ (&1 + w) pow (rfs_kreg eps + 2) <= &17 / &16 /\
     (!u y. s < u /\ u <= T0 /\ y IN rfs_neck_dom eps
            ==> sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
                       (\z. rfs_vscalar V s x %%
                            rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) z) y)
                <= &17 / &16 * eps)
     ==> rfs_strong_neck V (&2 * eps) x T0 e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> LABEL_TAC "ext" (last(CONJUNCTS th)) THEN STRIP_ASSUME_TAC th) THEN
  (* the source neck *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`;
                 `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT] (ASSUME
   `rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) eps x s e`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `dq:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`; `x:A`;
                 `eps:real`; `s:real`; `e:real^3->A`] SNGL_NECK_FWD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fw")) THEN
  ABBREV_TAC `Rq = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s x` THEN
  ABBREV_TAC `R0 = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) T0 x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s - &1 / Rq <= T0 - &1 / R0` (LABEL_TAC "win") THENL
   [SUBGOAL_THEN `inv R0 <= inv Rq` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom (&2 * eps) SUBSET rfs_neck_dom eps /\
                rfs_kreg (&2 * eps) <= rfs_kreg eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_DOM_MONO; MATCH_MP_TAC APX_KREG_MONO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the slices of the target window *)
  SUBGOAL_THEN
   `!u. T0 - &1 / R0 < u /\ u <= T0
        ==> smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#
               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (rfs_vatlas V u) /\
            riemannian_metric (rfs_vatlas V u) (rfs_vmetric V u) /\
            mfd_param (rfs_vtop V u) (rfs_vatlas V u) (rfs_neck_dom eps) (e:real^3->A)`
  (LABEL_TAC "sl") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < u` THENL
     [USE_THEN "fw" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s - u) * Rq < &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Rq * (s - u)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`;
                   `e:real^3->A`; `Rq * (u - s)`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s + (Rq * (u - s)) / Rq = u` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Rq` THEN CONV_TAC REAL_FIELD; SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "nk" (STRIP_ASSUME_TAC o REWRITE_RULE[rfs_neck]) THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0) (rfs_vatlas V T0) /\
    mfd_param (rfs_vtop V T0) (rfs_vatlas V T0) (rfs_neck_dom (&2 * eps)) (e:real^3->A) /\
    &0 < &2 * eps /\ (&3 / &2 * eps) pow 2 < (&2 * eps) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sl" (MP_TAC o SPEC `T0:real`) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      SUBGOAL_THEN `&0 < &1 / R0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom eps` THEN
      ASM_REWRITE_TAC[APX_NECK_DOM_OPEN];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the closeness of the target family *)
  SUBGOAL_THEN
   `!sg y. --(&1) < sg /\ sg <= &0 /\ y IN rfs_neck_dom (&2 * eps)
           ==> lck_dist2 (rfs_kreg (&2 * eps)) (cylinder_flow sg)
                 (\z. R0 %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                         (T0 + sg / R0)) (e:real^3->A) (rfs_vmetric V (T0 + sg / R0)) z) y
               <= (&3 / &2 * eps) pow 2`
  (LABEL_TAC "fam") THENL
   [MAP_EVERY X_GEN_TAC [`sg:real`; `y:real^3`] THEN STRIP_TAC THEN
    ABBREV_TAC `u = T0 + sg / R0` THEN
    SUBGOAL_THEN `T0 - &1 / R0 < u /\ u <= T0` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `--(&1) / R0 < sg / R0 /\ sg / R0 <= &0` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ALL_TAC] THEN
      EXPAND_TAC "u" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sg = R0 * (u - T0)` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN UNDISCH_TAC `&0 < R0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "sl" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `metric_field (rfs_neck_dom eps)
        (rfs_pullback (rfs_vatlas (V:(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (e:real^3->A)
           (rfs_vmetric V u))` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
      EXISTS_TAC `rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (R0 - Rq) / R0 /\ &0 <= R0 * (T0 - s) /\ &0 <= R0 * (T0 - u)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    (* the comparison time sg' of the source neck *)
    SUBGOAL_THEN
     `?sg'. sg' <= &0 /\ abs(sg - sg') <= w /\
            sqrt(lck_dist2 (rfs_kreg eps) (cylinder_flow sg')
                   (\z. Rq %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                          (e:real^3->A) (rfs_vmetric V u) z) y)
            <= &17 / &16 * eps`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `s < u` THENL
       [EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL; REAL_SUB_RZERO] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `R0 * (T0 - u) <= R0 * (T0 - s)` MP_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
          USE_THEN "ext" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      EXISTS_TAC `Rq * (u - s)` THEN
      SUBGOAL_THEN `(s - u) * Rq < &1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= Rq * (s - u)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `sg - Rq * (u - s) = sg * ((R0 - Rq) / R0) - Rq * (T0 - s)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `T0 + sg / R0 = u` THEN UNDISCH_TAC `&0 < R0` THEN
          CONV_TAC REAL_FIELD;
          ALL_TAC] THEN
        SUBGOAL_THEN `abs(sg * ((R0 - Rq) / R0)) <= (R0 - Rq) / R0 /\
                      Rq * (T0 - s) <= R0 * (T0 - s) /\ &0 <= Rq * (T0 - s)`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [REWRITE_TAC[REAL_ABS_MUL] THEN
            ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
            GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC];
        USE_THEN "cl" (MP_TAC o SPECL [`Rq * (u - s)`; `y:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `s + (Rq * (u - s)) / Rq = u` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < Rq` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt dq` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eps:real` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    (* rescale by R0 / Rq and shift the cylinder time *)
    MP_TAC(ISPECL [`rfs_kreg eps`; `eps:real`;
                   `\z. Rq %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                          (e:real^3->A) (rfs_vmetric V u) z`;
                   `sg:real`; `sg':real`; `w:real`; `R0 / Rq`; `&17 / &16 * eps`;
                   `y:real^3`] SNGL_CYL_RESCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
    SUBGOAL_THEN `R0 / Rq * Rq = R0` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Rq` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`eps:real`; `R0 / Rq`; `(&1 + w) pow (rfs_kreg eps + 2)`; `w:real`]
                  SNGL_NECK_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    ABBREV_TAC `L = lck_dist2 (rfs_kreg eps) (cylinder_flow sg)
                      (\z. R0 %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
                             (e:real^3->A) (rfs_vmetric V u) z) y` THEN
    SUBGOAL_THEN
     `metric_field (rfs_neck_dom eps) (cylinder_flow sg) /\
      metric_field (rfs_neck_dom eps)
        (\z. R0 %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
               (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
               (e:real^3->A) (rfs_vmetric V u) z)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= L /\ sqrt L <= &3 / &2 * eps` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC APX_LCK_DIST2_POS THEN
        EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L:real` THEN CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC LCK_DIST_MONO THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `L = sqrt L pow 2` SUBST1_TAC THENL
       [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]];
    ALL_TAC] THEN
  (* assembling the strong (2 eps)-neck at T0 *)
  REWRITE_TAC[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT; REAL_LT_01] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rfs_neck; GSYM P2B9_RFS_VSCALAR] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[rfs_close_on] THEN EXISTS_TAC `(&3 / &2 * eps) pow 2` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "fam" (MP_TAC o SPECL [`&0`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN DISCH_THEN ACCEPT_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "sl" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[APX_NECK_DOM_OPEN];
    REWRITE_TAC[rfs_close_fam; IN_ELIM_THM] THEN EXISTS_TAC `(&3 / &2 * eps) pow 2` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "fam" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* The neck case: necks accumulating at T0 (images in K) give a strong      *)
(* (2 eps)-neck at (x, T0) with image in K.                                  *)

let SNGL_NECK_CASE = prove
 (`?eps1. &0 < eps1 /\ eps1 <= &1 / &8 /\
     !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
      W eta T0 K x eps.
       p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\
       compact_in (rfs_vtop V T0) K /\ K SUBSET W /\ x IN K /\ &0 < eps /\ eps <= eps1 /\
       (!d. &0 < d ==> ?s e. T0 - d < s /\ s < T0 /\ rfs_strong_neck V eps x s e /\
                             IMAGE e (rfs_neck_dom eps) SUBSET K)
       ==> ?e. rfs_strong_neck V (&2 * eps) x T0 e /\
               IMAGE e (rfs_neck_dom (&2 * eps)) SUBSET K`,
  MP_TAC SNGL_NECK_RMONO THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`;
                       `K:A->bool`; `x:A`; `eps:real`] THEN
  DISCH_THEN(fun th -> LABEL_TAC "acc" (last(CONJUNCTS th)) THEN STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `T0 - eta < T0 /\ eps <= &1 / &8` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* R(x,.) is nondecreasing near T0 *)
  USE_THEN "rm" (MP_TAC o SPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`;
                                 `x:A`; `eps:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "acc" (MP_TAC o SPEC `d:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `dm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mono")))] THEN
  ABBREV_TAC `R0 = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) T0 x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL
   [USE_THEN "acc" (MP_TAC o SPEC `min dm eta`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `e0:real^3->A` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `eps:real`; `x:A`; `s0:real`; `&1`;
                   `e0:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "mono" (MP_TAC o SPECL [`s0:real`; `T0:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* constants *)
  MP_TAC(SPEC `rfs_kreg eps` SNGL_CHAIN2) THEN
  DISCH_THEN(X_CHOOSE_THEN `Mb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch"))) THEN
  ABBREV_TAC `nk = &(rfs_kreg eps + 2)` THEN
  SUBGOAL_THEN `&0 < nk` ASSUME_TAC THENL
   [EXPAND_TAC "nk" THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w = min (eps / &32) (inv(&32 * nk))` THEN
  SUBGOAL_THEN `&0 < w /\ &32 * w <= eps /\ (&1 + w) pow (rfs_kreg eps + 2) <= &17 / &16`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&32 * nk) /\ nk * inv(&32 * nk) = inv(&32)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < nk` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < w /\ &32 * w <= eps /\ nk * w <= inv(&32)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `nk * inv(&32 * nk)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_LE_REFL]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`rfs_kreg eps + 2`; `w:real`] P2B9_POW_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?th. &0 < th /\ th <= &1 / &4 /\ Mb * sqrt th <= eps / &16`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `q = (eps / &16) / (Mb + &1)` THEN
    SUBGOAL_THEN `&0 < q /\ (Mb + &1) * q = eps / &16` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_FIELD
         `~(m + &1 = &0) ==> (m + &1) * ((e / &16) / (m + &1)) = e / &16`) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `min (&1 / &4) (q pow 2)` THEN
    SUBGOAL_THEN `&0 < q pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Mb * q` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `Mb * q <= (Mb + &1) * q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  ABBREV_TAC `theta = R0 * min (w / &2) (eps / &64)` THEN
  SUBGOAL_THEN `&0 < theta /\ theta <= R0 * (w / &2) /\ theta <= R0 * (eps / &64)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "theta" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of R(x,.) at T0 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `x:A`;
                 `T0 - eta / &2`] P2C_VIEW_SCALAR_CONT_UPTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `T0:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `theta:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rc"))) THEN
  (* the tube at T0 *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `K:A->bool`;
                 `R0:real`; `rfs_kreg eps`; `th:real`] SNGL_PB_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tb"))) THEN
  (* a neck time close to T0 *)
  ABBREV_TAC `dd = min (min dm dc) (min d1 (min (eta / &2) (w / (&2 * R0))))` THEN
  SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "acc" (MP_TAC o SPEC `dd:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e:real^3->A` THEN
  SUBGOAL_THEN `rfs_neck_dom (&2 * eps) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET]] THEN
  SUBGOAL_THEN `T0 - dm < s /\ T0 - dc < s /\ T0 - d1 < s /\ T0 - eta / &2 < s /\
                T0 - s < w / (&2 * R0) /\ T0 - eta < s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `T0 - dd < s` THEN EXPAND_TAC "dd" THEN
    UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K:A->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the source closeness at time s *)
  MP_TAC(REWRITE_RULE[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT] (ASSUME
   `rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) eps x s e`)) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[rfs_close_fam; IN_ELIM_THM] o last o CONJUNCTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `dq:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `&0`))) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL;
              REAL_ARITH `--(&1) < &0`] THEN
  DISCH_THEN(LABEL_TAC "c0") THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`; `x:A`;
                 `eps:real`; `s:real`; `e:real^3->A`] SNGL_NECK_FWD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fw")) THEN
  ABBREV_TAC `Rq = rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) s x` THEN
  (* numeric facts at s *)
  SUBGOAL_THEN `&0 < Rq` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `eps:real`; `x:A`; `s:real`; `&1`;
                   `e:real^3->A`; `&0`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Rq <= R0` ASSUME_TAC THENL
   [USE_THEN "mono" (MP_TAC o SPECL [`s:real`; `T0:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 - Rq < theta` ASSUME_TAC THENL
   [USE_THEN "rc" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `R0 <= &2 * Rq /\ &32 * (R0 - Rq) <= eps * Rq` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `R0 * (eps / &64) <= R0 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R0 * (&1 / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `R0 / &2 <= Rq` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `eps * (R0 / &2) <= eps * Rq` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R0 - Rq) / R0 + R0 * (T0 - s) <= w` ASSUME_TAC THENL
   [SUBGOAL_THEN `(R0 - Rq) / R0 <= w / &2 /\ R0 * (T0 - s) <= w / &2` MP_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R0 * (w / (&2 * R0))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= b`) THEN
          UNDISCH_TAC `&0 < R0` THEN CONV_TAC REAL_FIELD]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `dq' = max (&0) dq` THEN
  SUBGOAL_THEN `&0 <= dq' /\ dq <= dq' /\ sqrt dq' <= eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dq'" THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < eps pow 2` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_LT]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt th /\ &0 <= th /\ &0 <= w` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt dq' + Mb * sqrt th) pow 2 <= &1 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&17 / &128) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL];
        ASM_REAL_ARITH_TAC];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. T0 - eta < v /\ v <= T0
        ==> metric_field (rfs_neck_dom eps)
              (rfs_pullback (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) v) (e:real^3->A)
                 (rfs_vmetric V v))`
  (LABEL_TAC "mf") THENL
   [X_GEN_TAC `v:real` THEN DISCH_TAC THEN
    USE_THEN "fw" (MP_TAC o SPEC `v:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) v` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (rfs_neck_dom eps) (cylinder_flow (&0)) /\
    metric_field (rfs_neck_dom eps)
      (rfs_pullback (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (e:real^3->A)
         (rfs_vmetric V s)) /\
    metric_field (rfs_neck_dom eps)
      (rfs_pullback (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0) (e:real^3->A)
         (rfs_vmetric V T0))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_NECK_CYL_FIELD_GEN THEN REAL_ARITH_TAC;
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the target neck *)
  MATCH_MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `W:A->bool`; `eta:real`; `T0:real`; `x:A`;
                       `eps:real`; `s:real`; `e:real^3->A`; `w:real`] SNGL_NECK_TARGET) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (rfs_neck_dom eps)
      (rfs_pullback (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (e:real^3->A)
         (rfs_vmetric V u))` ASSUME_TAC THENL
   [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 (rfs_kreg eps) (cylinder_flow (&0))
      (\w. Rq %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (e:real^3->A)
             (rfs_vmetric V s) w) y <= dq'` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dq:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "c0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 (rfs_kreg eps)
      (\w. R0 %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0) (e:real^3->A)
             (rfs_vmetric V T0) w)
      (\w. R0 %% rfs_pullback (rfs_vatlas V s) e (rfs_vmetric V s) w) y <= th /\
    lck_dist2 (rfs_kreg eps)
      (\w. R0 %% rfs_pullback (rfs_vatlas (V:(real->A topology)#
             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0) (e:real^3->A)
             (rfs_vmetric V T0) w)
      (\w. R0 %% rfs_pullback (rfs_vatlas V u) e (rfs_vmetric V u) w) y <= th`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "tb" MATCH_MP_TAC THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[APX_NECK_DOM_OPEN] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ch" (MP_TAC o ISPECL
    [`rfs_neck_dom eps`; `cylinder_flow (&0)`;
     `rfs_pullback (rfs_vatlas (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s) (e:real^3->A)
        (rfs_vmetric V s)`;
     `rfs_pullback (rfs_vatlas (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0) (e:real^3->A)
        (rfs_vmetric V T0)`;
     `rfs_pullback (rfs_vatlas (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) (e:real^3->A)
        (rfs_vmetric V u)`;
     `Rq:real`; `R0:real`; `dq':real`; `th:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt dq' + Mb * sqrt th` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The core of Lemma 11.23.  If x has strong (C, eps)                        *)
(* canonical neighbourhoods inside the compact set K at all times of         *)
(* (T0 - eta, T0), then at T0 it is the centre of a strong (2 eps)-neck, or  *)
(* of a (2C, Kc eps)-cap core, or lies in a 2C-component or a Kc eps-round   *)
(* component (the typed disjunction).                                         *)
(* ------------------------------------------------------------------------- *)

(* Same content as P2BT_STRONG_CANONICAL_ALT (pc_p2b_tube2, outside this    *)
(* unit's closure).                                                          *)

let SNGL_STRONG_CANON_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U.
     rfs_strong_canonical V C eps x t U <=>
     (?e. rfs_strong_neck V eps x t e /\ U = IMAGE e (rfs_neck_dom eps)) \/
     (?Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
     (x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) \/
     (x IN U /\ rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_strong_canonical; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

(* One of four monotone properties of d holds for all d > 0.                *)

let SNGL_PIGEON4 = prove
 (`!(P1:real->bool) P2 P3 P4 eta.
     (!d d'. d <= d' /\ P1 d ==> P1 d') /\ (!d d'. d <= d' /\ P2 d ==> P2 d') /\
     (!d d'. d <= d' /\ P3 d ==> P3 d') /\ (!d d'. d <= d' /\ P4 d ==> P4 d') /\
     (!d. &0 < d /\ d <= eta ==> P1 d \/ P2 d \/ P3 d \/ P4 d) /\ &0 < eta
     ==> (!d. &0 < d ==> P1 d) \/ (!d. &0 < d ==> P2 d) \/
         (!d. &0 < d ==> P3 d) \/ (!d. &0 < d ==> P4 d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m1") (CONJUNCTS_THEN2 (LABEL_TAC "m2")
    (CONJUNCTS_THEN2 (LABEL_TAC "m3") (CONJUNCTS_THEN2 (LABEL_TAC "m4")
    (CONJUNCTS_THEN2 (LABEL_TAC "cov") ASSUME_TAC))))) THEN
  MATCH_MP_TAC(TAUT `(~a /\ ~b /\ ~c /\ ~d ==> F) ==> a \/ b \/ c \/ d`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `d = min (min d1 d2) (min (min d3 d4) eta)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= eta /\ d <= d1 /\ d <= d2 /\ d <= d3 /\ d <= d4`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "cov" (MP_TAC o SPEC `d:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

(* R(x, T0) > 0 from canonical neighbourhoods on (T0 - eta, T0) and their   *)
(* derivative bounds (the hypothesis of P2C_CANON_DERIV_STATEMENT).         *)

let SNGL_SCALAR_POS_CANON = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W eta T0 x C eps eps0.
     p2c_regular_view V /\ &0 < eta /\ rfs_persists V W (T0 - eta) T0 /\ x IN W /\
     &1 < C /\ &0 < eps /\ eps <= eps0 /\
     (!top atlas g C eps x U.
         smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ &1 < C /\ &0 < eps /\ eps <= eps0 /\
         rfs_canonical_nbhd (top,atlas) g C eps x U
         ==> &0 < mfd_scalar atlas g x /\
             sqrt(rfs_scalar_grad2 atlas g x) <=
             max C (&2) * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
             abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
             max C (&2) * mfd_scalar atlas g x pow 2) /\
     (!s. T0 - eta < s /\ s < T0 ==> ?U. rfs_strong_canonical V C eps x s U)
     ==> &0 < rfs_vscalar V T0 x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cd") (LABEL_TAC "hyp"))))))))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `x:A`;
                 `max C (&2)`] SNGL_SCALAR_POS_UPTO) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "hyp" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (ASSUME_TAC o MATCH_MP SNGL_STRONG_SLICE)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)`; `W:A->bool`; `T0 - eta`; `T0:real`; `s:real`]
                SNGL_VIEW_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o ISPECL
    [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) s`;
     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) s`;
     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) s`;
     `C:real`; `eps:real`; `x:A`; `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM P2B9_RFS_VSCALAR] THEN SIMP_TAC[]);;

(* The core: the typed disjunction at T0.                                    *)

let SNGL_LIMIT_CANON = prove
 (`!u:A->bool.
     P2C_CANON_DERIV_STATEMENT u
     ==> ?Kc eps0. &2 <= Kc /\ &0 < eps0 /\
           !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
            C eps T0 x eta W K.
             p2c_regular_view V /\ &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < eta /\
             rfs_persists V W (T0 - eta) T0 /\ compact_in (rfs_vtop V T0) K /\
             K SUBSET W /\ x IN K /\
             (!s. T0 - eta < s /\ s < T0
                  ==> ?U. rfs_strong_canonical V C eps x s U /\ U SUBSET K)
             ==> (?e. rfs_strong_neck V (&2 * eps) x T0 e) \/
                 (?U Y. rfs_cap (rfs_vtop V T0,rfs_vatlas V T0) (rfs_vmetric V T0)
                                (&2 * C) (Kc * eps) U Y /\ x IN Y) \/
                 (?U. x IN U /\
                      rfs_c_component (rfs_vtop V T0,rfs_vatlas V T0) (rfs_vmetric V T0)
                                      (&2 * C) U) \/
                 (?U. x IN U /\
                      rfs_round_component (rfs_vtop V T0,rfs_vatlas V T0) (rfs_vmetric V T0)
                                          (Kc * eps) U)`,
  GEN_TAC THEN REWRITE_TAC[P2C_CANON_DERIV_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cd"))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] SNGL_CAP_CASE) THEN
  DISCH_THEN(X_CHOOSE_THEN `Kcap:real` (X_CHOOSE_THEN `eps0cap:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cap"))))) THEN
  MP_TAC(INST_TYPE [`:A`,`:A`] SNGL_NECK_CASE) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nck")))) THEN
  ABBREV_TAC `Kc = max (&2) Kcap` THEN
  SUBGOAL_THEN `&2 <= Kc /\ Kcap <= Kc /\ &0 < Kc` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `Kc:real` THEN
  EXISTS_TAC `min (min eps1 eps0d) (min (eps0cap / Kc) (&1 / (&40 * Kc)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)`; `C:real`; `eps:real`; `T0:real`; `x:A`;
                       `eta:real`; `W:A->bool`; `K:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  DISCH_THEN(fun th -> LABEL_TAC "hyp" (last(CONJUNCTS th)) THEN STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `Kc * eps <= eps0cap /\ Kc * eps <= &1 / &40 /\ Kcap * eps <= Kc * eps /\
                &2 * eps <= Kc * eps /\ (x:A) IN W`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ];
      SUBGOAL_THEN `eps * (&40 * Kc) <= &1` MP_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &40`];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* R(x, T0) > 0 *)
  SUBGOAL_THEN `&0 < rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) T0 x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SNGL_SCALAR_POS_CANON THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `eta:real`; `C:real`; `eps:real`; `eps0d:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "hyp" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  (* the type that occurs arbitrarily close to T0 *)
  MP_TAC(ISPECL
   [`\d. ?s e. T0 - d < s /\ s < T0 /\
               rfs_strong_neck (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) eps x s (e:real^3->A) /\
               IMAGE e (rfs_neck_dom eps) SUBSET K`;
    `\d. ?s U Y. T0 - d < s /\ s < T0 /\
                 rfs_cap (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) s,rfs_vatlas V s)
                         (rfs_vmetric V s) C eps U Y /\ (x:A) IN Y /\ U SUBSET K`;
    `\d. ?s U. T0 - d < s /\ s < T0 /\ (x:A) IN U /\
               rfs_c_component (rfs_vtop (V:(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) s,
                                rfs_vatlas V s) (rfs_vmetric V s) C U /\ U SUBSET K`;
    `\d. ?s U. T0 - d < s /\ s < T0 /\ (x:A) IN U /\
               rfs_round_component (rfs_vtop (V:(real->A topology)#
                                      (real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) s,
                                    rfs_vatlas V s) (rfs_vmetric V s) eps U /\ U SUBSET K`;
    `eta:real`] SNGL_PIGEON4) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MESON_TAC[REAL_ARITH `!d d' s. d <= d' /\ T0 - d < s ==> T0 - d' < s`]) THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    USE_THEN "hyp" (MP_TAC o SPEC `T0 - d / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SNGL_STRONG_CANON_ALT] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `T0 - d < T0 - d / &2 /\ T0 - d / &2 < T0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`T0 - d / &2`; `e:real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`T0 - d / &2`; `U:A->bool`; `Y:A->bool`] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`T0 - d / &2`; `U:A->bool`] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`T0 - d / &2`; `U:A->bool`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN
    USE_THEN "nck" (MP_TAC o SPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `W:A->bool`; `eta:real`; `T0:real`; `K:A->bool`; `x:A`; `eps:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    DISJ2_TAC THEN DISJ1_TAC THEN
    USE_THEN "cap" (MP_TAC o SPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `C:real`; `eps:real`; `&2 * C`; `Kc * eps`; `T0:real`; `x:A`; `eta:real`;
       `W:A->bool`; `K:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; MESON_TAC[]];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MP_TAC(ISPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `C:real`; `&2 * C`; `T0:real`; `x:A`; `eta:real`; `W:A->bool`; `K:A->bool`]
      SNGL_CCOMP_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; MESON_TAC[]];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MP_TAC(ISPECL
      [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `eps:real`; `Kc * eps`; `T0:real`; `x:A`; `eta:real`; `W:A->bool`; `K:A->bool`]
      SNGL_ROUND_CASE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The typed disjunction gives p3_canon_at (a strong en-neck                 *)
(* is a strong ec-neck for en <= ec, RFS_STRONG_NECK_EPS_MONO), and the      *)
(* headline Lemma 11.23 (route form).                                        *)
(* ------------------------------------------------------------------------- *)

let SNGL_TYPED_CANON = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C' en ec x t.
     p2c_regular_view V /\ en <= ec /\
     ((?e. rfs_strong_neck V en x t e) \/
      (?U Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C' ec U Y /\ x IN Y) \/
      (?U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C' U) \/
      (?U. x IN U /\
           rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) ec U))
     ==> p3_canon_at V C' ec x t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[p3_canon_at; SNGL_STRONG_CANON_ALT] THEN STRIP_TAC THENL
   [EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom ec)` THEN DISJ1_TAC THEN
    EXISTS_TAC `e:real^3->A` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFS_STRONG_NECK_EPS_MONO THEN EXISTS_TAC `en:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`; `en:real`; `x:A`; `t:real`; `&1`;
                   `e:real^3->A`; `s:real`] P2B9_REGULAR_NECK_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfs_strong_neck]; SIMP_TAC[]];
    EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `Y:A->bool` THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[]]);;

let P2C_LEMMA_11_23_ROUTE = prove
 (`!u:A->bool. P2C_LEMMA_11_23_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_23_ROUTE_STATEMENT; P2C_LEMMA_11_23_STATEMENT] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` SNGL_LIMIT_CANON) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "core"))))) THEN
  MAP_EVERY EXISTS_TAC [`Kc:real`; `eps0:real`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `x:A`; `t:real`;
                       `eta:real`; `W:A->bool`; `K:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2c_regular_view (rfs_view (hs:(A)rfs_history))` ASSUME_TAC THENL
   [UNDISCH_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (rfs_vtop (rfs_view (hs:(A)rfs_history)) t) K` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_view; rfs_vtop]; ALL_TAC] THEN
  MATCH_MP_TAC SNGL_TYPED_CANON THEN EXISTS_TAC `&2 * eps` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "core" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`eta:real`; `W:A->bool`; `K:A->bool`] THEN
  ASM_REWRITE_TAC[]);;

