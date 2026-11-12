(* ========================================================================= *)
(* Unit pc_rfa_scalar: the scalar curvature along a Ricci flow (MT Prop 4.1, *)
(* and the bodies of the statements P2A_REQ_RLOWER_STATEMENT and             *)
(* P2C_REQ_SCALAR_MIN_STATEMENT, assembled in pc_rfa_screq): continuity of   *)
(* local curvature quantities up to the initial time, the evolution          *)
(* inequality R' >= Lap R + (2/n) R^2 and the minimum principle for R.       *)
(* ========================================================================= *)

needs "src/pc_rfa_doubling.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Continuity up to the initial time of any local curvature                  *)
(* quantity that is jointly smooth along smooth families of metrics (the     *)
(* argument of RFA_EXT_RMNORM_CONTINUOUS, for a general functional Qf).     *)
(* ========================================================================= *)

let RFA_EXT_LOCAL_CONTINUOUS = prove
 (`!(Qf:(real^N->real^N^N)->real^N->real) V a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
     (!U ta tb G. lrg_lsmooth U ta tb G
                  ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                        (\z. lift(Qf (G (drop(fstcart z))) (sndcart z)))) /\
     (!G1 G2 s y. open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
                  ==> Qf G1 y = Qf G2 y) /\
     open V /\ &0 < e /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> (\w. lift(Qf (Gc (drop(fstcart w))) (sndcart w))) continuous_on
         {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN V}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Qs") (CONJUNCTS_THEN2 (LABEL_TAC "Ql")
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `O = interval(lift(a - e),lift b) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `V:real^N->bool`; `a:real`; `b:real`;
                 `Gc:real->real^N->real^N^N`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] RFA_SYMM_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_ELIM_THM] THEN
  X_GEN_TAC `w0:real^(1,N)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w0:real^(1,N)finite_sum) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. ~(v = vec 0)
        ==> &0 < v dot (matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) w0)
                        :real^N^N ** v)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) w0):real^N^N =
      (Gc:real->real^N->real^N^N) (drop(fstcart w0)) (sndcart w0)`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
        [GSYM LIFT_DROP] THEN
      ASM_SIMP_TAC[MATRIFY_VECTORIZE];
      ALL_TAC] THEN
    UNDISCH_TAC `!t. a <= t /\ t < b ==> metric_field V ((Gc:real->real^N->real^N^N) t)` THEN
    DISCH_THEN(MP_TAC o SPEC `drop(fstcart(w0:real^(1,N)finite_sum))`) THEN
    ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                 `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `w0:real^(1,N)finite_sum`] RFA_LOCAL_LSMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> if is_comb(concl th) && fst(strip_comb(concl th)) = `lrg_lsmooth:(real^N->bool)->real->real->(real->real^N->real^N^N)->bool`
                         then USE_THEN "Qs" (fun qs -> MP_TAC(MATCH_MP qs th)) else NO_TAC) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  EXISTS_TAC
   `\w. lift((Qf:(real^N->real^N^N)->real^N->real)
              ((\t y. matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                (pastecart (lift t) y)):real^N^N) (drop(fstcart w)))
              (sndcart w))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    USE_THEN "Ql" MATCH_MP_TAC THEN
    EXISTS_TAC `ball(sndcart(w0:real^(1,N)finite_sum),d)` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(w0:real^(1,N)finite_sum,w)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[dist; GSYM SNDCART_SUB; NORM_SNDCART];
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC
       `interval(lift(drop(fstcart(w0:real^(1,N)finite_sum)) - d),
                 lift(drop(fstcart w0) + d)) PCROSS ball(sndcart w0,d) SUBSET O` THEN
      EXPAND_TAC "O" THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      DISCH_THEN(MP_TAC o SPECL [`fstcart(w0:real^(1,N)finite_sum)`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[IN_BALL; IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LIFT_DROP; MATRIFY_VECTORIZE];
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_BALL; DIST_REFL;
                DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* The same for a manifold quantity read in the preferred chart, given a    *)
(* chart-invariant local quantity Qf and a family that is smooth up to time a. *)

let RFA_MQ_CHART_CONTINUOUS = prove
 (`!(Qf:(real^N->real^N^N)->real^N->real) (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) c.
     (!U ta tb G. lrg_lsmooth U ta tb G
                  ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                        (\z. lift(Qf (G (drop(fstcart z))) (sndcart z)))) /\
     (!G1 G2 s y. open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
                  ==> Qf G1 y = Qf G2 y) /\
     (!(h:A->real^N^N) c x. riemannian_metric atlas h /\ c IN atlas /\ x IN FST c
            ==> Qf (metric_local atlas (chart_at atlas x) h) (SND(chart_at atlas x) x) =
                Qf (metric_local atlas c h) (SND c x)) /\
     smooth_manifold_atlas top atlas /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
     (!c. c IN atlas
          ==> ?e FF. &0 < e /\
                     smooth_map_on
                       (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                     !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                           ==> FF(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y)) /\
     c IN atlas
     ==> continuous_map
           (subtopology
             (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                            (subtopology top (topspace top)))
             {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                 {t | a <= t /\ t < b})
                                               (subtopology top (topspace top))) /\
                  SND z IN FST c},
            euclideanreal)
           (\z. Qf (metric_local atlas (chart_at atlas (SND z)) (g (FST z)))
                    (SND(chart_at atlas (SND z)) (SND z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Qs") (CONJUNCTS_THEN2 (LABEL_TAC "Ql")
    (CONJUNCTS_THEN2 (LABEL_TAC "Qc") (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "rm") (CONJUNCTS_THEN2 (LABEL_TAC "Ext")
       ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "Ext" (MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(Qf:(real^N->real^N^N)->real^N->real)`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                 `e:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`]
         RFA_EXT_LOCAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "Qs" ACCEPT_TAC; USE_THEN "Ql" ACCEPT_TAC;
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "rm" (MP_TAC o C MATCH_MP (CONJ (ASSUME `a <= t:real`) (ASSUME `t < b:real`))) THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `continuous_map
     (subtopology euclidean
       {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
            sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)},
      euclideanreal)
     (\w. (Qf:(real^N->real^N^N)->real^N->real)
           (metric_local atlas (c:(A->bool)#(A->real^N))
                         ((g:real->A->real^N^N) (drop(fstcart w)))) (sndcart w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\w. (Qf:(real^N->real^N^N)->real^N->real)
          (metric_local atlas (c:(A->bool)#(A->real^N))
                        ((g:real->A->real^N^N) (drop(fstcart w)))) (sndcart w)) o
    (\z:real#A. pastecart (lift(FST z)) (SND c (SND z)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_ELIM_THM;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
                o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "Qc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
               {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                    sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(\z:real#A. pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z))) =
    (\(x,y). pastecart x y) o (\z. lift(FST z),SND c (SND z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^1)topology) (euclidean:(real^N)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[CONTINUOUS_MAP_LIFT; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                   `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (top:A topology) (FST(c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                     `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_SND) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                  IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND] THEN
      SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
           SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP
                                 (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN SIMP_TAC[]]);;


let RFA_MQ_CONTINUOUS = prove
 (`!(Qf:(real^N->real^N^N)->real^N->real) (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N).
     (!U ta tb G. lrg_lsmooth U ta tb G
                  ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                        (\z. lift(Qf (G (drop(fstcart z))) (sndcart z)))) /\
     (!G1 G2 s y. open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
                  ==> Qf G1 y = Qf G2 y) /\
     (!(h:A->real^N^N) c x. riemannian_metric atlas h /\ c IN atlas /\ x IN FST c
            ==> Qf (metric_local atlas (chart_at atlas x) h) (SND(chart_at atlas x) x) =
                Qf (metric_local atlas c h) (SND c x)) /\
     smooth_manifold_atlas top atlas /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
     (!c. c IN atlas
          ==> ?e FF. &0 < e /\
                     smooth_map_on
                       (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                     !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                           ==> FF(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y))
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. Qf (metric_local atlas (chart_at atlas (SND z)) (g (FST z)))
                    (SND(chart_at atlas (SND z)) (SND z)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o el 3 o CONJUNCTS) THEN
  MATCH_MP_TAC(INST_TYPE [`:real#A`,`:A`; `:real`,`:B`;
                          `:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC
   [`\c:(A->bool)#(A->real^N). \z:real#A.
       (Qf:(real^N->real^N^N)->real^N->real) (metric_local atlas (chart_at atlas (SND z)) ((g:real->A->real^N^N) (FST z)))
          (SND(chart_at atlas (SND z)) (SND z))`;
    `\c:(A->bool)#(A->real^N).
       {z:real#A | z IN topspace(prod_topology
                                   (subtopology euclideanreal {t | a <= t /\ t < b})
                                   (subtopology top (topspace top))) /\
                   SND z IN FST c}`;
    `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `subtopology (top:A topology) (topspace top)` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND; SUBTOPOLOGY_TOPSPACE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_MQ_CHART_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_CROSS; IN_INTER;
                IN_ELIM_THM] THEN
    STRIP_TAC THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_ELIM_THM; IN_CROSS; IN_INTER; TOPSPACE_PROD_TOPOLOGY;
             TOPSPACE_SUBTOPOLOGY; FST; SND] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The scalar curvature on a manifold along a Ricci flow:                    *)
(* chart independence, joint continuity, smoothness in charts, and the     *)
(* evolution equation R' = Lap R + 2 |Ric|^2 with |Ric|^2 >= R^2 / n.        *)
(* ========================================================================= *)

let RFA_MFD_SCALAR_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (h:A->real^N^N) c x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\
        c IN atlas /\ x IN FST c
        ==> lscalar (metric_local atlas (chart_at atlas x) h) (SND(chart_at atlas x) x) =
            lscalar (metric_local atlas c h) (SND c x)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `h:A->real^N^N`; `V:A->bool`; `psi:A->real^N`; `x:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `cc:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC LSCALAR_CHART_TRANS THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let RFA_MFD_SCALAR_CONTINUOUS_GEN = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
     (!c. c IN atlas
          ==> ?e FF. &0 < e /\
                     smooth_map_on
                       (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                     !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                           ==> FF(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y))
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. mfd_scalar atlas (g (FST z)) (SND z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MATCH_MP_TAC RFA_MQ_CONTINUOUS THEN ASM_REWRITE_TAC[LRG_LSMOOTH_LSCALAR] THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC LSCALAR_LOCAL; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_SCALAR_CHART THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let RFA_RICCI_FLOW_ON_EXT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t1.
     ricci_flow_on (top,atlas) a b g /\ a < t1
     ==> !c. c IN atlas
             ==> ?e FF. &0 < e /\
                        smooth_map_on
                          (interval(lift(t1 - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                        !t y. t1 <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                              ==> FF(pastecart (lift t) y) =
                                  (vectorize:real^N^N->real^(N,N)finite_prod)
                                  (metric_local atlas c (g t) y)`,
  REWRITE_TAC[ricci_flow_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `t1 - a:real` THEN
  EXISTS_TAC `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas (c:(A->bool)#(A->real^N))
                     ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
  ASM_SIMP_TAC[REAL_SUB_LT; REAL_ARITH `t1 - (t1 - a) = a:real`] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let RFA_MFD_SCALAR_CHART_SMOOTH = prove
 (`!(top:A topology) atlas a b (g:real->A->real^N^N) c.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas
     ==> smooth_map_on
           (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c INTER topspace top))
           (\z. lift(mfd_scalar atlas (g (drop(fstcart z))) (chart_inv c (sndcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST c INTER topspace top = FST (c:(A->bool)#(A->real^N))` SUBST1_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift(lscalar
                    ((\t. metric_local atlas (c:(A->bool)#(A->real^N))
                                       ((g:real->A->real^N^N) t)) (drop(fstcart z)))
                    (sndcart z))` THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_LSCALAR; OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[mfd_scalar] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) (drop s)`; `c:(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] RFA_MFD_SCALAR_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let RFA_MFD_SCALAR_EVOLUTION = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) t x.
     ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
     ==> ((\s. mfd_scalar atlas (g s) x) has_real_derivative
          rfa_lap atlas (g t) (mfd_scalar atlas (g t)) x +
          &2 * ltnorm2 2 (metric_local atlas (chart_at atlas x) (g t))
                         (lric2 (metric_local atlas (chart_at atlas x) (g t)))
                         (SND(chart_at atlas x) x)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
           (FST(chart_at atlas x))`;
    `a:real`; `b:real`;
    `\t. metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (x:A))
                      ((g:real->A->real^N^N) t)`;
    `t:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
   LSCALAR_EVOLUTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_lap] THEN
  SUBGOAL_THEN
   `llap (metric_local atlas (chart_at atlas x) ((g:real->A->real^N^N) t))
         (\y. mfd_scalar atlas (g t) (chart_inv (chart_at atlas (x:A)) y))
         (SND(chart_at atlas x) x) =
    llap (metric_local atlas (chart_at atlas x) (g t))
         (lscalar (metric_local atlas (chart_at atlas x) (g t)))
         (SND(chart_at atlas x) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN REWRITE_TAC[mfd_scalar] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) z`]
           RFA_MFD_SCALAR_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar]);;

let RFA_SUM_TERM_LE = prove
 (`!(f:A->real) s a. FINITE s /\ a IN s /\ (!x. x IN s ==> &0 <= f x)
                     ==> f a <= sum s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `s:A->bool`; `a:A`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sum (s DELETE (a:A)) (f:A->real)` MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_DELETE]; REAL_ARITH_TAC]);;

let RFA_RIC_SCALAR_LE = prove
 (`!U (G:real^N->real^N^N) y.
        metric_field U G /\ y IN U
        ==> lscalar G y pow 2 <= &(dimindex(:N)) * ltnorm2 2 G (lric2 G) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lscalar G y =
    sum(1..dimindex(:N))
      (\r. lricci (G:real^N->real^N^N) y (transp(S:real^N^N) ** basis r) (transp(S:real^N^N) ** basis r))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lric2 (G:real^N->real^N^N)`; `y:real^N`; `S:real^N^N`;
                   `\m:num. vec 0:real^N`] RFA_CONTR_FRAME) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[lric2; lscalar] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lric2 (G:real^N->real^N^N)`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) *
              sum(1..dimindex(:N))
                (\r. lricci (G:real^N->real^N^N) y (transp(S:real^N^N) ** basis r)
                            (transp(S:real^N^N) ** basis r) pow 2)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `\r. lricci (G:real^N->real^N^N) y (transp(S:real^N^N) ** basis r)
                             (transp(S:real^N^N) ** basis r)` RFA_SUM_SQUARE_LE) THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`\q. lricci (G:real^N->real^N^N) y (transp(S:real^N^N) ** basis r)
                             (transp(S:real^N^N) ** basis q) pow 2`;
                 `1..dimindex(:N)`; `r:num`] RFA_SUM_TERM_LE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_POW_2]);;

(* ========================================================================= *)
(* Lower bounds for the scalar curvature by the minimum                      *)
(* principle (RFA_MINP_SCALAR): a lower bound is preserved, the minimum is  *)
(* nondecreasing (P2C_REQ_SCALAR_MIN), and min(0, inf R(a)) is a lower bound  *)
(* for all later times (P2A_REQ_RLOWER).                                     *)
(* ========================================================================= *)

let RFA_SCALAR_LOWER_CONST = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    t1 r0.
     compact_space top /\ ricci_flow_on (top,atlas) a b g /\ a <= t1 /\ t1 < b /\
     (!t. t1 <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
     (!c. c IN atlas
          ==> ?e FF. &0 < e /\
                     smooth_map_on
                       (interval(lift(t1 - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                     !t y. t1 <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                           ==> FF(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y)) /\
     (!x. x IN topspace top ==> r0 <= mfd_scalar atlas (g t1) x)
     ==> !t x. t1 <= t /\ t < b /\ x IN topspace top
               ==> r0 <= mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `topspace(top:A topology)`;
    `t1:real`; `b:real`; `g:real->A->real^N^N`;
    `\t x. mfd_scalar (atlas:((A->bool)#(A->real^N))->bool) ((g:real->A->real^N^N) t) x`;
    `\t:real u:real. &0`; `\s:real. r0:real`] RFA_MINP_SCALAR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM compact_space];
      REWRITE_TAC[OPEN_IN_TOPSPACE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace(top:A topology))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFA_MFD_SCALAR_CHART_SMOOTH THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`; `x:A`]
             RFA_MFD_SCALAR_EVOLUTION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      EXISTS_TAC `rfa_lap atlas ((g:real->A->real^N^N) t) (mfd_scalar atlas (g t)) (x:A) +
                  &2 * ltnorm2 2 (metric_local atlas (chart_at atlas x) (g t))
                                 (lric2 (metric_local atlas (chart_at atlas x) (g t)))
                                 (SND(chart_at atlas x) x)` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= n ==> l + &0 <= l + &2 * n`) THEN
      MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))` THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
             CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                            (FST(chart_at atlas x)))
                     (metric_local atlas (chart_at atlas x) ((g:real->A->real^N^N) t))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                       ((g:real->A->real^N^N) t)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; LRG_LRIC2_FIELD];
      REPEAT STRIP_TAC THEN EXISTS_TAC `&0` THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

let RFA_MFD_SCALAR_SLICE_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) b (g:real->A->real^N^N) t1.
     smooth_manifold_atlas top atlas /\ t1 < b /\
     (!t. t1 <= t /\ t < b ==> riemannian_metric atlas (g t)) /\
     (!c. c IN atlas
          ==> ?e FF. &0 < e /\
                     smooth_map_on
                       (interval(lift(t1 - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                     !t y. t1 <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                           ==> FF(pastecart (lift t) y) =
                               (vectorize:real^N^N->real^(N,N)finite_prod)
                               (metric_local atlas c (g t) y))
     ==> continuous_map (top,euclideanreal) (mfd_scalar atlas (g t1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `t1:real`; `b:real`; `g:real->A->real^N^N`]
         RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | t1 <= t /\ t < b}`;
                 `top:A topology`;
                 `\t x. mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                   ((g:real->A->real^N^N) t) x`;
                 `t1:real`] RFA_SLICE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                  IN_ELIM_THM; SUBTOPOLOGY_TOPSPACE; REAL_LE_REFL; ETA_AX]);;

let RFA_SCALAR_MIN_BODY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    t1 t2 x.
       compact_space top /\ ricci_flow_on (top,atlas) a b g /\
       a < t1 /\ t1 <= t2 /\ t2 < b /\ x IN topspace top
       ==> ?y. y IN topspace top /\ mfd_scalar atlas (g t1) y <= mfd_scalar atlas (g t2) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `t1:real`]
         RFA_RICCI_FLOW_ON_EXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool) /\
                (!t. t1 <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:real`; `g:real->A->real^N^N`; `t1:real`]
         RFA_MFD_SCALAR_SLICE_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                 ((g:real->A->real^N^N) t1)) (topspace top)`
         REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `t1:real`;
                 `mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                             ((g:real->A->real^N^N) t1) (y:A)`]
         RFA_SCALAR_LOWER_CONST) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_RLOWER_BODY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N).
       compact_space top /\ ricci_flow_from (top,atlas) a b g
       ==> !t x. a <= t /\ t < b /\ x IN topspace top
                 ==> min (&0) (inf {mfd_scalar atlas (g a) y | y IN topspace top})
                     <= mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                              (g:real->A->real^N^N) /\
                smooth_manifold_atlas top atlas /\ a < b /\
                (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> ?e FF. &0 < e /\
                   smooth_map_on
                     (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                   !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                         ==> FF(pastecart (lift t) y) =
                             (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c ((g:real->A->real^N^N) t) y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `b:real`; `g:real->A->real^N^N`; `a:real`]
         RFA_MFD_SCALAR_SLICE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN topspace top
        ==> inf (IMAGE (mfd_scalar atlas ((g:real->A->real^N^N) a)) (topspace top)) <=
            mfd_scalar atlas (g a) (y:A)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC INF_LE_ELEMENT THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    SUBGOAL_THEN `real_compact (IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                        ((g:real->A->real^N^N) a)) (topspace top))`
    MP_TAC THENL
     [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[real_bounded] THEN
    MESON_TAC[REAL_ARITH `abs w <= B ==> --B <= w`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `r <= z ==> min (&0) r <= z`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `a:real`;
                 `inf (IMAGE (mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                         ((g:real->A->real^N^N) a)) (topspace top))`]
         RFA_SCALAR_LOWER_CONST) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* MT Prop 4.1: from R(s,.) >= r0 the scalar                                 *)
(* curvature satisfies R(t,.) >= n r0 / (n - 2 (t - s) r0), by comparison    *)
(* with the Riccati equation H' = (2/n) H^2; the denominator stays positive  *)
(* since otherwise R would blow up at a time of the flow.                    *)
(* ========================================================================= *)

let RFA_RICCI_FLOW_FROM_EXT_AT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) s.
     ricci_flow_from (top,atlas) a b g /\ a <= s
     ==> !c. c IN atlas
             ==> ?e FF. &0 < e /\
                        smooth_map_on
                          (interval(lift(s - e),lift b) PCROSS IMAGE (SND c) (FST c)) FF /\
                        !t y. s <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                              ==> FF(pastecart (lift t) y) =
                                  (vectorize:real^N^N->real^(N,N)finite_prod)
                                  (metric_local atlas c (g t) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                                 a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_from] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_RICCI_FLOW_ON_EXT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ASM_REAL_ARITH_TAC]);;

let RFA_RICCATI_ODE = prove
 (`!n r0 s t.
     &0 < n /\ &0 < n - &2 * (t - s) * r0
     ==> ((\u. n * r0 / (n - &2 * (u - s) * r0)) has_real_derivative
          (&2 / n) * (n * r0 / (n - &2 * (t - s) * r0)) pow 2) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\u. n * r0 / (n - &2 * (u - s) * r0)) has_real_derivative f') (atreal t)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < n - &2 * (t - s) * r0` THEN UNDISCH_TAC `&0 < n` THEN
  CONV_TAC REAL_FIELD);;

let RFA_SCALAR_RICCATI_BOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    s b' r0.
      compact_space top /\ ricci_flow_from (top,atlas) a b g /\ a <= s /\ s < b' /\
      b' <= b /\
      (!t. s <= t /\ t < b' ==> &0 < &(dimindex(:N)) - &2 * (t - s) * r0) /\
      (!x. x IN topspace top ==> r0 <= mfd_scalar atlas (g s) x)
      ==> !t x. s <= t /\ t < b' /\ x IN topspace top
                ==> &(dimindex(:N)) * r0 / (&(dimindex(:N)) - &2 * (t - s) * r0)
                    <= mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`];
    ALL_TAC] THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  SUBGOAL_THEN `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                              (g:real->A->real^N^N) /\
                smooth_manifold_atlas top atlas /\
                (!t. s <= t /\ t < b ==> riemannian_metric atlas (g t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`]
         RFA_RICCI_FLOW_FROM_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `topspace(top:A topology)`;
    `s:real`; `b':real`; `g:real->A->real^N^N`;
    `\t x. mfd_scalar (atlas:((A->bool)#(A->real^N))->bool) ((g:real->A->real^N^N) t) x`;
    `\t:real u. (&2 / n) * u pow 2`;
    `\u. n * r0 / (n - &2 * (u - s) * r0)`] RFA_MINP_SCALAR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM compact_space];
      REWRITE_TAC[OPEN_IN_TOPSPACE];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_CONTINUOUS_MAP_RESTRICT_TIME THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace(top:A topology))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFA_MFD_SCALAR_CHART_SMOOTH THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`; `x:A`]
             RFA_MFD_SCALAR_EVOLUTION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      EXISTS_TAC `rfa_lap atlas ((g:real->A->real^N^N) t) (mfd_scalar atlas (g t)) (x:A) +
                  &2 * ltnorm2 2 (metric_local atlas (chart_at atlas x) (g t))
                                 (lric2 (metric_local atlas (chart_at atlas x) (g t)))
                                 (SND(chart_at atlas x) x)` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
      SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
             CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                            (FST(chart_at atlas x)))
                     (metric_local atlas (chart_at atlas x) ((g:real->A->real^N^N) t))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                       ((g:real->A->real^N^N) t)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL
       [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
               (FST(chart_at atlas x))`;
        `metric_local atlas (chart_at atlas (x:A)) ((g:real->A->real^N^N) t)`;
        `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`] RFA_RIC_SCALAR_LE) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[mfd_scalar] THEN
      ABBREV_TAC `R = lscalar (metric_local atlas (chart_at atlas (x:A))
                                ((g:real->A->real^N^N) t)) (SND(chart_at atlas x) x)` THEN
      ABBREV_TAC `Q = ltnorm2 2 (metric_local atlas (chart_at atlas (x:A))
                                  ((g:real->A->real^N^N) t))
                       (lric2 (metric_local atlas (chart_at atlas x) (g t)))
                       (SND(chart_at atlas x) x)` THEN
      DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `y <= &2 * q ==> l + y <= l + &2 * q`) THEN
      SUBGOAL_THEN `(&2 / n) * R pow 2 <= (&2 / n) * (n * Q)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(&2 / n) * (n * Q) = &2 * Q` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`cc:real`; `B:real`] THEN DISCH_TAC THEN
      EXISTS_TAC `(&2 / n) * &2 * abs B` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(&2 / n) = &2 / n` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `u pow 2 - v pow 2 = (u + v) * (u - v)`; REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC RFA_RICCATI_ODE THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `n * r0 / (n - &2 * (s - s) * r0) = r0` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
        UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
        ASM_SIMP_TAC[]]];
    REWRITE_TAC[]]);;

(* The scalar curvature lower bound (MT Prop 4.1). *)

let RFA_SCALAR_LOWER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) s r0.
      compact_space top /\ ricci_flow_from (top,atlas) a b g /\ a <= s /\ s < b /\
      (!x. x IN topspace top ==> r0 <= mfd_scalar atlas (g s) x)
      ==> !t x. s <= t /\ t < b /\ x IN topspace top
                ==> &0 < &(dimindex(:N)) - &2 * (t - s) * r0 /\
                    &(dimindex(:N)) * r0 / (&(dimindex(:N)) - &2 * (t - s) * r0)
                    <= mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; DIMINDEX_GE_1; ARITH_RULE `0 < n <=> 1 <= n`];
    ALL_TAC] THEN
  ABBREV_TAC `n = &(dimindex(:N))` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool) /\
                (!u. s <= u /\ u < b ==> riemannian_metric atlas ((g:real->A->real^N^N) u))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `u:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. s <= u /\ u < b ==> &0 < n - &2 * (u - s) * r0` ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r0 <= &0` THENL
     [SUBGOAL_THEN `&0 <= (u - s) * --r0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ABBREV_TAC `T0 = s + n / (&2 * r0)` THEN
    SUBGOAL_THEN `&0 < &2 * r0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * (T0 - s) * r0 = n` ASSUME_TAC THENL
     [EXPAND_TAC "T0" THEN UNDISCH_TAC `&0 < &2 * r0` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `s < T0 /\ T0 <= u` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "T0" THEN REWRITE_TAC[REAL_LT_ADDR] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(u - s) * (&2 * r0) < (T0 - s) * (&2 * r0)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `n - &2 * (u - s) * r0 <= &0` THEN
        UNDISCH_TAC `&2 * (T0 - s) * r0 = n` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`; `T0:real`;
                   `r0:real`] RFA_SCALAR_RICCATI_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `v:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(v - s) * (&2 * r0) < (T0 - s) * (&2 * r0)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&2 * (T0 - s) * r0 = n` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`]
           RFA_RICCI_FLOW_FROM_EXT_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `s:real`; `b:real`; `g:real->A->real^N^N`]
           RFA_MFD_SCALAR_CONTINUOUS_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `?d. &0 < d /\
          !t'. s <= t' /\ t' < b /\ abs(t' - T0) < d
               ==> abs(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                  ((g:real->A->real^N^N) t') (x:A) -
                       mfd_scalar atlas (g T0) x) < &1`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclideanreal {t | s <= t /\ t < b}`;
                     `subtopology (top:A topology) (topspace top)`;
                     `\t x. mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                       ((g:real->A->real^N^N) t) x`;
                     `x:A`] RFA_SLICE_CONTINUOUS_LEFT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER]; ALL_TAC] THEN
      REWRITE_TAC[GSYM RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP; real_continuous_on] THEN
      DISCH_THEN(MP_TAC o SPEC `T0:real`) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN
      REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `M = abs(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                   ((g:real->A->real^N^N) T0) (x:A)) + &2` THEN
    SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [EXPAND_TAC "M" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < n / (&2 * M)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `h = min d (min (T0 - s) (n / (&2 * M))) / &2` THEN
    SUBGOAL_THEN `&0 < h /\ h < d /\ h < T0 - s /\ h < n / (&2 * M)`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * h * M < n` ASSUME_TAC THENL
     [UNDISCH_TAC `h < n / (&2 * M)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `T0 - h:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`T0 - h:real`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `&(dimindex(:N)) = n`] THEN
    SUBGOAL_THEN `n - &2 * ((T0 - h) - s) * r0 = &2 * h * r0` SUBST1_TAC THENL
     [UNDISCH_TAC `&2 * (T0 - s) * r0 = n` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `M < n * r0 / (&2 * h * r0)` MP_TAC THENL
     [SUBGOAL_THEN `n * r0 / (&2 * h * r0) = n / (&2 * h)` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(r0 = &0) /\ ~(h = &0)` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &2 * h` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      UNDISCH_TAC `&2 * h * M < n` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `abs(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                                ((g:real->A->real^N^N) T0) (x:A)) + &2 = M` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`; `b:real`;
                 `r0:real`] RFA_SCALAR_RICCATI_BOUND) THEN
  ASM_SIMP_TAC[REAL_LE_REFL]);;

