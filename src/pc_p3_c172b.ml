(* ========================================================================= *)
(* Unit pc_p3_c172b: MT Lemma 17.2, part B (caps, C-                       *)
(* components and round components persist just after a first bad time).   *)
(*                                                                         *)
(* The tube lemma at the initial time of a slab.  The C^k                  *)
(* distance between the slices at s and s0 tends to 0 uniformly on compact *)
(* sets as s decreases to s0, also when s0 is the initial time of a         *)
(* ricci_flow_from family (the open-interval form is P2BL_SLICES_TUBE of    *)
(* pc_p2b_ltr; here the smooth extension of ricci_flow_from below s0 is     *)
(* used, symmetrized and positive near each point, following the proof     *)
(* pattern of RFA_EXT_LOCAL_CONTINUOUS of pc_rfa_scalar).                   *)
(* ========================================================================= *)

needs "src/pc_p3_c172a.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_p3_c17top.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_LCK_EXT_CONTINUOUS = prove
 (`!V s0 b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) k.
     open V /\ &0 < e /\ s0 < b /\
     (!t. s0 <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(s0 - e),lift b) PCROSS V) FF /\
     (!t y. s0 <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> (\w. lift(lck_dist2 k (Gc s0) (Gc (drop(fstcart w))) (sndcart w))) continuous_on
         {w | s0 <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN V}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `O = interval(lift(s0 - e),lift b) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `V:real^N->bool`; `s0:real`; `b:real`;
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
    UNDISCH_TAC `!t. s0 <= t /\ t < b ==> metric_field V ((Gc:real->real^N->real^N^N) t)` THEN
    DISCH_THEN(MP_TAC o SPEC `drop(fstcart(w0:real^(1,N)finite_sum))`) THEN
    ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                 `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `w0:real^(1,N)finite_sum`] RFA_LOCAL_LSMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t0 = drop(fstcart(w0:real^(1,N)finite_sum))` THEN
  ABBREV_TAC `y0 = sndcart(w0:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `ball(y0:real^N,d) SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `interval(lift(t0 - d),lift(t0 + d)) PCROSS ball(y0:real^N,d) SUBSET O` THEN
    EXPAND_TAC "O" THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift t0`; `z:real^N`]) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lrg_lsmooth (ball(y0:real^N,d)) (t0 - d) (t0 + d)
                  (\t:real. (Gc:real->real^N->real^N^N) s0)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BL_LSMOOTH_CONST THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `ball(y0:real^N,d)`; `t0 - d`; `t0 + d`;
                 `\t:real. (Gc:real->real^N->real^N^N) s0`;
                 `\t y. matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                (pastecart (lift t) y)):real^N^N`]
                P2BL_LCK_FAMILY_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  EXISTS_TAC
   `\w. lift(lck_dist2 k ((Gc:real->real^N->real^N^N) s0)
              (\y. matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                     (pastecart (lift(drop(fstcart w))) y)):real^N^N)
              (sndcart w))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `ball(y0:real^N,d)` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL] THEN CONJ_TAC THENL
     [EXPAND_TAC "y0" THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(w0:real^(1,N)finite_sum,w)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[dist; GSYM SNDCART_SUB; NORM_SNDCART];
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^N) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(y0:real^N,d) SUBSET V` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LIFT_DROP; MATRIFY_VECTORIZE];
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_BALL; DIST_REFL;
                    DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* The C^k distance to the slice at s0, read in the preferred charts, is   *)
(* continuous on [s0,b) x (chart domain), for a family smooth from a <= s0. *)

let P3H_LCK_CHART_CONTINUOUS_FROM = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k c.
     ricci_flow_from (top,atlas) a b g /\ &0 < R /\ a <= s0 /\ s0 < b /\ c IN atlas
     ==> continuous_map
           (subtopology
             (prod_topology (subtopology euclideanreal {t | s0 <= t /\ t < b}) top)
             {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                 {t | s0 <= t /\ t < b}) top) /\
                  SND z IN FST c},
            euclideanreal)
           (\z. lck_dist2 k (metric_local atlas (chart_at atlas (SND z)) (\y. R %% g s0 y))
                            (metric_local atlas (chart_at atlas (SND z))
                                          (\y. R %% g (FST z) y))
                            (SND(chart_at atlas (SND z)) (SND z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
                !t. s0 <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^N^N`; `s0:real`]
                    RFA_RICCI_FLOW_FROM_METRIC) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^N^N`; `t:real`]
                    RFA_RICCI_FLOW_FROM_METRIC) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`; `s0:real`] RFA_RICCI_FLOW_FROM_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `s0:real`; `b:real`; `e:real`;
                 `\t:real. metric_local atlas (c:(A->bool)#(A->real^N))
                             (\y. R %% (g:real->A->real^N^N) t y)`;
                 `\w. R % (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w`; `k:num`]
                P3H_LCK_EXT_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `riemannian_metric atlas (\y. R %% (g:real->A->real^N^N) t y)` MP_TAC
      THENL [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; ETA_AX];
      REPEAT STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL; ETA_AX]];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `continuous_map
     (subtopology euclidean {w | s0 <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                 sndcart w IN (V:real^N->bool)}, euclideanreal)
     (\w. lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                         (\y. R %% (g:real->A->real^N^N) s0 y))
                      (metric_local atlas c (\y. R %% g (drop(fstcart w)) y)) (sndcart w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\w. lck_dist2 k (metric_local atlas (c:(A->bool)#(A->real^N))
                        (\y. R %% (g:real->A->real^N^N) s0 y))
                     (metric_local atlas c (\y. R %% g (drop(fstcart w)) y)) (sndcart w)) o
    (\z:real#A. pastecart (lift(FST z)) (SND c (SND z)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_ELIM_THM;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
                o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BL_LCK_CHART_INDEP THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                  CHART_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean {w | s0 <= drop(fstcart w) /\ drop(fstcart w) < b /\
                                         sndcart w IN (V:real^N->bool)}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "V" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[]] THEN
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
    MP_TAC(ISPECL [`subtopology euclideanreal {t | s0 <= t /\ t < b}`;
                   `top:A topology`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (top:A topology) (FST(c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND];
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

let P3H_LCK_SLICES_CONTINUOUS_FROM = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k.
     ricci_flow_from (top,atlas) a b g /\ &0 < R /\ a <= s0 /\ s0 < b
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | s0 <= t /\ t < b}) top,
            euclideanreal)
           (\z. lck_dist2 k (metric_local atlas (chart_at atlas (SND z)) (\y. R %% g s0 y))
                            (metric_local atlas (chart_at atlas (SND z))
                                          (\y. R %% g (FST z) y))
                            (SND(chart_at atlas (SND z)) (SND z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC
  THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^N^N`; `s0:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:real#A`,`:A`; `:real`,`:B`;
                          `:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC
   [`\c:(A->bool)#(A->real^N). \z:real#A.
       lck_dist2 k (metric_local atlas (chart_at atlas (SND z)) (\y. R %% (g:real->A->real^N^N) s0 y))
                   (metric_local atlas (chart_at atlas (SND z)) (\y. R %% g (FST z) y))
                   (SND(chart_at atlas (SND z)) (SND z))`;
    `\c:(A->bool)#(A->real^N).
       {z:real#A | z IN topspace(prod_topology
                                   (subtopology euclideanreal {t | s0 <= t /\ t < b}) top) /\
                   SND z IN FST c}`;
    `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC P3H_LCK_CHART_CONTINUOUS_FROM THEN EXISTS_TAC `a:real` THEN
      ASM_REWRITE_TAC[]];
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

(* The tube lemma from s0: on a compact K, the slices at s in [s0, s0 + eta) *)
(* are C^k close to the slice at s0.                                         *)

let P3H_SLICES_TUBE_FROM = prove
 (`!top atlas (g:real->A->real^N^N) a b R s0 k K th.
     ricci_flow_from (top,atlas) a b g /\ &0 < R /\ a <= s0 /\ s0 < b /\
     compact_in top K /\ &0 < th
     ==> ?eta. &0 < eta /\
               !s p. s0 <= s /\ s < s0 + eta /\ p IN K
                     ==> lck_dist2 k (metric_local atlas (chart_at atlas p)
                                                   (\y. R %% g s0 y))
                                     (metric_local atlas (chart_at atlas p)
                                                   (\y. R %% g s y))
                                     (SND(chart_at atlas p) p) < th`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `K:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  ABBREV_TAC
   `L = \s p. lck_dist2 k (metric_local atlas (chart_at atlas p)
                                        (\y. R %% (g:real->A->real^N^N) s0 y))
                          (metric_local atlas (chart_at atlas p) (\y. R %% g s y))
                          (SND(chart_at atlas p) (p:A))` THEN
  SUBGOAL_THEN
   `continuous_map (prod_topology (subtopology euclideanreal {t | s0 <= t /\ t < b})
                                  (subtopology top (K:A->bool)),
                    euclideanreal)
                   (\z. (L:real->A->real) (FST z) (SND z))`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ONCE_REWRITE_TAC[CONJUNCT2 PROD_TOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MATCH_MP_TAC P3H_LCK_SLICES_CONTINUOUS_FROM THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | s0 <= t /\ t < b}`; `top:A topology`;
                 `K:A->bool`; `L:real->A->real`] RFA_SUP_COMPACT_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP; real_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `s0:real`) THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `th:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sup(IMAGE ((L:real->A->real) s0) K) = &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE ((L:real->A->real) s0) K = {&0}` SUBST1_TAC THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[P2BL_LCK_DIST2_REFL] THEN ASM SET_TAC[];
      REWRITE_TAC[SUP_SING]];
    ALL_TAC] THEN
  EXISTS_TAC `min d (b - s0)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `p:A`] THEN
  REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | s0 <= t /\ t < b}`; `top:A topology`;
                 `K:A->bool`; `L:real->A->real`; `s:real`] RFA_SUP_COMPACT_ATTAINED) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                  IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs(sup(IMAGE ((L:real->A->real) s) K)) < th` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* On a slab, the slices at s >= ts near ts are C^k close to                *)
(* the slice at ts on any set with compact closure (identity map), so caps   *)
(* with the same core, C-components and round components persist (the typed *)
(* openness P2B_PROP_9_79_OPEN_TYPED of pc_p2b_ltr).                         *)
(* ========================================================================= *)

let P3H_SLAB_MCLOSE = prove
 (`!top atlas (g:real->A->real^3^3) a b s0 Q U delta.
     ricci_flow_from (top,atlas) a b g /\ a <= s0 /\ s0 < b /\ &0 < Q /\
     compact_in top (top closure_of U) /\ U SUBSET topspace top /\ &0 < delta
     ==> ?eta. &0 < eta /\
               !s. s0 <= s /\ s < s0 + eta
                   ==> rfs_mclose (rfs_kreg delta) delta atlas U
                         (\y. Q %% g s0 y)
                         (\y. Q %% mfd_pullback_metric atlas atlas (\x. x) (g s) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC
  THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `s0:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`; `a:real`; `b:real`; `Q:real`; `s0:real`;
                 `rfs_kreg delta`; `top closure_of (U:A->bool)`; `delta pow 2 / &2`]
                P3H_SLICES_TUBE_FROM) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[rfs_mclose] THEN
  EXISTS_TAC `delta pow 2 / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  SUBGOAL_THEN
   `lck_dist2 (rfs_kreg delta)
      (metric_local atlas (chart_at atlas p) (\y. Q %% (g:real->A->real^3^3) s0 y))
      (metric_local atlas (chart_at atlas p)
         (\y. Q %% mfd_pullback_metric atlas atlas (\x:A. x) (g s) y))
      (SND (chart_at atlas p) p) =
    lck_dist2 (rfs_kreg delta)
      (metric_local atlas (chart_at atlas p) (\y. Q %% g s0 y))
      (metric_local atlas (chart_at atlas p) (\y. Q %% g s y))
      (SND (chart_at atlas p) p)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)))
                      (FST(chart_at atlas p))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (p:A)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; OPEN_IN_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) s`; `q:A`] P2CF_PULLBACK_ID) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `eta:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CLOSURE_OF_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Persistence of the static canonical neighbourhoods along a slab. *)

let P3H_STATIC_PERSIST = prove
 (`?eps0. &0 < eps0 /\ eps0 <= &1 / &8 /\
     !top atlas (g:real->A->real^3^3) a b ts C eps x U.
       hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b g /\
       a <= ts /\ ts < b /\ &1 < C /\ &0 < eps /\ eps <= eps0 /\
       &0 < mfd_scalar atlas (g ts) x /\
       ((?Y. rfs_cap (top,atlas) (g ts) C eps U Y /\ x IN Y) \/
        (x IN U /\ rfs_c_component (top,atlas) (g ts) C U) \/
        (x IN U /\ rfs_round_component (top,atlas) (g ts) eps U))
       ==> ?N eta. open_in top N /\ x IN N /\ N SUBSET U /\ &0 < eta /\
                   !s y. ts <= s /\ s < ts + eta /\ s < b /\ y IN N
                         ==> (?Y. rfs_cap (top,atlas) (g s) C eps U Y /\ y IN Y) \/
                             (y IN U /\ rfs_c_component (top,atlas) (g s) C U) \/
                             (y IN U /\ rfs_round_component (top,atlas) (g s) eps U)`,
  MP_TAC(ISPECL [`(:A)`; `(:A)`] P2B_PROP_9_79_OPEN_TYPED) THEN
  REWRITE_TAC[P2B_PROP_9_79_OPEN_TYPED_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "cap"))))
    (CONJUNCTS_THEN2 (LABEL_TAC "ccomp") (LABEL_TAC "round")))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) ts)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `ts:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. ts <= s /\ s < b
                    ==> riemannian_metric atlas ((g:real->A->real^3^3) s) /\
                        mfd_complete (top,atlas) (g s)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `s:real`]
                  RFA_RICCI_FLOW_FROM_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BL_COMPACT_COMPLETE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = mfd_scalar atlas ((g:real->A->real^3^3) ts) x` THEN
  STRIP_TAC THENL
   [(* cap *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) ts`; `C:real`; `eps:real`; `U:A->bool`;
                   `Y:A->bool`] APX_CAP_CORE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_cap]; ALL_TAC] THEN
    USE_THEN "cap" (MP_TAC o SPECL [`C:real`; `eps:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`; `x:A`;
      `U:A->bool`; `Y:A->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `ts:real`; `Q:real`;
                   `U:A->bool`; `delta:real`] P3H_SLAB_MCLOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`Y:A->bool`; `eta:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[P2B_CAP_CORE_SUBSET]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) s`; `\x:A. x`; `\x:A. x`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID];
    (* C-component *)
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                    P3H_MFD_COMPONENT_OPEN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_c_component]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) IN connected_components_of top` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_c_component]; ALL_TAC] THEN
    USE_THEN "ccomp" (MP_TAC o SPECL [`C:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`; `x:A`;
      `U:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `ts:real`; `Q:real`;
                   `U:A->bool`; `delta:real`] P3H_SLAB_MCLOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `eta:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) s`; `\x:A. x`; `\x:A. x`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID];
    (* round component *)
    SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`]
                    P3H_MFD_COMPONENT_OPEN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[rfs_round_component]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) IN connected_components_of top` ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_round_component]; ALL_TAC] THEN
    USE_THEN "round" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `(g:real->A->real^3^3) ts`; `x:A`;
      `U:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `a:real`; `b:real`; `ts:real`; `Q:real`;
                   `U:A->bool`; `delta:real`] P3H_SLAB_MCLOSE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `eta:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
    DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) s`; `\x:A. x`; `\x:A. x`] o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID]]);;

(* History form: at a time ts of slab k, a static strong canonical          *)
(* neighbourhood of x persists on a box N x [ts, ts + d).                    *)

let P3H_OPEN_STATIC_HIST = prove
 (`?eps0. &0 < eps0 /\
     !(hs:(A)rfs_history) C eps k ts x U.
       rfs_history_ok hs /\ k <= hs_count hs /\
       hs_time hs k <= ts /\ ts < hs_time hs (k + 1) /\
       &1 < C /\ &0 < eps /\ eps <= eps0 /\
       &0 < mfd_scalar (hs_atlas hs k) (hs_metric hs k ts) x /\
       ((?Y. rfs_cap (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) C eps U Y /\ x IN Y) \/
        (x IN U /\ rfs_c_component (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) C U) \/
        (x IN U /\ rfs_round_component (hs_top hs k,hs_atlas hs k) (hs_metric hs k ts) eps U))
       ==> ?N d. open_in (hs_top hs k) N /\ x IN N /\ &0 < d /\
                 !s y. ts <= s /\ s < ts + d /\ s < hs_time hs (k + 1) /\ y IN N
                       ==> p3_canon_at (rfs_view hs) C eps y s`,
  MP_TAC(INST_TYPE [`:A`,`:A`] P3H_STATIC_PERSIST) THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pers")))) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "pers" (MP_TAC o SPECL
    [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
     `hs_metric (hs:(A)rfs_history) k`; `hs_time (hs:(A)rfs_history) k`;
     `hs_time (hs:(A)rfs_history) (k + 1)`; `ts:real`; `C:real`; `eps:real`; `x:A`;
     `U:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:A->bool` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`N:A->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[p3_canon_at; rfs_view; rfs_strong_canonical] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `U:A->bool` THEN DISJ2_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

