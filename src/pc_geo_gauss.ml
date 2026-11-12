(* ========================================================================= *)
(* pc_geo_gauss: the Gauss lemma (MFD_GAUSS_LEMMA), by the variation        *)
(* f(s,t) = exp_x(t(v + s w)), the symmetry lemma MFD_COVD_SYMMETRY and     *)
(* metric compatibility MFD_COVD_METRIC.  MFD_GAUSS_LEMMA belongs to the     *)
(* geodesics API pc_geo_iface.                                               *)
(*                                                                           *)
(* A product neighbourhood of the radial segment.                            *)
(* ========================================================================= *)

needs "src/pc_geo_covd.ml";;
needs "src/pc_geo_param.ml";;

prioritize_real();;
type_invention_error := true;;

let GEOG_FAMILY_DOMAIN = prove
 (`!D (v:real^N) w.
        open D /\ v IN D /\ (!u t. u IN D /\ &0 <= t /\ t <= &1 ==> t % u IN D)
        ==> ?d e. &0 < d /\ &0 < e /\ e <= &1 /\
                  !s t. abs s < d /\ --e < t /\ t < &1 + e
                        ==> t % (v + s % w) IN D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (\r:real^1. drop r % (v:real^N)) (interval[vec 0,vec 1])`;
                 `(:real^N) DIFF D`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; NOT_IN_EMPTY; IN_IMAGE;
                  IN_INTERVAL_1; DROP_VEC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!r p. &0 <= r /\ r <= &1 /\ dist(r % (v:real^N),p) < k ==> p IN D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r % (v:real^N)`; `p:real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_IMAGE; IN_INTERVAL_1; DROP_VEC] THEN
      EXISTS_TAC `lift r` THEN ASM_REWRITE_TAC[LIFT_DROP];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `M = norm(v:real^N) + norm(w:real^N) + &1` THEN
  SUBGOAL_THEN `&0 < M /\ norm(v:real^N) <= M /\ norm(w:real^N) <= M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN
    MP_TAC(ISPEC `w:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = k / (&4 * M)` THEN
  SUBGOAL_THEN `&0 < d /\ d * M = k / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `min (&1) d`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `max (&0) (min (&1) t)` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t' = max (&0) (min (&1) t)` THEN
  SUBGOAL_THEN `abs(t' - t) <= d /\ abs t <= &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_ARITH
   `t' % v - t % (v + s % w):real^N = (t' - t) % v - (t * s) % w`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(t' - t) * norm(v:real^N) + abs t * abs s * norm(w:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^N) = a /\ norm(y:real^N) = b ==> norm(x - y) <= a + b`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_MUL; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * M + &2 * d * M` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Coordinate curves of two-parameter maps smooth in charts:                 *)
(* continuity, C^1 on compact subintervals, differentiable velocity fields. *)
(* ========================================================================= *)

let GEOG_SLICE_CONTINUOUS = prove
 (`!top (f:real->real->A) S0 J s t.
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        s IN S0 /\ t IN J
        ==> continuous_map (subtopology euclideanreal S0,top) (\s. f s t) /\
            continuous_map (subtopology euclideanreal J,top) (f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN] THENL
   [SUBGOAL_THEN
     `(\s. (f:real->real->A) s t) o drop =
      (\z. f (drop(fstcart z)) (drop(sndcart z))) o (\r. pastecart r (lift t))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC];
    SUBGOAL_THEN
     `(f:real->real->A) s o drop =
      (\z. f (drop(fstcart z)) (drop(sndcart z))) o (\r. pastecart (lift s) r)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC]] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
                {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
     REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
     REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]]));;

(* The chart representatives of the coordinate curves are smooth near each *)
(* parameter value.                                                         *)

let GEOG_SLICE_REP_SMOOTH = prove
 (`!top atlas (f:real->real->A) S0 J (c:(A->bool)#(A->real^N)) s t.
        smooth_manifold_atlas top atlas /\ real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        smooth_map_on
          {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
          (\z. SND c (f (drop(fstcart z)) (drop(sndcart z)))) /\
        c IN atlas /\ s IN S0 /\ t IN J
        ==> open {r | pastecart r (lift t) IN
                      {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}} /\
            smooth_map_on
              {r | pastecart r (lift t) IN
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}}
              (\r. SND c (f (drop r) t)) /\
            open {r | pastecart (lift s) r IN
                      {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}} /\
            smooth_map_on
              {r | pastecart (lift s) r IN
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}}
              (\r. SND c (f s (drop r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Oc = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                    (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (Oc:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Oc" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
    EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {r | pastecart r (lift t) IN (Oc:real^(1,1)finite_sum->bool)} /\
    open {r | pastecart (lift s) r IN (Oc:real^(1,1)finite_sum->bool)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\r. SND (c:(A->bool)#(A->real^N)) ((f:real->real->A) (drop r) t)) =
      (\z. SND c (f (drop(fstcart z)) (drop(sndcart z)))) o (\r. pastecart r (lift t))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC];
    SUBGOAL_THEN
     `(\r. SND (c:(A->bool)#(A->real^N)) ((f:real->real->A) s (drop r))) =
      (\z. SND c (f (drop(fstcart z)) (drop(sndcart z)))) o (\r. pastecart (lift s) r)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]; ALL_TAC]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

(* The coordinate curves are C^1 on compact subintervals. *)

let GEOG_SLICE_C1 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J s t.
        smooth_manifold_atlas top atlas /\ real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        s IN S0 /\ t IN J
        ==> (!a b. a <= b /\ real_interval[a,b] SUBSET S0
                   ==> mfd_c1_curve (top,atlas) (\s. f s t) a b) /\
            (!a b. a <= b /\ real_interval[a,b] SUBSET J
                   ==> mfd_c1_curve (top,atlas) (f s) a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `s:real`; `t:real`] GEOG_SLICE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_c1_curve] THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `S0:real->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`; `s:real`; `t:real`] GEOG_SLICE_REP_SMOOTH) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[smooth_map_on] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{r | pastecart r (lift t) IN
                     {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                      (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1] THEN
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`drop r`; `t:real`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> can (term_match []
      `real_interval[a,b] SUBSET S0`) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`; `s:real`; `t:real`] GEOG_SLICE_REP_SMOOTH) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[smooth_map_on] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{r | pastecart (lift s) r IN
                     {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                      (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1] THEN
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `drop r`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> can (term_match []
      `real_interval[a,b] SUBSET J`) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN ASM_REWRITE_TAC[]]);;

(* The coordinate velocity fields are differentiable along the other       *)
(* coordinate curves.                                                        *)

let GEOG_SLICE_FIELD_DIFF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J s t.
        smooth_manifold_atlas top atlas /\ real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        s IN S0 /\ t IN J
        ==> mfd_field_diff atlas (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) J /\
            mfd_field_diff atlas (\s'. f s' t) (\s'. mfd_vel atlas (f s') t) S0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_field_diff] THEN
  CONJ_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(f:real->real->A) s r IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`;
                     `J:real->bool`; `s:real`; `r:real`] GEOG_SLICE_CONTINUOUS) THEN
      ASM_REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(f:real->real->A) s r`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s r)` THEN
    STRIP_TAC THEN
    ABBREV_TAC `Oc = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                      (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}` THEN
    SUBGOAL_THEN `open (Oc:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Oc" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
      EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Oc:real^(1,1)finite_sum->bool`; `s:real`; `r:real`] GEOC_PAIR_NEAR) THEN
    ANTS_TAC THENL [EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "nt")))) THEN
    ABBREV_TAC `H = \z. frechet_derivative
                          (\z. SND (c:(A->bool)#(A->real^N))
                                 ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                          (at z) (pastecart (vec 1) (vec 0))` THEN
    SUBGOAL_THEN
     `(H:real^(1,1)finite_sum->real^N) differentiable at (pastecart (lift s) (lift r))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `smooth_map_on Oc (H:real^(1,1)finite_sum->real^N)` ASSUME_TAC THENL
       [EXPAND_TAC "H" THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Oc" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\q. (H:real^(1,1)finite_sum->real^N) (pastecart (lift s) q)` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `q:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN
      USE_THEN "nt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(drop q - r) < e`))) THEN
      EXPAND_TAC "Oc" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN STRIP_TAC THEN
      REWRITE_TAC[mfd_field_rep] THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                     `c:(A->bool)#(A->real^N)`; `s:real`; `drop q`] GEOC_VEL_CHART2) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`H:real^(1,1)finite_sum->real^N`; `lift s`; `lift r`]
        GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[differentiable; has_vector_derivative]];
    SUBGOAL_THEN `(f:real->real->A) r t IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`;
                     `J:real->bool`; `r:real`; `t:real`] GEOG_SLICE_CONTINUOUS) THEN
      ASM_REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(f:real->real->A) r t`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) r t)` THEN
    STRIP_TAC THEN
    ABBREV_TAC `Oc = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                      (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N))}` THEN
    SUBGOAL_THEN `open (Oc:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Oc" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
      EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Oc:real^(1,1)finite_sum->bool`; `r:real`; `t:real`] GEOC_PAIR_NEAR) THEN
    ANTS_TAC THENL [EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ns") (K ALL_TAC)))) THEN
    ABBREV_TAC `H = \z. frechet_derivative
                          (\z. SND (c:(A->bool)#(A->real^N))
                                 ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                          (at z) (pastecart (vec 0) (vec 1))` THEN
    SUBGOAL_THEN
     `(H:real^(1,1)finite_sum->real^N) differentiable at (pastecart (lift r) (lift t))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `smooth_map_on Oc (H:real^(1,1)finite_sum->real^N)` ASSUME_TAC THENL
       [EXPAND_TAC "H" THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Oc" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Oc:real^(1,1)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\q. (H:real^(1,1)finite_sum->real^N) (pastecart q (lift t))` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `q:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN
      USE_THEN "ns" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(drop q - r) < e`))) THEN
      EXPAND_TAC "Oc" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN STRIP_TAC THEN
      REWRITE_TAC[mfd_field_rep] THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_DROP] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                     `c:(A->bool)#(A->real^N)`; `drop q`; `t:real`] GEOC_VEL_CHART2) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`H:real^(1,1)finite_sum->real^N`; `lift r`; `lift t`]
        GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[differentiable; has_vector_derivative]]]);;

(* ========================================================================= *)
(* The family f(s,t) = exp_x(t(v + s w)): continuity and chart               *)
(* smoothness, its t-curves are geodesics of constant speed, and the        *)
(* differential of exp_x along curves.                                      *)
(* ========================================================================= *)

let GEOG_PHI_SMOOTH = prove
 (`!s (v:real^N) w.
        open s
        ==> smooth_map_on s
              (\z:real^(1,1)finite_sum. drop(sndcart z) % (v + drop(fstcart z) % w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOF_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_SNDCART];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC GEOF_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_FSTCART]]);;

(* Continuity and chart smoothness of the family. *)

let GEOG_EXP_FAMILY_CHARTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w d e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        (!s t. abs s < d /\ --e < t /\ t < &1 + e
               ==> t % (v + s % w) IN mfd_exp_dom (top,atlas) g x)
        ==> continuous_map
              (subtopology euclidean
                 {pastecart (lift s) (lift t) |
                  s IN real_interval(--d,d) /\ t IN real_interval(--e,&1 + e)},top)
              (\z. mfd_exp (top,atlas) g x (drop(sndcart z) % (v + drop(fstcart z) % w))) /\
            (!c. c IN atlas
                 ==> smooth_map_on
                       {pastecart (lift s) (lift t) |
                        s IN real_interval(--d,d) /\ t IN real_interval(--e,&1 + e) /\
                        mfd_exp (top,atlas) g x (t % (v + s % w)) IN FST c}
                       (\z. SND c (mfd_exp (top,atlas) g x
                                     (drop(sndcart z) % (v + drop(fstcart z) % w)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fam"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) x` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D2 = {pastecart (lift s) (lift t) |
                    s IN real_interval(--d,d) /\ t IN real_interval(--e,&1 + e)}` THEN
  ABBREV_TAC `Phi = \z:real^(1,1)finite_sum. drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)` THEN
  SUBGOAL_THEN `IMAGE (Phi:real^(1,1)finite_sum->real^N) D2 SUBSET D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"; "D2"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN USE_THEN "fam" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w))) =
                E o (Phi:real^(1,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean D2,top)
      (\z. (E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (D:real^N->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    EXPAND_TAC "Phi" THEN MATCH_MP_TAC GEOG_PHI_SMOOTH THEN REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `\s t. (E:real^N->A) (t % ((v:real^N) + s % w))`;
                 `real_interval(--d,d)`; `real_interval(--e,&1 + e)`;
                 `FST(c:(A->bool)#(A->real^N))`] GEOC_PAIR_CHART_OPEN) THEN
  ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC
       `continuous_map (subtopology euclidean D2,top)
          (\z. (E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)))` THEN
      EXPAND_TAC "D2" THEN REWRITE_TAC[];
      ASM_MESON_TAC[MFDM_CHART]];
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `E:real^N->A`; `D:real^N->bool`; `c:(A->bool)#(A->real^N)`]
    GEOP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. SND (c:(A->bool)#(A->real^N))
          ((E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)))) =
    (\u. SND c (E u)) o (Phi:real^(1,1)finite_sum->real^N)`
  SUBST1_TAC THENL [EXPAND_TAC "Phi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{u | u IN D /\ (E:real^N->A) u IN FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "fam" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    EXPAND_TAC "Phi" THEN MATCH_MP_TAC GEOG_PHI_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* The t-curves of the family are geodesics of constant speed. *)

let GEOG_EXP_FAMILY_GEO = prove
 (`!top atlas (g:A->real^N^N) (x:A) (u:real^N) e.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < e /\
        (!t. --e < t /\ t < &1 + e ==> t % u IN mfd_exp_dom (top,atlas) g x)
        ==> mfd_geodesic (top,atlas) g (\t. mfd_exp (top,atlas) g x (t % u))
                         (real_interval(--e,&1 + e)) /\
            mfd_exp (top,atlas) g x (&0 % u) = x /\
            (!t. --e < t /\ t < &1 + e
                 ==> mfd_tnorm g (mfd_exp (top,atlas) g x (t % u))
                       (mfd_vel atlas (\t. mfd_exp (top,atlas) g x (t % u)) t) =
                     mfd_tnorm g x u)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fam")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x u` THEN
  STRIP_TAC THEN
  ABBREV_TAC `J = real_interval(--e,&1 + e)` THEN
  SUBGOAL_THEN
   `!t. t IN J ==> t IN M /\ mfd_exp (top,atlas) (g:A->real^N^N) x (t % u) = gam t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "fam" (fun th -> MP_TAC(MATCH_MP th (ASSUME `--e < t /\ t < &1 + e`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) gam J` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `M:real->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_geodesic (top,atlas) (g:A->real^N^N)
      (\t. mfd_exp (top,atlas) g x (t % u)) J`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `{J:real->bool}`; `\K:real->bool. (gam:real->A)`;
                   `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % u)`]
      GEOM_GEODESIC_GLUE) THEN
    REWRITE_TAC[UNIONS_1; IN_SING; FORALL_UNWIND_THM2] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "J" THEN REWRITE_TAC[IS_REALINTERVAL_INTERVAL]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&0) IN J /\ t IN J` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % u)`;
                 `J:real->bool`; `t:real`; `&0`] MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `mfd_vel atlas (\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % u)) (&0) =
    mfd_vel atlas (gam:real->A) (&0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> can (term_match []
      `!t. t IN (J:real->bool) ==> t IN (M:real->bool) /\ P t`) (concl th))) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "J" THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* The differential of exp_x read along curves through its domain. *)

let GEOG_DEXP_CURVE = prove
 (`!top atlas (g:A->real^N^N) (x:A) (u:real->real^N) h r0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        u r0 IN mfd_exp_dom (top,atlas) g x /\
        ((\r. u(drop r)) has_vector_derivative h) (at (lift r0))
        ==> mfd_vel atlas (\r. mfd_exp (top,atlas) g x (u r)) r0 =
            mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (u r0) h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS; mfd_vel] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) x` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(E:real^N->A) (u(r0:real)) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean D,top) (E:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(E:real^N->A) (u(r0:real))`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((E:real^N->A) (u(r0:real)))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `E:real^N->A`; `D:real^N->bool`; `c:(A->bool)#(A->real^N)`]
    GEOP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. SND (c:(A->bool)#(A->real^N)) ((E:real^N->A) y)) differentiable at (u(r0:real))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y | y IN D /\ (E:real^N->A) y IN FST (c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  SUBGOAL_THEN
   `(\r. SND (c:(A->bool)#(A->real^N)) ((E:real^N->A) (u(drop r)))) =
    (\y. SND c (E y)) o (\r. (u:real->real^N)(drop r))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
  ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

(* ========================================================================= *)
(* Small helpers and the derivative computation of the Gauss                 *)
(* lemma.                                                                    *)
(* ========================================================================= *)

(* The metric at a point is symmetric and positive semidefinite. *)

let GEOG_G_SYM_POS = prove
 (`!top atlas (g:A->real^N^N) p.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p IN topspace top
        ==> (!a b. a dot (g p ** b) = b dot (g p ** a)) /\
            (!a. &0 <= a dot (g p ** a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) p IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `a:real^N` THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    UNDISCH_TAC
     `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                   (metric_local atlas c (g:A->real^N^N))` THEN
    REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) p` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[]]);;

(* A real function with constant derivative c on an interval. *)

let GEOG_CONST_DERIV = prove
 (`!(phi:real->real) J c.
        is_realinterval J /\
        (!t. t IN J ==> (phi has_real_derivative c) (atreal t))
        ==> !a b. a IN J /\ b IN J ==> phi b - phi a = c * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. (phi:real->real) t - c * t`; `J:real->bool`]
    HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    SUBGOAL_THEN `&0 = c - c * &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
    DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `a:real`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `b:real`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Affine curves and the quadratic form along them. *)

let GEOG_AFFINE_VD = prove
 (`!(v:real^N) w x. ((\r:real^1. v + drop r % w) has_vector_derivative w) (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(\h:real^1. drop h % (w:real^N)) = (\h. vec 0 + drop h % w)`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[GEOF_LINEAR_DROP_VMUL]);;

let GEOG_DOT_BILINEAR = prove
 (`!G:real^N^N. bilinear (\x y:real^N. lift(x dot (G ** y)))`,
  GEN_TAC THEN REWRITE_TAC[bilinear; linear] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD; DOT_RMUL;
              DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL]);;

let GEOG_QUAD_DERIV = prove
 (`!(G:real^N^N) v w.
        ((\r. lift((v + drop r % w) dot (G ** (v + drop r % w)))) has_vector_derivative
         lift(v dot (G ** w) + w dot (G ** v))) (at (vec 0))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\(x:real^N) (y:real^N). lift(x dot ((G:real^N^N) ** y))`;
                 `\r:real^1. (v:real^N) + drop r % w`; `\r:real^1. (v:real^N) + drop r % w`;
                 `w:real^N`; `w:real^N`; `vec 0:real^1`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[GEOG_AFFINE_VD; GEOG_DOT_BILINEAR] THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_ADD]);;

(* ========================================================================= *)
(* The derivative of <d_t f, d_s f> along the radial geodesic.               *)
(* ========================================================================= *)

let GEOG_GAUSS_DERIV = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w d e t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < d /\ &0 < e /\
        (!s t. abs s < d /\ --e < t /\ t < &1 + e
               ==> t % (v + s % w) IN mfd_exp_dom (top,atlas) g x) /\
        --e < t /\ t < &1 + e
        ==> ((\r. lift(mfd_vel atlas (\t. mfd_exp (top,atlas) g x (t % v)) (drop r) dot
                       (g(mfd_exp (top,atlas) g x (drop r % v)) **
                        mfd_vel atlas (\s. mfd_exp (top,atlas) g x (drop r % (v + s % w)))
                                (&0))))
             has_vector_derivative lift(v dot (g x ** w))) (at (lift t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "fam") STRIP_ASSUME_TAC))))))) THEN
  ABBREV_TAC `S0 = real_interval(--d,d)` THEN
  ABBREV_TAC `J = real_interval(--e,&1 + e)` THEN
  SUBGOAL_THEN `real_open S0 /\ is_realinterval S0 /\ real_open J /\ is_realinterval J /\
                &0 IN S0 /\ t IN J`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S0"; "J"] THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* continuity and chart smoothness of the family *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`; `d:real`; `e:real`]
    GEOG_EXP_FAMILY_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the radial geodesic gamma0(t) = exp(t v) *)
  SUBGOAL_THEN
   `mfd_geodesic (top,atlas) (g:A->real^N^N)
      (\t. mfd_exp (top,atlas) g x (t % v)) J`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `e:real`] GEOG_EXP_FAMILY_GEO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      USE_THEN "fam" (fun th -> MP_TAC(SPECL [`&0`; `r:real`] th)) THEN
      REWRITE_TAC[REAL_ABS_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)`;
                 `J:real->bool`] MFD_GEODESIC_VEL_PARALLEL) THEN
  ASM_REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  (* the general facts on the coordinate curves *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\s t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w))`;
                 `S0:real->bool`; `J:real->bool`; `&0`; `t:real`] GEOG_SLICE_FIELD_DIFF) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\s t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w))`;
                 `S0:real->bool`; `J:real->bool`; `&0`; `t:real`] GEOG_SLICE_C1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`;
                 `\s t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w))`;
                 `S0:real->bool`; `J:real->bool`; `&0`; `t:real`] MFD_COVD_SYMMETRY) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sym") THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (\t. mfd_exp (top,atlas) g x (t % v))
      (mfd_vel atlas (\t. mfd_exp (top,atlas) g x (t % v))) t = vec 0`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x (t % v) IN topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)`;
                   `J:real->bool`; `t:real`] GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* metric compatibility along the radial geodesic *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)`;
                 `J:real->bool`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                          (\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % v))`;
                 `\t'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                          (\s'. mfd_exp (top,atlas) (g:A->real^N^N) x (t' % (v + s' % w)))
                          (&0)`;
                 `t:real`] MFD_COVD_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_ADD_LID] THEN
  USE_THEN "sym" (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(MESON[]
   `(a:real^1) = b ==> ((f:real^1->real^1) has_vector_derivative a) net
                       ==> (f has_vector_derivative b) net`) THEN
  AP_TERM_TAC THEN
  (* metric compatibility along the s-curve at time t *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\s. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w))`;
                 `S0:real->bool`;
                 `\s'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                          (\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s' % w))) t`;
                 `\s'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                          (\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s' % w))) t`;
                 `&0`] MFD_COVD_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; LIFT_NUM] THEN
  DISCH_THEN(LABEL_TAC "dsig") THEN
  (* the energy along the s-curve is the quadratic form at x *)
  SUBGOAL_THEN
   `!r. abs r < d
        ==> mfd_vel atlas (\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + r % w))) t dot
            (g(mfd_exp (top,atlas) g x (t % (v + r % w))) **
             mfd_vel atlas (\t. mfd_exp (top,atlas) g x (t % (v + r % w))) t) =
            (v + r % w) dot (g x ** (v + r % w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(v:real^N) + r % w`; `e:real`]
      GEOG_EXP_FAMILY_GEO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real` THEN STRIP_TAC THEN
      USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[mfd_tnorm; SQRT_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\r. lift(mfd_vel atlas (\t. mfd_exp (top,atlas) (g:A->real^N^N) x
                                    (t % (v + drop r % w))) t dot
               (g(mfd_exp (top,atlas) g x (t % (v + drop r % w))) **
                mfd_vel atlas (\t. mfd_exp (top,atlas) g x (t % (v + drop r % w))) t)))
     has_vector_derivative lift(v dot (g x ** w) + w dot (g x ** v))) (at (vec 0))`
  (LABEL_TAC "dquad") THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\r. lift(((v:real^N) + drop r % w) dot ((g:A->real^N^N) x **
                                                       (v + drop r % w)))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[GEOG_QUAD_DERIV] THEN
    X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_0; NORM_1] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!r. abs r < d ==> P r`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "dsig" (fun th1 -> REMOVE_THEN "dquad" (fun th2 ->
    MP_TAC(MATCH_MP VECTOR_DERIVATIVE_UNIQUE_AT (CONJ th1 th2)))) THEN
  REWRITE_TAC[LIFT_EQ] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)`]
    GEOG_G_SYM_POS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "symx") (K ALL_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "symp") (K ALL_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!A B V W:real. A = B /\ W = V ==> A + B = V + W ==> B = V`) THEN
  CONJ_TAC THENL [USE_THEN "symp" MATCH_ACCEPT_TAC; USE_THEN "symx" MATCH_ACCEPT_TAC]);;

(* ========================================================================= *)
(* The Gauss lemma (MFD_GAUSS_LEMMA).                                        *)
(* ========================================================================= *)

let MFD_GAUSS_LEMMA = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) v v dot
            (g(mfd_exp (top,atlas) g x v) **
             mfd_differential (open_set_atlas (:real^N)) atlas
               (mfd_exp (top,atlas) g x) v w) =
            v dot (g x ** w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_exp_dom (top,atlas) (g:A->real^N^N) x`; `v:real^N`; `w:real^N`]
    GEOG_FAMILY_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `phi = \t. mfd_vel atlas (\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)) t dot
              (g(mfd_exp (top,atlas) g x (t % v)) **
               mfd_vel atlas (\s. mfd_exp (top,atlas) g x (t % (v + s % w))) (&0))` THEN
  SUBGOAL_THEN
   `!t. t IN real_interval(--e,&1 + e)
        ==> (phi has_real_derivative (v dot ((g:A->real^N^N) x ** w))) (atreal t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN EXPAND_TAC "phi" THEN
    REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`; `d:real`; `e:real`;
                   `t:real`] GEOG_GAUSS_DERIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real->real`; `real_interval(--e,&1 + e)`;
                 `v dot ((g:A->real^N^N) x ** w)`] GEOG_CONST_DERIV) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* phi at 0 vanishes *)
  SUBGOAL_THEN `(phi:real->real) (&0) = &0` SUBST1_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_GEODESIC_CONST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
    ALL_TAC] THEN
  (* phi at 1 is the left hand side *)
  SUBGOAL_THEN
   `(phi:real->real) (&1) =
    mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) (g:A->real^N^N) x) v v dot
    (g(mfd_exp (top,atlas) g x v) **
     mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g x) v w)`
  SUBST1_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `\t:real. t % (v:real^N)`; `v:real^N`; `&1`]
      GEOG_DEXP_CURVE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `\s:real. (v:real^N) + s % w`; `w:real^N`; `&0`]
      GEOG_DEXP_CURVE) THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[GEOG_AFFINE_VD] THEN DISCH_THEN SUBST1_TAC THEN
    ANTS_TAC THENL
     [REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[GEOF_LINEAR_DROP_VMUL];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

