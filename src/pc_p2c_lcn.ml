(* ========================================================================= *)
(* Unit pc_p2c_lcn (Part 2C): local compactness in form N, the theorem       *)
(* |- !u. P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT u (statement in              *)
(* pc_p2b_lcreqn).                                                           *)
(* A local limit in one normal chart about the base points: CGT gives a      *)
(* uniform injectivity radius at x n; phi n is the normal chart              *)
(* w |-> exp(E n ** w) of the time-0 slice; the pullbacks of the flows by    *)
(* phi n are Ricci flows on a ball of real^3 with uniform bounds (Shi on the *)
(* ball manifold, the gauge of Lemma 5.7 at time 0, space-time jets), so a  *)
(* subsequence converges (Arzela-Ascoli, P2CM_LOCAL_LIMIT); the limit is     *)
(* smooth up to time 0 by the time-mirrored Seeley extension.  The per-view  *)
(* machinery of pc_p2c_flloc / pc_p2c_flseq is used with the limit           *)
(* manifold (euclidean, open_set_atlas (:real^3)) and the map phi n.        *)
(* ========================================================================= *)

needs "src/pc_p2b_lcreqn.ml";;
needs "src/pc_p2c_fl514.ml";;
needs "src/pc_p2c_fl515.ml";;
needs "src/pc_p2c_cgunif.ml";;
needs "src/pc_cmp_cgt.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_rfa_spread.ml";;
needs "src/pc_p2c_stdinit.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smooth extension past the FINAL time of a slab (time-first               *)
(* coordinates), the mirror of PDE_SEELEY by the time reflection            *)
(* t |-> (a + b) - t; the iterated partials of the reflected map carry the  *)
(* sign (-1) for each time index (PDE_ITERATED_PARTIAL_COMPOSE).             *)
(* ------------------------------------------------------------------------- *)

let P2CD_TREFL_HAS_DERIVATIVE = prove
 (`!c (z:real^(1,N)finite_sum).
     ((\w:real^(1,N)finite_sum. pastecart (lift(c - drop(fstcart w))) (sndcart w))
      has_derivative (\h. pastecart (--fstcart h) (sndcart h))) (at z)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN
    SUBGOAL_THEN `(\h:real^(1,N)finite_sum. --fstcart h:real^1) = (\h. vec 0 - fstcart h)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_LZERO]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_FSTCART];
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART]]);;

let P2CD_TREFL_PARTIAL_BASIS = prove
 (`!c (z:real^(1,N)finite_sum) i.
     1 <= i /\ i <= dimindex(:N) + 1
     ==> partial_derivative i
           (\w:real^(1,N)finite_sum. pastecart (lift(c - drop(fstcart w))) (sndcart w)) z =
         (if i = 1 then --(&1) else &1) % (basis i:real^(1,N)finite_sum)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MP_TAC(SPECL [`c:real`; `z:real^(1,N)finite_sum`] P2CD_TREFL_HAS_DERIVATIVE) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PASTECART_EQ] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_CMUL; SNDCART_CMUL] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `1` (INST_TYPE [`:1`,`:M`; `:N`,`:N`] TEXT_BASIS_LOW)) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN VECTOR_ARITH_TAC;
    SUBGOAL_THEN `i = dimindex(:1) + (i - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[DIMINDEX_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `i - 1` (INST_TYPE [`:1`,`:M`; `:N`,`:N`] TEXT_BASIS_HIGH)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_NEG_0]]);;

let P2CD_TREFL_ITERATED_PARTIAL = prove
 (`!(f:real^(1,N)finite_sum->real^K) s c l.
     open s /\ smooth_map_on s f /\ ALL (\i. 1 <= i /\ i <= dimindex(:N) + 1) l
     ==> !z. pastecart (lift(c - drop(fstcart z))) (sndcart z) IN s
             ==> iterated_partial l
                   (\z. f(pastecart (lift(c - drop(fstcart z))) (sndcart z))) z =
                 ITLIST (\i r. (if i = 1 then --(&1) else &1) * r) l (&1) %
                 iterated_partial l f (pastecart (lift(c - drop(fstcart z))) (sndcart z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^K`;
    `\w:real^(1,N)finite_sum. pastecart (lift(c - drop(fstcart w))) (sndcart w)
                               :real^(1,N)finite_sum`;
    `s:real^(1,N)finite_sum->bool`;
    `\i. if i = 1 then --(&1) else &1`; `\i:num. i`; `l:num list`]
   PDE_ITERATED_PARTIAL_COMPOSE) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; MAP_ID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 + n = n + 1`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^(1,N)finite_sum. pastecart (--fstcart h) (sndcart h)
                                           :real^(1,N)finite_sum` THEN
      REWRITE_TAC[P2CD_TREFL_HAS_DERIVATIVE];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CD_TREFL_PARTIAL_BASIS THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

let P2CD_TREFL_SMOOTH = prove
 (`!c. smooth_map_on (:real^(1,N)finite_sum)
         (\w. pastecart (lift(c - drop(fstcart w))) (sndcart w):real^(1,N)finite_sum)`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; LIFT_SUB; LIFT_DROP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN `(fstcart:real^(1,N)finite_sum->real^1) = fstcart o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN `(sndcart:real^(1,N)finite_sum->real^N) = sndcart o (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

let P2CD_TREFL_CONTINUOUS = prove
 (`!c. (\w. pastecart (lift(c - drop(fstcart w))) (sndcart w):real^(1,N)finite_sum)
       continuous_on (:real^(1,N)finite_sum)`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  REWRITE_TAC[P2CD_TREFL_SMOOTH]);;

let P2CD_TREFL_INVOL = prove
 (`!c (w:real^(1,N)finite_sum).
     pastecart (lift(c - drop(fstcart (pastecart (lift(c - drop(fstcart w))) (sndcart w)))))
               (sndcart (pastecart (lift(c - drop(fstcart w))) (sndcart w))) = w`,
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `c - (c - x) = x:real`; LIFT_DROP; PASTECART_FST_SND]);;

(* The slab sets are exchanged by the reflection. *)

let P2CD_SLAB_SET_TOP = prove
 (`!a b (U:real^N->bool).
        {pastecart (lift t) y | a < t /\ t <= b /\ y IN U} =
        {w:real^(1,N)finite_sum | a < drop(fstcart w) /\ drop(fstcart w) <= b /\
                                  sndcart w IN U}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; FORALL_LIFT; IN_ELIM_THM] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; PASTECART_INJ] THEN
  REWRITE_TAC[LIFT_EQ] THEN MESON_TAC[]);;

let P2CD_TREFL_SLAB = prove
 (`!a b (U:real^N->bool) (w:real^(1,N)finite_sum).
     pastecart (lift((a + b) - drop(fstcart w))) (sndcart w) IN
       {pastecart (lift t) y | a < t /\ t <= b /\ y IN U} <=>
     w IN {pastecart (lift t) y | a <= t /\ t < b /\ y IN U}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2CD_SLAB_SET_TOP; PDE_SLAB_SET] THEN
  REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `a < (a + b) - d <=> d < b`;
              REAL_ARITH `(a + b) - d <= b <=> a <= d`] THEN
  CONV_TAC TAUT);;

let P2CD_UPTO_TOP = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
     open U /\ a < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U) (\z. u (drop(fstcart z)) (sndcart z)) /\
     (\w. u (drop(fstcart w)) (sndcart w)) continuous_on
       {pastecart (lift t) y | a < t /\ t <= b /\ y IN U} /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
          ==> ?h. h continuous_on {pastecart (lift t) y | a < t /\ t <= b /\ y IN U} /\
                  !t y. a < t /\ t < b /\ y IN U
                        ==> h(pastecart (lift t) y) =
                            iterated_partial l (\z. u (drop(fstcart z)) (sndcart z))
                                             (pastecart (lift t) y))
     ==> ?e FF. &0 < e /\
                smooth_map_on (interval(lift a,lift(b + e)) PCROSS U) FF /\
                !t y. a < t /\ t <= b /\ y IN U ==> FF(pastecart (lift t) y) = u t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hu"))))) THEN
  ABBREV_TAC `R = \w:real^(1,N)finite_sum. pastecart (lift((a + b) - drop(fstcart w))) (sndcart w)
                                           :real^(1,N)finite_sum` THEN
  ABBREV_TAC `uf = \w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `!w. (uf:real^(1,N)finite_sum->real^K) ((R:real^(1,N)finite_sum->real^(1,N)finite_sum) w) =
                    (u:real->real^N->real^K) ((a + b) - drop(fstcart w)) (sndcart w)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["uf"; "R"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,N)finite_sum) (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2CD_TREFL_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^(1,N)finite_sum.
                  w IN interval(lift a,lift b) PCROSS (U:real^N->bool)
                  ==> (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN interval(lift a,lift b) PCROSS U`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^(1,N)finite_sum.
                  w IN {pastecart (lift t) y | a <= t /\ t < b /\ y IN U}
                  ==> (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN
                      {pastecart (lift t) y | a < t /\ t <= b /\ y IN (U:real^N->bool)}`
  ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[P2CD_TREFL_SLAB]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift a,lift b) PCROSS (U:real^N->bool))
                  (uf:real^(1,N)finite_sum->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "uf" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                 `\t:real y:real^N. (u:real->real^N->real^K) ((a + b) - t) y`] PDE_SEELEY) THEN
  REWRITE_TAC[pde_upto_classical] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(\w:real^(1,N)finite_sum. (u:real->real^N->real^K) ((a + b) - drop(fstcart w)) (sndcart w)) =
                    (uf:real^(1,N)finite_sum->real^K) o (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{pastecart (lift t) y | a < t /\ t <= b /\ y IN (U:real^N->bool)}` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "uf" THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]];
      SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (u:real->real^N->real^K) ((a + b) - drop(fstcart z)) (sndcart z)) =
                    (uf:real^(1,N)finite_sum->real^K) o (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SUBSET; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      USE_THEN "hu" (MP_TAC o C MP
        (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l`) o SPEC `l:num list`) THEN
      DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\w:real^(1,N)finite_sum.
                    ITLIST (\i r. (if i = 1 then --(&1) else &1) * r) l (&1) %
                    (h:real^(1,N)finite_sum->real^K) ((R:real^(1,N)finite_sum->real^(1,N)finite_sum) w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        SUBGOAL_THEN `(\w:real^(1,N)finite_sum. (h:real^(1,N)finite_sum->real^K)
                         ((R:real^(1,N)finite_sum->real^(1,N)finite_sum) w)) = h o R`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
          REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `{pastecart (lift t) y | a < t /\ t <= b /\ y IN (U:real^N->bool)}` THEN
          ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (u:real->real^N->real^K) ((a + b) - drop(fstcart z)) (sndcart z)) =
                      (\z. (uf:real^(1,N)finite_sum->real^K)
                             (pastecart (lift((a + b) - drop(fstcart z))) (sndcart z)))`
        SUBST1_TAC THENL
         [EXPAND_TAC "uf" THEN REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                                            LIFT_DROP];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`uf:real^(1,N)finite_sum->real^K`;
                       `interval(lift a,lift b) PCROSS (U:real^N->bool)`; `a + b:real`;
                       `l:num list`] P2CD_TREFL_ITERATED_PARTIAL) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
          UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
          REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SYM];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; PASTECART_IN_PCROSS;
                    IN_INTERVAL_1] THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        EXPAND_TAC "R" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
        CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`(a + b) - t:real`; `y:real^N`] o
          check (fun th -> is_forall(concl th) &&
                           can (find_term ((=) `h:real^(1,N)finite_sum->real^K`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "uf" THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `G:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `(G:real^(1,N)finite_sum->real^K) o
                                   (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(a + b) - t:real`; `y:real^N`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `G:real^(1,N)finite_sum->real^K`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The time-0 slices, a uniform injectivity radius at the base               *)
(* points (CGT), and the normal charts phi w = exp_x(E ** w).               *)
(* ------------------------------------------------------------------------- *)

let P2CD_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x.
     p2c_regular_view V /\ x IN topspace (rfs_vtop V (&0))
     ==> hausdorff_space (rfs_vtop V (&0)) /\
         smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
         riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_regular_view] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* A uniform injectivity radius at the base points (CMP_T2_CGT). *)

let P2CD_INJ = prove
 (`!K r1 v0.
     &0 < K /\ &0 < r1 /\ &0 < v0
     ==> ?i0. &0 < i0 /\ i0 < r1 /\
              !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x.
                p2c_regular_view V /\ x IN topspace (rfs_vtop V (&0)) /\
                compact_in (rfs_vtop V (&0))
                  (rfs_vtop V (&0) closure_of rfs_vball V (&0) x r1) /\
                (!y. y IN rfs_vball V (&0) x r1
                     ==> mfd_rm_norm (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) y <= K) /\
                (?v. mfd_has_volume (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                    (rfs_vball V (&0) x r1) v /\ v0 <= v)
                ==> mfd_inj_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x i0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[CMP_T2_CGT_STATEMENT] (ISPEC `(:A)` CMP_T2_CGT)) THEN
  DISCH_THEN(MP_TAC o SPECL [`K:real`; `r1:real`; `v0:real`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i0:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cgt"))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CD_SLICE o CONJ
    (ASSUME `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))`)) THEN
  USE_THEN "cgt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM P2CO_VBALL] THEN
  ASM_MESON_TAC[]);;

(* The normal chart at x for an orthonormal frame E, on ball(vec 0,r0). *)

let P2CD_NCHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E i0 r0.
     p2c_regular_view V /\ x IN topspace (rfs_vtop V (&0)) /\
     mfd_inj_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x i0 /\
     mfd_orthonormal_frame (rfs_vmetric V (&0)) x E /\ &0 < r0 /\ r0 <= i0
     ==> mfd_param (rfs_vtop V (&0)) (rfs_vatlas V (&0)) (ball(vec 0,r0))
           (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w)) /\
         mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** vec 0) = x /\
         IMAGE (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w))
               (ball(vec 0,r0)) = rfs_vball V (&0) x r0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CD_SLICE o CONJ
    (ASSUME `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))`)) THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)`;
                 `x:A`; `i0:real`; `r0:real`] MFD_INJ_BALL_MONO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)`;
                 `x:A`; `E:real^3^3`; `r0:real`] P2CU_NCH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[P2CO_VBALL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)`;
                 `x:A`] MFD_EXP_DOM) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One view with its normal chart phi on ball(vec 0,r0) in the              *)
(* per-view setting p2cv_one of pc_p2c_flloc, with the "limit manifold"      *)
(* (euclidean, open_set_atlas (:real^3)), t0 = 0 and q = 1; the pullback     *)
(* family p2cv_pb is rfs_pullback in the coordinates of the ball.           *)
(* ------------------------------------------------------------------------- *)

let P2CD_T01 = prove
 (`!s. &0 + s / &1 = s`,
  REWRITE_TAC[REAL_DIV_1; REAL_ADD_LID]);;

let P2CD_PB_RFS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (phi:real^3->A) s z.
     p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) phi s z =
     rfs_pullback (rfs_vatlas V s) phi (rfs_vmetric V s) z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2cv_pb; mfd_pullback_metric; rfs_pullback; P2CD_T01; MATRIX_CMUL_LID] THEN
  SIMP_TAC[RFB_OPEN_SET_CHART_AT; IN_UNIV; SND] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]);;

let P2CD_PB_RFS_FUN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (phi:real^3->A) s.
     p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) phi s =
     rfs_pullback (rfs_vatlas V s) phi (rfs_vmetric V s)`,
  REWRITE_TAC[FUN_EQ_THM; P2CD_PB_RFS]);;

(* The chart (:real^3),\x.x of the open set atlas and the ball. *)

let P2CD_C0 = prove
 (`((:real^3),(\x:real^3. x)) IN open_set_atlas (:real^3) /\
   !r. IMAGE (SND((:real^3),(\x:real^3. x))) (FST((:real^3),(\x:real^3. x)) INTER ball(vec 0,r)) =
       ball(vec 0,r) /\
       (!G:real^3->real^3^3. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) G = G)`,
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND; INTER_UNIV; IMAGE_ID;
              P2C_OPEN_SET_METRIC_LOCAL_UNIV]);;

let P2CD_ONE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E i0 r0 r1 a0 K.
     p2c_regular_view V /\ x IN topspace (rfs_vtop V (&0)) /\
     mfd_inj_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x i0 /\
     mfd_orthonormal_frame (rfs_vmetric V (&0)) x E /\ &0 < r0 /\ r0 <= i0 /\ r0 <= r1 /\
     a0 < &0 /\ rfs_persists V (rfs_vball V (&0) x r1) a0 (&0) /\
     (!s y. a0 < s /\ s <= &0 /\ y IN rfs_vball V (&0) x r1
            ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) y <= K)
     ==> p2cv_one V (euclidean,open_set_atlas (:real^3)) (ball(vec 0,r0))
           (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w))
           (&0) (&1) /\
         rfs_persists V
           (IMAGE (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w))
                  (ball(vec 0,r0))) a0 (&0) /\
         (!s z. a0 < s /\ s <= &0 /\
                z IN IMAGE (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x
                                        (E ** w)) (ball(vec 0,r0))
                ==> p3_vrm V s z <= K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CD_SLICE o CONJ
    (ASSUME `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))`)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `i0:real`; `r0:real`] P2CD_NCHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0) x r0 SUBSET rfs_vball V (&0) x r1`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CO_VBALL] THEN MATCH_MP_TAC P2CU_BALL_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2cv_one] THEN ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH] THEN
    REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; INST_TYPE [`:3`,`:N`] P2C_EUCLID_FACTS] THEN
    REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL; BALL_EQ_EMPTY; REAL_LT_01] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `mfd_param (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (&0)) (rfs_vatlas V (&0))
                   (ball(vec 0,r0))
                   (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w))` THEN
    REWRITE_TAC[mfd_param] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CO_PERSISTS_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (&0) x r1`; `&0`] THEN
    ASM_SIMP_TAC[P2CR_REGULAR_FROM_SMOOTH; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[P2CO_VBALL] THEN CONJ_TAC THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[p3_vrm] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The chart data of one view (p2cd_ok), the normal chart                   *)
(* p2cd_phi, the time-0 pullback = the normal-coordinate metric, and the     *)
(* comparison of the pullbacks at all times with the Euclidean metric.      *)
(* ------------------------------------------------------------------------- *)

let p2cd_phi = new_definition
 `p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
           (x:A) (E:real^3^3) (w:real^3) =
    mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w)`;;

let P2CD_PHI_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) x E.
     p2cd_phi V x E =
     (\w. mfd_exp (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x (E ** w))`,
  REWRITE_TAC[FUN_EQ_THM; p2cd_phi]);;

let p2cd_ok = new_definition
 `p2cd_ok (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
          (x:A) (E:real^3^3) r0 r1 a0 K <=>
    p2c_regular_view V /\ x IN topspace (rfs_vtop V (&0)) /\
    mfd_inj_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x r0 /\
    mfd_orthonormal_frame (rfs_vmetric V (&0)) x E /\
    &0 < r0 /\ r0 <= r1 /\ a0 < &0 /\ &0 <= K /\ K * r0 pow 2 <= &1 /\
    rfs_persists V (rfs_vball V (&0) x r1) a0 (&0) /\
    (!s y. a0 < s /\ s <= &0 /\ y IN rfs_vball V (&0) x r1
           ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) y <= K)`;;

(* Unfold the assumption p2cd_ok ... (wherever it is in the list). *)

let p2cd_ok_tac =
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cd_ok] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2cd_ok"
                     with Failure _ -> false));;

let P2CD_OK_ONE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K r.
     p2cd_ok V x E r0 r1 a0 K /\ &0 < r /\ r <= r0
     ==> p2cv_one V (euclidean,open_set_atlas (:real^3)) (ball(vec 0,r)) (p2cd_phi V x E)
                  (&0) (&1) /\
         rfs_persists V (IMAGE (p2cd_phi V x E) (ball(vec 0,r))) (&0 + a0 / &1) (&0 + &0 / &1) /\
         (!s z. a0 < s /\ s <= &0 /\ z IN IMAGE (p2cd_phi V x E) (ball(vec 0,r))
                ==> p3_vrm V (&0 + s / &1) z <= K * &1) /\
         mfd_param (rfs_vtop V (&0)) (rfs_vatlas V (&0)) (ball(vec 0,r)) (p2cd_phi V x E) /\
         p2cd_phi V x E (vec 0) = x /\
         IMAGE (p2cd_phi V x E) (ball(vec 0,r)) = rfs_vball V (&0) x r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cd_ok; P2CD_T01; REAL_MUL_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r:real`] P2CD_NCHART) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r:real`; `r1:real`; `a0:real`; `K:real`] P2CD_ONE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM p2cd_phi; ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[]);;

(* The time-0 pullback is the metric in normal coordinates: a metric field  *)
(* on the ball, between half and twice the Euclidean metric.                 *)

let P2CD_OK_PB0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K.
     p2cd_ok V x E r0 r1 a0 K
     ==> (!w. w IN ball(vec 0,r0)
              ==> p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) (&0) w =
                  cmp_expmetric (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x E w) /\
         metric_field (ball(vec 0,r0))
           (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) (&0)) /\
         (!w v. w IN ball(vec 0,r0)
                ==> inv(&2) * norm v pow 2 <=
                    v dot (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) (&0) w
                           ** v) /\
                    v dot (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) (&0) w
                           ** v) <= &2 * norm v pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2cd_ok]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CD_SLICE o CONJ
    (ASSUME `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))`)) THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `K:real`] P2CU_EXPMETRIC_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `mfd_rm_norm:((A->bool)#(A->real^3)->bool)->(A->real^3^3)->A->real`))
          (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0)`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) (&0)`;
                   `x:A`; `r0:real`; `r1:real`] P2CU_BALL_MONO) THEN
    ASM_REWRITE_TAC[P2CO_VBALL; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "qf") (LABEL_TAC "eq"))))) THEN
  SUBGOAL_THEN
   `!w. w IN ball(vec 0,r0)
        ==> p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                    (p2cd_phi V (x:A) E) (&0) w =
            cmp_expmetric (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x E w`
  (LABEL_TAC "pb0") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[P2CD_PB_RFS; rfs_pullback; P2CD_PHI_ALT] THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^3) IN ball(vec 0,r0)`)]);
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "pb0" ACCEPT_TAC;
    MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
    EXISTS_TAC `cmp_expmetric (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                           (real->A->real^3^3)) (&0),rfs_vatlas V (&0))
                              (rfs_vmetric V (&0)) x E` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "pb0" ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`w:real^3`; `v:real^3`] THEN DISCH_TAC THEN
    USE_THEN "pb0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^3) IN ball(vec 0,r0)`)]) THEN
    USE_THEN "qf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM IN_BALL_0]]);;

let P2CD_PERSISTS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) W a a' b.
     rfs_persists V W a b /\ a <= a' ==> rfs_persists V W a' b`,
  REWRITE_TAC[P2CO_PERSISTS_ALT] THEN MESON_TAC[REAL_LET_TRANS]);;

(* Comparison of the pullbacks at two times of [a1,0], a0 < a1 < 0. *)

let P2CD_OK_QF0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K a1 w v s1 s2.
     p2cd_ok V x E r0 r1 a0 K /\ a0 < a1 /\ a1 < &0 /\ w IN ball(vec 0,r0) /\
     (a1 < s1 \/ s1 = &0) /\ s1 <= &0 /\ (a1 < s2 \/ s2 = &0) /\ s2 <= &0
     ==> v dot (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s1 w ** v) <=
         exp(&8 * K * (&0 - a1)) *
         (v dot (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s2 w ** v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN p2cd_ok_tac THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `r0:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; P2CD_T01; REAL_MUL_RID] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `ball(vec 0:real^3,r0)`;
                 `p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) x E`;
                 `&0`; `&1`; `a1:real`; `&0`; `((:real^3),(\x:real^3. x))`; `K:real`;
                 `w:real^3`; `v:real^3`; `s1:real`; `s2:real`] P2CV_QF_ALL) THEN
  REWRITE_TAC[P2CD_C0; P2CD_T01; REAL_MUL_RID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2CD_PERSISTS_MONO THEN EXISTS_TAC `a0:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* Comparison with the Euclidean metric at all times of [a1,0], a0 < a1 < 0. *)

let P2CD_OK_QF = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K a1 s w v.
     p2cd_ok V x E r0 r1 a0 K /\ a0 < a1 /\ a1 < &0 /\ (a1 < s \/ s = &0) /\ s <= &0 /\
     w IN ball(vec 0,r0)
     ==> norm v pow 2 <=
         (&2 * exp(&8 * K * (&0 - a1))) *
         (v dot (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s w ** v)) /\
         v dot (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s w ** v) <=
         (&2 * exp(&8 * K * (&0 - a1))) * norm v pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`] P2CD_OK_PB0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (MP_TAC o SPECL [`w:real^3`; `v:real^3`]))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `a1:real`;
                 `w:real^3`; `v:real^3`; `&0`; `s:real`] P2CD_OK_QF0) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `a1:real`;
                 `w:real^3`; `v:real^3`; `s:real`; `&0`] P2CD_OK_QF0) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ABBREV_TAC `Ex = exp(&8 * K * (&0 - a1))` THEN
  SUBGOAL_THEN `&0 <= Ex` ASSUME_TAC THENL
   [EXPAND_TAC "Ex" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `Ex * (v dot (p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                            (p2cd_phi V (x:A) E) (&0) w ** v)) <=
      Ex * (&2 * norm(v:real^3) pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Shi's estimates for the pulled-back flows on the ball                     *)
(* manifold (subtopology euclidean B, restrict_atlas (open_set_atlas UNIV) B),*)
(* B = ball(vec 0,r0), uniformly over the views: the balls of the region    *)
(* manifold lie in Euclidean balls (Euclidean comparison of P2CD_OK_QF),     *)
(* RFA_P2_THM_3_28 at the final times s in [a0/2,0] from a1 = 3 a0/4, and    *)
(* the transfer to the chart (P2CQ_REGION_RMD2).                             *)
(* ------------------------------------------------------------------------- *)

(* The ball part of FLT_EUCLID_BALL (pc_p2b_flatknc), from MFD_DIST_EUCLIDEAN. *)

let P2CD_EUCLID_BALL = prove
 (`!(x:real^3) r. mfd_ball (euclidean,open_set_atlas (:real^3)) (\x. mat 1) x r = ball(x,r)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `(:real^3)` MFD_DIST_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[mfd_ball; EXTENSION; IN_ELIM_THM; IN_BALL]);;

(* Balls of the region manifold of the chart ball. *)

let P2CD_REGION_BALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K a1 s w d.
     p2cd_ok V x E r0 r1 a0 K /\ a0 < a1 /\ a1 < &0 /\ (a1 < s \/ s = &0) /\ s <= &0 /\
     &0 < d /\ cball(w,d) SUBSET ball(vec 0,r0)
     ==> mfd_ball (subtopology euclidean (ball(vec 0,r0)),
                   restrict_atlas (open_set_atlas (:real^3)) (ball(vec 0,r0)))
                  (restrict_metric (open_set_atlas (:real^3)) (ball(vec 0,r0))
                     (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s))
                  w (d / sqrt(&2 * exp(&8 * K * (&0 - a1)))) SUBSET ball(w,d) /\
         compact_in (subtopology euclidean (ball(vec 0,r0)))
           (subtopology euclidean (ball(vec 0,r0)) closure_of
            mfd_ball (subtopology euclidean (ball(vec 0,r0)),
                      restrict_atlas (open_set_atlas (:real^3)) (ball(vec 0,r0)))
                     (restrict_metric (open_set_atlas (:real^3)) (ball(vec 0,r0))
                        (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s))
                     w (d / sqrt(&2 * exp(&8 * K * (&0 - a1)))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN p2cd_ok_tac THEN
  ABBREV_TAC `L = &2 * exp(&8 * K * (&0 - a1))` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,r0)` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(w:real^3,d) SUBSET ball(vec 0,r0)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `r0:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `riemannian_metric (restrict_atlas (open_set_atlas (:real^3)) (ball(vec 0,r0)))
      (restrict_metric (open_set_atlas (:real^3)) (ball(vec 0,r0))
         (p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                  (p2cd_phi V (x:A) E) s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CQ_PB_RIEM THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `a0:real`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `ball(vec 0:real^3,r0)`; `ball(w:real^3,d)`; `(\x:real^3. mat 1):real^3->real^3^3`;
                   `restrict_metric (open_set_atlas (:real^3)) (ball(vec 0,r0))
                      (p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                               (p2cd_phi V (x:A) E) s)`;
                   `w:real^3`; `d:real`; `sqrt L`] P2CQ_REGION_BALL_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; GSYM OPEN_IN; OPEN_BALL; P2CD_EUCLID_BALL; SUBSET_REFL] THEN
      ASM_SIMP_TAC[SQRT_POS_LT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(w:real^3,d)` THEN
        ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`z:real^3`; `v:real^3`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN ball(vec 0,r0)` ASSUME_TAC THENL
       [UNDISCH_TAC `cball(w:real^3,d) SUBSET ball(vec 0,r0)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `(z:real^3) IN ball(w,d)` THEN REWRITE_TAC[IN_BALL; IN_CBALL] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                     `ball(vec 0:real^3,r0)`; `(\x:real^3. mat 1):real^3->real^3^3`;
                     `p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                              (p2cd_phi V (x:A) E) s`; `L:real`; `z:real^3`] P2CQ_RESTRICT_QF) THEN
      ASM_SIMP_TAC[GEOL_EUCLID_FACTS; GSYM OPEN_IN; OPEN_BALL; SQRT_POW_2; REAL_LT_IMP_LE] THEN
      ANTS_TAC THENL
       [X_GEN_TAC `u:real^3` THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID; DOT_SQUARE_NORM] THEN
        EXPAND_TAC "L" THEN
        MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                       `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `a1:real`;
                       `s:real`; `z:real^3`; `u:real^3`] P2CD_OK_QF) THEN
        ASM_SIMP_TAC[];
        DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN REWRITE_TAC[]];
      SIMP_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC P2CQ_REGION_BALL_COMPACT THEN
    EXISTS_TAC `ball(w:real^3,d)` THEN
    ASM_SIMP_TAC[GSYM OPEN_IN; OPEN_BALL; EUCLIDEAN_CLOSURE_OF; CLOSURE_BALL;
                 COMPACT_IN_EUCLIDEAN; COMPACT_CBALL]]);;

(* Shi's estimates in the normal coordinates, uniformly over the views, at *)
(* the final times s in [b,0] for any a0 < b < 0 (from a1 = (a0 + b) / 2    *)
(* with tau = (b - a0) / 2); P2CD_SHI is the case b = a0 / 2.               *)

let P2CD_SHI_GEN = prove
 (`!r0 r1 a0 b K l rho.
     &0 < rho /\ rho < r0 /\ a0 < b /\ b < &0 /\ &0 <= K
     ==> ?C. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
              x E s w.
               p2cd_ok V x E r0 r1 a0 K /\ b <= s /\ s <= &0 /\ w IN ball(vec 0,rho)
               ==> lrm_deriv_norm2 l
                     (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s) w <= C`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a1 = (a0 + b) / &2` THEN
  SUBGOAL_THEN `a0 < a1 /\ a1 < &0 /\ a1 < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `L = &2 * exp(&8 * K * (&0 - a1))` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `d = (r0 - rho) / &2` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = d / sqrt L` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "curv"))
    (INST_TYPE [`:real^3`,`:B`] P2CQ_PB_CURV) THEN
  ABBREV_TAC `Kc = sqrt C0 * K + &1` THEN
  SUBGOAL_THEN `&0 < Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3)` RFA_P2_THM_3_28) THEN REWRITE_TAC[P2_THM_3_28_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num`; `Kc:real`; `r:real`; `(b - a0) / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cl:real` (LABEL_TAC "Cl")) THEN EXISTS_TAC `Cl:real` THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `E:real^3^3`; `s:real`; `w:real^3`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN p2cd_ok_tac THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `r0:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,r0) /\ cball(w:real^3,d) SUBSET ball(vec 0,r0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN ball(vec 0,rho)` THEN
    REWRITE_TAC[IN_BALL_0; SUBSET; IN_CBALL; IN_BALL; DIST_0] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z:real^3`; `w:real^3`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`w:real^3`; `z:real^3`] NORM_SUB) THEN
    UNDISCH_TAC `dist(w:real^3,z) <= d` THEN
    REWRITE_TAC[dist] THEN EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `a1:real`;
                 `s:real`; `w:real^3`; `d:real`] P2CD_REGION_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rbin") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. (a0 < t \/ t = &0) /\ t <= &0
        ==> riemannian_metric (restrict_atlas (open_set_atlas (:real^3)) (ball(vec 0,r0)))
              (restrict_metric (open_set_atlas (:real^3)) (ball(vec 0,r0))
                 (p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                          (p2cd_phi V (x:A) E) t))`
  (LABEL_TAC "riem") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CQ_PB_RIEM THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `a0:real`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Cl" (MP_TAC o SPECL
   [`subtopology euclidean (ball(vec 0:real^3,r0))`;
    `restrict_atlas (open_set_atlas (:real^3)) (ball(vec 0:real^3,r0))`;
    `a1:real`; `s:real`;
    `\t. restrict_metric (open_set_atlas (:real^3)) (ball(vec 0:real^3,r0))
           (p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                    (p2cd_phi V (x:A) E) t)`; `w:real^3`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
      MATCH_MP_TAC P2CQ_PB_UPTO THEN MAP_EVERY EXISTS_TAC [`a0:real`; `&0`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt C0 * K` THEN
      CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "Kc" THEN REAL_ARITH_TAC] THEN
      USE_THEN "curv" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `a0:real`; `&0`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `(y:real^3) IN ball(vec 0,r0)` ASSUME_TAC THENL
       [USE_THEN "rbin" (MP_TAC o SPEC `y:real^3` o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        UNDISCH_TAC `cball(w:real^3,d) SUBSET ball(vec 0,r0)` THEN
        MP_TAC(ISPECL [`w:real^3`; `d:real`] BALL_SUBSET_CBALL) THEN
        UNDISCH_TAC `(y:real^3) IN ball(w,d)` THEN SET_TAC[];
        ASM_REWRITE_TAC[]] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> try fst(dest_const t) = "p3_vrm" with Failure _ -> false))
              (concl th))) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(vec 0:real^3,r0))`;
                 `restrict_atlas (open_set_atlas (:real^3)) (ball(vec 0:real^3,r0))`;
                 `restrict_metric (open_set_atlas (:real^3)) (ball(vec 0:real^3,r0))
                    (p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                             (p2cd_phi V (x:A) E) s)`; `w:real^3`; `r / &2`]
                MFD_CENTRE_IN_BALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN
      REWRITE_TAC[INST_TYPE [`:3`,`:N`] GEOL_EUCLID_FACTS; GSYM OPEN_IN; OPEN_BALL];
      USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM rfa_rmd2] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `ball(vec 0:real^3,r0)`;
                 `p2cv_pb (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (&0) (&1) (open_set_atlas (:real^3))
                          (p2cd_phi V (x:A) E) s`;
                 `((:real^3),(\x:real^3. x))`; `w:real^3`; `l:num`] P2CQ_REGION_RMD2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INST_TYPE [`:3`,`:N`] GEOL_EUCLID_FACTS; GSYM OPEN_IN; OPEN_BALL; P2CD_C0;
                IN_UNIV; FST] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[P2CD_C0; SND]]);;

let P2CD_SHI = prove
 (`!r0 r1 a0 K l rho.
     &0 < rho /\ rho < r0 /\ a0 < &0 /\ &0 <= K
     ==> ?C. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
              x E s w.
               p2cd_ok V x E r0 r1 a0 K /\ a0 / &2 <= s /\ s <= &0 /\ w IN ball(vec 0,rho)
               ==> lrm_deriv_norm2 l
                     (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) s) w <= C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CD_SHI_GEN THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The C^m bounds of the time-0 pullbacks (the gauge of MT                  *)
(* Lemma 5.7, P2C_GAUGE, fed with Shi at time 0 for the orders l >= 1 and  *)
(* with the curvature bound for l = 0, RFA_R1_RMD0).                         *)
(* ------------------------------------------------------------------------- *)

(* Slice-level derivative norms at phi w are the chart-level ones at w. *)

let P2CD_RMD_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K l w.
     p2cd_ok V x E r0 r1 a0 K /\ w IN ball(vec 0,r0)
     ==> rfa_rmd2 l (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (p2cd_phi V x E w) =
         lrm_deriv_norm2 l
           (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) (&0)) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN p2cd_ok_tac THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CD_SLICE o CONJ
    (ASSUME `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))`)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `r0:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  REWRITE_TAC[P2CD_PB_RFS_FUN] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC P2AP_PULLBACK_RMD_GEN THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)`; `ball(vec 0:real^3,r0)`] THEN
  ASM_REWRITE_TAC[]);;

(* Points of the metric ball are images of points of the coordinate ball. *)

let P2CD_BALL_IMAGE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K r y.
     p2cd_ok V x E r0 r1 a0 K /\ &0 < r /\ r <= r0 /\ y IN rfs_vball V (&0) x r
     ==> ?w. w IN ball(vec 0,r) /\ y = p2cd_phi V x E w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `r:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `(y:A) IN IMAGE (p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) x E) (ball(vec 0,r))` THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

(* The gauge: C^m closeness of the time-0 pullbacks to the Euclidean metric *)
(* on ball(vec 0,r0/2), uniformly over the views, when Cg r0^2 <= 1.        *)

let P2CD_GAUGE0 = prove
 (`!K. &0 <= K
       ==> ?Cg. &0 < Cg /\
            !r0 r1 a0 m.
              &0 < r0 /\ a0 < &0 /\ Cg * r0 pow 2 <= &1
              ==> ?B. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) x E w.
                     p2cd_ok V x E r0 r1 a0 K /\ norm w < r0 / &2
                     ==> lck_dist2 m (\z:real^3. mat 1)
                           (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E)
                                    (&0)) w <= B`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmd0"))
    (INST_TYPE [`:3`,`:N`] RFA_R1_RMD0) THEN
  SUBGOAL_THEN `&0 <= sqrt C0 * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  EXISTS_TAC `sqrt C0 * K + &1` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r0:real`; `r1:real`; `a0:real`; `m:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l. ?Cs. !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
              x E w.
               p2cd_ok V x E r0 r1 a0 K /\ w IN ball(vec 0,&7 / &8 * r0)
               ==> lrm_deriv_norm2 l
                     (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) (&0)) w
                   <= Cs`
  MP_TAC THENL
   [X_GEN_TAC `l:num` THEN
    MP_TAC(ISPECL [`r0:real`; `r1:real`; `a0:real`; `K:real`; `l:num`; `&7 / &8 * r0`]
                  (INST_TYPE [`:A`,`:A`] P2CD_SHI)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Cs:num->real` (LABEL_TAC "Cs")) THEN
  MP_TAC(ISPEC `(:A)` P2C_GAUGE) THEN REWRITE_TAC[P2C_GAUGE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`m:num`; `\l. if l = 0 then sqrt C0 * K + &1 else sqrt(abs((Cs:num->real) l))`;
    `&3 / &4 * r0`; `r0 / &2`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS; REAL_ARITH `&0 <= x ==> &0 <= x + &1`];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt C0 * K + &1) * r0 pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_MUL] THEN
      CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN
      MP_TAC(SPEC `r0:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN DISCH_THEN(LABEL_TAC "gauge") THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `E:real^3^3`; `w:real^3`] THEN STRIP_TAC THEN p2cd_ok_tac THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2CD_SLICE o CONJ
    (ASSUME `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3))`)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`] P2CD_OK_PB0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pb0" o CONJUNCT1) THEN
  SUBGOAL_THEN `(w:real^3) IN ball(vec 0,r0)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lck_dist2 m (\z:real^3. mat 1)
                (cmp_expmetric (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                            (real->A->real^3^3)) (&0),rfs_vatlas V (&0))
                               (rfs_vmetric V (&0)) x E) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LCK_DIST2_LOCAL THEN
    EXISTS_TAC `ball(vec 0:real^3,r0)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "pb0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "gauge" (MP_TAC o SPECL
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3)) (&0)`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) (&0)`;
    `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0)`; `x:A`; `E:real^3^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0)`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) (&0)`;
                     `x:A`; `r0:real`; `&3 / &4 * r0`] MFD_INJ_BALL_MONO) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[mfd_inj_ball]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `l:num`] THEN STRIP_TAC THEN REWRITE_TAC[GSYM rfa_rmd2] THEN
    SUBGOAL_THEN `(y:A) IN rfs_vball (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (&0) x (&7 / &8 * r0)`
    ASSUME_TAC THENL
     [REWRITE_TAC[P2CO_VBALL] THEN
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (&0)`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) (&0)`;
                     `x:A`; `&3 / &4 * r0`; `&7 / &8 * r0`] P2CU_BALL_MONO) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`;
                   `&7 / &8 * r0`; `y:A`] P2CD_BALL_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w':real^3` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `(w':real^3) IN ball(vec 0,r0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(w':real^3) IN ball(vec 0,&7 / &8 * r0)` THEN
      REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `l = 0` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C0 * K pow 2` THEN
      CONJ_TAC THENL
       [USE_THEN "rmd0" MATCH_MP_TAC THEN
        EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) x E w') IN
                       rfs_vball V (&0) x (&7 / &8 * r0)` THEN
          REWRITE_TAC[P2CO_VBALL] THEN
          MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) (&0)`;
                         `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (&0)`;
                         `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) (&0)`;
                         `x:A`; `&7 / &8 * r0`] P2CU_BALL_SUBSET) THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> try fst(dest_const t) = "mfd_rm_norm" with Failure _ -> false))
                (concl th))) THEN
          REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) (&0)`;
                         `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (&0)`;
                         `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) (&0)`;
                         `x:A`; `&7 / &8 * r0`; `r1:real`] P2CU_BALL_MONO) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          UNDISCH_TAC `(p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) x E w') IN
                       rfs_vball V (&0) x (&7 / &8 * r0)` THEN
          REWRITE_TAC[P2CO_VBALL] THEN SET_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt C0 * K) pow 2` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC]];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                     `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `l:num`;
                     `w':real^3`] P2CD_RMD_SLICE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN
      USE_THEN "Cs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The pulled-back flows of one view on a coordinate ball, and               *)
(* the hypotheses p2ca_seqhyp of the local limit theorem for the sequence   *)
(* (space-time jets P2CH_ST_JETS from Shi and the time-0 gauge).            *)
(* ------------------------------------------------------------------------- *)

let P2CD_VIEW_FLOW_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 b K R.
     p2cd_ok V x E r0 r1 a0 K /\ &0 < R /\ R <= r0 /\ a0 < b /\ b < &0
     ==> (!t. b <= t /\ t <= &0
              ==> metric_field (ball(vec 0,R))
                    (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) t)) /\
         lricci_flow (ball(vec 0,R)) (b) (&0)
           (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E)) /\
         (?e (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
            &0 < e /\
            smooth_map_on (interval(lift(b - e),lift(&0 + e)) PCROSS ball(vec 0,R)) FF /\
            (!t y. b <= t /\ t <= &0 /\ y IN ball(vec 0,R)
                   ==> FF(pastecart (lift t) y) =
                       vectorize(p2cv_pb V (&0) (&1) (open_set_atlas (:real^3))
                                         (p2cd_phi V x E) t y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
              CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [p2cd_ok]) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                 `x:A`; `E:real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`; `R:real`]
                P2CD_OK_ONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `ball(vec 0:real^3,R)`;
                   `p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) x E`;
                   `&0`; `&1`; `a0:real`; `&0`; `t:real`; `((:real^3),(\x:real^3. x))`]
                  P2CV_P_FIELD_AT) THEN
    REWRITE_TAC[P2CD_C0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `ball(vec 0:real^3,R)`;
                   `p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) x E`;
                   `&0`; `&1`; `b:real`; `&0`; `((:real^3),(\x:real^3. x))`] P2CV_LFLOW) THEN
    REWRITE_TAC[P2CD_C0; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC P2CD_PERSISTS_MONO THEN EXISTS_TAC `&0 + a0 / &1` THEN
    ASM_REWRITE_TAC[P2CD_T01] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
                   `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `ball(vec 0:real^3,R)`;
                   `p2cd_phi (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) x E`;
                   `&0`; `&1`; `b:real`; `&0`; `a0:real`; `&0`; `((:real^3),(\x:real^3. x))`]
                  P2CV_EXT) THEN
    REWRITE_TAC[P2CD_C0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC]);;

let P2CD_VIEW_FLOW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K R.
     p2cd_ok V x E r0 r1 a0 K /\ &0 < R /\ R <= r0
     ==> (!t. a0 / &2 <= t /\ t <= &0
              ==> metric_field (ball(vec 0,R))
                    (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E) t)) /\
         lricci_flow (ball(vec 0,R)) (a0 / &2) (&0)
           (p2cv_pb V (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi V x E)) /\
         (?e (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
            &0 < e /\
            smooth_map_on (interval(lift(a0 / &2 - e),lift(&0 + e)) PCROSS ball(vec 0,R)) FF /\
            (!t y. a0 / &2 <= t /\ t <= &0 /\ y IN ball(vec 0,R)
                   ==> FF(pastecart (lift t) y) =
                       vectorize(p2cv_pb V (&0) (&1) (open_set_atlas (:real^3))
                                         (p2cd_phi V x E) t y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2CD_VIEW_FLOW_GEN THEN
  MAP_EVERY EXISTS_TAC [`r0:real`; `r1:real`; `a0:real`; `K:real`] THEN
  ASM_REWRITE_TAC[] THEN p2cd_ok_tac THEN ASM_REAL_ARITH_TAC);;

(* Time-0 jets of the sequence on compact subsets of ball(vec 0,r0/2). *)

let P2CD_SEQ_JETS0 = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x E r0 r1 a0 K B m Kc.
     (!n. p2cd_ok (V n) (x n) (E n) r0 r1 a0 K) /\
     (!n w. norm w < r0 / &2
            ==> lck_dist2 m (\z:real^3. mat 1)
                  (p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                           (p2cd_phi (V n) (x n) (E n)) (&0)) w <= B) /\
     compact Kc /\ Kc SUBSET ball(vec 0,r0 / &2)
     ==> !p q. 1 <= p /\ p <= dimindex(:3) /\ 1 <= q /\ q <= dimindex(:3)
               ==> ?C. !n l y. l IN pde_index_lists m (:3) /\ y IN Kc
                               ==> abs(drop(iterated_partial l
                                        (\z. lift(p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                                                   (p2cd_phi (V n) (x n) (E n)) (&0) z$p$q)) y))
                                   <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `GG = \s:real. p2cv_pb ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3)) (@n. &n = s)) (&0) (&1)
                              (open_set_atlas (:real^3))
                              (p2cd_phi (V (@n. &n = s)) ((x:num->A) (@n. &n = s))
                                        ((E:num->real^3^3) (@n. &n = s))) (&0)` THEN
  SUBGOAL_THEN
   `!n. (GG:real->real^3->real^3^3) (&n) =
        p2cv_pb ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) n) (&0) (&1) (open_set_atlas (:real^3))
                (p2cd_phi (V n) ((x:num->A) n) ((E:num->real^3^3) n)) (&0)`
  (LABEL_TAC "GGn") THENL
   [GEN_TAC THEN EXPAND_TAC "GG" THEN REWRITE_TAC[REAL_OF_NUM_EQ; SELECT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r0 /\ a0 < &0` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "p2cd_ok" with Failure _ -> false))
          (concl th))) THEN
    SIMP_TAC[p2cd_ok];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{&n | n IN (:num)}`; `ball(vec 0:real^3,r0 / &2)`; `Kc:real^3->bool`;
                 `(\z:real^3. mat 1):real^3->real^3^3`; `GG:real->real^3->real^3^3`;
                 `m:num`; `B + &1`] P2CJ_JB_FROM_LCK) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_METRIC_FIELD_ID; OPEN_BALL] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN CONJ_TAC THEN X_GEN_TAC `s:real` THENL
     [DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
      USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n`;
                     `(x:num->A) n`; `(E:num->real^3^3) n`; `r0:real`; `r1:real`; `a0:real`;
                     `K:real`; `r0 / &2`] P2CD_VIEW_FLOW) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1) THEN REWRITE_TAC[REAL_LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` SUBST1_TAC)
                                             ASSUME_TAC) THEN
      USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x < b + &1`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN ball(vec 0,r0 / &2)` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:num`; `q:num`]) THEN ASM_REWRITE_TAC[rfa_jb] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real` o CONJUNCT2) THEN EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `l:(num)list`; `y:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&n`; `l:(num)list`; `y:real^3`]) THEN
  USE_THEN "GGn" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  ANTS_TAC THENL [MESON_TAC[]; SIMP_TAC[]]);;

(* The hypotheses of the local limit theorem on ball(vec 0,r0/2) over      *)
(* [b,0] (a0 < b < 0), for every sequence of chart data with Cg r0^2 <= 1;  *)
(* P2CD_SEQHYP is the case b = a0 / 2.                                     *)

let P2CD_SEQHYP_GEN = prove
 (`!K. &0 <= K
       ==> ?Cg. &0 < Cg /\
            !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
             x E r0 r1 a0 b.
               &0 < r0 /\ a0 < b /\ b < &0 /\ Cg * r0 pow 2 <= &1 /\
               (!n. p2cd_ok (V n) (x n) (E n) r0 r1 a0 K)
               ==> p2ca_seqhyp (ball(vec 0,r0 / &2)) (b) (&0)
                     (\n. p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                                  (p2cd_phi (V n) (x n) (E n)))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0")) o
              MATCH_MP (INST_TYPE [`:A`,`:A`] P2CD_GAUGE0)) THEN
  EXISTS_TAC `Cg:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `E:num->real^3^3`; `r0:real`; `r1:real`; `a0:real`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ok"))))) THEN
  SUBGOAL_THEN `a0 < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a1 = (a0 + b) / &2` THEN
  SUBGOAL_THEN `a0 < a1 /\ a1 < &0 /\ a1 < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Lm = &2 * exp(&8 * K * (&0 - a1))` THEN
  SUBGOAL_THEN `&0 <= Lm` ASSUME_TAC THENL
   [EXPAND_TAC "Lm" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (!t. b <= t /\ t <= &0
             ==> metric_field (ball(vec 0,r0 / &2))
                   (p2cv_pb ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) n) (&0) (&1) (open_set_atlas (:real^3))
                            (p2cd_phi (V n) ((x:num->A) n) ((E:num->real^3^3) n)) t)) /\
        lricci_flow (ball(vec 0,r0 / &2)) (b) (&0)
          (p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3)) (p2cd_phi (V n) (x n) (E n))) /\
        (?e (FF:real^(1,3)finite_sum->real^(3,3)finite_prod).
           &0 < e /\
           smooth_map_on (interval(lift(b - e),lift(&0 + e)) PCROSS ball(vec 0,r0 / &2)) FF /\
           (!t y. b <= t /\ t <= &0 /\ y IN ball(vec 0,r0 / &2)
                  ==> FF(pastecart (lift t) y) =
                      vectorize(p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                                        (p2cd_phi (V n) (x n) (E n)) t y)))`
  (LABEL_TAC "vf") THENL
   [GEN_TAC THEN MATCH_MP_TAC P2CD_VIEW_FLOW_GEN THEN
    MAP_EVERY EXISTS_TAC [`r0:real`; `r1:real`; `a0:real`; `K:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n t y v. b <= t /\ t <= &0 /\ y IN ball(vec 0,r0 / &2)
              ==> norm v pow 2 <=
                  Lm * (v dot (p2cv_pb ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                          (real->A->real^3^3)) n) (&0) (&1) (open_set_atlas (:real^3))
                                       (p2cd_phi (V n) ((x:num->A) n) ((E:num->real^3^3) n)) t y ** v)) /\
                  v dot (p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                                 (p2cd_phi (V n) (x n) (E n)) t y ** v) <= Lm * norm v pow 2`
  (LABEL_TAC "qf") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "Lm" THEN
    MATCH_MP_TAC P2CD_OK_QF THEN
    MAP_EVERY EXISTS_TAC [`r0:real`; `r1:real`; `a0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN ball(vec 0,r0 / &2)` THEN REWRITE_TAC[IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2ca_seqhyp] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "vf" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN USE_THEN "vf" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    GEN_TAC THEN USE_THEN "vf" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN EXISTS_TAC `Lm:real` THEN REPEAT STRIP_TAC THEN
    USE_THEN "qf" (MP_TAC o SPECL [`n:num`; `t:real`; `y:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Kc:real^3->bool`; `l:(num)list`; `p:num`; `q:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(vec 0:real^3,r0 / &2)`; `Kc:real^3->bool`; `b:real`; `&0`;
                 `\n. p2cv_pb ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) n) (&0) (&1) (open_set_atlas (:real^3))
                              (p2cd_phi (V n) ((x:num->A) n) ((E:num->real^3^3) n))`;
                 `Lm:real`] P2CH_ST_JETS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `b <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[OPEN_BALL; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CV_ENTRY_BOUNDS THEN
      EXISTS_TAC `ball(vec 0:real^3,r0 / &2)` THEN
      SUBGOAL_THEN `(y:real^3) IN ball(vec 0,r0 / &2)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
      CONJ_TAC THENL
       [USE_THEN "vf" (MP_TAC o SPEC `n:num`) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `v:real^3` THEN
        USE_THEN "qf" (MP_TAC o SPECL [`n:num`; `t:real`; `y:real^3`; `v:real^3`]) THEN
        ASM_SIMP_TAC[]];
      REPEAT STRIP_TAC THEN
      USE_THEN "qf" (MP_TAC o SPECL [`n:num`; `t:real`; `y:real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `j:num` THEN
      MP_TAC(ISPECL [`r0:real`; `r1:real`; `a0:real`; `b:real`; `K:real`; `j:num`; `&3 / &4 * r0`]
                    (INST_TYPE [`:A`,`:A`] P2CD_SHI_GEN)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`; `y:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^3) IN ball(vec 0,r0 / &2)` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`m:num`; `p':num`; `q':num`] THEN STRIP_TAC THEN
      USE_THEN "g0" (MP_TAC o C MP (CONJ (ASSUME `&0 < r0`) (CONJ (ASSUME `a0 < &0`)
                                     (ASSUME `Cg * r0 pow 2 <= &1`))) o
                     SPECL [`r0:real`; `r1:real`; `a0:real`; `m:num`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) THEN
      MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)`;
                     `x:num->A`; `E:num->real^3^3`; `r0:real`; `r1:real`; `a0:real`; `K:real`;
                     `B:real`; `m:num`; `Kc:real^3->bool`] P2CD_SEQ_JETS0) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(MP_TAC o SPECL [`p':num`; `q':num`]) THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(MP_TAC o SPECL [`l:(num)list`; `p:num`; `q:num`]) THEN ASM_REWRITE_TAC[]]);;

let P2CD_SEQHYP = prove
 (`!K. &0 <= K
       ==> ?Cg. &0 < Cg /\
            !(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
             x E r0 r1 a0.
               &0 < r0 /\ a0 < &0 /\ Cg * r0 pow 2 <= &1 /\
               (!n. p2cd_ok (V n) (x n) (E n) r0 r1 a0 K)
               ==> p2ca_seqhyp (ball(vec 0,r0 / &2)) (a0 / &2) (&0)
                     (\n. p2cv_pb (V n) (&0) (&1) (open_set_atlas (:real^3))
                                  (p2cd_phi (V n) (x n) (E n)))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sg")) o
              MATCH_MP (INST_TYPE [`:A`,`:A`] P2CD_SEQHYP_GEN)) THEN
  EXISTS_TAC `Cg:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `E:num->real^3^3`; `r0:real`; `r1:real`; `a0:real`] THEN
  STRIP_TAC THEN
  USE_THEN "sg" (MP_TAC o SPECL
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `E:num->real^3^3`; `r0:real`; `r1:real`; `a0:real`; `a0 / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of the limit flow up to time 0: the local form of              *)
(* the final-time extension (reflection of P2CB_UPTO), the continuous       *)
(* extensions of the iterated partials of the limit to the half-open slab   *)
(* (a,b] from the closed-box limits of the Arzela-Ascoli context (mirror of *)
(* P2CB_CTX_DATA), and the flows up to time 0 on open subsets of a ball.    *)
(* ------------------------------------------------------------------------- *)

let P2CD_TREFL_PCROSS = prove
 (`!a b (O:real^N->bool) (w:real^(1,N)finite_sum).
     pastecart (lift((a + b) - drop(fstcart w))) (sndcart w) IN
       {x | a < drop x /\ drop x <= b} PCROSS O <=>
     w IN {x | a <= drop x /\ drop x < b} PCROSS O`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP; PASTECART_FST_SND] THEN
  REWRITE_TAC[REAL_ARITH `a < (a + b) - d <=> d < b`;
              REAL_ARITH `(a + b) - d <= b <=> a <= d`] THEN
  CONV_TAC TAUT);;

let P2CD_TREFL_OPEN_PCROSS = prove
 (`!a b (O:real^N->bool) (w:real^(1,N)finite_sum).
     pastecart (lift((a + b) - drop(fstcart w))) (sndcart w) IN
       interval(lift a,lift b) PCROSS O <=>
     w IN interval(lift a,lift b) PCROSS O`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP; PASTECART_FST_SND] THEN
  REWRITE_TAC[REAL_ARITH `a < (a + b) - d <=> d < b`;
              REAL_ARITH `(a + b) - d < b <=> a < d`] THEN
  CONV_TAC TAUT);;

let P2CD_UPTO_TOP_LOC = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
     open U /\ a < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U) (\z. u (drop(fstcart z)) (sndcart z)) /\
     (!y0. y0 IN U
           ==> ?O. open O /\ y0 IN O /\ O SUBSET U /\
                   (\z. u (drop(fstcart z)) (sndcart z)) continuous_on
                     ({x | a < drop x /\ drop x <= b} PCROSS O) /\
                   !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
                       ==> ?h. h continuous_on ({x | a < drop x /\ drop x <= b} PCROSS O) /\
                               !w. w IN interval(lift a,lift b) PCROSS O
                                   ==> h w = iterated_partial l
                                               (\z. u (drop(fstcart z)) (sndcart z)) w)
     ==> ?e FF. &0 < e /\
                smooth_map_on (interval(lift a,lift(b + e)) PCROSS U) FF /\
                !t y. a < t /\ t <= b /\ y IN U ==> FF(pastecart (lift t) y) = u t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))) THEN
  ABBREV_TAC `R = \w:real^(1,N)finite_sum. pastecart (lift((a + b) - drop(fstcart w))) (sndcart w)
                                           :real^(1,N)finite_sum` THEN
  ABBREV_TAC `uf = \w:real^(1,N)finite_sum. (u:real->real^N->real^K) (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `!w. (uf:real^(1,N)finite_sum->real^K) ((R:real^(1,N)finite_sum->real^(1,N)finite_sum) w) =
                    (u:real->real^N->real^K) ((a + b) - drop(fstcart w)) (sndcart w)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["uf"; "R"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,N)finite_sum) (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2CD_TREFL_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:real^(1,N)finite_sum->real^(1,N)finite_sum) continuous_on (:real^(1,N)finite_sum)`
  ASSUME_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!O w. w IN interval(lift a,lift b) PCROSS (O:real^N->bool)
                      ==> (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN
                          interval(lift a,lift b) PCROSS O`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2CD_TREFL_OPEN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `!O w. w IN {x | a <= drop x /\ drop x < b} PCROSS (O:real^N->bool)
                      ==> (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN
                          {x | a < drop x /\ drop x <= b} PCROSS O`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2CD_TREFL_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift a,lift b) PCROSS (U:real^N->bool))
                  (uf:real^(1,N)finite_sum->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "uf" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (u:real->real^N->real^K) ((a + b) - drop(fstcart z)) (sndcart z)) =
    (uf:real^(1,N)finite_sum->real^K) o (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                 `\t:real y:real^N. (u:real->real^N->real^K) ((a + b) - t) y`] P2CB_UPTO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SUBSET; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `O:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hu"))))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{x | a < drop x /\ drop x <= b} PCROSS (O:real^N->bool)` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "uf" THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    USE_THEN "hu" (MP_TAC o C MP
      (ASSUME `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l`) o SPEC `l:num list`) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\w:real^(1,N)finite_sum.
                  ITLIST (\i r. (if i = 1 then --(&1) else &1) * r) l (&1) %
                  (h:real^(1,N)finite_sum->real^K) ((R:real^(1,N)finite_sum->real^(1,N)finite_sum) w)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      SUBGOAL_THEN `(\w:real^(1,N)finite_sum. (h:real^(1,N)finite_sum->real^K)
                       ((R:real^(1,N)finite_sum->real^(1,N)finite_sum) w)) = h o R`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{x | a < drop x /\ drop x <= b} PCROSS (O:real^N->bool)` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(uf:real^(1,N)finite_sum->real^K) o (R:real^(1,N)finite_sum->real^(1,N)finite_sum) =
        (\z. uf (pastecart (lift((a + b) - drop(fstcart z))) (sndcart z)))`
      SUBST1_TAC THENL
       [EXPAND_TAC "R" THEN REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      SUBGOAL_THEN `(w:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS U` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS O` THEN
        ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`uf:real^(1,N)finite_sum->real^K`;
                     `interval(lift a,lift b) PCROSS (U:real^N->bool)`; `a + b:real`;
                     `l:num list`] P2CD_TREFL_ITERATED_PARTIAL) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
        UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
        REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SYM];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
      REWRITE_TAC[P2CD_TREFL_OPEN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `pastecart (lift((a + b) - drop(fstcart(w:real^(1,N)finite_sum)))) (sndcart w) =
                    (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w` SUBST1_TAC THENL
       [EXPAND_TAC "R" THEN REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[pde_upto] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `G:real^(1,N)finite_sum->real^K`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `(G:real^(1,N)finite_sum->real^K) o
                                   (R:real^(1,N)finite_sum->real^(1,N)finite_sum)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(a + b) - t:real`; `y:real^N`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `G:real^(1,N)finite_sum->real^K`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC]);;

(* The iterated partials of the local limit extend continuously to the     *)
(* half-open slab (a,b] near every point (mirror of P2CB_CTX_DATA).         *)

let P2CD_CTX_DATA_TOP = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H G y0.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     (!t y. a <= t /\ t <= b /\ y IN V ==> G t y = p2cm_lim Gs sub t y) /\
     y0 IN V
     ==> ?O. open O /\ y0 IN O /\ O SUBSET V /\
             (\z. vectorize(G (drop(fstcart z)) (sndcart z))) continuous_on
               ({x | a < drop x /\ drop x <= b} PCROSS O) /\
             !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
                 ==> ?h. h continuous_on ({x | a < drop x /\ drop x <= b} PCROSS O) /\
                         !w. w IN interval(lift a,lift b) PCROSS O
                             ==> h w = iterated_partial l
                                         (\z. vectorize(G (drop(fstcart z)) (sndcart z))) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ctx") (CONJUNCTS_THEN2 (LABEL_TAC "id") ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `open (V:real^N->bool) /\ a < b /\
    (!i. cball((c:num->real^N) i,(r:num->real) i) SUBSET V) /\
    (!y. y IN V ==> ?i. &0 < r i /\ y IN ball(c i,r i)) /\
    (!i p q l. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
               ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
               ==> (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) l
                     continuous_on p2cm_box a b c r i)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ctx" (MP_TAC o REWRITE_RULE[p2cm_ctx]) THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(y0:real^N) IN V`) o SPEC `y0:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `ball:real^N#real->real^N->bool`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball((c:num->real^N) i,(r:num->real) i) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((c:num->real^N) i,(r:num->real) i)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | a < drop x /\ drop x <= b} PCROSS ball((c:num->real^N) i,(r:num->real) i) SUBSET
    p2cm_box a b c r i`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2cm_box] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[BALL_SUBSET_CBALL; SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q w. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
            w IN {x | a < drop x /\ drop x <= b} PCROSS ball((c:num->real^N) i,(r:num->real) i)
            ==> lift((G:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$p$q) =
                (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) [] w`
  (LABEL_TAC "ent0") THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `w:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < drop(fstcart(w:real^(1,N)finite_sum)) /\ drop(fstcart w) <= b /\
                  sndcart w IN ball((c:num->real^N) i,(r:num->real) i)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^(1,N)finite_sum) IN
                   {x | a < drop x /\ drop x <= b} PCROSS ball((c:num->real^N) i,(r:num->real) i)` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      CONV_TAC TAUT;
      ALL_TAC] THEN
    SUBGOAL_THEN `sndcart(w:real^(1,N)finite_sum) IN V /\
                  sndcart w IN cball((c:num->real^N) i,(r:num->real) i)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
      ALL_TAC] THEN
    USE_THEN "id" (MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                   `sndcart(w:real^(1,N)finite_sum)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                   `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p:num`; `q:num`; `drop(fstcart(w:real^(1,N)finite_sum))`;
                   `sndcart(w:real^(1,N)finite_sum)`] P2CM_CTX_LIM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  EXISTS_TAC `ball((c:num->real^N) i,(r:num->real) i)` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CB_VECTORIZE_CONTINUOUS THEN REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "ent0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `p2cm_box a b (c:num->real^N) r i` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL]];
    ALL_TAC] THEN
  X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
  EXISTS_TAC `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (lambda p q. drop((H:num#num#num->(num)list->real^(1,N)finite_sum->real^1)
                                        (i,p,q) l w))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CB_VECTORIZE_CONTINUOUS THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `p2cm_box a b (c:num->real^N) r i` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                 `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] P2CM_CTX_FLOW) THEN
  USE_THEN "ctx" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open(interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)) /\
    interval(lift a,lift b) PCROSS ball(c i,r i) SUBSET interval(lift a,lift b) PCROSS V`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))) w =
    iterated_partial l (\z. vectorize(p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                                        (drop(fstcart z)) (sndcart z))) w`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:(num)list`;
                   `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                             (drop(fstcart z)) (sndcart z))`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN USE_THEN "id" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `ball((c:num->real^N) i,(r:num->real) i) SUBSET V` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CB_VEC_ENTRY_EQ THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`l:(num)list`;
                 `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                           (drop(fstcart z)) (sndcart z))`;
                 `w:real^(1,N)finite_sum`; `p:num`; `q:num`] P2CB_ITERATED_PARTIAL_ENTRY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (V:real^N->bool)` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                 `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `i:num`; `p:num`; `q:num`] P2CM_CTX_REP) THEN
  USE_THEN "ctx" (fun th -> ASM_REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hl"))) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterated_partial l
                ((H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []) w` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "Hl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`l:(num)list`;
                   `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)`;
                   `\z. lift(p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                               (drop(fstcart z)) (sndcart z)$p$q)`;
                   `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)]);;

(* Local limits are smooth up to the final time (mirror of P2CB_UPTO_CTX). *)

let P2CD_UPTO_TOP_CTX = prove
 (`!a b (U:real^N->bool) (G:real->real^N->real^N^N).
     open U /\ a < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
                   (\z. vectorize(G (drop(fstcart z)) (sndcart z))) /\
     (!y0. y0 IN U
           ==> ?V (Gs:num->real->real^N->real^N^N)
                 (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ee c r (sub:num->num)
                 (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1).
                 y0 IN V /\ V SUBSET U /\ p2cm_ctx V a b Gs FF ee c r sub H /\
                 (!t y. a <= t /\ t <= b /\ y IN V ==> G t y = p2cm_lim Gs sub t y))
     ==> ?e (Fx:real^(1,N)finite_sum->real^(N,N)finite_prod).
           &0 < e /\ smooth_map_on (interval(lift a,lift(b + e)) PCROSS U) Fx /\
           !t y. a < t /\ t <= b /\ y IN U ==> Fx(pastecart (lift t) y) = vectorize(G t y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))) THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod) ((G:real->real^N->real^N^N) t y)`]
                P2CD_UPTO_TOP_LOC) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:real^N->bool`; `Gs:num->real->real^N->real^N^N`;
                       `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                       `c:num->real^N`; `r:num->real`; `sub:num->num`;
                       `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                 `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `G:real->real^N->real^N^N`; `y0:real^N`] P2CD_CTX_DATA_TOP) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `O:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* A coordinate Ricci flow on an open set, smooth up to its final time, is a *)
(* flow up to that time of the open set manifold.                            *)

let P2CD_RF_OPEN = prove
 (`!O a b (g:real->real^3->real^3^3).
     open O /\ lricci_flow O a b g /\ metric_field O (g b) /\
     (?e (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod).
        &0 < e /\ smooth_map_on (interval(lift a,lift(b + e)) PCROSS O) Fx /\
        !t y. a < t /\ t <= b /\ y IN O ==> Fx(pastecart (lift t) y) = vectorize(g t y))
     ==> rfs_flow_upto (subtopology euclidean O,open_set_atlas O) a b g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
      `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lricci_flow] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "lricci_flow" with Failure _ -> false)) THEN
  REWRITE_TAC[rfs_flow_upto; ricci_flow_on; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN] THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(real^3->bool)#(real^3->real^3)` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FST; SND; IMAGE_ID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
                                           (g (drop(fstcart z)) (sndcart z))` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT; RFB_OPEN_SET_MFD_RICCI];
    X_GEN_TAC `c:(real^3->bool)#(real^3->real^3)` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FST; SND; IMAGE_ID] THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]]);;

(* ------------------------------------------------------------------------- *)
(* The radius, and the main theorem (form N of local compactness).          *)
(* ------------------------------------------------------------------------- *)

let P2CD_RADIUS = prove
 (`!i0 K Cg. &0 < i0 /\ &0 <= K /\ &0 <= Cg
             ==> ?r0. &0 < r0 /\ r0 <= i0 / &2 /\ K * r0 pow 2 <= &1 /\ Cg * r0 pow 2 <= &1`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = K + Cg + &1` THEN
  SUBGOAL_THEN `&1 <= D` ASSUME_TAC THENL [EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv D /\ inv D <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `min i0 (inv D) / &2` THEN
  SUBGOAL_THEN `&0 < min i0 (inv D) /\ min i0 (inv D) <= i0 /\ min i0 (inv D) <= inv D`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(min i0 (inv D) / &2) pow 2 <= (inv D / &2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `D * (inv D / &2) pow 2 = inv D / &4` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= D` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `D * (min i0 (inv D) / &2) pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * (inv D / &2) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (min i0 (inv D) / &2) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * (min i0 (inv D) / &2) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D * (min i0 (inv D) / &2) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN ASM_REAL_ARITH_TAC]);;

(* The main theorem: local compactness in form N. *)

let P2CD_LOCAL_COMPACT_N = prove
 (`!u:A->bool. P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:num->A`; `r1:real`; `a0:real`; `K:real`; `v0:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hyp"))))) THEN
  (* uniform injectivity radius *)
  MP_TAC(SPECL [`K:real`; `r1:real`; `v0:real`] (INST_TYPE [`:A`,`:A`] P2CD_INJ)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))) THEN
  SUBGOAL_THEN
   `!n. mfd_inj_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) (&0),rfs_vatlas (V n) (&0))
                     (rfs_vmetric (V n) (&0)) ((x:num->A) n) i0`
  (LABEL_TAC "injn") THENL
   [GEN_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
    USE_THEN "hyp" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  (* orthonormal frames *)
  SUBGOAL_THEN
   `!n. ?E. mfd_orthonormal_frame
              (rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) n) (&0)) ((x:num->A) n) E`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "hyp" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) n`; `(x:num->A) n`] P2CD_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC P2CU_FRAME_EXISTS THEN
    EXISTS_TAC `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) n) (&0)` THEN
    EXISTS_TAC `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) n) (&0)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `E:num->real^3^3` (LABEL_TAC "frame")) THEN
  (* the constant of the gauge and the radius *)
  MP_TAC(SPEC `K:real` (INST_TYPE [`:A`,`:A`] P2CD_SEQHYP)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh"))) THEN
  MP_TAC(SPECL [`i0:real`; `K:real`; `Cg:real`] P2CD_RADIUS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. p2cd_ok ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) n) ((x:num->A) n) ((E:num->real^3^3) n) r0 r1 a0 K`
  (LABEL_TAC "ok") THENL
   [GEN_TAC THEN USE_THEN "hyp" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[p2cd_ok] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) (&0)`;
                     `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) n) (&0)`;
                     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) n) (&0)`;
                     `(x:num->A) n`; `i0:real`; `r0:real`] MFD_INJ_BALL_MONO) THEN
      MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n`; `(x:num->A) n`] P2CD_SLICE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `Gs = \n. p2cv_pb ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) n) (&0) (&1) (open_set_atlas (:real^3))
                     (p2cd_phi (V n) ((x:num->A) n) ((E:num->real^3^3) n))` THEN
  SUBGOAL_THEN `p2ca_seqhyp (ball(vec 0,r0 / &2)) (a0 / &2) (&0)
                  (Gs:num->real->real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "Gs" THEN USE_THEN "sh" MATCH_MP_TAC THEN EXISTS_TAC `r1:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^3,r0 / &2)`; `a0 / &2`; `&0`;
                 `Gs:num->real->real^3->real^3^3`] P2CB_CTX_SEQHYP) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                       `c:num->real^3`; `r:num->real`; `sub:num->num`;
                       `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
  DISCH_THEN(LABEL_TAC "ctx") THEN
  MAP_EVERY EXISTS_TAC
   [`r0 / &2`; `sub:num->num`;
    `\k. p2cd_phi ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) ((sub:num->num) k)) ((x:num->A) (sub k))
                  ((E:num->real^3^3) (sub k))`;
    `p2cm_lim (Gs:num->real->real^3->real^3^3) sub`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    USE_THEN "ctx" (MP_TAC o REWRITE_RULE[p2cm_ctx]) THEN SIMP_TAC[p3_subseq];
    X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) ((sub:num->num) k)`;
                   `(x:num->A) ((sub:num->num) k)`; `(E:num->real^3^3) ((sub:num->num) k)`;
                   `r0:real`; `r1:real`;
                   `a0:real`; `K:real`; `r0 / &2`] P2CD_OK_ONE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a0 / &2`; `&0`; `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`;
                          `ee:num->real`; `c:num->real^3`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC;
    ALL_TAC] THENL
   [(* flows up to time 0 on open subsets *)
    X_GEN_TAC `O:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `lricci_flow (ball(vec 0:real^3,r0 / &2)) (a0 / &2) (&0)
                    (p2cm_lim (Gs:num->real->real^3->real^3^3) sub)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2CM_CTX_FLOW THEN
      MAP_EVERY EXISTS_TAC [`FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`;
                            `ee:num->real`; `c:num->real^3`; `r:num->real`;
                            `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2CD_RF_OPEN THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r0 / &2)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,r0 / &2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CM_CTX_METRIC THEN
      MAP_EVERY EXISTS_TAC [`a0 / &2`; `&0`; `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`;
                            `ee:num->real`; `c:num->real^3`; `r:num->real`;
                            `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`a0 / &2`; `&0`; `ball(vec 0:real^3,r0 / &2)`;
                     `p2cm_lim (Gs:num->real->real^3->real^3^3) sub`] P2CD_UPTO_TOP_CTX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          CONJ_TAC THENL
           [UNDISCH_TAC `lricci_flow (ball(vec 0:real^3,r0 / &2)) (a0 / &2) (&0)
                           (p2cm_lim (Gs:num->real->real^3->real^3^3) sub)` THEN
            SIMP_TAC[lricci_flow];
            X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
            MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,r0 / &2)`; `Gs:num->real->real^3->real^3^3`;
                                  `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`;
                                  `ee:num->real`; `c:num->real^3`; `r:num->real`; `sub:num->num`;
                                  `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`] THEN
            ASM_REWRITE_TAC[SUBSET_REFL]]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
        `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `interval(lift(a0 / &2),lift(&0 + e)) PCROSS ball(vec 0:real^3,r0 / &2)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    (* convergence *)
    MAP_EVERY X_GEN_TAC [`Kc:real^3->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(vec 0:real^3,r0 / &2)`; `a0 / &2`; `&0`;
                   `Gs:num->real->real^3->real^3^3`;
                   `FF:num->real^(1,3)finite_sum->real^(3,3)finite_prod`; `ee:num->real`;
                   `c:num->real^3`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,3)finite_sum->real^1`;
                   `Kc:real^3->bool`; `m:num`; `eta:real`] P2CM_CTX_LCK) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `s:real`; `w:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Gs" THEN REWRITE_TAC[P2CD_PB_RFS_FUN]]);;

