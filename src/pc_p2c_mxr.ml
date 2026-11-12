(* ========================================================================= *)
(* Unit pc_p2c_mxr (Part 2C): P2C_MAXEXT_REGULAR of pc_p2c_views (loaded     *)
(* through pc_p2c_hreg).  The maximal extension p3_maxext hs (p3_omega hs)   *)
(* gl of a history at its horizon T, for a limit metric gl on Omega, is a    *)
(* regular view.  Below T the regions are history regions                    *)
(* (P2CY_HISTORY_REGULAR and the P2AH_ lemmas); at T the slab flow converges *)
(* on compact subsets of Omega with all spatial derivatives                  *)
(* (rfs_limit_metric), the time and mixed derivatives converge because they  *)
(* are jet polynomials (Ricci flow equation, pc_rf_glue), and the one-sided  *)
(* extension past T is the time reflection of P2CB_UPTO (pc_p2c_flfrom).     *)
(* ========================================================================= *)

needs "src/pc_p2c_hreg.ml";;
needs "src/pc_p2c_flfrom.ml";;

prioritize_real();;
type_invention_error := true;;

let p2um_mentions name th =
  can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th);;

(* ------------------------------------------------------------------------- *)
(* Smooth extension past the FINAL time of a slab: the time-reflection       *)
(* lemmas of pc_p2c_lcn (P2UM_TREFL_HAS_DERIVATIVE ... P2UM_TREFL_INVOL,     *)
(* P2UM_TREFL_PCROSS, P2UM_TREFL_OPEN_PCROSS, P2UM_UPTO_TOP_LOC), proved     *)
(* again here so that this unit does not load pc_p2c_lcn.  The time          *)
(* reflection t |-> (a + b) - t turns P2CB_UPTO (pc_p2c_flfrom, the          *)
(* extension below the initial time) into the extension past the final time. *)
(* ------------------------------------------------------------------------- *)

let P2UM_TREFL_HAS_DERIVATIVE = prove
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

let P2UM_TREFL_PARTIAL_BASIS = prove
 (`!c (z:real^(1,N)finite_sum) i.
     1 <= i /\ i <= dimindex(:N) + 1
     ==> partial_derivative i
           (\w:real^(1,N)finite_sum. pastecart (lift(c - drop(fstcart w))) (sndcart w)) z =
         (if i = 1 then --(&1) else &1) % (basis i:real^(1,N)finite_sum)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MP_TAC(SPECL [`c:real`; `z:real^(1,N)finite_sum`] P2UM_TREFL_HAS_DERIVATIVE) THEN
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

let P2UM_TREFL_ITERATED_PARTIAL = prove
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
      REWRITE_TAC[P2UM_TREFL_HAS_DERIVATIVE];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC P2UM_TREFL_PARTIAL_BASIS THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

let P2UM_TREFL_SMOOTH = prove
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

let P2UM_TREFL_CONTINUOUS = prove
 (`!c. (\w. pastecart (lift(c - drop(fstcart w))) (sndcart w):real^(1,N)finite_sum)
       continuous_on (:real^(1,N)finite_sum)`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  REWRITE_TAC[P2UM_TREFL_SMOOTH]);;

let P2UM_TREFL_INVOL = prove
 (`!c (w:real^(1,N)finite_sum).
     pastecart (lift(c - drop(fstcart (pastecart (lift(c - drop(fstcart w))) (sndcart w)))))
               (sndcart (pastecart (lift(c - drop(fstcart w))) (sndcart w))) = w`,
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ARITH `c - (c - x) = x:real`; LIFT_DROP; PASTECART_FST_SND]);;

(* The slab sets are exchanged by the reflection. *)


let P2UM_TREFL_PCROSS = prove
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

let P2UM_TREFL_OPEN_PCROSS = prove
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

let P2UM_UPTO_TOP_LOC = prove
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
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2UM_TREFL_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:real^(1,N)finite_sum->real^(1,N)finite_sum) continuous_on (:real^(1,N)finite_sum)`
  ASSUME_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!O w. w IN interval(lift a,lift b) PCROSS (O:real^N->bool)
                      ==> (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN
                          interval(lift a,lift b) PCROSS O`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2UM_TREFL_OPEN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `!O w. w IN {x | a <= drop x /\ drop x < b} PCROSS (O:real^N->bool)
                      ==> (R:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN
                          {x | a < drop x /\ drop x <= b} PCROSS O`
  ASSUME_TAC THENL [EXPAND_TAC "R" THEN REWRITE_TAC[P2UM_TREFL_PCROSS]; ALL_TAC] THEN
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
                     `l:num list`] P2UM_TREFL_ITERATED_PARTIAL) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
        UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
        REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SYM];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
      REWRITE_TAC[P2UM_TREFL_OPEN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
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

(* ------------------------------------------------------------------------- *)
(* A one-sided smooth extension past the final time from                     *)
(* uniform convergence of all space-time partials.  If u is smooth on        *)
(* (a,b) x U, its partials of every order converge uniformly on compact     *)
(* sets as t -> b- to continuous limits J l, and u b = J [], then u extends  *)
(* smoothly to (a,b+e) x U (P2UM_UPTO_TOP_LOC with the extensions h of      *)
(* P2UM_HCONT).                                                              *)
(* ------------------------------------------------------------------------- *)

let P2UM_HCONT = prove
 (`!a b (O:real^N->bool) (f:real^(1,N)finite_sum->real^K) (J:real^N->real^K).
     open O /\ a < b /\
     f continuous_on (interval(lift a,lift b) PCROSS O) /\ J continuous_on O /\
     (!e. &0 < e
          ==> ?d. &0 < d /\
                  !t y. b - d < t /\ t < b /\ y IN O
                        ==> norm(f(pastecart (lift t) y) - J y) < e)
     ==> (\w. if drop(fstcart w) < b then f w else J(sndcart w)) continuous_on
         ({x | a < drop x /\ drop x <= b} PCROSS O)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; FORALL_IN_PCROSS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`s0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `drop s0 < b` THENL
   [MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (O:real^N->bool)) /\
                  pastecart (s0:real^1) (y0:real^N) IN interval(lift a,lift b) PCROSS O`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `pastecart (s0:real^1) (y0:real^N)` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> can (find_term ((=) `interval(lift a,lift b)`)) (concl th) &&
                       p2um_mentions "open" th)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`f:real^(1,N)finite_sum->real^K`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS O`
      MP_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART; PASTECART_FST_SND] THEN
      SIMP_TAC[];
      UNDISCH_TAC `(f:real^(1,N)finite_sum->real^K) continuous_on
                   (interval(lift a,lift b) PCROSS O)` THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 = lift b` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[continuous_within; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
              REAL_LT_REFL] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\
                     !y. y IN O /\ dist(y,y0) < d1
                         ==> dist((J:real^N->real^K) y,J y0) < e / &2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(J:real^N->real^K) continuous_on O` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2` o check (fun th ->
    is_forall(concl th) && p2um_mentions "vector_norm" th)) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(drop x - b) < d2 /\ dist(y:real^N,y0) < d1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist(pastecart (x:real^1) (y:real^N),pastecart (lift b) y0) < d1` THEN
    UNDISCH_TAC `dist(pastecart (x:real^1) (y:real^N),pastecart (lift b) y0) < d2` THEN
    REWRITE_TAC[dist; PASTECART_SUB] THEN
    MP_TAC(ISPEC `pastecart (x - lift b) (y - y0:real^N)` NORM_FSTCART) THEN
    MP_TAC(ISPEC `pastecart (x - lift b) (y - y0:real^N)` NORM_SNDCART) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`drop x`; `y:real^N`] o check (fun th ->
      is_forall(concl th) && p2um_mentions "vector_norm" th)) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && p2um_mentions "distance" th)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && p2um_mentions "distance" th)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2UM_UPTO_FROM_LIMIT = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K) (J:(num)list->real^N->real^K).
     open U /\ a < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
                   (\z. u (drop(fstcart z)) (sndcart z)) /\
     (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
          ==> J l continuous_on U) /\
     (!l K. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
            compact K /\ K SUBSET U
            ==> !e. &0 < e
                    ==> ?d. &0 < d /\
                            !t y. b - d < t /\ t < b /\ y IN K
                                  ==> norm(iterated_partial l
                                             (\z. u (drop(fstcart z)) (sndcart z))
                                             (pastecart (lift t) y) - J l y) < e) /\
     (!y. y IN U ==> u b y = J [] y)
     ==> ?e FF. &0 < e /\
                smooth_map_on (interval(lift a,lift(b + e)) PCROSS U) FF /\
                !t y. a < t /\ t <= b /\ y IN U ==> FF(pastecart (lift t) y) = u t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "JC")
    (CONJUNCTS_THEN2 (LABEL_TAC "UNI") (LABEL_TAC "TOP")))))) THEN
  MATCH_MP_TAC P2UM_UPTO_TOP_LOC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `y0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
    check (fun th -> concl th = `open(U:real^N->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(y0:real^N,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  SUBGOAL_THEN `ball(y0:real^N,r) SUBSET U` ASSUME_TAC THENL
   [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
        ==> (\w. if drop(fstcart w) < b
                 then iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z)) w
                 else (J:(num)list->real^N->real^K) l (sndcart w))
            continuous_on ({x | a < drop x /\ drop x <= b} PCROSS ball(y0,r))`
  (LABEL_TAC "HC") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN MATCH_MP_TAC P2UM_HCONT THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL];
        MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "UNI" (MP_TAC o SPECL [`l:num list`; `cball(y0:real^N,r)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "HC" (MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
    REWRITE_TAC[FORALL_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `drop x = b` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "TOP" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  EXISTS_TAC `\w. if drop(fstcart w) < b
                  then iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z)) w
                  else (J:(num)list->real^N->real^K) l (sndcart w)` THEN
  USE_THEN "HC" (fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART; LIFT_DROP] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The stage flow at the final time.  In a chart (U,phi) the                *)
(* spatial jets of the slab flow converge on compact subsets of the image   *)
(* of U INTER Om as t -> ts- (P2UM_STAGE_JETS: rfs_limit_metric measures in  *)
(* the preferred charts; the horizon analogue of P3S_EVENT_JETS), hence all *)
(* space-time partials converge to the jet polynomials of the limit          *)
(* (P2UM_STAGE_ST: JP_ST_REP, JP_EVAL_UNIFORM_LIMIT).                        *)
(* ------------------------------------------------------------------------- *)

let P2UM_STAGE_JETS = prove
 (`!top atlas (g:real->A->real^3^3) Om ts gl a (U:A->bool) (phi:A->real^3) K l.
     smooth_manifold_atlas top atlas /\ a < ts /\
     (!t. a < t /\ t < ts ==> riemannian_metric atlas (g t)) /\
     open_in top Om /\ rfs_limit_metric (top,atlas) Om ts g gl /\
     (U,phi) IN atlas /\ compact K /\ K SUBSET IMAGE phi (U INTER Om) /\
     ALL (\i. 1 <= i /\ i <= dimindex(:3)) l
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t y. ts - d < t /\ t < ts /\ y IN K
                           ==> norm(iterated_partial l
                                      ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                       metric_local atlas (U,phi) (g t)) y -
                                    iterated_partial l
                                      (vectorize o metric_local atlas (U,phi) gl) y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER Om))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "MF") (LABEL_TAC "LIM") o
              GEN_REWRITE_RULE I [rfs_limit_metric] o
              check (fun th -> p2um_mentions "rfs_limit_metric" th)) THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER Om)`; `K:real^3->bool`;
                 `metric_local atlas (U:A->bool,phi:A->real^3) (gl:A->real^3^3)`;
                 `\t. metric_local atlas (U:A->bool,phi:A->real^3) ((g:real->A->real^3^3) t)`;
                 `ts:real`; `ts - a:real`; `l:num list`] P3S_LCK_JET_CONV) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_LT; REAL_ARITH `ts - (ts - a) = a:real`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "MF" (MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[FST; SND]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P3S_METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && p2um_mentions "riemannian_metric" th)) THEN
      ASM_REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `e':real` THEN DISCH_TAC THEN
  USE_THEN "LIM" (MP_TAC o SPECL [`IMAGE (chart_inv (U:A->bool,phi:A->real^3)) K`;
                                  `LENGTH (l:num list)`; `e':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^3) U)` THEN CONJ_TAC THENL
       [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER Om)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `(U:A->bool,phi:A->real^3)`] MFDD_CHART_INV_CONTINUOUS) THEN
        ASM_REWRITE_TAC[FST; SND]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?x:A. x IN U INTER Om /\ (y:real^3) = (phi:A->real^3) x` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `K SUBSET IMAGE (phi:A->real^3) (U INTER Om)` THEN
        REWRITE_TAC[SUBSET; IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`; `phi:A->real^3`; `Om:A->bool`; `x:A`]
        MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DLIM"))) THEN
  EXISTS_TAC `min d (ts - a)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < t /\ ts - d < t` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ts - min d (ts - a) < t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?x0:A. x0 IN U INTER Om /\ (y:real^3) = (phi:A->real^3) x0`
  (X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `(y:real^3) IN K` THEN
    UNDISCH_TAC `K SUBSET IMAGE (phi:A->real^3) (U INTER Om)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top /\ x0 IN U /\ x0 IN Om` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:A) IN U INTER Om` THEN
    MP_TAC(ISPECL [`top:A topology`; `Om:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lck_dist2 (LENGTH (l:num list))
      (metric_local atlas (U,phi) (gl:A->real^3^3))
      (metric_local atlas (U,phi) ((g:real->A->real^3^3) t)) ((phi:A->real^3) x0) =
    lck_dist2 (LENGTH l)
      (metric_local atlas (chart_at atlas x0) gl)
      (metric_local atlas (chart_at atlas x0) (g t))
      (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x0) x0)`
  SUBST1_TAC THENL
   [ALL_TAC;
    USE_THEN "DLIM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(phi:A->real^3) x0` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`; `Om:A->bool`; `x0:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    ASM_SIMP_TAC[IN_INTER]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Om:A->bool`;
                 `gl:A->real^3^3`; `(g:real->A->real^3^3) t`;
                 `gl:A->real^3^3`; `(g:real->A->real^3^3) t`;
                 `U:A->bool`; `phi:A->real^3`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A))`;
                 `x0:A`; `LENGTH (l:num list)`] P3S_LCK_TRANSFER) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)))
               (FST(chart_at atlas x0) INTER Om))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[];
    USE_THEN "MF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P3S_METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)))
                      (FST(chart_at atlas x0))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) && p2um_mentions "riemannian_metric" th)) THEN
      ASM_REWRITE_TAC[riemannian_metric; PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A))`;
                   `U:A->bool`; `phi:A->real^3`; `gl:A->real^3^3`; `z:A`]
      METRIC_LOCAL_TRANS) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; chart_trans; o_THM];
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A))`;
                   `(g:real->A->real^3^3) t`; `z:A`]
      METRIC_LOCAL_TRANS) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; chart_trans; o_THM]]);;

(* All space-time partials of the chart representative converge to the jet  *)
(* polynomials of the limit metric.                                          *)

let P2UM_STAGE_ST = prove
 (`!top atlas (g:real->A->real^3^3) Om ts gl a (U:A->bool) (phi:A->real^3) K L.
     ricci_flow_on (top,atlas) a ts g /\ open_in top Om /\
     rfs_limit_metric (top,atlas) Om ts g gl /\
     (U,phi) IN atlas /\ compact K /\ K SUBSET IMAGE phi (U INTER Om) /\
     ALL (\h. 1 <= h /\ h <= dimindex(:3) + 1) L
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t y. ts - d < t /\ t < ts /\ y IN K
                           ==> norm(iterated_partial L
                                      (\w. (vectorize:real^3^3->real^(3,3)finite_prod)
                                           (metric_local atlas (U,phi)
                                              (g (drop(fstcart w))) (sndcart w)))
                                      (pastecart (lift t) y) -
                                    vectorize((lambda i j. jp_eval (jp_st (dimindex(:3)) L i j)
                                                             (metric_local atlas (U,phi) gl) y)
                                              :real^3^3)) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on] o
    check (fun th -> p2um_mentions "ricci_flow_on" th)) THEN
  SUBGOAL_THEN `lricci_flow (IMAGE (phi:A->real^3) U) a ts
                  (\t. metric_local atlas (U,phi) ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `ts:real`; `g:real->A->real^3^3`; `(U:A->bool,phi:A->real^3)`]
      PDE_RF_CHART_LOCAL) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER Om)) /\
                metric_field (IMAGE (phi:A->real^3) (U INTER Om))
                             (metric_local atlas (U,phi) (gl:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)` o CONJUNCT1 o
                  GEN_REWRITE_RULE I [rfs_limit_metric] o
                  check (fun th -> p2um_mentions "rfs_limit_metric" th)) THEN
      ASM_REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t y i j. jp_eval (jp_st (dimindex(:3)) L i j)
                                    (metric_local atlas (U:A->bool,phi:A->real^3)
                                       ((g:real->A->real^3^3) t)) y`;
                 `\y i j. jp_eval (jp_st (dimindex(:3)) L i j)
                                  (metric_local atlas (U:A->bool,phi:A->real^3)
                                     (gl:A->real^3^3)) y`;
                 `K:real^3->bool`; `ts:real`] PDE_VECTORIZE_UNIFORM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\t. metric_local atlas (U:A->bool,phi:A->real^3)
                          ((g:real->A->real^3^3) t)`;
                   `metric_local atlas (U:A->bool,phi:A->real^3) (gl:A->real^3^3)`;
                   `IMAGE (phi:A->real^3) (U INTER Om)`; `K:real^3->bool`; `ts:real`]
                  JP_EVAL_UNIFORM_LIMIT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
      MATCH_MP_TAC P2UM_STAGE_JETS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `Om:A->bool`; `a:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `jp_st (dimindex(:3)) L i j`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC JP_VALID_ST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[jp_conv];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  EXISTS_TAC `min d1 (ts - a)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (phi:A->real^3) U` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN K` THEN
    UNDISCH_TAC `K SUBSET IMAGE (phi:A->real^3) (U INTER Om)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `a:real`; `ts:real`;
                 `\t. metric_local atlas (U:A->bool,phi:A->real^3) ((g:real->A->real^3^3) t)`]
    JP_ST_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`L:num list`; `t:real`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The slab flow on Om, closed by the limit metric at ts, is a               *)
(* Ricci flow smooth up to ts (P2UM_STAGE_UPTO, from P2UM_UPTO_FROM_LIMIT   *)
(* and P2UM_STAGE_ST); restricted metrics of a metric known only on W, the   *)
(* identity pullback to a restricted atlas, and the left extension of a     *)
(* flow up to b.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2UM_RIEMANNIAN_RESTRICT_ON = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ open_in top W /\
     (!c. c IN atlas
          ==> metric_field (IMAGE (SND c) (FST c INTER W)) (metric_local atlas c g))
     ==> riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o check (fun th ->
      is_forall(concl th) && p2um_mentions "metric_field" th)) THEN
    ASM_REWRITE_TAC[FST; SND];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

let P2UM_PULLBACK_RESTRICT = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W
     ==> mfd_pullback_metric (restrict_atlas atlas W) atlas (\y. y) g x =
         restrict_metric atlas W g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[mfd_pullback_metric; SND] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2A_MPULLBACK_LOCAL THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `W:A->bool`; `z:A`]
      MFDR_CHART_INV_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]);;

(* A flow on (a,b) that is a flow up to b on (c,b] is one on (a,b].          *)

let P2UM_RFU_EXTEND_LEFT = prove
 (`!top atlas a c b (g:real->A->real^3^3).
     ricci_flow_on (top,atlas) a b g /\ rfs_flow_upto (top,atlas) c b g /\ a <= c
     ==> rfs_flow_upto (top,atlas) a b g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RF") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "RFC") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EXTU")))
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c < b /\ a < b` STRIP_ASSUME_TAC THENL
   [USE_THEN "RFC" (MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
  USE_THEN "EXTU" (MP_TAC o SPEC `cc:(A->bool)#(A->real^3)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AG"))))) THEN
  ABBREV_TAC `Ic = IMAGE (SND(cc:(A->bool)#(A->real^3))) (FST cc)` THEN
  ABBREV_TAC `R = \z:real^(1,3)finite_sum.
                    (vectorize:real^3^3->real^(3,3)finite_prod)
                    (metric_local atlas (cc:(A->bool)#(A->real^3))
                       ((g:real->A->real^3^3) (drop(fstcart z))) (sndcart z))` THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift a,lift b) PCROSS Ic)
                  (R:real^(1,3)finite_sum->real^(3,3)finite_prod) /\ open Ic`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "RF" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["R"; "Ic"] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "Ic" THEN MP_TAC(ISPECL [`top:A topology`;
                   `atlas:((A->bool)#(A->real^3))->bool`; `cc:(A->bool)#(A->real^3)`]
                   MFDM_CHART) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `m = (c + b) / &2` THEN
  SUBGOAL_THEN `a < m /\ c < m /\ m < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t y. c < t /\ t < b /\ y IN Ic
                      ==> (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                            (pastecart (lift t) y) =
                          (R:real^(1,3)finite_sum->real^(3,3)finite_prod)
                            (pastecart (lift t) y)`
  (LABEL_TAC "FR") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "AG" MATCH_MP_TAC THEN EXPAND_TAC "Ic" THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`e:real`; `\z:real^(1,3)finite_sum. if drop(fstcart z) < m
                                        then (R:real^(1,3)finite_sum->real^(3,3)finite_prod) z
                                        else (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod) z`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop s < b` THENL
     [EXISTS_TAC `interval(lift a,lift b) PCROSS (Ic:real^3->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `R:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
      REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`s':real^1`; `y':real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(SPECL [`drop s'`; `y':real^3`] (ASSUME
        `!t y. c < t /\ t < b /\ y IN Ic
               ==> (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                     (pastecart (lift t) y) =
                   (R:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift t) y)`)) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `interval(lift c,lift(b + e)) PCROSS (Ic:real^3->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `Fx:real^(1,3)finite_sum->real^(3,3)finite_prod` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
      REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`s':real^1`; `y':real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`drop s'`; `y':real^3`] (ASSUME
        `!t y. c < t /\ t < b /\ y IN Ic
               ==> (Fx:real^(1,3)finite_sum->real^(3,3)finite_prod)
                     (pastecart (lift t) y) =
                   (R:real^(1,3)finite_sum->real^(3,3)finite_prod) (pastecart (lift t) y)`)) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN COND_CASES_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      USE_THEN "AG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* The slab flow on Om, with the limit metric at ts, is a flow up to ts.    *)

let P2UM_STAGE_UPTO = prove
 (`!top atlas (g:real->A->real^3^3) Om ts gl a.
     ricci_flow_on (top,atlas) a ts g /\ open_in top Om /\
     rfs_limit_metric (top,atlas) Om ts g gl
     ==> rfs_flow_upto (subtopology top Om,restrict_atlas atlas Om) a ts
           (\t. restrict_metric atlas Om (if t = ts then gl else g t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on] o
    check (fun th -> p2um_mentions "ricci_flow_on" th)) THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "MF") (LABEL_TAC "LIM") o
              GEN_REWRITE_RULE I [rfs_limit_metric] o
              check (fun th -> p2um_mentions "rfs_limit_metric" th)) THEN
  REWRITE_TAC[rfs_flow_upto] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFO_CONG THEN
    EXISTS_TAC `\t. restrict_metric atlas Om ((g:real->A->real^3^3) t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFO_RESTRICT THEN ASM_REWRITE_TAC[];
      SIMP_TAC[REAL_LT_IMP_NE]];
    REWRITE_TAC[] THEN MATCH_MP_TAC P2UM_RIEMANNIAN_RESTRICT_ON THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER Om))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. y IN IMAGE (phi:A->real^3) (U INTER Om)
          ==> metric_local (restrict_atlas atlas Om) (U INTER Om,phi)
                (restrict_metric atlas Om (if t = ts then gl else (g:real->A->real^3^3) t)) y =
              metric_local atlas (U,phi) (if t = ts then gl else g t) y`
  (LABEL_TAC "RL") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`a:real`; `ts:real`; `IMAGE (phi:A->real^3) (U INTER Om)`;
    `\t y. (vectorize:real^3^3->real^(3,3)finite_prod)
           (metric_local atlas (U:A->bool,phi:A->real^3)
              (if t = ts then gl else (g:real->A->real^3^3) t) y)`;
    `\L y. (vectorize:real^3^3->real^(3,3)finite_prod)
           ((lambda i j. jp_eval (jp_st (dimindex(:3)) L i j)
                                 (metric_local atlas (U:A->bool,phi:A->real^3)
                                    (gl:A->real^3^3)) y):real^3^3)`]
   P2UM_UPTO_FROM_LIMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^3) (U INTER Om))
                 (metric_local atlas (U,phi) (gl:A->real^3^3))`
  ASSUME_TAC THENL
   [USE_THEN "MF" (MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[FST; SND]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* smoothness below ts *)
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                    (metric_local atlas (U:A->bool,phi:A->real^3)
                       ((g:real->A->real^3^3) (drop(fstcart z))) (sndcart z))` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      SIMP_TAC[REAL_LT_IMP_NE];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift ts) PCROSS IMAGE (phi:A->real^3) U` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)` o check (fun th ->
          is_forall(concl th) && p2um_mentions "smooth_map_on" th &&
          p2um_mentions "metric_local" th)) THEN
        ASM_REWRITE_TAC[FST; SND]]];
    (* the limits are continuous *)
    X_GEN_TAC `L:num list` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    SUBGOAL_THEN
     `(\y. (vectorize:real^3^3->real^(3,3)finite_prod)
           ((lambda i j. jp_eval (jp_st (dimindex(:3)) L i j)
                                 (metric_local atlas (U:A->bool,phi:A->real^3)
                                    (gl:A->real^3^3)) y):real^3^3)) =
      vectorize o (\y. (lambda i j. jp_eval (jp_st (dimindex(:3)) L i j)
                                         (metric_local atlas (U,phi) gl) y):real^3^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER Om)`;
                   `metric_local atlas (U:A->bool,phi:A->real^3) (gl:A->real^3^3)`]
      JP_METRIC_FIELD_GOOD) THEN
    ASM_REWRITE_TAC[jp_good] THEN SIMP_TAC[];
    (* uniform convergence of all partials *)
    MAP_EVERY X_GEN_TAC [`L:num list`; `K:real^3->bool`] THEN STRIP_TAC THEN
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `Om:A->bool`; `ts:real`; `gl:A->real^3^3`;
                   `a:real`; `U:A->bool`; `phi:A->real^3`; `K:real^3->bool`; `L:num list`]
      P2UM_STAGE_ST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,3)finite_sum)) L` THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SYM];
      DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
    EXISTS_TAC `min d (ts - a)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < t /\ ts - d < t` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ts - min d (ts - a) < t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "D" (MP_TAC o SPECL [`t:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `interval(lift a,lift ts) PCROSS IMAGE (phi:A->real^3) (U INTER Om)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    SIMP_TAC[REAL_LT_IMP_NE];
    (* the value at ts *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[jp_st; jp_eval; iterated_partial; o_THM; MATRIFY_VECTORIZE;
                PDE_MATRIX_LAMBDA_ETA]]);;

(* ------------------------------------------------------------------------- *)
(* Views.  The parts of p3_maxext, persistence for a general                 *)
(* view, and congruence of the region notions of p2c_regular_view for two   *)
(* views that agree on [a,b] (P2UM_VIEW_CONG).                                *)
(* ------------------------------------------------------------------------- *)

let P2UM_MAXEXT_PARTS = prove
 (`!(hs:(A)rfs_history) Om gl t.
     rfs_vtop (p3_maxext hs Om gl) t =
       (if t = rfs_horizon hs then subtopology (hs_top hs (hs_count hs)) Om
        else rfs_top_at hs t) /\
     rfs_vatlas (p3_maxext hs Om gl) t =
       (if t = rfs_horizon hs then restrict_atlas (hs_atlas hs (hs_count hs)) Om
        else rfs_atlas_at hs t) /\
     rfs_vmetric (p3_maxext hs Om gl) t =
       (if t = rfs_horizon hs then restrict_metric (hs_atlas hs (hs_count hs)) Om gl
        else rfs_metric_at hs t)`,
  REWRITE_TAC[p3_maxext; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2UM_PERSISTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     rfs_persists V W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
             open_in (rfs_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists; rfs_vtop; rfs_vatlas]);;

let P2UM_VIEW_CONG = prove
 (`!(V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    V2 W a b.
     a < b /\
     (!s. a <= s /\ s <= b
          ==> rfs_vtop V1 s = rfs_vtop V2 s /\ rfs_vatlas V1 s = rfs_vatlas V2 s /\
              rfs_vmetric V1 s = rfs_vmetric V2 s)
     ==> (rfs_persists V1 W a b <=> rfs_persists V2 W a b) /\
         (p2c_vflow V1 W a b <=> p2c_vflow V2 W a b) /\
         (p2c_vflow_from V1 W a b <=> p2c_vflow_from V2 W a b) /\
         (open_in (rfs_vtop V1 a) W <=> open_in (rfs_vtop V2 a) W) /\
         (!s. a <= s /\ s <= b
              ==> (mfd_diffeo (rfs_vtop V1 s) (rfs_vatlas V1 s) W
                              (rfs_vtop V1 b) (rfs_vatlas V1 b) W (\y:A. y) (\y. y) <=>
                   mfd_diffeo (rfs_vtop V2 s) (rfs_vatlas V2 s) W
                              (rfs_vtop V2 b) (rfs_vatlas V2 b) W (\y:A. y) (\y. y)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ")) THEN
  SUBGOAL_THEN
   `rfs_vtop (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) b = rfs_vtop V2 b /\
    rfs_vatlas V1 b = rfs_vatlas V2 b /\ rfs_vmetric V1 b = rfs_vmetric V2 b`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_vtop (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) a = rfs_vtop V2 a`
  ASSUME_TAC THENL
   [USE_THEN "EQ" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s <= b
        ==> p2c_vfam (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) W b s = p2c_vfam V2 W b s`
  (LABEL_TAC "FAM") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_vfam] THEN
    USE_THEN "EQ" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_persists (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) W a b <=> rfs_persists V2 W a b`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2UM_PERSISTS] THEN EQ_TAC THEN DISCH_TAC THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "EQ" (MP_TAC o SPEC `s:real`) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && p2um_mentions "smooth_manifold_atlas" th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. rfs_flow_upto M a b
          (p2c_vfam (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) W b) <=>
        rfs_flow_upto M a b (p2c_vfam V2 W b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2CF_RFU_CONG THENL
     [EXISTS_TAC `p2c_vfam (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W b`;
      EXISTS_TAC `p2c_vfam (V2:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W b`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "FAM" (MP_TAC o SPEC `t:real`) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. ricci_flow_from M a b
          (p2c_vfam (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)) W b) <=>
        ricci_flow_from M a b (p2c_vfam V2 W b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PDE_RFF_CONG THENL
     [EXISTS_TAC `p2c_vfam (V1:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W b`;
      EXISTS_TAC `p2c_vfam (V2:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W b`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "FAM" (MP_TAC o SPEC `t:real`) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vflow; p2c_vflow_from] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  USE_THEN "EQ" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A nonempty region W persisting in the maximal extension                  *)
(* over (a,T], T the horizon.  The context p2um_ctx, the basic facts (W is  *)
(* open in the last stage S and inside Om, 0 <= a, W persists in the history *)
(* below T), identity diffeomorphisms of W from the slices below T to S and *)
(* to the slice at T.                                                        *)
(* ------------------------------------------------------------------------- *)

let p2um_ctx = new_definition
 `p2um_ctx (hs:(A)rfs_history) gl W a <=>
    rfs_history_ok hs /\
    open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
    rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
      (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
    a < rfs_horizon hs /\
    rfs_persists (p3_maxext hs (p3_omega hs) gl) W a (rfs_horizon hs) /\
    ~(W = {})`;;

let P2UM_CTX_FACTS = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a
     ==> hausdorff_space (hs_top hs (hs_count hs)) /\
         smooth_manifold_atlas (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
         ricci_flow_from (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
           (hs_time hs (hs_count hs)) (rfs_horizon hs) (hs_metric hs (hs_count hs)) /\
         hs_time hs (hs_count hs) < rfs_horizon hs /\
         (!s. hs_time hs (hs_count hs) <= s /\ s < rfs_horizon hs
              ==> rfs_top_at hs s = hs_top hs (hs_count hs) /\
                  rfs_atlas_at hs s = hs_atlas hs (hs_count hs) /\
                  rfs_metric_at hs s = hs_metric hs (hs_count hs) s) /\
         W SUBSET p3_omega hs /\ open_in (hs_top hs (hs_count hs)) W /\
         smooth_manifold_atlas (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                               (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) /\
         &0 <= a /\
         (!b. a < b /\ b < rfs_horizon hs ==> rfs_persists (rfs_view hs) W a b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2um_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count (hs:(A)rfs_history)`] P2AH_STAGE) THEN
  ASM_REWRITE_TAC[LE_REFL; GSYM rfs_horizon] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [P2UM_PERSISTS] o
    check (fun th -> p2um_mentions "rfs_persists" th)) THEN
  DISCH_THEN(LABEL_TAC "P") THEN
  USE_THEN "P" (MP_TAC o SPEC `rfs_horizon (hs:(A)rfs_history)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[P2UM_MAXEXT_PARTS] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!b. a < b /\ b < rfs_horizon (hs:(A)rfs_history)
                    ==> rfs_persists (rfs_view hs) W a b`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real` THEN STRIP_TAC THEN REWRITE_TAC[P2AH_PERSISTS] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "P" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[P2UM_MAXEXT_PARTS] THEN
    SUBGOAL_THEN `~(s = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`;
                 `(a + rfs_horizon (hs:(A)rfs_history)) / &2`] P2AH_PERSISTS_NONEMPTY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* The slices below T map identically onto the last stage on W. *)

let P2UM_CTX_DIFF = prove
 (`!(hs:(A)rfs_history) gl W a s.
     p2um_ctx hs gl W a /\ a < s /\ s < rfs_horizon hs
     ==> smooth_manifold_atlas (rfs_top_at hs s) (rfs_atlas_at hs s) /\
         mfd_diffeo (rfs_top_at hs s) (rfs_atlas_at hs s) W
                    (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W
                    (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  ABBREV_TAC `b = max s (hs_time (hs:(A)rfs_history) (hs_count hs))` THEN
  SUBGOAL_THEN `a < b /\ s <= b /\ hs_time (hs:(A)rfs_history) (hs_count hs) <= b /\
                b < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` THEN
    REWRITE_TAC[P2AH_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `b:real`]
    P2AH_HISTORY_REGION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real` o check (fun th ->
    is_forall(concl th) && p2um_mentions "rfs_metric_at" th)) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* The restriction of the last stage to Om, as a diffeomorphism of W.        *)

let P2UM_CTX_RESTRICT_DIFF = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a
     ==> mfd_diffeo (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W
                    (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                    (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W
                    (\y:A. y) (\y. y) /\
         mfd_diffeo (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                    (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W
                    (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W
                    (\y:A. y) (\y. y) /\
         mfd_diffeo (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
                    (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W
                    (subtopology (hs_top hs (hs_count hs)) W)
                    (restrict_atlas (hs_atlas hs (hs_count hs)) W) W
                    (\y:A. y) (\y. y) /\
         open_in (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  SUBGOAL_THEN `mfd_diffeo (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W
                  (hs_top hs (hs_count hs)) (hs_atlas (hs:(A)rfs_history) (hs_count hs)) W
                  (\y:A. y) (\y. y)`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W
               (subtopology (hs_top hs (hs_count hs)) (p3_omega hs))
               (restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)) W
               (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                   `hs_atlas (hs:(A)rfs_history) (hs_count hs)`; `W:A->bool`;
                   `hs_top (hs:(A)rfs_history) (hs_count hs)`;
                   `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
                   `p3_omega (hs:(A)rfs_history)`; `W:A->bool`; `\y:A. y`; `\y:A. y`]
      APX_MFD_DIFFEO_RESTRICT_TARGET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                   `hs_atlas (hs:(A)rfs_history) (hs_count hs)`; `p3_omega (hs:(A)rfs_history)`;
                   `hs_top (hs:(A)rfs_history) (hs_count hs)`;
                   `hs_atlas (hs:(A)rfs_history) (hs_count hs)`; `W:A->bool`;
                   `W:A->bool`; `W:A->bool`; `\y:A. y`; `\y:A. y`]
      APX_MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]]);;

(* The left end a, when W is open there: the slice is a smooth manifold     *)
(* and maps identically onto the last stage on W (P2CY_HIST_FROM_SMOOTH).   *)

let P2UM_CTX_SLICE_A = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a /\ open_in (rfs_top_at hs a) W
     ==> smooth_manifold_atlas (rfs_top_at hs a) (rfs_atlas_at hs a) /\
         mfd_diffeo (rfs_top_at hs a) (rfs_atlas_at hs a) W
                    (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W
                    (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `a:real`] P2AH_SLAB_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`] P2AH_STAGE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SL"))))) THEN
    USE_THEN "SL" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = (max a (hs_time (hs:(A)rfs_history) (hs_count hs)) + rfs_horizon hs) / &2` THEN
  SUBGOAL_THEN `a < c /\ hs_time (hs:(A)rfs_history) (hs_count hs) <= c /\ c < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `hs:(A)rfs_history` P2CY_HIST_FROM_SMOOTH) THEN
  ASM_REWRITE_TAC[p2cz_from_smooth; P2AH_VIEW_PARTS] THEN
  DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `c:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th ->
    is_forall(concl th) && p2um_mentions "rfs_metric_at" th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* Diffeomorphisms of W onto the slice of the maximal extension at T.        *)

let P2UM_CTX_DIFFEO_T = prove
 (`!(hs:(A)rfs_history) gl W a s.
     p2um_ctx hs gl W a /\ a < s /\ s <= rfs_horizon hs
     ==> mfd_diffeo (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) s) W
                    (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs)) W
                    (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_RESTRICT_DIFF) THEN
  REWRITE_TAC[P2UM_MAXEXT_PARTS] THEN
  ASM_CASES_TAC `s = rfs_horizon (hs:(A)rfs_history)` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `s:real`]
    P2UM_CTX_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC P2AH_DIFFEO_TRANS THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                        `hs_atlas (hs:(A)rfs_history) (hs_count hs)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The case b = T of the region clauses.  In the context                     *)
(* p2um_ctx, the region family p2c_vfam of the maximal extension on W is a  *)
(* Ricci flow on (a,T) (the history region flow below T moved to the atlas  *)
(* of the slice at T, P3S_RFO_TRANSPORT_W and P2AH_PB_COMPOSE as in          *)
(* P2AH_REF_CHANGE, joined with the stage flow on (c,T)), smooth up to T    *)
(* (P2UM_STAGE_UPTO on the last stage), smooth from a when W is open at a   *)
(* (P2AH_HISTORY_FROM), and the identity of W is a diffeomorphism from the  *)
(* slice at a to the slice at T.                                             *)
(* ------------------------------------------------------------------------- *)

(* The history family moved to the atlas of the slice at T is the region    *)
(* family of the maximal extension (t below T).                             *)

let P2UM_CTX_FAM = prove
 (`!(hs:(A)rfs_history) gl W a t x.
     p2um_ctx hs gl W a /\ x IN W /\ ~(t = rfs_horizon hs) /\
     smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at hs t) /\
     mfd_diffeo (rfs_top_at hs t) (rfs_atlas_at hs t) W
                (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W (\y. y) (\y. y)
     ==> restrict_metric (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W
           (mfd_pullback_metric (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs))
              (restrict_atlas (hs_atlas hs (hs_count hs)) W) (\y. y)
              (restrict_metric (hs_atlas hs (hs_count hs)) W
                 (mfd_pullback_metric (hs_atlas hs (hs_count hs)) (rfs_atlas_at hs t) (\y. y)
                    (rfs_metric_at hs t)))) x =
         p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs) t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_RESTRICT_DIFF) THEN
  ASM_REWRITE_TAC[p2c_vfam; P2UM_MAXEXT_PARTS; ETA_AX] THEN
  MATCH_MP_TAC P2AH_PB_COMPOSE THEN
  MAP_EVERY EXISTS_TAC [`subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                        `hs_top (hs:(A)rfs_history) (hs_count hs)`;
                        `rfs_top_at (hs:(A)rfs_history) t`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]);;

(* The history part: a Ricci flow on (a,w) for any w < T.                   *)

let P2UM_CTX_RFO_HIST = prove
 (`!(hs:(A)rfs_history) gl W a c w.
     p2um_ctx hs gl W a /\ a < c /\ hs_time hs (hs_count hs) <= c /\ c < w /\
     w < rfs_horizon hs
     ==> ricci_flow_on
           (subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W,
            restrict_atlas (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W)
           a w (p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_RESTRICT_DIFF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  SUBGOAL_THEN `rfs_top_at hs c = hs_top hs (hs_count hs) /\
                rfs_atlas_at (hs:(A)rfs_history) c = hs_atlas hs (hs_count hs)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th ->
      is_forall(concl th) && p2um_mentions "rfs_metric_at" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count (hs:(A)rfs_history)`; `W:A->bool`;
                 `a:real`; `c:real`; `w:real`] P2AH_RF_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL; GSYM rfs_horizon] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                 `restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                 `subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) W`;
                 `restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) W`;
                 `W:A->bool`; `a:real`; `w:real`; `p2ah_famx (hs:(A)rfs_history) W c`]
    P3S_RFO_TRANSPORT_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC P2CF_RFO_CONG THEN
  EXISTS_TAC `\t. restrict_metric
                    (restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)) W
                    (mfd_pullback_metric
                       (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs))
                       (restrict_atlas (hs_atlas hs (hs_count hs)) W) (\x:A. x)
                       (p2ah_famx hs W c t))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `t:real`]
    P2UM_CTX_DIFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(t = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2ah_famx] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2UM_CTX_FAM THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]);;

(* The stage part: the last stage restricted to W, closed by the limit      *)
(* metric, is a flow up to T on (c,T] for t_n <= c < T.                     *)

let P2UM_CTX_RFU_STAGE = prove
 (`!(hs:(A)rfs_history) gl W a c.
     p2um_ctx hs gl W a /\ hs_time hs (hs_count hs) <= c /\ c < rfs_horizon hs
     ==> rfs_flow_upto
           (subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W,
            restrict_atlas (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W)
           c (rfs_horizon hs) (p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_RESTRICT_DIFF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                 `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
                 `hs_metric (hs:(A)rfs_history) (hs_count hs)`; `p3_omega (hs:(A)rfs_history)`;
                 `rfs_horizon (hs:(A)rfs_history)`; `gl:A->real^3^3`;
                 `hs_time (hs:(A)rfs_history) (hs_count hs)`] P2UM_STAGE_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> p2um_mentions "ricci_flow_from" th)) THEN
    SIMP_TAC[ricci_flow_from];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                 `restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                 `hs_time (hs:(A)rfs_history) (hs_count hs)`; `rfs_horizon (hs:(A)rfs_history)`;
                 `\t. restrict_metric (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)
                        (if t = rfs_horizon hs then gl else hs_metric hs (hs_count hs) t)`;
                 `W:A->bool`] P2CF_RFU_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  MATCH_MP_TAC P2CF_RFU_CONG THEN
  EXISTS_TAC `\t. restrict_metric
                    (restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)) W
                    (restrict_metric (hs_atlas hs (hs_count hs)) (p3_omega hs)
                       (if t = rfs_horizon hs then gl else hs_metric hs (hs_count hs) t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFU_LEFT THEN
    EXISTS_TAC `hs_time (hs:(A)rfs_history) (hs_count hs)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = rfs_horizon (hs:(A)rfs_history)` THENL
   [ASM_REWRITE_TAC[p2c_vfam; P2UM_MAXEXT_PARTS; ETA_AX]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
    is_forall(concl th) && p2um_mentions "rfs_metric_at" th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam; P2UM_MAXEXT_PARTS; ETA_AX] THEN
  MATCH_MP_TAC P2CF_RESTRICT_METRIC_CONG THEN
  EXISTS_TAC `subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2UM_PULLBACK_RESTRICT THEN
  EXISTS_TAC `hs_top (hs:(A)rfs_history) (hs_count hs)` THEN ASM_REWRITE_TAC[]);;

(* The whole interval (a,T): history part joined with the stage part.       *)

let P2UM_CTX_RFO = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a
     ==> ricci_flow_on
           (subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W,
            restrict_atlas (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W)
           a (rfs_horizon hs) (p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  ABBREV_TAC `c = (max a (hs_time (hs:(A)rfs_history) (hs_count hs)) + rfs_horizon hs) / &2` THEN
  SUBGOAL_THEN `a < c /\ hs_time (hs:(A)rfs_history) (hs_count hs) <= c /\ c < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC PDE_RFO_UNION2 THEN
  MAP_EVERY EXISTS_TAC [`(c + rfs_horizon (hs:(A)rfs_history)) / &2`; `c:real`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2UM_CTX_RFO_HIST THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `c:real`]
      P2UM_CTX_RFU_STAGE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[rfs_flow_upto];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Conjunct 2 at b = T: a flow on (a,T], smooth up to T.                    *)

let P2UM_CTX_RFU = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a
     ==> rfs_flow_upto
           (subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W,
            restrict_atlas (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W)
           a (rfs_horizon hs) (p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  ABBREV_TAC `c = (max a (hs_time (hs:(A)rfs_history) (hs_count hs)) + rfs_horizon hs) / &2` THEN
  SUBGOAL_THEN `a < c /\ hs_time (hs:(A)rfs_history) (hs_count hs) <= c /\ c < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2UM_RFU_EXTEND_LEFT THEN EXISTS_TAC `c:real` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2UM_CTX_RFO THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2UM_CTX_RFU_STAGE THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The history part from a, when W is open in the slice at a.               *)

let P2UM_CTX_RFF_HIST = prove
 (`!(hs:(A)rfs_history) gl W a c.
     p2um_ctx hs gl W a /\ a < c /\ hs_time hs (hs_count hs) <= c /\ c < rfs_horizon hs /\
     open_in (rfs_top_at hs a) W
     ==> ricci_flow_from
           (subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W,
            restrict_atlas (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W)
           a c (p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_RESTRICT_DIFF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  SUBGOAL_THEN `rfs_top_at hs c = hs_top hs (hs_count hs) /\
                rfs_atlas_at (hs:(A)rfs_history) c = hs_atlas hs (hs_count hs)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o check (fun th ->
      is_forall(concl th) && p2um_mentions "rfs_metric_at" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W a c` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `a:real`; `c:real`] P2AH_HISTORY_FROM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                 `restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)`;
                 `subtopology (hs_top (hs:(A)rfs_history) (hs_count hs)) W`;
                 `restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) W`;
                 `W:A->bool`; `a:real`; `c:real`; `p2ah_fam (hs:(A)rfs_history) W c`]
    P2AH_RFF_TRANSPORT_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC PDE_RFF_CONG THEN
  EXISTS_TAC `\t. restrict_metric
                    (restrict_atlas (hs_atlas (hs:(A)rfs_history) (hs_count hs)) (p3_omega hs)) W
                    (mfd_pullback_metric
                       (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs))
                       (restrict_atlas (hs_atlas hs (hs_count hs)) W) (\x:A. x)
                       (p2ah_fam hs W c t))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(t = c) /\ ~(t = rfs_horizon (hs:(A)rfs_history))` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (rfs_top_at hs t) (rfs_atlas_at (hs:(A)rfs_history) t) /\
    mfd_diffeo (rfs_top_at hs t) (rfs_atlas_at hs t) W
               (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) W (\y:A. y) (\y. y)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `t:real = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2UM_CTX_SLICE_A THEN
      EXISTS_TAC `gl:A->real^3^3` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2UM_CTX_DIFF THEN
      MAP_EVERY EXISTS_TAC [`gl:A->real^3^3`; `a:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2ah_fam] THEN ASM_REWRITE_TAC[ETA_AX] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2UM_CTX_FAM THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]);;

(* Conjunct 3 at b = T: the flow on (a,T) is smooth from a.                 *)

let P2UM_CTX_RFF = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a /\ open_in (rfs_top_at hs a) W
     ==> ricci_flow_from
           (subtopology (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) W,
            restrict_atlas (restrict_atlas (hs_atlas hs (hs_count hs)) (p3_omega hs)) W)
           a (rfs_horizon hs) (p2c_vfam (p3_maxext hs (p3_omega hs) gl) W (rfs_horizon hs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  ABBREV_TAC `c = (max a (hs_time (hs:(A)rfs_history) (hs_count hs)) + rfs_horizon hs) / &2` THEN
  SUBGOAL_THEN `a < c /\ hs_time (hs:(A)rfs_history) (hs_count hs) <= c /\ c < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC PDE_RFF_FROM_ON THEN EXISTS_TAC `c:real` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2UM_CTX_RFF_HIST THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2UM_CTX_RFO THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* Conjunct 5 at b = T: the identity of W from the slice at a to the slice  *)
(* at T.                                                                     *)

let P2UM_CTX_DIFFEO_A = prove
 (`!(hs:(A)rfs_history) gl W a.
     p2um_ctx hs gl W a /\ open_in (rfs_top_at hs a) W
     ==> mfd_diffeo (rfs_vtop (p3_maxext hs (p3_omega hs) gl) a)
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) a) W
                    (rfs_vtop (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs))
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs)) W
                    (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2UM_CTX_RESTRICT_DIFF) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_ctx]) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`]
    P2UM_CTX_SLICE_A) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS] THEN
  MATCH_MP_TAC P2AH_DIFFEO_TRANS THEN
  MAP_EVERY EXISTS_TAC [`hs_top (hs:(A)rfs_history) (hs_count hs)`;
                        `hs_atlas (hs:(A)rfs_history) (hs_count hs)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* P2C_MAXEXT_REGULAR.  The hypotheses p2um_hyp of the statement; the case   *)
(* split of a persisting W (empty; below T, where the maximal extension      *)
(* agrees with the history view, P2UM_VIEW_CONG and P2CY_HISTORY_REGULAR; at *)
(* T, the case b = T above; beyond T, W is empty); the slices; the five      *)
(* clauses of p2c_regular_view; the main theorem.                            *)
(* ------------------------------------------------------------------------- *)

let p2um_hyp = new_definition
 `p2um_hyp (hs:(A)rfs_history) gl <=>
    rfs_history_ok hs /\
    open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
    rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
      (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl`;;

let P2UM_CASES = prove
 (`!(hs:(A)rfs_history) gl W a b.
     p2um_hyp hs gl /\ a < b /\ rfs_persists (p3_maxext hs (p3_omega hs) gl) W a b
     ==> W = {} \/
         (b < rfs_horizon hs /\
          !s. a <= s /\ s <= b
              ==> rfs_vtop (p3_maxext hs (p3_omega hs) gl) s = rfs_vtop (rfs_view hs) s /\
                  rfs_vatlas (p3_maxext hs (p3_omega hs) gl) s = rfs_vatlas (rfs_view hs) s /\
                  rfs_vmetric (p3_maxext hs (p3_omega hs) gl) s = rfs_vmetric (rfs_view hs) s) \/
         (b = rfs_horizon hs /\ p2um_ctx hs gl W a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_hyp]) THEN
  ASM_CASES_TAC `W:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `b < rfs_horizon (hs:(A)rfs_history)` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(s = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS; P2AH_VIEW_PARTS]];
    DISJ2_TAC] THEN
  ASM_CASES_TAC `b = rfs_horizon (hs:(A)rfs_history)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[p2um_ctx]; ALL_TAC] THEN
  SUBGOAL_THEN `W:A->bool = {}` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC P2AH_SLICE_EMPTY THEN
  MAP_EVERY EXISTS_TAC [`hs:(A)rfs_history`; `b:real`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) W a b` THEN
  REWRITE_TAC[P2UM_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; P2UM_MAXEXT_PARTS] THEN SIMP_TAC[]);;

(* Clause 1: the nonempty slices.                                            *)

let P2UM_SLICE_REG = prove
 (`!(hs:(A)rfs_history) gl t.
     p2um_hyp hs gl /\ ~(topspace(rfs_vtop (p3_maxext hs (p3_omega hs) gl) t) = {})
     ==> hausdorff_space (rfs_vtop (p3_maxext hs (p3_omega hs) gl) t) /\
         smooth_manifold_atlas (rfs_vtop (p3_maxext hs (p3_omega hs) gl) t)
                               (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) t) /\
         riemannian_metric (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) t)
                           (rfs_vmetric (p3_maxext hs (p3_omega hs) gl) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_hyp]) THEN
  ASM_CASES_TAC `t = rfs_horizon (hs:(A)rfs_history)` THENL
   [ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs_count (hs:(A)rfs_history)`] P2AH_STAGE) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2UM_RIEMANNIAN_RESTRICT_ON THEN
      EXISTS_TAC `hs_top (hs:(A)rfs_history) (hs_count hs)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_limit_metric] o
        check (fun th -> p2um_mentions "rfs_limit_metric" th)) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(topspace(rfs_top_at (hs:(A)rfs_history) t) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(topspace(rfs_vtop (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) t) = {})` THEN
    ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS] THEN
  MP_TAC(ISPEC `{}:A->bool` P2CY_HISTORY_REGULAR) THEN
  REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT; p2c_regular_view] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[P2AH_VIEW_PARTS]);;

(* Clause 2: persisting sets carry flows up to the right end.                *)

let P2UM_C2 = prove
 (`!(hs:(A)rfs_history) gl W a b.
     p2um_hyp hs gl /\ a < b /\ rfs_persists (p3_maxext hs (p3_omega hs) gl) W a b
     ==> p2c_vflow (p3_maxext hs (p3_omega hs) gl) W a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_hyp]) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
    P2UM_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THENL
   [ASM_REWRITE_TAC[p2c_vflow] THEN MATCH_MP_TAC P2CF_RFU_EMPTY THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) {} a b` THEN
    REWRITE_TAC[P2UM_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    MP_TAC(ISPECL [`p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl`;
                   `rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `a:real`; `b:real`]
      P2UM_VIEW_CONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) W a b` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `W:A->bool` P2CY_HISTORY_REGULAR) THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT; p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[p2c_vflow; P2UM_MAXEXT_PARTS] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2UM_CTX_RFU THEN ASM_REWRITE_TAC[]]);;

(* Clause 3: sets open at the left end carry flows smooth from there.        *)

let P2UM_C3 = prove
 (`!(hs:(A)rfs_history) gl W a b.
     p2um_hyp hs gl /\ a < b /\ open_in (rfs_vtop (p3_maxext hs (p3_omega hs) gl) a) W /\
     rfs_persists (p3_maxext hs (p3_omega hs) gl) W a b
     ==> p2c_vflow_from (p3_maxext hs (p3_omega hs) gl) W a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_hyp]) THEN
  SUBGOAL_THEN `p2c_vflow (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) W a b`
  ASSUME_TAC THENL [MATCH_MP_TAC P2UM_C2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
    P2UM_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THENL
   [ASM_REWRITE_TAC[p2c_vflow_from] THEN MATCH_MP_TAC P2CF_RFF_EMPTY THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) {} a b` THEN
    REWRITE_TAC[P2UM_PERSISTS] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    MP_TAC(ISPECL [`p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl`;
                   `rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `a:real`; `b:real`]
      P2UM_VIEW_CONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) W a b` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (rfs_view (hs:(A)rfs_history)) a) W` ASSUME_TAC THENL
     [UNDISCH_TAC `open_in (rfs_vtop (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) a) W` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `W:A->bool` P2CY_HISTORY_REGULAR) THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT; p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(a = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) a) W` ASSUME_TAC THENL
     [UNDISCH_TAC `open_in (rfs_vtop (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) a) W` THEN
      ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS];
      ALL_TAC] THEN
    REWRITE_TAC[p2c_vflow_from; P2UM_MAXEXT_PARTS] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2UM_CTX_RFF THEN ASM_REWRITE_TAC[]]);;

(* Clause 4: identity diffeomorphisms from the slices in (a,b] to b.         *)

let P2UM_C4 = prove
 (`!(hs:(A)rfs_history) gl W a b s.
     p2um_hyp hs gl /\ a < s /\ s <= b /\ rfs_persists (p3_maxext hs (p3_omega hs) gl) W a b
     ==> mfd_diffeo (rfs_vtop (p3_maxext hs (p3_omega hs) gl) s)
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) s) W
                    (rfs_vtop (p3_maxext hs (p3_omega hs) gl) b)
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) b) W (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_hyp]) THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
    P2UM_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THENL
   [REWRITE_TAC[P2CF_DIFFEO_EMPTY];
    MP_TAC(ISPECL [`p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl`;
                   `rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `a:real`; `b:real`]
      P2UM_VIEW_CONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) && p2um_mentions "mfd_diffeo" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) W a b` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `W:A->bool` P2CY_HISTORY_REGULAR) THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT; p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`; `s:real`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2UM_CTX_DIFFEO_T THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]]);;

(* Clause 5: the identity diffeomorphism from a to b when W is open at a.   *)

let P2UM_C5 = prove
 (`!(hs:(A)rfs_history) gl W a b.
     p2um_hyp hs gl /\ a < b /\ open_in (rfs_vtop (p3_maxext hs (p3_omega hs) gl) a) W /\
     rfs_persists (p3_maxext hs (p3_omega hs) gl) W a b
     ==> mfd_diffeo (rfs_vtop (p3_maxext hs (p3_omega hs) gl) a)
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) a) W
                    (rfs_vtop (p3_maxext hs (p3_omega hs) gl) b)
                    (rfs_vatlas (p3_maxext hs (p3_omega hs) gl) b) W (\y:A. y) (\y. y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2um_hyp]) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `gl:A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
    P2UM_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THENL
   [REWRITE_TAC[P2CF_DIFFEO_EMPTY];
    MP_TAC(ISPECL [`p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl`;
                   `rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `a:real`; `b:real`]
      P2UM_VIEW_CONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
      is_forall(concl th) && p2um_mentions "mfd_diffeo" th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `rfs_persists (rfs_view (hs:(A)rfs_history)) W a b` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_persists (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) W a b` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_vtop (rfs_view (hs:(A)rfs_history)) a) W` ASSUME_TAC THENL
     [UNDISCH_TAC `open_in (rfs_vtop (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) a) W` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `W:A->bool` P2CY_HISTORY_REGULAR) THEN
    REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT; p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:A->bool`; `a:real`; `b:real`] o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) a) W` ASSUME_TAC THENL
     [UNDISCH_TAC `open_in (rfs_vtop (p3_maxext (hs:(A)rfs_history) (p3_omega hs) gl) a) W` THEN
      SUBGOAL_THEN `~(a = rfs_horizon (hs:(A)rfs_history))` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[P2UM_MAXEXT_PARTS]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2UM_CTX_DIFFEO_A THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: P2C_MAXEXT_REGULAR_STATEMENT of pc_p2c_views.          *)
(* ------------------------------------------------------------------------- *)

let P2UM_MAXEXT_REGULAR = prove
 (`!u:A->bool. P2C_MAXEXT_REGULAR_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_MAXEXT_REGULAR_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `gl:A->real^3^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2um_hyp (hs:(A)rfs_history) gl` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2um_hyp]; ALL_TAC] THEN
  REWRITE_TAC[p2c_regular_view] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2UM_SLICE_REG THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2UM_C2 THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2UM_C3 THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2UM_C4 THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2UM_C5 THEN ASM_REWRITE_TAC[]]);;

