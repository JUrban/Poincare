(* ========================================================================= *)
(* Unit pc_p3_s16l15 (Part 3 proofs; MT Ch 16): MT Lemma 16.15 (p. 379-381). *)
(* Part (1): curves with L+ < L0 stay in the parabolic ball B(x,tt,r/2) for  *)
(* tau <= taup (P3N_PAR_BALL: real induction over the corner-free pieces,    *)
(* the metric comparison on the parabolic neighbourhood and AM-GM). Part     *)
(* (2): they miss the evolving cap regions Phi{d < A0 + 50} for h^2/2 after  *)
(* each surgery (P3N_1615_CAP: separation of the scalar curvature near the   *)
(* parabolic ball, the first exit from the cap region P3N_CAP_EXIT,          *)
(* Prop 16.13 on the shifted curve). The assembly P3N_LEMMA_16_15_FIX (with  *)
(* the second scale rr <= r') is stated against the Prop 16.13 body (with    *)
(* 1/2 <= theta0), Prop 16.5, Prop 12.31 and Thm 12.5; route theorem         *)
(* P3N_LEMMA_16_15_ROUTE.                                                    *)
(* ========================================================================= *)

needs "src/pc_p3_s16len.ml";;
needs "src/pc_p2a_brg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Real-analysis tools for Lemma 16.15 part (1): real                       *)
(* induction on an interval (P3N_RIND), the integral of inv(sqrt t) on      *)
(* [0,b] and the AM-GM bound 2S <= lam/sqrt t + sqrt t S^2/lam.            *)
(* ========================================================================= *)

(* real induction: P holds at a, propagates to the right from every point  *)
(* up to which it holds, and holds at every point up to which it holds      *)
(* strictly below                                                           *)

let P3N_RIND = prove
 (`!P a b. a <= b /\ P a /\
     (!x. a <= x /\ x < b /\ (!y. a <= y /\ y <= x ==> P y)
          ==> ?d. &0 < d /\ !y. x < y /\ y < x + d /\ y <= b ==> P y) /\
     (!x. a < x /\ x <= b /\ (!y. a <= y /\ y < x ==> P y) ==> P x)
     ==> !x. a <= x /\ x <= b ==> P x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "right") (LABEL_TAC "left")))) THEN
  ABBREV_TAC `S = {x | a <= x /\ x <= b /\ !y. a <= y /\ y <= x ==> (P:real->bool) y}` THEN
  SUBGOAL_THEN `(a:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:real = a` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `a:real` THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `b:real` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `s = sup S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN `a <= s /\ s <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "lub" MATCH_MP_TAC THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. a <= y /\ y < s ==> (P:real->bool) y` (LABEL_TAC "below") THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x. x IN S /\ y < x` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `s <= y` MP_TAC THENL
       [USE_THEN "lub" MATCH_MP_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real->bool) s` ASSUME_TAC THENL
   [ASM_CASES_TAC `s:real = a` THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "left" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. a <= y /\ y <= s ==> (P:real->bool) y` (LABEL_TAC "upto") THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_CASES_TAC `y:real = s` THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "below" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = b` ASSUME_TAC THENL
   [ASM_CASES_TAC `s < b` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    USE_THEN "right" (MP_TAC o C MP (end_itlist CONJ
      [ASSUME `a <= s`; ASSUME `s < b`; ASSUME `!y. a <= y /\ y <= s ==> (P:real->bool) y`]) o
      SPEC `s:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
    SUBGOAL_THEN `min (s + d / &2) b IN S` MP_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_CASES_TAC `y <= s` THENL
       [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "d" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      DISCH_TAC THEN
      SUBGOAL_THEN `min (s + d / &2) b <= s` MP_TAC THENL
       [USE_THEN "ub" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* the integral of inv(sqrt t) on [0,b] is 2 sqrt b *)

let P3N_INV_SQRT_INTEGRAL = prove
 (`!b. &0 <= b
       ==> ((\t. inv(sqrt t)) has_real_integral (&2 * sqrt b)) (real_interval[&0,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. &2 * sqrt t`; `\t. inv(sqrt t)`; `{}:real->bool`; `&0`; `b:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  REWRITE_TAC[SQRT_0; REAL_MUL_RZERO; REAL_SUB_RZERO; COUNTABLE_EMPTY; DIFF_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < sqrt x` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt x) = &2 * inv(&2 * sqrt x)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN FIRST_ASSUM ACCEPT_TAC]);;

(* AM-GM in the form used for the length bound *)

let P3N_AMGM_SQRT = prove
 (`!t S lam. &0 < t /\ &0 < lam
             ==> &2 * S <= lam * inv(sqrt t) + sqrt t * S pow 2 / lam`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt t` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = sqrt t` THEN DISCH_TAC THEN
  SUBGOAL_THEN `lam * inv q + q * S pow 2 / lam - &2 * S = (lam - q * S) pow 2 / (lam * q)`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < q` THEN UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (lam - q * S) pow 2 / (lam * q)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Curves in one stage of a history.  The pointwise speed in a               *)
(* restricted atlas (P3N_SPEED_RESTRICT, as in P2AP_LENGTH_RESTRICT) and a  *)
(* space-time curve on a corner-free backward-time interval inside stage k  *)
(* is a C1 curve of stage k (P3N_ST_SLAB_C1).                               *)
(* ========================================================================= *)

let P3N_SPEED_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^N^N) (gamma:real->A) a b t.
     smooth_manifold_atlas top atlas /\ open_in top W /\ a < b /\
     mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b /\
     t IN real_interval[a,b]
     ==> mfd_speed (restrict_atlas atlas W) (restrict_metric atlas W g) gamma a b t =
         mfd_speed atlas g gamma a b t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AP_C1_CURVE_RESTRICT) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top /\ gamma t IN W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`
         PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U INTER W:A->bool,phi:A->real^N) IN restrict_atlas atlas W` ASSUME_TAC THENL
   [REWRITE_TAC[IN_RESTRICT_ATLAS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                 `restrict_metric (atlas:((A->bool)#(A->real^N))->bool) W g`;
                 `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U INTER W:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT; IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* a C1 curve inside W is a C1 curve of the restricted manifold (the        *)
(* argument of P2CO_C1_CURVE_SUBTOP of pc_p2c_lrestrict, outside this closure) *)

let P3N_C1_CURVE_SUBTOP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W (gamma:real->A) a b.
     mfd_c1_curve (top,atlas) gamma a b /\
     (!t. t IN real_interval[a,b] ==> gamma t IN W)
     ==> mfd_c1_curve (subtopology top W,restrict_atlas atlas W) gamma a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  MAP_EVERY X_GEN_TAC [`UW:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `s:real^1` THEN
  ASM_CASES_TAC `(s:real^1) IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) (drop s) IN W` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `(s:real^1) IN interval[lift a,lift b]` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

(* open-set continuity on [a,b] gives a continuous map on [c,d] (the       *)
(* argument of P2AU_CONT_MAP_INTERVAL of pc_p2a_flow, outside this closure) *)

let P3N_CONT_MAP_INTERVAL = prove
 (`!top (gamma:real->A) a b c d.
     a <= c /\ d <= b /\
     (!s. a <= s /\ s <= b ==> gamma s IN topspace top) /\
     (!s0 O. a <= s0 /\ s0 <= b /\ open_in top O /\ gamma s0 IN O
             ==> ?e. &0 < e /\ !s. a <= s /\ s <= b /\ abs(s - s0) < e ==> gamma s IN O)
     ==> continuous_map (subtopology euclideanreal (real_interval[c,d]),top) gamma`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `O:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `u0:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u0:real`; `O:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `real_interval(u0 - e,u0 + e) INTER real_interval[c,d]` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `real_interval(u0 - e,u0 + e)` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL];
    REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTER; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* a space-time curve on [s1,s2], 0 < s1, all of whose times lie in stage k *)

let P3N_ST_SLAB_C1 = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b0 k s1 s2.
     rfs_st_curve hs tt gamma (&0) b0 /\ k <= hs_count hs /\
     &0 < s1 /\ s1 <= s2 /\ s2 <= b0 /\
     hs_time hs k <= tt - s2 /\ tt - s1 < hs_time hs (k + 1) /\
     (!s. s1 <= s /\ s <= s2 ==> rfs_top_at hs (tt - s) = hs_top hs k)
     ==> mfd_c1_curve (hs_top hs k,hs_atlas hs k) gamma s1 s2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve])
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "top")))))))) THEN
  REWRITE_TAC[mfd_c1_curve] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC P3N_CONT_MAP_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`s1:real`; `s2:real`] THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "top" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (CONJ (ASSUME `s1 <= s`)
                                                             (ASSUME `s <= s2`)))]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "topspace" with Failure _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s0:real`; `O:A->bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s0:real`; `O:A->bool`] o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
            (concl th))) THEN
      USE_THEN "top" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `s1 <= s0`)
                                                         (ASSUME `s0 <= s2`))]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `e:real` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{s | &0 < drop s /\ drop s <= b0 /\ hs_time (hs:(A)rfs_history) k <= tt - drop s /\
                     tt - drop s < hs_time hs (k + 1) /\
                     (gamma:real->A) (drop s) IN FST(c:(A->bool)#(A->real^3))}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Speed comparison on a parabolic region.  For a C1 curve of               *)
(* the slice at tt inside a region W persisting on (tt - r^2,tt] with      *)
(* |Rm| <= r^-2, the tt-speed is at most sqrt 2 times the speed in the     *)
(* slice at tt - s, for 0 < s <= r^2/8 (P2AP_METRIC_COMPARE in the         *)
(* restricted atlas, P3N_SPEED_RESTRICT, P2B9S_PB_SPEED).                   *)
(* ========================================================================= *)

let P3N_PAR_SPEED_CMP = prove
 (`!(hs:(A)rfs_history) W tt r (gamma:real->A) s1 s2 s.
     rfs_history_ok hs /\ &0 < r /\
     p2a_region (rfs_view hs) W (tt - r pow 2) tt /\
     (!t z. tt - r pow 2 < t /\ t <= tt /\ z IN W
            ==> p3_vrm (rfs_view hs) t z <= inv(r pow 2)) /\
     mfd_c1_curve (rfs_top_at hs tt,rfs_atlas_at hs tt) gamma s1 s2 /\ s1 < s2 /\
     (!u. u IN real_interval[s1,s2] ==> gamma u IN W) /\
     &0 < s /\ s <= r pow 2 / &8 /\ s IN real_interval[s1,s2]
     ==> mfd_speed (rfs_atlas_at hs tt) (rfs_metric_at hs tt) gamma s1 s2 s pow 2 <=
         &2 * mfd_speed (rfs_atlas_at hs (tt - s)) (rfs_metric_at hs (tt - s))
                        gamma s1 s2 s pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - s`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  REPEAT STRIP_TAC THEN
  (* the region facts at tt - s and tt *)
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2a_region; p2a_persists; rfs_view; p2a_vtop; p2a_vatlas] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2a_region"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pers") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (K ALL_TAC))) THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) tt) W` ASSUME_TAC THENL
   [USE_THEN "pers" (MP_TAC o SPEC `tt:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo (rfs_top_at (hs:(A)rfs_history) tt) (rfs_atlas_at hs tt) W
                           (rfs_top_at hs (tt - s)) (rfs_atlas_at hs (tt - s)) W
                           (\y:A. y) (\y. y)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN USE_THEN "dif" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the curve in the restricted atlas and its velocity *)
  SUBGOAL_THEN `mfd_c1_curve (subtopology (rfs_top_at (hs:(A)rfs_history) tt) W,
                              restrict_atlas (rfs_atlas_at hs tt) W) gamma s1 s2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_C1_CURVE_SUBTOP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `v = mfd_velocity (restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) tt) W)
                               (gamma:real->A) s1 s2 s` THEN
  (* the metric comparison at gamma s *)
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `W:A->bool`; `tt - r pow 2`; `tt:real`;
                 `inv(r pow 2)`; `tt - s`; `(gamma:real->A) s`; `v:real^3`]
                P2AP_METRIC_COMPARE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2AB_SVS THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  REWRITE_TAC[REAL_ARITH `tt - (tt - s) = s`] THEN
  SUBGOAL_THEN `exp(&4 * inv(r pow 2) * s) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * (&4 * inv(r pow 2) * s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
        ALL_TAC];
      ALL_TAC] THEN
    (SUBGOAL_THEN `inv(r pow 2) * s <= &1 / &8` MP_TAC THENL
      [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
       ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
       REAL_ARITH_TAC]);
    ALL_TAC] THEN
  (* the two speeds in the restricted atlas *)
  SUBGOAL_THEN
   `mfd_speed (rfs_atlas_at (hs:(A)rfs_history) tt) (rfs_metric_at hs tt) (gamma:real->A)
              s1 s2 s =
    sqrt(v dot (p2a_rmetric (rfs_view hs) W tt tt (gamma s) ** v)) /\
    mfd_speed (rfs_atlas_at hs (tt - s)) (rfs_metric_at hs (tt - s)) gamma s1 s2 s =
    sqrt(v dot (p2a_rmetric (rfs_view hs) W tt (tt - s) (gamma s) ** v))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                     `W:A->bool`; `rfs_metric_at (hs:(A)rfs_history) tt`; `gamma:real->A`;
                     `s1:real`; `s2:real`; `s:real`] P3N_SPEED_RESTRICT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[mfd_speed; p2a_rmetric; rfs_view; p2a_vatlas; p2a_vmetric; ETA_AX] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(tt - s = tt)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                   `rfs_top_at (hs:(A)rfs_history) (tt - s)`;
                   `rfs_atlas_at (hs:(A)rfs_history) (tt - s)`; `W:A->bool`; `W:A->bool`;
                   `\y:A. y`; `\y:A. y`; `rfs_metric_at (hs:(A)rfs_history) (tt - s)`;
                   `gamma:real->A`; `s1:real`; `s2:real`; `s:real`] P2B9S_PB_SPEED) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(\y:A. y) o (gamma:real->A) = gamma` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN BETA_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                   `W:A->bool`;
                   `mfd_pullback_metric (rfs_atlas_at (hs:(A)rfs_history) tt)
                                        (rfs_atlas_at hs (tt - s)) (\y:A. y)
                                        (rfs_metric_at hs (tt - s))`;
                   `gamma:real->A`; `s1:real`; `s2:real`; `s:real`] P3N_SPEED_RESTRICT) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[mfd_speed; p2a_rmetric; rfs_view; p2a_vatlas; p2a_vmetric; ETA_AX] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* conclusion from the comparison *)
  ABBREV_TAC `q1 = v dot (p2a_rmetric (rfs_view (hs:(A)rfs_history)) W tt tt
                                      ((gamma:real->A) s) ** v)` THEN
  ABBREV_TAC `q2 = v dot (p2a_rmetric (rfs_view (hs:(A)rfs_history)) W tt (tt - s)
                                      ((gamma:real->A) s) ** v)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= q1` ASSUME_TAC THENL
   [EXPAND_TAC "q1" THEN
    REWRITE_TAC[p2a_rmetric; rfs_view; p2a_vatlas; p2a_vmetric; ETA_AX] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                   `W:A->bool`; `rfs_metric_at (hs:(A)rfs_history) tt`]
                  RIEMANNIAN_METRIC_RESTRICT) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`subtopology (rfs_top_at (hs:(A)rfs_history) tt) W`;
                   `restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) tt) W`;
                   `restrict_metric (rfs_atlas_at (hs:(A)rfs_history) tt) W
                                    (rfs_metric_at hs tt)`; `(gamma:real->A) s`]
                  RIEMANNIAN_METRIC_POS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        MP_TAC(ISPECL [`subtopology (rfs_top_at (hs:(A)rfs_history) tt) W`;
                       `restrict_atlas (rfs_atlas_at (hs:(A)rfs_history) tt) W`;
                       `gamma:real->A`; `s1:real`; `s2:real`; `s:real`]
                      MFD_C1_CURVE_IN_TOPSPACE) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(&4 * inv(r pow 2) * s)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= exp(&4 * inv(r pow 2) * s) * q2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `q1 <= &2 * q2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&4 * inv(r pow 2) * s) * q2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2]);;

(* ========================================================================= *)
(* The distance bound on a corner-free piece.  On [s1,s2] with              *)
(* 0 < s1, s2 <= r^2/8 and no event time in tt - [s1,s2), a space-time     *)
(* curve inside the parabolic ball W = B(x,tt,r) is a C1 curve of the       *)
(* slice at tt, and its tt-distance is at most the integral of any w with  *)
(* 2 |X|_(tt-s) <= w s inside the piece.                                    *)
(* ========================================================================= *)

let P3N_PAR_PIECE = prove
 (`!(hs:(A)rfs_history) tt x r b0 (gamma:real->A) s1 s2 w.
     rfs_history_ok hs /\ &0 < r /\
     p2a_region (rfs_view hs) (rfs_vball (rfs_view hs) tt x r) (tt - r pow 2) tt /\
     (!t z. tt - r pow 2 < t /\ t <= tt /\ z IN rfs_vball (rfs_view hs) tt x r
            ==> p3_vrm (rfs_view hs) t z <= inv(r pow 2)) /\
     rfs_st_curve hs tt gamma (&0) b0 /\
     &0 < s1 /\ s1 < s2 /\ s2 <= b0 /\ s2 <= r pow 2 / &8 /\
     (!s j. s1 <= s /\ s < s2 /\ j <= hs_count hs + 1 ==> ~(tt - s = hs_time hs j)) /\
     (!s. s1 <= s /\ s <= s2 ==> gamma s IN rfs_vball (rfs_view hs) tt x r) /\
     w real_integrable_on real_interval[s1,s2] /\
     (!s. s1 < s /\ s < s2
          ==> &2 * mfd_speed (rfs_atlas_at hs (tt - s)) (rfs_metric_at hs (tt - s))
                             gamma (&0) b0 s <= w s)
     ==> mfd_joinable (rfs_top_at hs tt,rfs_atlas_at hs tt) (gamma s1) (gamma s2) /\
         mfd_dist (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt)
                  (gamma s1) (gamma s2)
         <= real_integral (real_interval[s1,s2]) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r` THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2a_region; p2a_persists; rfs_view; p2a_vtop; p2a_vatlas] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2a_region"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pers") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (K ALL_TAC))) THEN
  (* the stage k of the times tt - [s1,s2] *)
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) (tt - s2)) W` ASSUME_TAC THENL
   [USE_THEN "pers" (MP_TAC o SPEC `tt - s2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= tt - s2 /\ tt - s2 < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC
  THENL
   [MATCH_MP_TAC P2A_TOPSPACE_LIVE THEN EXISTS_TAC `(gamma:real->A) s2` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "open_in" with Failure _ -> false)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `W:A->bool`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `gamma:real->A`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - s2`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) (tt - s2)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `tt - s1 < hs_time (hs:(A)rfs_history) (k + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tt - hs_time (hs:(A)rfs_history) (k + 1)`; `k + 1`] o
      check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> try fst(dest_const t) = "hs_count" with Failure _ -> false))
            (concl th))) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2
                    ==> rfs_top_at (hs:(A)rfs_history) (tt - s) = hs_top hs k /\
                        rfs_atlas_at hs (tt - s) = hs_atlas hs k`
  (LABEL_TAC "stage") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `tt - s`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* C1 in the stage, pushed to the slice at tt *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `b0:real`; `k:num`;
                 `s1:real`; `s2:real`] P3N_ST_SLAB_C1) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "stage" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - s2`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  USE_THEN "stage" (MP_TAC o SPEC `s2:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_diffeo (hs_top (hs:(A)rfs_history) k) (hs_atlas hs k) W
                           (rfs_top_at hs tt) (rfs_atlas_at hs tt) W (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [USE_THEN "stage" (MP_TAC o SPEC `s2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "dif" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                             (gamma:real->A) s1 s2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) k`; `hs_atlas (hs:(A)rfs_history) k`;
                   `rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                   `W:A->bool`; `\y:A. y`; `gamma:real->A`; `s1:real`; `s2:real`]
                  GRGD_C1_CURVE_PUSH) THEN
    SUBGOAL_THEN `(\y:A. y) o (gamma:real->A) = gamma` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN BETA_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `mfd_diffeo (hs_top (hs:(A)rfs_history) k) (hs_atlas hs k) W
                            (rfs_top_at hs tt) (rfs_atlas_at hs tt) W (\y:A. y) (\y. y)` THEN
    REWRITE_TAC[mfd_diffeo; homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `W:A->bool`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `gamma:real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_length (rfs_atlas_at (hs:(A)rfs_history) tt) (rfs_metric_at hs tt)
                         (gamma:real->A) s1 s2` THEN
  CONJ_TAC THENL [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_OPEN_INTERVAL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON_OPEN_INTERVAL] THEN
    MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
    EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) tt` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON_OPEN_INTERVAL];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s IN real_interval[s1,s2]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `W:A->bool`; `tt:real`; `r:real`; `gamma:real->A`;
                 `s1:real`; `s2:real`; `s:real`] P3N_PAR_SPEED_CMP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
    X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `W:A->bool`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `gamma:real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_atlas_at (hs:(A)rfs_history) (tt - s)`; `rfs_metric_at (hs:(A)rfs_history) (tt - s)`;
                 `gamma:real->A`; `s1:real`; `s2:real`; `&0`; `b0:real`; `s:real`]
                P2A_SPEED_INTERIOR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `S = mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (tt - s))
                            (rfs_metric_at hs (tt - s)) (gamma:real->A) (&0) b0 s` THEN
  ABBREV_TAC `S0 = mfd_speed (rfs_atlas_at (hs:(A)rfs_history) tt) (rfs_metric_at hs tt)
                             (gamma:real->A) s1 s2 s` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= S0 /\ &0 <= S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "S0" THEN MATCH_MP_TAC MFD_SPEED_POS_LE THEN
      EXISTS_TAC `rfs_top_at (hs:(A)rfs_history) tt` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN
      MP_TAC(ISPECL [`rfs_atlas_at (hs:(A)rfs_history) (tt - s)`;
                     `rfs_metric_at (hs:(A)rfs_history) (tt - s)`;
                     `gamma:real->A`; `s1:real`; `s2:real`; `&0`; `b0:real`; `s:real`]
                    P2A_SPEED_INTERIOR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "stage" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      MATCH_MP_TAC MFD_SPEED_POS_LE THEN EXISTS_TAC `hs_top (hs:(A)rfs_history) k` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt - s`] P3_HIST_VIEW_SLICES) THEN
      ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
      USE_THEN "stage" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * S` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`S0:real`; `&2 * S`] REAL_LE_SQUARE_ABS) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_MUL; REAL_POS] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * S pow 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN MP_TAC(SPEC `S:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    EXPAND_TAC "S" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Gaps of finite sets of times, the closed balls of the slice              *)
(* at tt are closed in the nearby slices of a parabolic region, and the     *)
(* continuity of a space-time curve in W with respect to the tt-distance.   *)
(* ========================================================================= *)

let P3N_FINITE_GAP_RIGHT = prove
 (`!C x. FINITE C ==> ?d. &0 < d /\ !c. c IN C /\ x < c ==> x + d <= c`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`C:real->bool`,`C:real->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c0:real`; `C:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `x < c0` THENL
   [EXISTS_TAC `min d (c0 - x)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `c:real` THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `c:real` THEN
    STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let P3N_FINITE_GAP_LEFT = prove
 (`!C x. FINITE C ==> ?d. &0 < d /\ !c. c IN C /\ c < x ==> c <= x - d`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`C:real->bool`,`C:real->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c0:real`; `C:real->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `c0 < x` THENL
   [EXISTS_TAC `min d (x - c0)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `c:real` THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `c:real` THEN
    STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* closed balls of radius c < r about x at time tt are closed in the slices *)
(* of the parabolic region on (tt - r^2,tt]                                  *)

let P3N_PAR_KC_CLOSED = prove
 (`!(hs:(A)rfs_history) tt x r c s.
     rfs_history_ok hs /\ &0 < r /\
     p2a_region (rfs_view hs) (rfs_vball (rfs_view hs) tt x r) (tt - r pow 2) tt /\
     c < r /\ tt - r pow 2 < s /\ s <= tt
     ==> closed_in (rfs_top_at hs s)
           (mfd_cball (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt) x c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r` THEN
  ABBREV_TAC `K = mfd_cball (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                            (rfs_metric_at hs tt) x c` THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2a_region; p2a_persists; rfs_view; p2a_vtop; p2a_vatlas] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2a_region"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pers") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET W` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K"; "W"] THEN
    REWRITE_TAC[rfs_vball; rfs_view; SUBSET; mfd_cball; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in (rfs_top_at (hs:(A)rfs_history) tt) K` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2AB_COMPACT THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "K" THEN MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "dif" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact_in (subtopology (rfs_top_at (hs:(A)rfs_history) s) W) K` MP_TAC THENL
   [SUBGOAL_THEN `IMAGE (\y:A. y) K = K` (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology (rfs_top_at (hs:(A)rfs_history) tt) W` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` P2AB_SVS) THEN ASM_REWRITE_TAC[p2a_svs] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `s:real`) THEN
  REWRITE_TAC[rfs_view; p2a_vtop]);;

(* continuity of a space-time curve in W for the distance at time tt *)

let P3N_PAR_CONT = prove
 (`!(hs:(A)rfs_history) tt x r b0 (gamma:real->A) s0 e.
     rfs_history_ok hs /\ &0 < r /\
     p2a_region (rfs_view hs) (rfs_vball (rfs_view hs) tt x r) (tt - r pow 2) tt /\
     rfs_st_curve hs tt gamma (&0) b0 /\
     &0 <= s0 /\ s0 <= b0 /\ s0 < r pow 2 /\
     gamma s0 IN rfs_vball (rfs_view hs) tt x r /\ &0 < e
     ==> ?d. &0 < d /\
             !s. &0 <= s /\ s <= b0 /\ abs(s - s0) < d
                 ==> gamma s IN rfs_vball (rfs_view hs) tt x r /\
                     mfd_joinable (rfs_top_at hs tt,rfs_atlas_at hs tt) (gamma s0) (gamma s) /\
                     mfd_dist (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt)
                              (gamma s0) (gamma s) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r` THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[p2a_region; p2a_persists; rfs_view; p2a_vtop; p2a_vatlas] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "p2a_region"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pers") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  ABBREV_TAC `O = W INTER mfd_ball (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                                   (rfs_metric_at hs tt) ((gamma:real->A) s0) e` THEN
  SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) (tt - s0)) O` ASSUME_TAC THENL
   [SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) tt) W /\
                  open_in (rfs_top_at hs (tt - s0)) W` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "pers" (MP_TAC o SPEC `tt:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        USE_THEN "pers" (MP_TAC o SPEC `tt - s0`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (rfs_top_at (hs:(A)rfs_history) tt) O` ASSUME_TAC THENL
     [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(O:A->bool) SUBSET W` ASSUME_TAC THENL
     [EXPAND_TAC "O" THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
    USE_THEN "dif" (MP_TAC o SPEC `tt - s0`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\y:A. y`; `subtopology (rfs_top_at (hs:(A)rfs_history) (tt - s0)) W`;
                   `subtopology (rfs_top_at (hs:(A)rfs_history) tt) W`; `O:A->bool`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `O:A->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) (tt - s0)`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; mfd_ball; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gamma:real->A) s0 IN topspace(rfs_top_at (hs:(A)rfs_history) tt)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(gamma:real->A) s0 IN W` THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve"
    with Failure _ -> false)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`s0:real`; `O:A->bool`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  USE_THEN "d" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; mfd_ball; IN_ELIM_THM] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The induction along the curve for Lemma 16.15 part (1).                  *)
(* p3n_parctx collects the data (parabolic region, |Rm| <= r^-2, the curve, *)
(* the majorant w of 2|X|, int w < r); p3n_parq s says gamma s is joined to *)
(* x at time tt with d_tt(x,gamma s) <= int_0^s w.  The property holds at 0, *)
(* extends to the right (P3N_PAR_RIGHT: a limit at the corner on the left   *)
(* end of a piece) and passes to left limits (P3N_PAR_LEFT: the closed balls *)
(* stay closed in the slices), hence holds on [0,b] (P3N_PAR_INDUCT).       *)
(* ========================================================================= *)

let p3n_parctx = new_definition
 `p3n_parctx (hs:(A)rfs_history) tt (x:A) r b0 b (gamma:real->A) (w:real->real) <=>
    rfs_history_ok hs /\ x IN topspace(rfs_top_at hs tt) /\ &0 < r /\
    p2a_region (rfs_view hs) (rfs_vball (rfs_view hs) tt x r) (tt - r pow 2) tt /\
    (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
           ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
    rfs_st_curve hs tt gamma (&0) b0 /\ gamma (&0) = x /\
    &0 < b /\ b <= b0 /\ b <= r pow 2 / &8 /\
    w real_integrable_on real_interval[&0,b] /\
    (!t. t IN real_interval[&0,b] ==> &0 <= w t) /\
    (!s. &0 < s /\ s < b
         ==> &2 * mfd_speed (rfs_atlas_at hs (tt - s)) (rfs_metric_at hs (tt - s))
                            gamma (&0) b0 s <= w s) /\
    real_integral (real_interval[&0,b]) w < r`;;

let p3n_parq = new_definition
 `p3n_parq (hs:(A)rfs_history) tt (x:A) (gamma:real->A) (w:real->real) s <=>
    mfd_joinable (rfs_top_at hs tt,rfs_atlas_at hs tt) x (gamma s) /\
    mfd_dist (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt) x (gamma s)
    <= real_integral (real_interval[&0,s]) w`;;

(* monotonicity of the integral of a nonnegative integrable function *)

let P3N_INT_MONO = prove
 (`!w b p q p' q'.
     w real_integrable_on real_interval[&0,b] /\
     (!t. t IN real_interval[&0,b] ==> &0 <= w t) /\
     &0 <= p' /\ p' <= p /\ p <= q /\ q <= q' /\ q' <= b
     ==> real_integral (real_interval[p,q]) w <= real_integral (real_interval[p',q']) w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* the corner set of backward event times is finite *)

let P3N_CORNERS_FINITE = prove
 (`!(hs:(A)rfs_history) tt.
     FINITE (IMAGE (\j. tt - hs_time hs j) {j | j <= hs_count hs + 1})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LE]);;

let P3N_CORNERS_IN = prove
 (`!(hs:(A)rfs_history) tt s j.
     j <= hs_count hs + 1 /\ tt - s = hs_time hs j
     ==> s IN IMAGE (\j. tt - hs_time hs j) {j | j <= hs_count hs + 1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* extension to the right *)

let P3N_PAR_RIGHT = prove
 (`!(hs:(A)rfs_history) tt x r b0 b (gamma:real->A) w s0.
     p3n_parctx hs tt x r b0 b gamma w /\ &0 <= s0 /\ s0 < b /\
     (!y. &0 <= y /\ y <= s0 ==> p3n_parq hs tt x gamma w y)
     ==> ?d. &0 < d /\ !y. s0 < y /\ y < s0 + d /\ y <= b ==> p3n_parq hs tt x gamma w y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_parctx] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q")))) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  USE_THEN "Q" (MP_TAC o REWRITE_RULE[p3n_parq] o SPEC `s0:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[&0,s0]) w <=
                real_integral (real_interval[&0,b]) w` ASSUME_TAC THENL
   [MATCH_MP_TAC P3N_INT_MONO THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\j. tt - hs_time (hs:(A)rfs_history) j) {j | j <= hs_count hs + 1}`;
                 `s0:real`] P3N_FINITE_GAP_RIGHT) THEN
  REWRITE_TAC[P3N_CORNERS_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gap"))) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`; `gamma:real->A`;
                 `s0:real`; `&1`] P3N_PAR_CONT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inW"))) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s0 <= s /\ s <= y
                    ==> (gamma:real->A) s IN rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r`
  (LABEL_TAC "W") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "inW" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `D0 = mfd_dist (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                            (rfs_metric_at hs tt) ((gamma:real->A) s0) (gamma y)` THEN
  ABBREV_TAC `I0 = real_integral (real_interval[s0,y]) (w:real->real)` THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> mfd_joinable (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                         ((gamma:real->A) s0) (gamma y) /\ D0 < I0 + e`
  (LABEL_TAC "eta") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`;
                   `gamma:real->A`; `s0:real`; `e:real`] P3N_PAR_CONT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d3"))) THEN
    ABBREV_TAC `s1 = s0 + min d3 (y - s0) / &2` THEN
    SUBGOAL_THEN `s0 < s1 /\ s1 < y /\ abs(s1 - s0) < d3` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "d3" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`;
                   `gamma:real->A`; `s1:real`; `y:real`; `w:real->real`] P3N_PAR_PIECE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
       [MAP_EVERY X_GEN_TAC [`s:real`; `j:num`] THEN STRIP_TAC THEN DISCH_TAC THEN
        USE_THEN "gap" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC P3N_CORNERS_IN THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
            ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "W" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      STRIP_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) s1` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                   `rfs_metric_at (hs:(A)rfs_history) tt`; `(gamma:real->A) s0`;
                   `(gamma:real->A) s1`; `(gamma:real->A) y`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `real_integral (real_interval[s1,y]) w <= I0` MP_TAC THENL
     [EXPAND_TAC "I0" THEN MATCH_MP_TAC P3N_INT_MONO THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                             ((gamma:real->A) s0) (gamma y) /\ D0 <= I0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "eta" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "eta" (MP_TAC o SPEC `(D0 - I0) / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[p3n_parq] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) s0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                 `rfs_metric_at (hs:(A)rfs_history) tt`; `x:A`;
                 `(gamma:real->A) s0`; `(gamma:real->A) y`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real->real`; `&0`; `y:real`; `s0:real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* passage to left limits *)

let P3N_PAR_LEFT = prove
 (`!(hs:(A)rfs_history) tt x r b0 b (gamma:real->A) w s.
     p3n_parctx hs tt x r b0 b gamma w /\ &0 < s /\ s <= b /\
     (!y. &0 <= y /\ y < s ==> p3n_parq hs tt x gamma w y)
     ==> p3n_parq hs tt x gamma w s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3n_parctx] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Q")))) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
  ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
  ABBREV_TAC `K = mfd_cball (rfs_top_at (hs:(A)rfs_history) tt,rfs_atlas_at hs tt)
                            (rfs_metric_at hs tt) x (real_integral (real_interval[&0,b]) w)` THEN
  SUBGOAL_THEN `!y. &0 <= y /\ y < s ==> (gamma:real->A) y IN K` (LABEL_TAC "inK") THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN
    USE_THEN "Q" (MP_TAC o REWRITE_RULE[p3n_parq] o SPEC `y:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[mfd_cball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `real_integral (real_interval[&0,y]) w` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3N_INT_MONO THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET rfs_vball (rfs_view (hs:(A)rfs_history)) tt x r`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; mfd_cball; rfs_vball; rfs_view; mfd_ball;
                                    IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* gamma s lies in K, by closedness in the slice at tt - s *)
  SUBGOAL_THEN `(gamma:real->A) s IN K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`;
                   `real_integral (real_interval[&0,b]) w`; `tt - s`] P3N_PAR_KC_CLOSED) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[closed_in] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve"
      with Failure _ -> false)) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `topspace(rfs_top_at (hs:(A)rfs_history) (tt - s)) DIFF K`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d5:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s - min d5 s / &2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `d5:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN
    USE_THEN "inK" (MP_TAC o SPEC `s - min d5 s / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the last piece [s',s] *)
  MP_TAC(ISPECL [`IMAGE (\j. tt - hs_time (hs:(A)rfs_history) j) {j | j <= hs_count hs + 1}`;
                 `s:real`] P3N_FINITE_GAP_LEFT) THEN
  REWRITE_TAC[P3N_CORNERS_FINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gap"))) THEN
  ABBREV_TAC `s' = s - min d4 s / &2` THEN
  SUBGOAL_THEN `&0 < s' /\ s' < s /\ s - d4 < s'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "Q" (MP_TAC o REWRITE_RULE[p3n_parq] o SPEC `s':real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`;
                 `gamma:real->A`; `s':real`; `s:real`; `w:real->real`] P3N_PAR_PIECE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [MAP_EVERY X_GEN_TAC [`u:real`; `j:num`] THEN STRIP_TAC THEN DISCH_TAC THEN
      USE_THEN "gap" (MP_TAC o SPEC `u:real`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC P3N_CORNERS_IN THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gamma:real->A) u IN K` MP_TAC THENL
       [ASM_CASES_TAC `u:real = s` THENL
         [ASM_REWRITE_TAC[]; USE_THEN "inK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        ASM SET_TAC[]];
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  REWRITE_TAC[p3n_parq] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) s'` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) tt`; `rfs_atlas_at (hs:(A)rfs_history) tt`;
                 `rfs_metric_at (hs:(A)rfs_history) tt`; `x:A`;
                 `(gamma:real->A) s'`; `(gamma:real->A) s`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real->real`; `&0`; `s:real`; `s':real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* the induction *)

let P3N_PAR_INDUCT = prove
 (`!(hs:(A)rfs_history) tt x r b0 b (gamma:real->A) w.
     p3n_parctx hs tt x r b0 b gamma w
     ==> !s. &0 <= s /\ s <= b ==> p3n_parq hs tt x gamma w s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`\s. p3n_parq (hs:(A)rfs_history) tt (x:A) (gamma:real->A)
                                              (w:real->real) s`; `&0`; `b:real`] P3N_RIND)) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p3n_parctx (hs:(A)rfs_history) tt x r b0 b (gamma:real->A) w` THEN
    REWRITE_TAC[p3n_parctx] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `p3n_parctx (hs:(A)rfs_history) tt x r b0 b (gamma:real->A) w` THEN
    REWRITE_TAC[p3n_parctx; p3n_parq] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`] P3_HIST_VIEW_SLICES) THEN
    ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL; REAL_INTEGRAL_REFL; REAL_LE_REFL];
    X_GEN_TAC `s0:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`; `b:real`;
                   `gamma:real->A`; `w:real->real`; `s0:real`] P3N_PAR_RIGHT) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`; `b:real`;
                   `gamma:real->A`; `w:real->real`; `s:real`] P3N_PAR_LEFT) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Lemma 16.15 part (1) in general form (P3N_PAR_BALL).  A                   *)
(* space-time curve from x with |Rm| <= r^-2 on the parabolic neighbourhood *)
(* P(x,tt,r,-r^2) stays in B(x,tt,r/2) up to backward time b <= r^2/8 when *)
(* 2 lam sqrt b + int_0^b F / lam < r/2, F majorizing sqrt t |X|^2 (MT p.  *)
(* 380-381: metric comparison, Cauchy-Schwarz in the AM-GM form, and the    *)
(* length of a curve leaving B(x,tt,r/2)).                                  *)
(* ========================================================================= *)

let P3N_PAR_BALL = prove
 (`!(hs:(A)rfs_history) tt x r b0 b (gamma:real->A) Fn lam.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs tt) /\ &0 < r /\
     rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
            ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
     rfs_st_curve hs tt gamma (&0) b0 /\ gamma (&0) = x /\
     &0 < b /\ b <= b0 /\ b <= r pow 2 / &8 /\
     Fn real_integrable_on real_interval[&0,b] /\
     (!t. t IN real_interval[&0,b] ==> &0 <= Fn t) /\
     (!t. &0 < t /\ t < b
          ==> sqrt t * mfd_speed (rfs_atlas_at hs (tt - t)) (rfs_metric_at hs (tt - t))
                                 gamma (&0) b0 t pow 2 <= Fn t) /\
     &0 < lam /\ &2 * lam * sqrt b + real_integral (real_interval[&0,b]) Fn / lam < r / &2
     ==> !t. &0 <= t /\ t <= b ==> gamma t IN rfs_vball (rfs_view hs) tt x (r / &2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (rfs_view (hs:(A)rfs_history)) (rfs_vball (rfs_view hs) tt x r)
                           (tt - r pow 2) tt` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AB_REGION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r (r pow 2)` THEN
      REWRITE_TAC[rfs_parabolic_exists]];
    ALL_TAC] THEN
  ABBREV_TAC `Ib = real_integral (real_interval[&0,b]) (Fn:real->real)` THEN
  ABBREV_TAC `w = \t. lam * inv(sqrt t) + (Fn:real->real) t / lam` THEN
  SUBGOAL_THEN `((w:real->real) has_real_integral (lam * &2 * sqrt b + Ib / lam))
                (real_interval[&0,b])` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC P3N_INV_SQRT_INTEGRAL THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
      EXPAND_TAC "Ib" THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real->real) real_integrable_on real_interval[&0,b] /\
                real_integral (real_interval[&0,b]) w < r / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real_integrable_on] THEN
      EXISTS_TAC `lam * &2 * sqrt b + Ib / lam` THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,b] ==> &0 <= (w:real->real) t` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "w" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `t IN real_interval[&0,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 < s /\ s < b
        ==> &2 * mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (tt - s))
                           (rfs_metric_at hs (tt - s)) (gamma:real->A) (&0) b0 s
            <= (w:real->real) s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "w" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * inv(sqrt s) +
                sqrt s * mfd_speed (rfs_atlas_at (hs:(A)rfs_history) (tt - s))
                                   (rfs_metric_at hs (tt - s)) (gamma:real->A) (&0) b0 s pow 2 /
                lam` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3N_AMGM_SQRT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> a + x <= a + y`) THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `b0:real`; `b:real`;
                 `gamma:real->A`; `w:real->real`] P3N_PAR_INDUCT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p3n_parctx] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[p3n_parq] o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `real_integral (real_interval[&0,t]) w` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,b]) w` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3N_INT_MONO THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Tools for Lemma 16.15 part (2): C1 maps under a translation              *)
(* of the parameter, and the scalar curvature separation of the parabolic   *)
(* ball from an evolving surgery cap.                                        *)
(* ========================================================================= *)

let P3N_CD1_TRANSLATE = prove
 (`!S (f:real^1->real^N) c.
     continuously_differentiable 1 S f
     ==> continuously_differentiable 1 {u | c + u IN S} (\u. f(c + u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ONE; continuously_differentiable] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\u:real^1. (f':real^1->real^1->real^N) (c + u)` THEN BETA_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\u:real^1. (f:real^1->real^N) (c + u)) = f o (\u. c + u)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(f':real^1->real^1->real^N) (c + u) = f' (c + u) o (\h. vec 0 + h)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      BETA_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN EXISTS_TAC `S:real^1->bool` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]]];
    X_GEN_TAC `h:real^1` THEN
    SUBGOAL_THEN `(\u:real^1. (f':real^1->real^1->real^N) (c + u) h) =
                  (\v. f' v h) o (\u. c + u)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^1->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[]]]);;

(* the scalar curvature separation: R >= h^-2 c/(2(1-s)) on the cap region  *)
(* and |R| <= 6 r^-2 on the parabolic ball are incompatible when            *)
(* 12 h^2 < c r^2                                                            *)

let P3N_1615_SEP = prove
 (`!c h r s R0.
     &0 < c /\ &0 < h /\ &0 < r /\ h pow 2 * &12 < c * r pow 2 /\ &0 <= s /\ s < &1 /\
     inv(h pow 2) * c / (&2 * (&1 - s)) <= R0 /\ abs R0 <= &6 * inv(r pow 2)
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ &0 < r pow 2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(h pow 2) * c / (&2 * (&1 - s)) = c * inv(&2 * h pow 2 * (&1 - s))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < h pow 2` THEN UNDISCH_TAC `s < &1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * inv(&2 * h pow 2) <= c * inv(&2 * h pow 2 * (&1 - s))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= h pow 2 * s` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * inv(&2 * h pow 2) - &6 * inv(r pow 2) =
                (c * r pow 2 - h pow 2 * &12) / (&2 * h pow 2 * r pow 2)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < h pow 2` THEN UNDISCH_TAC `&0 < r pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c * r pow 2 - h pow 2 * &12) / (&2 * h pow 2 * r pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* A space-time curve restricted to [a1,b1] and shifted to                  *)
(* start at backward time 0 from tt - a1 is again a space-time curve.       *)
(* ========================================================================= *)

let P3N_ST_CURVE_SHIFT = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b0 a1 b1.
     rfs_st_curve hs tt gamma (&0) b0 /\ &0 <= a1 /\ a1 <= b1 /\ b1 <= b0
     ==> rfs_st_curve hs (tt - a1) (\s. gamma(a1 + s)) (&0) (b1 - a1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_st_curve] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ARITH `(tt - a1) - x = tt - (a1 + x)`] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a1 + tau0`; `O:A->bool`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`k:num`; `c:(A->bool)#(A->real^3)`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `c:(A->bool)#(A->real^3)`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "continuously_differentiable"
                               with Failure _ -> false)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `lift a1` o MATCH_MP P3N_CD1_TRANSLATE) THEN
    REWRITE_TAC[IN_ELIM_THM; DROP_ADD; LIFT_DROP] THEN BETA_TAC THEN
    REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{u | &0 < a1 + drop u /\ a1 + drop u <= b0 /\
                     hs_time (hs:(A)rfs_history) k <= tt - (a1 + drop u) /\
                     tt - (a1 + drop u) < hs_time hs (k + 1) /\
                     (gamma:real->A) (a1 + drop u) IN FST(c:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Vector derivatives and speeds under a translation of the                 *)
(* parameter.                                                                *)
(* ========================================================================= *)

let P3N_HVD_TRANSLATE = prove
 (`!(F1:real^1->real^N) v x c S.
     (F1 has_vector_derivative v) (at (c + x) within (IMAGE (\u. c + u) S))
     ==> ((\u. F1(c + u)) has_vector_derivative v) (at x within S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\u:real^1. c + u) has_vector_derivative vec 1) (at x within S)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\u:real^1. c:real^1`; `vec 0:real^1`; `\u:real^1. u`; `vec 1:real^1`;
                   `at (x:real^1) within S`] HAS_VECTOR_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; HAS_VECTOR_DERIVATIVE_ID; VECTOR_ADD_LID] THEN
    BETA_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^1. c + u`; `F1:real^1->real^N`; `vec 1:real^1`; `v:real^N`;
                 `S:real^1->bool`; `x:real^1`] VECTOR_DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC[o_DEF; DROP_VEC; VECTOR_MUL_LID] THEN BETA_TAC THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P3N_HVD_TRANSLATE_EQ = prove
 (`!(F1:real^1->real^N) v x c S.
     ((\u. F1(c + u)) has_vector_derivative v) (at x within S) <=>
     (F1 has_vector_derivative v) (at (c + x) within (IMAGE (\u. c + u) S))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[P3N_HVD_TRANSLATE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\u:real^1. (F1:real^1->real^N) (c + u)`; `v:real^N`; `c + x:real^1`;
                 `--c:real^1`; `IMAGE (\u:real^1. c + u) S`] P3N_HVD_TRANSLATE) THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_ARITH `c + --c + u:real^N = u`;
                            VECTOR_ARITH `--c + c + x:real^N = x`] THEN
  REWRITE_TAC[ETA_AX; GSYM IMAGE_o; o_DEF] THEN BETA_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `--c + c + u:real^N = u`; IMAGE_ID] THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* the speed of a curve shifted in the parameter *)

let P3N_SPEED_SHIFT = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (gamma:real->A) a b c t.
     mfd_speed atlas g (\s. gamma(c + s)) a b t =
     mfd_speed atlas g gamma (c + a) (c + b) (c + t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_speed; mfd_velocity] THEN BETA_TAC THEN
  ABBREV_TAC `ch = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((gamma:real->A) (c + t))` THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (ch:(A->bool)#(A->real^3)) ((gamma:real->A) (c + drop s)))
                      (at (lift t) within interval[lift a,lift b]) =
    vector_derivative (\s. SND ch (gamma (drop s)))
                      (at (lift (c + t)) within interval[lift (c + a),lift (c + b)])`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[vector_derivative] THEN AP_TERM_TAC THEN ABS_TAC THEN
  MP_TAC(ISPECL [`\s. SND (ch:(A->bool)#(A->real^3)) ((gamma:real->A) (drop s))`; `f':real^3`;
                 `lift t`; `lift c`; `interval[lift a,lift b]`] P3N_HVD_TRANSLATE_EQ) THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION; GSYM LIFT_ADD] THEN BETA_TAC THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP]);;

(* ========================================================================= *)
(* Integrals under a translation of the variable, and the                   *)
(* energy of a shifted space-time curve.                                    *)
(* ========================================================================= *)

let P3N_INTEGRAL_SHIFT = prove
 (`!(f:real->real) i a b.
     (f has_real_integral i) (real_interval[a,b])
     ==> ((\x. f(a + x)) has_real_integral i) (real_interval[&0,b - a])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `i:real`; `a:real`; `b:real`; `&1`; `a:real`]
                HAS_REAL_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; REAL_ABS_1; REAL_INV_1; REAL_MUL_LID] THEN
  SUBGOAL_THEN `IMAGE (\x. x - a) (real_interval[a,b]) = real_interval[&0,b - a]`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real` THEN STRIP_TAC THEN EXISTS_TAC `y + a` THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P3N_INTEGRAL_SHIFT_EQ = prove
 (`!(f:real->real) a b.
     f real_integrable_on real_interval[a,b]
     ==> (\x. f(a + x)) real_integrable_on real_interval[&0,b - a] /\
         real_integral (real_interval[&0,b - a]) (\x. f(a + x)) =
         real_integral (real_interval[a,b]) f`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_INTEGRABLE_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o MATCH_MP P3N_INTEGRAL_SHIFT) THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[real_integrable_on] THEN
    EXISTS_TAC `real_integral (real_interval[a,b]) (f:real->real)` THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* the energy integrand of a shifted curve is the shifted integrand of the  *)
(* curve on [a1,b1] *)

let P3N_ENERGY_INTEGRAND_SHIFT = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) a1 b1.
     (\tau. mfd_scalar (rfs_atlas_at hs ((tt - a1) - tau)) (rfs_metric_at hs ((tt - a1) - tau))
                       ((\s. gamma(a1 + s)) tau) +
            mfd_speed (rfs_atlas_at hs ((tt - a1) - tau)) (rfs_metric_at hs ((tt - a1) - tau))
                      (\s. gamma(a1 + s)) (&0) (b1 - a1) tau pow 2) =
     (\x. (\tau. mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                            (gamma tau) +
                 mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           gamma a1 b1 tau pow 2) (a1 + x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN BETA_TAC THEN
  REWRITE_TAC[P3N_SPEED_SHIFT; REAL_ADD_RID; REAL_ARITH `a1 + (b1 - a1) = b1`;
              REAL_ARITH `(tt - a1) - t = tt - (a1 + t)`]);;

(* ========================================================================= *)
(* The first exit of a space-time curve from an evolving cap                *)
(* region (Lemma 16.15 part (2)).  Images of compact sets under a           *)
(* parametrization are closed, of open sets open (P3N_PARAM_IMAGE_TOP); a   *)
(* curve in Phi(Kc) at backward time tau1 that is outside it at tauq leaves  *)
(* it at some tau2 in (tauq,tau1] through the top time ts + th0 h^2 or     *)
(* through Phi(Kc DIFF Ka) (P3N_CAP_EXIT).                                  *)
(* ========================================================================= *)

let P3N_PARAM_IMAGE_TOP = prove
 (`!top atlas (Wc:real^3->bool) (Phi:real^3->A) Kc Ka.
     smooth_manifold_atlas top atlas /\ hausdorff_space top /\ mfd_param top atlas Wc Phi /\
     compact Kc /\ Kc SUBSET Wc /\ open Ka /\ Ka SUBSET Wc
     ==> closed_in top (IMAGE Phi Kc) /\ open_in top (IMAGE Phi Ka)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `Wc:real^3->bool`; `Phi:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (Wc:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `IMAGE (Phi:real^3->A) Wc` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e':A->real^3`; `subtopology top (IMAGE (Phi:real^3->A) Wc)`;
                 `subtopology euclidean (Wc:real^3->bool)`; `Ka:real^3->bool`]
                OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `Ka:real^3->bool` THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN Wc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]]);;

let P3N_CAP_EXIT = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) b0 (Phi:real^3->A) Wc Kc Ka Ks ts h th0 Te
    tauq tau1.
     rfs_history_ok hs /\ rfs_st_curve hs tt gamma (&0) b0 /\
     &0 <= tauq /\ tauq < tau1 /\ tau1 <= b0 /\
     compact Kc /\ open Ka /\ Ks SUBSET Kc /\ Ka SUBSET Kc /\ Kc SUBSET Wc /\
     (!t. ts <= t /\ t < Te ==> mfd_param (rfs_top_at hs t) (rfs_atlas_at hs t) Wc Phi) /\
     (ts + th0 * h pow 2 < Te \/ tt < Te \/
      DISJOINT (IMAGE Phi Wc) (topspace(rfs_top_at hs Te))) /\
     (ts <= tt - tauq /\ tt - tauq < Te ==> ~(gamma tauq IN IMAGE Phi Kc)) /\
     gamma tau1 IN IMAGE Phi Ks /\ ts <= tt - tau1 /\ tt - tau1 <= ts + th0 * h pow 2 /\
     tt - tau1 < Te
     ==> ?t2. tauq < t2 /\ t2 <= tau1 /\ tt - t2 <= ts + th0 * h pow 2 /\ tt - t2 < Te /\
              (!s. t2 <= s /\ s <= tau1 ==> gamma s IN IMAGE Phi Kc) /\
              (tt - t2 = ts + th0 * h pow 2 \/ gamma t2 IN IMAGE Phi (Kc DIFF Ka))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[rfs_st_curve] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_st_curve"
    with Failure _ -> false)) THEN
  ABBREV_TAC `TT = ts + th0 * h pow 2` THEN
  SUBGOAL_THEN `!t. ts <= t /\ t < Te
                    ==> closed_in (rfs_top_at (hs:(A)rfs_history) t) (IMAGE (Phi:real^3->A) Kc) /\
                        open_in (rfs_top_at hs t) (IMAGE Phi Ka)`
  (LABEL_TAC "topo") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P3N_PARAM_IMAGE_TOP THEN
    EXISTS_TAC `rfs_atlas_at (hs:(A)rfs_history) t` THEN EXISTS_TAC `Wc:real^3->bool` THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] P3_HIST_VIEW_SLICES) THEN
      ASM_REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas] THEN SIMP_TAC[];
      MP_TAC(ISPEC `hs:(A)rfs_history` P2AB_SVS) THEN ASM_REWRITE_TAC[p2a_svs] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `t:real`) THEN REWRITE_TAC[rfs_view; p2a_vtop];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `E = {u | tauq <= u /\ u <= tau1 /\
                       !s. u <= s /\ s <= tau1
                           ==> tt - s <= TT /\ tt - s < Te /\
                               (gamma:real->A) s IN IMAGE (Phi:real^3->A) Kc}` THEN
  SUBGOAL_THEN `(tau1:real) IN E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `s:real = tau1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `E:real->bool` INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `tau1:real` THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `tauq:real` THEN EXPAND_TAC "E" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `t2 = inf E` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lb") (LABEL_TAC "glb")) THEN
  SUBGOAL_THEN `tauq <= t2 /\ t2 <= tau1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "glb" MATCH_MP_TAC THEN EXPAND_TAC "E" THEN SIMP_TAC[IN_ELIM_THM];
      USE_THEN "lb" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. t2 < s /\ s <= tau1
                    ==> tt - s <= TT /\ tt - s < Te /\
                        (gamma:real->A) s IN IMAGE (Phi:real^3->A) Kc`
  (LABEL_TAC "above") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?u. u IN E /\ u < s` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `s <= t2` MP_TAC THENL
       [USE_THEN "glb" MATCH_MP_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(u:real) IN E` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the limits at t2 *)
  SUBGOAL_THEN `tt - t2 <= TT` ASSUME_TAC THENL
   [ASM_CASES_TAC `t2:real = tau1` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "above" (MP_TAC o SPEC `t2 + min (tt - t2 - TT) (tau1 - t2) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tt - t2 < Te` ASSUME_TAC THENL
   [ASM_CASES_TAC `t2:real = tau1` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `tt - t2 <= Te` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "above" (MP_TAC o SPEC `t2 + min (tt - t2 - Te) (tau1 - t2) / &2`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `tt - t2 = Te` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_disj(concl th))) THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t2:real`; `topspace(rfs_top_at (hs:(A)rfs_history) Te)`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `tt - t2 = Te` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "above" (MP_TAC o SPEC `t2 + min d (tau1 - t2) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t2 + min d (tau1 - t2) / &2` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts <= tt - t2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t2 IN IMAGE (Phi:real^3->A) Kc` ASSUME_TAC THENL
   [ASM_CASES_TAC `t2:real = tau1` THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "topo" (MP_TAC o SPEC `tt - t2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[closed_in] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t2:real`;
      `topspace(rfs_top_at (hs:(A)rfs_history) (tt - t2)) DIFF IMAGE (Phi:real^3->A) Kc`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
            (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "above" (MP_TAC o SPEC `t2 + min d (tau1 - t2) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t2 + min d (tau1 - t2) / &2` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tauq < t2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b /\ ~(b = a) ==> a < b`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term (fun t -> t = `tauq:real`)) (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `t2:real = tauq` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
                    ASM_REWRITE_TAC[];
                    ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `t2:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s:real = t2` THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "above" (MP_TAC o SPEC `s:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `tt - t2 = TT` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t2 IN IMAGE (Phi:real^3->A) Ka` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "topo" (MP_TAC o SPEC `tt - t2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t2:real`; `IMAGE (Phi:real^3->A) Ka`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "open_in" with Failure _ -> false))
          (concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `u = t2 - min d1 (min (TT - (tt - t2)) (min (Te - (tt - t2)) (t2 - tauq))) / &2` THEN
  SUBGOAL_THEN `(u:real) IN E` MP_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC;
                           EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t2 < s` THENL
     [USE_THEN "above" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(gamma:real->A) s IN IMAGE (Phi:real^3->A) Ka` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN USE_THEN "lb" (MP_TAC o C MP (ASSUME `(u:real) IN E`) o SPEC `u:real`) THEN
  EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* On a stretch [a1,b1] away from 0 where R >= 0, the energy                *)
(* integrand of the curve restricted to [a1,b1] is integrable and its       *)
(* integral is at most L+ / sqrt taup, taup <= a1.                          *)
(* ========================================================================= *)

let P3N_1615_ENERGY_LE = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) tau0 a1 b1 taup.
     &0 < taup /\ taup <= a1 /\ a1 < b1 /\ b1 <= tau0 /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     (!tau. a1 <= tau /\ tau <= b1
            ==> &0 <= mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                 (gamma tau))
     ==> (\tau. mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           (gamma tau) +
                mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                          gamma a1 b1 tau pow 2)
         real_integrable_on real_interval[a1,b1] /\
         real_integral (real_interval[a1,b1])
           (\tau. mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                             (gamma tau) +
                  mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                            gamma a1 b1 tau pow 2)
         <= real_integral (real_interval[&0,tau0])
              (\tau. sqrt tau *
                     (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau))
                                           (rfs_metric_at hs (tt - tau)) (gamma tau)) +
                      mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                gamma (&0) tau0 tau pow 2)) / sqrt taup`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  ABBREV_TAC `L = \tau. sqrt tau *
                (max (&0) (mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                      (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)) +
                 mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           gamma (&0) tau0 tau pow 2)` THEN
  ABBREV_TAC `E = \tau. mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                   (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau) +
                        mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  gamma a1 b1 tau pow 2` THEN
  SUBGOAL_THEN `!tau. tau IN real_interval[&0,tau0] ==> &0 <= (L:real->real) tau`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "L" THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tau. tau IN real_interval(a1,b1)
                      ==> (E:real->real) tau = inv(sqrt tau) * (L:real->real) tau`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["E"; "L"] THEN BETA_TAC THEN
    MP_TAC(ISPECL [`rfs_atlas_at (hs:(A)rfs_history) (tt - tau)`;
                   `rfs_metric_at (hs:(A)rfs_history) (tt - tau)`; `gamma:real->A`;
                   `a1:real`; `b1:real`; `&0`; `tau0:real`; `tau:real`] P2A_SPEED_INTERIOR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `max (&0) (mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                    (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)) =
                  mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau)) (gamma tau)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> max (&0) x = x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt tau` MP_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\tau. inv(sqrt tau) * (L:real->real) tau) real_integrable_on
                real_interval[a1,b1]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING_PRODUCT THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real->real) real_integrable_on real_interval[a1,b1] /\
                real_integral (real_interval[a1,b1]) E =
                real_integral (real_interval[a1,b1]) (\tau. inv(sqrt tau) * (L:real->real) tau)`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_ON_OPEN_INTERVAL;
                     GSYM REAL_INTEGRAL_OPEN_INTERVAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
      EXISTS_TAC `\tau. inv(sqrt tau) * (L:real->real) tau` THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_OPEN_INTERVAL] THEN BETA_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_INTEGRAL_EQ THEN BETA_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[a1,b1]) (\tau. inv(sqrt taup) * (L:real->real) tau)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[a1,b1]) (\tau. inv(sqrt taup) * (L:real->real) tau) =
                inv(sqrt taup) * real_integral (real_interval[a1,b1]) L` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P3N_INT_MONO THEN EXISTS_TAC `tau0:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Facts of the setting of Prop 16.4 used by Lemma 16.15:                  *)
(* canonical neighbourhoods at the radius r' below the horizon, and the     *)
(* surgery parameters r(t) <= eps and delta(t) <= dlt on [T(i-1),horizon).   *)
(* ========================================================================= *)

let P3N_1615_CANON = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt rs' ks' dd (hs:(A)rfs_history).
     p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs
     ==> !t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
               inv(r' pow 2) <= rfs_vscalar (rfs_view hs) t x
               ==> p3_canon_at (rfs_view hs) C eps x t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3_canon_at] THEN
  UNDISCH_TAC `rfs_canonical_assumption (rfs_view (hs:(A)rfs_history)) C eps (p3_stepf rs')` THEN
  REWRITE_TAC[rfs_view; rfs_canonical_assumption] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `inv(r' pow 2) <= rfs_vscalar (rfs_view (hs:(A)rfs_history)) t x` THEN
  REWRITE_TAC[rfs_view; rfs_vscalar] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    UNDISCH_TAC `rs' (SUC i) = (r':real)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[p3_seq_ok];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [UNDISCH_TAC `rs' (SUC i) = (r':real)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[p3_seq_ok; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `rs' (SUC i) = (r':real)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[p3_stepf] THEN
  MP_TAC(ISPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P3_STEP_LE THEN ASM_REAL_ARITH_TAC);;

let P3N_1615_PARAMS = prove
 (`!C eps hf md g0 A0 i rs ks ds r' dlt rs' ks' dd (hs:(A)rfs_history) t.
     1 <= i /\ rs 0 = eps /\
     p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\
     p3_T (i - 1) <= t /\ t < rfs_horizon hs
     ==> p3_stepf dd t <= dlt /\ p3_stepf rs' t <= eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i <= p3_step t /\ p3_step t <= SUC i` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`t:real`; `i - 1`] P3_STEP_GE) THEN ANTS_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC];
      MATCH_MP_TAC P3_STEP_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p3_stepf] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dd:num->real) i` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `dd:num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `(rs:num->real) 0 = eps` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(rs:num->real) 0 = rs' 0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `rs':num->real`)) (concl th) &&
        can (find_term (fun t -> t = `ks':num->real`)) (concl th))) THEN
      REWRITE_TAC[LE_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `rs':num->real` P3_SEQ_MONO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_0]]);;

(* ========================================================================= *)
(* The persistence end Te of the evolving cap region from the               *)
(* two cases of Prop 16.5 (with tc the horizon).                            *)
(* ========================================================================= *)

let P3N_1615_TE = prove
 (`!(hs:(A)rfs_history) k (Phi:real^3->A) ts h g0 A (G:real->real^3->real^3^3)
    th0 th1 dcl tt.
     rfs_history_ok hs /\ ts = hs_time hs k /\ ts < rfs_horizon hs /\ &0 < h /\
     &0 <= th0 /\ th0 < th1 /\ tt < rfs_horizon hs /\
     (p3_view_close
        (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
        (&0) (&1) {x | p3_std_dist g0 x < A} (rfs_view hs) ts (inv(h pow 2)) Phi
        {s | &0 <= s /\ s < th1 /\ ts + s * h pow 2 <= rfs_horizon hs /\
             ts + s * h pow 2 < rfs_horizon hs} dcl \/
      ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= rfs_horizon hs /\
           hs_time hs k' < ts + th1 * h pow 2 /\
           p3_view_close
             (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
             (&0) (&1) {x | p3_std_dist g0 x < A} (rfs_view hs) ts (inv(h pow 2)) Phi
             {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dcl /\
           DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A}) (topspace(hs_top hs k')))
     ==> ?J Te. p3_view_close
                  (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
                  (&0) (&1) {x | p3_std_dist g0 x < A} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
                ts < Te /\
                (!t. ts <= t /\ t < Te ==> (t - ts) / h pow 2 IN J /\ (t - ts) / h pow 2 < th1) /\
                (ts + th0 * h pow 2 < Te \/ tt < Te \/
                 DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A}) (topspace(rfs_top_at hs Te)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `th0 * h pow 2 < th1 * h pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= th0 * h pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. ts <= t ==> &0 <= (t - ts) / h pow 2 /\
                                ts + (t - ts) / h pow 2 * h pow 2 = t`
  (LABEL_TAC "sdef") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < h pow 2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t < ts + th1 * h pow 2 ==> (t - ts) / h pow 2 < th1` (LABEL_TAC "slt") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k':num` STRIP_ASSUME_TAC) o
    check (fun th -> is_disj(concl th))) THENL
   [MAP_EVERY EXISTS_TAC
     [`{s | &0 <= s /\ s < th1 /\ ts + s * h pow 2 <= rfs_horizon (hs:(A)rfs_history) /\
            ts + s * h pow 2 < rfs_horizon hs}`;
      `min (ts + th1 * h pow 2) (rfs_horizon (hs:(A)rfs_history))`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "sdef" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `(t - ts) / h pow 2 < th1` ASSUME_TAC THENL
       [USE_THEN "slt" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MAP_EVERY EXISTS_TAC
     [`{s | &0 <= s /\ ts + s * h pow 2 < hs_time (hs:(A)rfs_history) k'}`;
      `hs_time (hs:(A)rfs_history) k'`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `ts = hs_time (hs:(A)rfs_history) k` THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "sdef" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `(t - ts) / h pow 2 < th1` ASSUME_TAC THENL
       [USE_THEN "slt" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN DISJ2_TAC THEN
      MP_TAC(ISPECL [`hs:(A)rfs_history`; `k':num`; `hs_time (hs:(A)rfs_history) k'`]
                    APX_RFS_SLAB) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
        DISCH_THEN(MP_TAC o SPEC `k':num` o CONJUNCT1 o CONJUNCT2) THEN ASM_SIMP_TAC[];
        SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* A point of the curve in B(x,tt,r/2) at a time of the                    *)
(* closeness set of a surgery cap is not in the evolving cap region         *)
(* Phi{d < A'} (the scalar curvature separation, MT p. 381).                *)
(* ========================================================================= *)

let P3N_1615_SEPPT = prove
 (`!c dl0 (hs:(A)rfs_history) tt x r (gamma:real->A) sig (Phi:real^3->A) ts h g0 A0 A'
    (G:real->real^3->real^3^3) J dcl y.
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t x. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) x) /\
     (!t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) x u v) /\
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\ &0 < A' /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A'} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     (tt - sig - ts) / h pow 2 IN J /\ &0 <= (tt - sig - ts) / h pow 2 /\
     (tt - sig - ts) / h pow 2 < &1 /\ &0 < h /\ &0 < dcl /\ dcl <= dl0 /\
     &0 < r /\ h pow 2 * &12 < c * r pow 2 /\ &0 <= sig /\ sig < r pow 2 /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
            ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
     gamma sig IN rfs_vball (rfs_view hs) tt x (r / &2) /\
     gamma sig IN topspace(rfs_top_at hs (tt - sig)) /\
     y IN {x | p3_std_dist g0 x < A'} /\ gamma sig = Phi y
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  ABBREV_TAC `s = (tt - sig - ts) / h pow 2` THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `ts + s * h pow 2 = tt - sig` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN UNDISCH_TAC `&0 < h pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts + s * h pow 2`] P3_HIST_VIEW_SLICES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < A'}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A':real`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                 `h:real`; `G:real->real^3->real^3^3`; `g0:real^3->real^3^3`;
                 `{x:real^3 | p3_std_dist g0 x < A'}`; `J:real->bool`; `dcl:real`;
                 `s:real`; `y:real^3`] P3N_1613_RBOUND) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `ts + s * h pow 2 = tt - sig`; rfs_view; rfs_vatlas; rfs_vmetric] THEN
  REWRITE_TAC[SYM(ASSUME `(gamma:real->A) sig = (Phi:real^3->A) y`)] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p3_vrm (rfs_view (hs:(A)rfs_history)) (tt - sig) ((gamma:real->A) sig)
                <= inv(r pow 2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(gamma:real->A) sig IN rfs_vball (rfs_view (hs:(A)rfs_history)) tt x (r / &2)` THEN
    REWRITE_TAC[rfs_vball; rfs_view; mfd_ball; IN_ELIM_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) (tt - sig)`;
                 `rfs_atlas_at (hs:(A)rfs_history) (tt - sig)`;
                 `rfs_metric_at (hs:(A)rfs_history) (tt - sig)`; `(gamma:real->A) sig`]
                P3N_SCALAR_LE_RM) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ts + s * h pow 2 = tt - sig`; rfs_view; rfs_vtop;
                                rfs_vatlas; rfs_vmetric]) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `p3_vrm (rfs_view (hs:(A)rfs_history)) (tt - sig) ((gamma:real->A) sig)
               <= inv(r pow 2)` THEN
  REWRITE_TAC[p3_vrm; rfs_view; rfs_vatlas; rfs_vmetric] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `h:real`; `r:real`; `s:real`;
                `mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - sig))
                            (rfs_metric_at hs (tt - sig)) ((gamma:real->A) sig)`] P3N_1615_SEP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* ========================================================================= *)
(* The late case of Lemma 16.15(2) (MT p. 381): a curve that               *)
(* stays in the cap region Phi{d <= A} on [t2,tau1], enters it from the top *)
(* or the side at t2 > taup and reaches Phi{d < A/2} at tau1 has, by Prop   *)
(* 16.13 applied to the shifted curve, energy > ell = L0 / sqrt taup, while *)
(* its energy is at most L+ / sqrt taup < ell.                              *)
(* ========================================================================= *)

let P3N_1615_LATE = prove
 (`!(hs:(A)rfs_history) tt (gamma:real->A) tau0 (Phi:real^3->A) ts h g0 A th0 ell L0 taup
    t2 tau1.
     (!Tp tq (gm:real->A).
        Tp <= ts + th0 * h pow 2 /\
        (!s. ts <= s /\ s <= Tp
             ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET topspace(rfs_top_at hs s)) /\
        ts <= tq /\ tq <= ts + h pow 2 / &2 /\ tq <= Tp /\
        rfs_st_curve hs Tp gm (&0) (Tp - tq) /\
        (!tau. &0 <= tau /\ tau <= Tp - tq
               ==> gm tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
        (Tp = ts + th0 * h pow 2 \/ gm (&0) IN IMAGE Phi {x | p3_std_dist g0 x = A}) /\
        gm (Tp - tq) IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
        (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau)) (gm tau) +
               mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                         gm (&0) (Tp - tq) tau pow 2)
        real_integrable_on real_interval[&0,Tp - tq]
        ==> ell < p3_energy hs Tp gm (Tp - tq)) /\
     rfs_st_curve hs tt gamma (&0) tau0 /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     p3_Lplus hs tt gamma tau0 < L0 /\ L0 = ell * sqrt taup /\ &0 < taup /\ &0 < ell /\
     taup < t2 /\ t2 <= tau1 /\ tau1 <= tau0 /\
     tt - t2 <= ts + th0 * h pow 2 /\
     (!s. t2 <= s /\ s <= tau1 ==> gamma s IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
     (tt - t2 = ts + th0 * h pow 2 \/
      gamma t2 IN IMAGE Phi ({x | p3_std_dist g0 x <= A} DIFF {x | p3_std_dist g0 x < A})) /\
     (!s. ts <= s /\ s <= tt - t2
          ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET topspace(rfs_top_at hs s)) /\
     ts <= tt - tau1 /\ tt - tau1 <= ts + h pow 2 / &2 /\
     gamma tau1 IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
     (!tau. t2 <= tau /\ tau <= tau1
            ==> &0 <= mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                 (gamma tau))
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h13") MP_TAC) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 <= t2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `tau0:real`; `t2:real`;
                 `tau1:real`] P3N_ST_CURVE_SHIFT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the energy of the shifted curve is below ell *)
  SUBGOAL_THEN
   `(\tau. mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) ((tt - t2) - tau))
                      (rfs_metric_at hs ((tt - t2) - tau)) ((\s. (gamma:real->A)(t2 + s)) tau) +
           mfd_speed (rfs_atlas_at hs ((tt - t2) - tau)) (rfs_metric_at hs ((tt - t2) - tau))
                     (\s. gamma(t2 + s)) (&0) (tau1 - t2) tau pow 2)
    real_integrable_on real_interval[&0,tau1 - t2] /\
    p3_energy hs (tt - t2) (\s. gamma(t2 + s)) (tau1 - t2) < ell`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `t2:real = tau1` THENL
     [SUBGOAL_THEN `tau1 - t2 = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[p3_energy; REAL_INTEGRAL_REFL; REAL_INTEGRABLE_ON_REFL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t2 < tau1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `tau0:real`; `t2:real`;
                   `tau1:real`; `taup:real`] P3N_1615_ENERGY_LE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "ebd" o REWRITE_RULE[GSYM p3_Lplus])) THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `t2:real`; `tau1:real`]
                  P3N_ENERGY_INTEGRAND_SHIFT) THEN
    DISCH_THEN(fun eq -> PURE_REWRITE_TAC[p3_energy] THEN SUBST1_TAC eq) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P3N_INTEGRAL_SHIFT_EQ) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `p3_Lplus (hs:(A)rfs_history) tt gamma tau0 / sqrt taup` THEN CONJ_TAC THENL
     [USE_THEN "ebd" ACCEPT_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Prop 16.13 for the shifted curve *)
  USE_THEN "h13" (MP_TAC o SPECL [`tt - t2`; `tt - tau1`; `\s. (gamma:real->A)(t2 + s)`]) THEN
  PURE_REWRITE_TAC[REAL_ARITH `(tt - t2) - (tt - tau1) = tau1 - t2`] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `tau:real` THEN STRIP_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `tau1:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "IMAGE" with Failure _ -> false))
            (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      BETA_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
      SUBGOAL_THEN `{x:real^3 | p3_std_dist g0 x = A} =
                    {x | p3_std_dist g0 x <= A} DIFF {x | p3_std_dist g0 x < A}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      BETA_TAC THEN REWRITE_TAC[REAL_ARITH `t2 + (tau1 - t2) = tau1`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Lemma 16.15(2) for one surgery cap (MT p. 381): the                     *)
(* region of the cap is parametrised by Phi on [ts,Te) (Prop 16.5), the     *)
(* scalar curvature is positive there, and a curve point in the small cap  *)
(* region Phi{d < A0 + 50} at a time of [ts,tp] gives a contradiction:      *)
(* before taup by the separation from the parabolic ball, after taup by     *)
(* the first exit (P3N_CAP_EXIT) and the late case (P3N_1615_LATE).         *)
(* ========================================================================= *)

let P3N_1615_MPARAM = prove
 (`!(hs:(A)rfs_history) (Phi:real^3->A) ts h (G:real->real^3->real^3^3) W J dcl Te th1.
     &0 < h /\ th1 <= &1 /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) W (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     (!t. ts <= t /\ t < Te ==> (t - ts) / h pow 2 IN J /\ (t - ts) / h pow 2 < th1)
     ==> !t. ts <= t /\ t < Te ==> mfd_param (rfs_top_at hs t) (rfs_atlas_at hs t) W Phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `th1:real`)) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `inv(h pow 2)`;
                 `G:real->real^3->real^3^3`; `W:real^3->bool`; `J:real->bool`; `dcl:real`;
                 `(t - ts) / h pow 2`] P3N_VIEW_CLOSE_ELIM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts + (t - ts) / h pow 2 / inv(h pow 2) = t` SUBST1_TAC THENL
   [MP_TAC(ASSUME `&0 < h pow 2`) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[mfd_param; rfs_view; rfs_vtop; rfs_vatlas] THEN MESON_TAC[]);;

let P3N_1615_RPOS = prove
 (`!c dl0 (hs:(A)rfs_history) (Phi:real^3->A) ts h (G:real->real^3->real^3^3) g0 A0 A' J dcl
    Te th1 t y.
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t x. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) x) /\
     (!t x u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) x u v) /\
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\ &0 < A' /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {x | p3_std_dist g0 x < A'} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     &0 < h /\ &0 < dcl /\ dcl <= dl0 /\ th1 <= &1 /\
     (!t. ts <= t /\ t < Te ==> (t - ts) / h pow 2 IN J /\ (t - ts) / h pow 2 < th1) /\
     ts <= t /\ t < Te /\ p3_std_dist g0 y < A'
     ==> &0 < mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) (Phi y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `th1:real`)) (concl th))) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= (t - ts) / h pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ts + (t - ts) / h pow 2 * h pow 2 = t` ASSUME_TAC THENL
   [MP_TAC(ASSUME `&0 < h pow 2`) THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `s = (t - ts) / h pow 2` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `ts + s * h pow 2`] P3_HIST_VIEW_SLICES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | p3_std_dist g0 x < A'}` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A':real`] P3N_STD_BALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`;
                 `h:real`; `G:real->real^3->real^3^3`; `g0:real^3->real^3^3`;
                 `{x:real^3 | p3_std_dist g0 x < A'}`; `J:real->bool`; `dcl:real`;
                 `s:real`; `y:real^3`] P3N_1613_RBOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(REWRITE_TAC[IN_ELIM_THM] THEN FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `ts + s * h pow 2 = t`; rfs_view; rfs_vatlas; rfs_vmetric] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= b ==> &0 < b`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let P3N_1615_CAP = prove
 (`!c dl0 (hs:(A)rfs_history) tt x r (gamma:real->A) tau0 (Phi:real^3->A) ts h g0 A0 A
    (G:real->real^3->real^3^3) J dcl Te th0 th1 ell L0 taup tp tau1.
     (!Tp tq (gm:real->A).
        Tp <= ts + th0 * h pow 2 /\
        (!s. ts <= s /\ s <= Tp
             ==> IMAGE Phi {z | p3_std_dist g0 z <= A} SUBSET topspace(rfs_top_at hs s)) /\
        ts <= tq /\ tq <= ts + h pow 2 / &2 /\ tq <= Tp /\
        rfs_st_curve hs Tp gm (&0) (Tp - tq) /\
        (!tau. &0 <= tau /\ tau <= Tp - tq
               ==> gm tau IN IMAGE Phi {z | p3_std_dist g0 z <= A}) /\
        (Tp = ts + th0 * h pow 2 \/ gm (&0) IN IMAGE Phi {z | p3_std_dist g0 z = A}) /\
        gm (Tp - tq) IN IMAGE Phi {z | p3_std_dist g0 z < A / &2} /\
        (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau)) (gm tau) +
               mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                         gm (&0) (Tp - tq) tau pow 2)
        real_integrable_on real_interval[&0,Tp - tq]
        ==> ell < p3_energy hs Tp gm (Tp - tq)) /\
     (!(G0:real^3->real^3^3) H V z dl.
        metric_field V G0 /\ metric_field V H /\ z IN V /\ c <= lscalar G0 z /\
        (!u v. ~collinear {vec 0,u,v} ==> &0 <= lsectional G0 z u v) /\
        &0 < dl /\ dl <= dl0 /\ lck_dist2 (rfs_kreg dl) G0 H z < dl pow 2
        ==> lscalar G0 z / &2 <= lscalar H z) /\
     &0 < c /\ p3_std_flow g0 (&1) G /\
     (!t y. &0 <= t /\ t < &1 ==> c / (&1 - t) <= lscalar (G t) y) /\
     (!t y u v. &0 <= t /\ t < &1 /\ ~collinear {vec 0,u,v}
                ==> &0 <= lsectional (G t) y u v) /\
     rfs_history_ok hs /\ p3_std_initial g0 A0 /\
     p3_view_close
       (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
       (&0) (&1) {z | p3_std_dist g0 z < A + &1} (rfs_view hs) ts (inv(h pow 2)) Phi J dcl /\
     ts < Te /\
     (!t. ts <= t /\ t < Te ==> (t - ts) / h pow 2 IN J /\ (t - ts) / h pow 2 < th1) /\
     (ts + th0 * h pow 2 < Te \/ tt < Te \/
      DISJOINT (IMAGE Phi {z | p3_std_dist g0 z < A + &1}) (topspace(rfs_top_at hs Te))) /\
     &0 < h /\ &0 < dcl /\ dcl <= dl0 /\ &1 / &2 <= th0 /\ th0 < th1 /\ th1 <= &1 /\
     &0 < A /\ &2 * (A0 + &50) < A /\
     &0 < r /\ h pow 2 * &12 < c * r pow 2 /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
            ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
     rfs_st_curve hs tt gamma (&0) tau0 /\
     (!tau. &0 <= tau /\ tau <= min taup tau0
            ==> gamma tau IN rfs_vball (rfs_view hs) tt x (r / &2)) /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     p3_Lplus hs tt gamma tau0 < L0 /\ L0 = ell * sqrt taup /\
     &0 < taup /\ taup < r pow 2 /\ &0 < ell /\
     ts <= tt - tau1 /\ tt - tau1 <= tp /\ tp <= ts + h pow 2 / &2 /\
     (!s. ts <= s /\ s <= tp
          ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET topspace(rfs_top_at hs s)) /\
     &0 <= tau1 /\ tau1 <= tau0 /\
     gamma tau1 IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50}
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h13") MP_TAC) THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 < h pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `h pow 2 / &2 <= th0 * h pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (th0 - &1 / &2) * x ==> x / &2 <= th0 * x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_dist g0 (vec 0:real^3) = &0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the sets *)
  SUBGOAL_THEN `{z:real^3 | p3_std_dist g0 z < A0 + &50} SUBSET {z | p3_std_dist g0 z <= A} /\
                {z:real^3 | p3_std_dist g0 z < A0 + &50} SUBSET {z | p3_std_dist g0 z < A / &2} /\
                {z:real^3 | p3_std_dist g0 z < A} SUBSET {z | p3_std_dist g0 z <= A} /\
                {z:real^3 | p3_std_dist g0 z <= A} SUBSET {z | p3_std_dist g0 z < A + &1}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact {z:real^3 | p3_std_dist g0 z <= A} /\
                open {z:real^3 | p3_std_dist g0 z < A}` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A:real`] P3N_STD_SUBLEVEL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    ALL_TAC] THEN
  (* the parametrisation of the cap region on [ts,Te) *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `Phi:real^3->A`; `ts:real`; `h:real`;
                 `G:real->real^3->real^3^3`; `{z:real^3 | p3_std_dist g0 z < A + &1}`;
                 `J:real->bool`; `dcl:real`; `Te:real`; `th1:real`] P3N_1615_MPARAM) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  (* the curve point at tau1 is below the horizon Te of the closeness *)
  SUBGOAL_THEN `tt - tau1 < Te` ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term (fun t -> t = `Te:real`)) (concl th))) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Te:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `tp:real`)) (concl th) &&
      can (find_term (fun t -> t = `A0 + &50`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(vec 0:real^3) IN {z | p3_std_dist g0 z < A0 + &50} /\
                  (vec 0:real^3) IN {z | p3_std_dist g0 z < A + &1}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (IMAGE (Phi:real^3->A) {z | p3_std_dist g0 z < A + &1})
                          (topspace(rfs_top_at (hs:(A)rfs_history) Te))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the closeness facts at the curve times *)
  SUBGOAL_THEN `!sig. ts <= tt - sig /\ tt - sig < Te
                      ==> (tt - sig - ts) / h pow 2 IN J /\ &0 <= (tt - sig - ts) / h pow 2 /\
                          (tt - sig - ts) / h pow 2 < &1`
  (LABEL_TAC "cl") THENL
   [X_GEN_TAC `sig:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `tt - sig:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `th1:real`)) (concl th))) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* no curve point in the cap region near the parabolic ball *)
  SUBGOAL_THEN `!sig y. &0 <= sig /\ sig <= min taup tau0 /\
                        ts <= tt - sig /\ tt - sig < Te /\
                        y IN {z | p3_std_dist g0 z < A + &1} /\ (gamma:real->A) sig = Phi y
                        ==> F`
  (LABEL_TAC "sep") THENL
   [MAP_EVERY X_GEN_TAC [`sig:real`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "cl" (MP_TAC o SPEC `sig:real`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`;
                   `gamma:real->A`; `sig:real`; `Phi:real^3->A`; `ts:real`; `h:real`;
                   `g0:real^3->real^3^3`; `A0:real`; `A + &1`; `G:real->real^3->real^3^3`;
                   `J:real->bool`; `dcl:real`; `y:real^3`] P3N_1615_SEPPT) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(ASSUME `sig <= min taup tau0`) THEN REWRITE_TAC[REAL_LE_MIN] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `r / &2`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `rfs_st_curve (hs:(A)rfs_history) tt (gamma:real->A) (&0) tau0` THEN
      REWRITE_TAC[rfs_st_curve] THEN
      DISCH_THEN(MP_TAC o SPEC `sig:real` o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL
       [MP_TAC(ASSUME `sig <= min taup tau0`) THEN REWRITE_TAC[REAL_LE_MIN] THEN
        ASM_REAL_ARITH_TAC;
        SIMP_TAC[]]];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> can (find_term (fun t -> t = `tau1:real`)) (concl th) &&
                     can (find_term (fun t -> t = `A0 + &50`)) (concl th) &&
                     not (is_forall(concl th)))) THEN
  ASM_CASES_TAC `tau1 <= taup` THENL
   [(* early case: separation *)
    USE_THEN "sep" (MATCH_MP_TAC o SPECL [`tau1:real`; `y1:real^3`]) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REWRITE_TAC[REAL_LE_MIN];
      UNDISCH_TAC `(y1:real^3) IN {z | p3_std_dist g0 z < A0 + &50}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* late case: first exit after taup, then Prop 16.13 *)
  SUBGOAL_THEN `taup < tau1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `tau0:real`;
                 `Phi:real^3->A`; `{z:real^3 | p3_std_dist g0 z < A + &1}`;
                 `{z:real^3 | p3_std_dist g0 z <= A}`; `{z:real^3 | p3_std_dist g0 z < A}`;
                 `{z:real^3 | p3_std_dist g0 z < A0 + &50}`; `ts:real`; `h:real`; `th0:real`;
                 `Te:real`; `taup:real`; `tau1:real`] P3N_CAP_EXIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
     (STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "sep" (MATCH_MP_TAC o SPECL [`taup:real`; `y2:real^3`]) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(y2:real^3) IN {z | p3_std_dist g0 z <= A}` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real` (fun th -> let cs = CONJUNCTS th in
                                               MAP_EVERY ASSUME_TAC cs)) THEN
  MATCH_MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `gamma:real->A`; `tau0:real`;
                 `Phi:real^3->A`; `ts:real`; `h:real`; `g0:real^3->real^3^3`; `A:real`;
                 `th0:real`; `ell:real`; `L0:real`; `taup:real`; `t2:real`; `tau1:real`]
                P3N_1615_LATE) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
   [(* the region Phi{d <= A} persists up to tt - t2 *)
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_param" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] P3_HIST_VIEW_SLICES) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_top_at (hs:(A)rfs_history) s`; `rfs_atlas_at (hs:(A)rfs_history) s`;
                   `{z:real^3 | p3_std_dist g0 z < A + &1}`; `Phi:real^3->A`]
                  GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (Phi:real^3->A) {z | p3_std_dist g0 z < A + &1}` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    (* gamma tau1 in Phi{d < A/2} *)
    MATCH_MP_TAC(SET_RULE `!f (s:real^3->bool) t (y:A).
                             y IN IMAGE f s /\ s SUBSET t ==> y IN IMAGE f t`) THEN
    EXISTS_TAC `{z:real^3 | p3_std_dist g0 z < A0 + &50}` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    (* positive scalar curvature on the cap region *)
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `t2:real`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "IMAGE" with Failure _ -> false))
          (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y3:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC P3N_1615_RPOS THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `dl0:real`; `ts:real`; `h:real`;
                          `G:real->real^3->real^3^3`; `g0:real^3->real^3^3`; `A0:real`;
                          `A + &1`; `J:real->bool`; `dcl:real`; `Te:real`; `th1:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The arithmetic of Lemma 16.15 and its part (1) in the                   *)
(* setting of the statement: with taup = min (r'^4/(1024 L0^2)) (r'^2/8)    *)
(* and lam = 4 L0 / r, the majorant integral of P3N_PAR_BALL is below r/2;  *)
(* h = hf(dl rho, dl) with dl <= dlt small has 12 h^2 < c r^2.              *)
(* ========================================================================= *)

let P3N_1615_ARITH1 = prove
 (`!r r' L0 b Ib.
     &0 < r' /\ r' <= r /\ &0 < L0 /\ &0 <= b /\ b <= r' pow 4 / (&1024 * L0 pow 2) /\
     Ib < L0
     ==> &2 * (&4 * L0 / r) * sqrt b + Ib / (&4 * L0 / r) < r / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * L0 / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r' pow 2 <= r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b <= r' pow 2 / (&32 * L0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((r' pow 2 / (&32 * L0)) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r' pow 4 / (&1024 * L0 pow 2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < L0` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (&4 * L0 / r) * sqrt b <= r / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&4 * L0 / r) * (r' pow 2 / (&32 * L0))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 * (&4 * L0 / r) * (r' pow 2 / (&32 * L0)) = r' pow 2 / (&4 * r)`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < L0`; `&0 < r`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < r ==> &0 < &4 * r`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Ib / (&4 * L0 / r) < r / &4` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `r / &4 * &4 * L0 / r = L0` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3N_1615_HSMALL = prove
 (`!C hf rho dl eps c r' r dlt.
     p3_hfun C hf /\ &0 < rho /\ &0 < dl /\ dl <= dlt /\ dlt <= &1 /\
     dlt <= c * r' pow 2 / (&13 * (eps pow 2 + &1)) /\ rho <= eps /\ &0 < c /\
     &0 < r' /\ r' <= r
     ==> hf (dl * rho) dl pow 2 * &12 < c * r pow 2`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `p3_hfun C (hf:real->real->real)` THEN REWRITE_TAC[p3_hfun] THEN
  DISCH_THEN(MP_TAC o SPECL [`dl * rho:real`; `dl:real`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; STRIP_TAC] THEN
  ABBREV_TAC `h = (hf:real->real->real) (dl * rho) dl` THEN
  SUBGOAL_THEN `h <= eps * dlt` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(dl * rho) * dl` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * rho` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h pow 2 <= eps pow 2 * dlt` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps * dlt) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps pow 2 * dlt <= eps pow 2 * (c * r' pow 2 / (&13 * (eps pow 2 + &1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&12 * (eps pow 2 * (c * r' pow 2 / (&13 * (eps pow 2 + &1)))) <
                c * r' pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < c * r' pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= eps pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&12 * (eps pow 2 * (c * r' pow 2 / (&13 * (eps pow 2 + &1)))) =
                  (c * r' pow 2) * ((&12 * eps pow 2) / (&13 * (eps pow 2 + &1)))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 <= eps pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= e ==> &0 < &13 * (e + &1)`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * r' pow 2 <= c * r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3N_1615_PART1 = prove
 (`!(hs:(A)rfs_history) tt x r r' (gamma:real->A) tau0 L0 taup.
     rfs_history_ok hs /\ x IN topspace(rfs_top_at hs tt) /\ &0 < r' /\ r' <= r /\
     rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
     (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
            ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
     &0 < tau0 /\ rfs_st_curve hs tt gamma (&0) tau0 /\ gamma (&0) = x /\
     (\tau. sqrt tau *
            (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                  (gamma tau)) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) tau0 tau pow 2))
     real_integrable_on real_interval[&0,tau0] /\
     p3_Lplus hs tt gamma tau0 < L0 /\ &0 < L0 /\
     taup = min (r' pow 4 / (&1024 * L0 pow 2)) (r' pow 2 / &8)
     ==> &0 < taup /\ taup < r pow 2 /\
         !tau. &0 <= tau /\ tau <= min taup tau0
               ==> gamma tau IN rfs_vball (rfs_view hs) tt x (r / &2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r' pow 2 <= r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r' pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < taup /\ taup <= r' pow 4 / (&1024 * L0 pow 2) /\ taup <= r' pow 2 / &8`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_ARITH `&0 < &1024 /\ &0 < &8`];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[p3_Lplus]) THEN
  ABBREV_TAC `Fn = \tau. sqrt tau *
                (max (&0) (mfd_scalar (rfs_atlas_at (hs:(A)rfs_history) (tt - tau))
                                      (rfs_metric_at hs (tt - tau)) ((gamma:real->A) tau)) +
                 mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                           gamma (&0) tau0 tau pow 2)` THEN
  SUBGOAL_THEN `!t. &0 <= t ==> &0 <= (Fn:real->real) t` (LABEL_TAC "fpos") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "Fn" THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2; REAL_LE_MAX; REAL_LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `tau0:real`;
                 `min taup tau0`; `gamma:real->A`; `Fn:real->real`; `&4 * L0 / r`]
                P3N_PAR_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THENL
     [(* integrable on the subinterval *)
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      (* nonnegative *)
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      USE_THEN "fpos" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      (* the speed term *)
      REPEAT STRIP_TAC THEN EXPAND_TAC "Fn" THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> b <= a + b`) THEN
      REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL];
      (* lam > 0 *)
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      (* the majorant integral *)
      MATCH_MP_TAC P3N_1615_ARITH1 THEN EXISTS_TAC `r':real` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `real_integral (real_interval[&0,tau0]) (Fn:real->real)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL; IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
        MAP_EVERY EXISTS_TAC [`&0`; `tau0:real`] THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "fpos" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* MT Lemma 16.15 (p. 379) with the second scale rr (0 < rr <= r', rr <= r), *)
(* from Prop 16.13 (with 1/2 <= theta0), Prop 16.5, Prop 12.31 and Thm 12.5. *)
(* Constants: taup = min (rr^4/(1024 L0^2)) (rr^2/8), ell = L0 / sqrt taup,  *)
(* A1 and theta0 from 16.13 at (r',ell), A = max A1 (2(A0 + 50) + 1), d13    *)
(* from 16.13 at A, c from 12.31, dl0 from P3N_LEN_SCALAR, th1 = (1 +        *)
(* theta0)/2, d165 from 16.5 at (r',A + 1,min dl0 (1/10),th1), and           *)
(* dlt = min (min d13 d165) (min 1 (c rr^2 / (13 (eps^2 + 1)))).  16.13 and  *)
(* 16.5 keep the canonical parameter r'.                                     *)
(* ========================================================================= *)

let P3N_LEMMA_16_15_FIX = prove
 (`!u:A->bool.
     (?eps1613. &0 < eps1613 /\
       !C eps hf md g0 A0 r ell.
          &1 < C /\ &0 < eps /\ eps <= eps1613 /\
          p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
          &0 < r /\ &0 < ell
          ==> ?A1 theta0. &0 < A1 /\ &0 < theta0 /\ &1 / &2 <= theta0 /\ theta0 < &1 /\
                !A. A1 <= A
                  ==> ?d0. &0 < d0 /\
                        !rp dl (hs:(A)rfs_history) k i Phi xi ts h Tp tp gamma.
                           p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                           (!t x. &0 <= t /\ t < rfs_horizon hs /\
                                  x IN topspace(rfs_top_at hs t) /\
                                  inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                                  ==> p3_canon_at (rfs_view hs) C eps x t) /\
                           1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                           ts = hs_time hs k /\ h = p3_hscale hf rp dl ts /\
                           p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                           dl ts <= d0 /\ rp ts <= eps /\
                           Tp <= ts + theta0 * h pow 2 /\
                           (!s. ts <= s /\ s <= Tp
                                ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET
                                    topspace(rfs_top_at hs s)) /\
                           ts <= tp /\ tp <= ts + h pow 2 / &2 /\ tp <= Tp /\
                           rfs_st_curve hs Tp gamma (&0) (Tp - tp) /\
                           (!tau. &0 <= tau /\ tau <= Tp - tp
                                  ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
                           (Tp = ts + theta0 * h pow 2 \/
                            gamma (&0) IN IMAGE Phi {x | p3_std_dist g0 x = A}) /\
                           gamma (Tp - tp) IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
                           (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau))
                                             (rfs_metric_at hs (Tp - tau)) (gamma tau) +
                                  mfd_speed (rfs_atlas_at hs (Tp - tau))
                                            (rfs_metric_at hs (Tp - tau))
                                            gamma (&0) (Tp - tp) tau pow 2)
                           real_integrable_on real_interval[&0,Tp - tp]
                           ==> ell < p3_energy hs Tp gamma (Tp - tp)) /\
     P3_PROP_16_5_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u /\
     P2_PROP_12_31_STATEMENT /\ P2_THM_12_5_STATEMENT
     ==> P3_LEMMA_16_15_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_16_5_STATEMENT; P3_LEMMA_16_15_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps1613:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1613")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `eps165:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p165")))
      (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (LABEL_TAC "p1231") (LABEL_TAC "p125"))))) THEN
  EXISTS_TAC `min eps1613 eps165` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1613 /\ eps <= eps165` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_std_initial g0 A0` THEN SIMP_TAC[p3_std_initial]; ALL_TAC] THEN
  (* the model constants: c from Prop 12.31 and dl0 *)
  USE_THEN "p1231" (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`] o
                    REWRITE_RULE[P2_PROP_12_31_STATEMENT]) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  MP_TAC(SPEC `c:real` P3N_LEN_SCALAR) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `rs:num->real`; `ks:num->real`; `ds:num->real`; `r':real`;
                       `rr:real`; `L0:real`] THEN
  STRIP_TAC THEN
  (* taup and ell *)
  ABBREV_TAC `taup = min (rr pow 4 / (&1024 * L0 pow 2)) (rr pow 2 / &8)` THEN
  SUBGOAL_THEN `&0 < taup` ASSUME_TAC THENL
   [EXPAND_TAC "taup" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; REAL_ARITH `&0 < &1024 /\ &0 < &8`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt taup` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `ell = L0 / sqrt taup` THEN
  SUBGOAL_THEN `&0 < ell /\ L0 = ell * sqrt taup` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ell" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `&0 < sqrt taup` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* Prop 16.13 at (r',ell) and A *)
  USE_THEN "p1613" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`;
                                    `md:real->real`; `g0:real^3->real^3^3`; `A0:real`;
                                    `r':real`; `ell:real`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real` (X_CHOOSE_THEN `theta0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a1"))))))) THEN
  ABBREV_TAC `A = max A1 (&2 * (A0 + &50) + &1)` THEN
  SUBGOAL_THEN `A1 <= A /\ &2 * (A0 + &50) < A /\ &0 < A` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "a1" (MP_TAC o SPEC `A:real`) THEN ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d13:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d13"))) THEN
  ABBREV_TAC `th1 = (&1 + theta0) / &2` THEN
  SUBGOAL_THEN `&0 < th1 /\ th1 < &1 /\ theta0 < th1 /\ th1 <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Prop 16.5 at A + 1 *)
  USE_THEN "p165" (MP_TAC o SPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                                   `g0:real^3->real^3^3`; `A0:real`; `r':real`; `A + &1`;
                                   `min dl0 (&1 / &10)`; `th1:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d165:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d165"))) THEN
  (* dlt and taup *)
  SUBGOAL_THEN `&0 < c * rr pow 2 / (&13 * (eps pow 2 + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT];
      MATCH_MP_TAC(REAL_ARITH `&0 <= e ==> &0 < &13 * (e + &1)`) THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`min (min d13 d165) (min (&1) (c * rr pow 2 / (&13 * (eps pow 2 + &1))))`;
    `taup:real`] THEN
  ABBREV_TAC `dlt = min (min d13 d165) (min (&1) (c * rr pow 2 / (&13 * (eps pow 2 + &1))))` THEN
  SUBGOAL_THEN `&0 < dlt /\ dlt <= d13 /\ dlt <= d165 /\ dlt <= &1 /\
                dlt <= c * rr pow 2 / (&13 * (eps pow 2 + &1))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dlt" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`rs':num->real`; `ks':num->real`; `dd:num->real`; `hs:(A)rfs_history`;
                       `x:A`; `tt:real`; `r:real`; `tau0:real`; `gamma:real->A`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  (* the setting *)
  SUBGOAL_THEN `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd)
                                (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_p16_setting; p3_step_hyp] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history)` ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `r':real`; `dlt:real`; `rs':num->real`; `ks':num->real`;
                 `dd:num->real`; `hs:(A)rfs_history`] P3N_1615_CANON) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  (* part (1) *)
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`; `rr:real`; `gamma:real->A`;
                 `tau0:real`; `L0:real`; `taup:real`] P3N_1615_PART1) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "part1"))) THEN
  CONJ_TAC THENL [USE_THEN "part1" ACCEPT_TAC; ALL_TAC] THEN
  (* part (2): one surgery cap *)
  MAP_EVERY X_GEN_TAC [`k:num`; `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `tp:real`] THEN
  DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
  X_GEN_TAC `tau1:real` THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `ts = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `h = p3_hscale hf (p3_stepf rs') (p3_stepf dd) ts` THEN
  SUBGOAL_THEN `p3_T (i - 1) <= ts /\ ts < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `i:num`; `rs:num->real`; `ks:num->real`;
                 `ds:num->real`; `r':real`; `dlt:real`; `rs':num->real`; `ks':num->real`;
                 `dd:num->real`; `hs:(A)rfs_history`; `ts:real`] P3N_1615_PARAMS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                 `g0:real^3->real^3^3`; `A0:real`; `p3_stepf rs'`; `p3_stepf dd`;
                 `hs:(A)rfs_history`; `k:num`] P3N_STRUCT_BASIC) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < p3_stepf rs' ts /\ &0 < p3_stepf dd ts` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) (hs:(A)rfs_history)` THEN
    REWRITE_TAC[p3_struct] THEN
    DISCH_THEN(MP_TAC o SPEC `ts:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `h pow 2 * &12 < c * r pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[p3_hscale] THEN
    MATCH_MP_TAC P3N_1615_HSMALL THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `eps:real`; `rr:real`; `dlt:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  (* Prop 16.5 at the cap, up to the horizon *)
  USE_THEN "d165" (MP_TAC o SPECL [`p3_stepf rs'`; `p3_stepf dd`; `hs:(A)rfs_history`; `k:num`;
                                   `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`;
                                   `h:real`; `rfs_horizon (hs:(A)rfs_history)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN TRY(REWRITE_TAC[REAL_LE_REFL]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->real^3->real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k:num`; `Phi:real^3->A`; `ts:real`; `h:real`;
                 `g0:real^3->real^3^3`; `A + &1`; `G:real->real^3->real^3^3`; `theta0:real`;
                 `th1:real`; `min dl0 (&1 / &10)`; `tt:real`] P3N_1615_TE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->bool` (X_CHOOSE_THEN `Te:real`
    (fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs))) THEN
  (* the curvature of the model flow *)
  SUBGOAL_THEN `!t y. &0 <= t /\ t < &1
                      ==> c / (&1 - t) <= lscalar ((G:real->real^3->real^3^3) t) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM P2C_OPEN_SET_MFD_SCALAR] THEN
    USE_THEN "c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `G:real->real^3->real^3^3`]
                P3N_STD_SEC_NONNEG) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  (* Prop 16.13 at the cap *)
  SUBGOAL_THEN
   `!Tp tq (gm:real->A).
      Tp <= ts + theta0 * h pow 2 /\
      (!s. ts <= s /\ s <= Tp
           ==> IMAGE Phi {z | p3_std_dist g0 z <= A} SUBSET topspace(rfs_top_at hs s)) /\
      ts <= tq /\ tq <= ts + h pow 2 / &2 /\ tq <= Tp /\
      rfs_st_curve hs Tp gm (&0) (Tp - tq) /\
      (!tau. &0 <= tau /\ tau <= Tp - tq
             ==> gm tau IN IMAGE Phi {z | p3_std_dist g0 z <= A}) /\
      (Tp = ts + theta0 * h pow 2 \/ gm (&0) IN IMAGE Phi {z | p3_std_dist g0 z = A}) /\
      gm (Tp - tq) IN IMAGE Phi {z | p3_std_dist g0 z < A / &2} /\
      (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau)) (gm tau) +
             mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                       gm (&0) (Tp - tq) tau pow 2)
      real_integrable_on real_interval[&0,Tp - tq]
      ==> ell < p3_energy hs Tp gm (Tp - tq)`
  (LABEL_TAC "h13") THENL
   [MAP_EVERY X_GEN_TAC [`Tp:real`; `tq:real`; `gm:real->A`] THEN
    DISCH_THEN(fun th -> let cs = CONJUNCTS th in MAP_EVERY ASSUME_TAC cs) THEN
    USE_THEN "d13" (MP_TAC o SPECL [`p3_stepf rs'`; `p3_stepf dd`; `hs:(A)rfs_history`; `k:num`;
                                    `j:num`; `Phi:real^3->A`; `xi:real^3->real^3`; `ts:real`;
                                    `h:real`; `Tp:real`; `tq:real`; `gm:real->A`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the cap lemma *)
  MATCH_MP_TAC(ISPECL [`c:real`; `dl0:real`; `hs:(A)rfs_history`; `tt:real`; `x:A`; `r:real`;
                       `gamma:real->A`; `tau0:real`; `Phi:real^3->A`; `ts:real`; `h:real`;
                       `g0:real^3->real^3^3`; `A0:real`; `A:real`; `G:real->real^3->real^3^3`;
                       `J:real->bool`; `min dl0 (&1 / &10)`; `Te:real`; `theta0:real`;
                       `th1:real`; `ell:real`; `L0:real`; `taup:real`; `tp:real`; `tau1:real`]
                      P3N_1615_CAP) THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC));;

(* ========================================================================= *)
(* The route theorem for Lemma 16.15 (the route statements: 16.13 with       *)
(* 1/2 <= theta0, and the route with 12.31 and 12.5).                        *)
(* ========================================================================= *)

let P3N_LEMMA_16_15_ROUTE = prove
 (`!u:A->bool. P3_LEMMA_16_15_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_LEMMA_16_15_ROUTE_STATEMENT] THEN
  MP_TAC(ISPEC `u:A->bool` P3N_LEMMA_16_15_FIX) THEN
  REWRITE_TAC[GSYM P3_PROP_16_13_STATEMENT]);;

