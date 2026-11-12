(* ========================================================================= *)
(* pc_wan_pstep: from weak solutions on the whole space to classical         *)
(* equations for their mollifications, Friedrichs convergence, passage to    *)
(* the limit and the spatial regularity step.                                *)
(*   - convergence in L^2 (wan_l2c) and its algebra;                         *)
(*   - the mollifier sequence, commutators and Friedrichs convergence;       *)
(*   - the mollified equation;                                               *)
(*   - Cauchy sequences from the level-0 energy estimate, limits;            *)
(*   - the spatial regularity step;                                          *)
(*   - whole-space Sobolev classes wan_hd and their algebra;                 *)
(*   - the spatial bootstrap.                                                *)
(* ========================================================================= *)

needs "src/pc_wan_pen.ml";;

prioritize_real();;
type_invention_error := true;;

let wan_l2c = new_definition
 `wan_l2c (u:num->real^M->real^K) (v:real^M->real^K) <=>
    (!n. u n IN lspace (:real^M) (&2)) /\ v IN lspace (:real^M) (&2) /\
    ((\n. lnorm (:real^M) (&2) (\x. u n x - v x)) ---> &0) sequentially`;;

let WAN_LNORM2_SQ = prove
 (`!(f:real^M->real^K) s.
     f IN lspace s (&2)
     ==> lnorm s (&2) f pow 2 = drop(integral s (\x. lift(norm(f x) pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RPOW_POW] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `&2`; `f:real^M->real^K`] LNORM_RPOW) THEN
  ASM_REWRITE_TAC[RPOW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let WAN_L2C_SQ = prove
 (`!(u:num->real^M->real^K) v.
     wan_l2c u v <=>
     (!n. u n IN lspace (:real^M) (&2)) /\ v IN lspace (:real^M) (&2) /\
     ((\n. drop(integral (:real^M) (\x. lift(norm(u n x - v x) pow 2)))) ---> &0)
       sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_l2c] THEN
  MATCH_MP_TAC(TAUT `(a /\ b ==> (c <=> d)) ==> (a /\ b /\ c <=> a /\ b /\ d)`) THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. (\x. (u:num->real^M->real^K) n x - v x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. drop(integral (:real^M) (\x. lift(norm((u:num->real^M->real^K) n x - v x) pow 2))) =
        lnorm (:real^M) (&2) (\x. u n x - v x) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`\x. (u:num->real^M->real^K) n x - v x`; `(:real^M)`] WAN_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) e`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `t = lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `t pow 2 <= t` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `e pow 2`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `t = lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `t pow 2 < e pow 2` MP_TAC THENL
     [MP_TAC(SPEC `t pow 2` REAL_ABS_REFL) THEN ASM_SIMP_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Comparison principles for L^2 convergence.                               *)
(* ------------------------------------------------------------------------- *)

let WAN_L2C_MEM = prove
 (`!(u:num->real^M->real^K) v.
     wan_l2c u v ==> (!n. u n IN lspace (:real^M) (&2)) /\ v IN lspace (:real^M) (&2)`,
  SIMP_TAC[wan_l2c]);;

let WAN_L2C_DIFF_LSPACE = prove
 (`!(u:num->real^M->real^K) v n.
     wan_l2c u v ==> (\x. u n x - v x) IN lspace (:real^M) (&2)`,
  REWRITE_TAC[wan_l2c] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
  ASM_REWRITE_TAC[REAL_POS; ETA_AX]);;

let WAN_L2C_BOUND1 = prove
 (`!(u:num->real^M->real^K) v (w:num->real^M->real^L) z B.
     wan_l2c u v /\ (!n. w n IN lspace (:real^M) (&2)) /\ z IN lspace (:real^M) (&2) /\
     (!n. lnorm (:real^M) (&2) (\x. w n x - z x) <=
          B * lnorm (:real^M) (&2) (\x. u n x - v x))
     ==> wan_l2c w z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))) THEN
  UNDISCH_TAC `wan_l2c (u:num->real^M->real^K) v` THEN
  REWRITE_TAC[wan_l2c] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. B * lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)` THEN
  ASM_SIMP_TAC[REALLIM_NULL_LMUL] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lnorm (:real^M) (&2) (\x. (w:num->real^M->real^L) n x - z x)`
  MP_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  USE_THEN "bd" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC);;

let WAN_L2C_BOUND2 = prove
 (`!(u:num->real^M->real^K) v (u1:num->real^M->real^P) v1 (w:num->real^M->real^L) z B.
     wan_l2c u v /\ wan_l2c u1 v1 /\
     (!n. w n IN lspace (:real^M) (&2)) /\ z IN lspace (:real^M) (&2) /\
     (!n. lnorm (:real^M) (&2) (\x. w n x - z x) <=
          B * (lnorm (:real^M) (&2) (\x. u n x - v x) +
               lnorm (:real^M) (&2) (\x. u1 n x - v1 x)))
     ==> wan_l2c w z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))) THEN
  UNDISCH_TAC `wan_l2c (u1:num->real^M->real^P) v1` THEN
  UNDISCH_TAC `wan_l2c (u:num->real^M->real^K) v` THEN
  REWRITE_TAC[wan_l2c] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. B * (lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x) +
                       lnorm (:real^M) (&2) (\x. (u1:num->real^M->real^P) n x - v1 x))` THEN
  ASM_SIMP_TAC[REALLIM_NULL_LMUL; REALLIM_NULL_ADD] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lnorm (:real^M) (&2) (\x. (w:num->real^M->real^L) n x - z x)`
  MP_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  USE_THEN "bd" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Algebra of L^2 convergence.                                              *)
(* ------------------------------------------------------------------------- *)

let WAN_L2C_ADD = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l2c u v /\ wan_l2c u' v'
     ==> wan_l2c (\n x. u n x + u' n x) (\x. v x + v' x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c] o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c] o CONJUNCT2) THEN
  MATCH_MP_TAC(ISPECL [`u:num->real^M->real^K`; `v:real^M->real^K`;
                       `u':num->real^M->real^K`; `v':real^M->real^K`] WAN_L2C_BOUND2) THEN
  EXISTS_TAC `&1` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LSPACE_ADD; REAL_POS; ETA_AX] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `(\x. ((u:num->real^M->real^K) n x + u' n x) - (v x + v' x)) =
    (\x. (\x. u n x - v x) x + (\x. u' n x - v' x) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LNORM_TRIANGLE THEN
  ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX] THEN REAL_ARITH_TAC);;

let WAN_L2C_SUB = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l2c u v /\ wan_l2c u' v'
     ==> wan_l2c (\n x. u n x - u' n x) (\x. v x - v' x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c] o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c] o CONJUNCT2) THEN
  MATCH_MP_TAC(ISPECL [`u:num->real^M->real^K`; `v:real^M->real^K`;
                       `u':num->real^M->real^K`; `v':real^M->real^K`] WAN_L2C_BOUND2) THEN
  EXISTS_TAC `&1` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_MUL_LID] THEN
  SUBGOAL_THEN
   `(\x. ((u:num->real^M->real^K) n x - u' n x) - (v x - v' x)) =
    (\x. (\x. u n x - v x) x + (\x. --(u' n x - v' x)) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
  ASM_SIMP_TAC[LSPACE_SUB; LSPACE_NEG; REAL_POS; ETA_AX; LNORM_NEG] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[]]);;

let WAN_L2C_NEG = prove
 (`!(u:num->real^M->real^K) v.
     wan_l2c u v ==> wan_l2c (\n x. --(u n x)) (\x. --(v x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c]) THEN
  MATCH_MP_TAC WAN_L2C_BOUND1 THEN
  MAP_EVERY EXISTS_TAC [`u:num->real^M->real^K`; `v:real^M->real^K`; `&1`] THEN
  ASM_SIMP_TAC[LSPACE_NEG; ETA_AX; REAL_MUL_LID] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `(\x. --((u:num->real^M->real^K) n x) - --(v x)) = (\x. --(u n x - v x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[LNORM_NEG; REAL_LE_REFL]]);;

let WAN_L2C_CMUL = prove
 (`!(u:num->real^M->real^K) v c.
     wan_l2c u v ==> wan_l2c (\n x. c % u n x) (\x. c % v x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c]) THEN
  MATCH_MP_TAC WAN_L2C_BOUND1 THEN
  MAP_EVERY EXISTS_TAC [`u:num->real^M->real^K`; `v:real^M->real^K`; `abs c`] THEN
  ASM_SIMP_TAC[LSPACE_CMUL; ETA_AX] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `(\x. c % (u:num->real^M->real^K) n x - c % v x) = (\x. c % (\x. u n x - v x) x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LNORM_MUL THEN
  ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX] THEN REAL_ARITH_TAC);;

let WAN_L2C_MUL = prove
 (`!(u:num->real^M->real^K) v (m:real^M->real) B.
     wan_l2c u v /\ (\x. lift(m x)) continuous_on (:real^M) /\ (!x. abs(m x) <= B)
     ==> wan_l2c (\n x. m x % u n x) (\x. m x % v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[wan_l2c] (ASSUME `wan_l2c (u:num->real^M->real^K) v`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^M`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^M->real^K. h IN lspace (:real^M) (&2)
                       ==> (\x. m x % h x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2C_BOUND1 THEN
  MAP_EVERY EXISTS_TAC [`u:num->real^M->real^K`; `v:real^M->real^K`; `B:real`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `(\x. (u:num->real^M->real^K) n x - v x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `lnorm (:real^M) (&2) (\x. B % (\x. (u:num->real^M->real^K) n x - v x) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^M->bool` THEN
    ASM_SIMP_TAC[LSPACE_CMUL; LSPACE_SUB; REAL_POS; ETA_AX; NEGLIGIBLE_EMPTY] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; NOT_IN_EMPTY; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= B ==> abs B = B`];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ASM_SIMP_TAC[LNORM_MUL; REAL_ARITH `~(&2 = &0)`; REAL_ARITH `&0 <= B ==> abs B = B`]]);;

let WAN_L2C_ZERO = prove
 (`wan_l2c (\n:num x:real^M. vec 0:real^K) (\x. vec 0)`,
  REWRITE_TAC[wan_l2c; VECTOR_SUB_REFL] THEN
  SIMP_TAC[LSPACE_0; LNORM_0; REAL_ARITH `~(&2 = &0)`; REALLIM_CONST]);;

let WAN_L2C_CONST = prove
 (`!v:real^M->real^K. v IN lspace (:real^M) (&2) ==> wan_l2c (\n. v) v`,
  REWRITE_TAC[wan_l2c; VECTOR_SUB_REFL] THEN
  SIMP_TAC[LNORM_0; REAL_ARITH `~(&2 = &0)`; REALLIM_CONST]);;

let WAN_L2C_EQ = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l2c u v /\ (!n x. u' n x = u n x) /\ (!x. v' x = v x) ==> wan_l2c u' v'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u':num->real^M->real^K = u /\ v':real^M->real^K = v`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

let WAN_L2C_VSUM = prove
 (`!(u:A->num->real^M->real^K) v t.
     FINITE t /\ (!i. i IN t ==> wan_l2c (u i) (v i))
     ==> wan_l2c (\n x. vsum t (\i. u i n x)) (\x. vsum t (\i. v i x))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; WAN_L2C_ZERO; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(u:A->num->real^M->real^K) a`; `(v:A->real^M->real^K) a`;
                 `\n x. vsum s (\i. (u:A->num->real^M->real^K) i n x)`;
                 `\x. vsum s (\i. (v:A->real^M->real^K) i x)`] WAN_L2C_ADD) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Completeness, Cauchy property and uniqueness of L^2 limits.              *)
(* ------------------------------------------------------------------------- *)

let WAN_SQ_SMALL = prove
 (`!A e. &0 <= A /\ &0 < e /\ A < &2 * min (&1) (e / &4) ==> A pow 2 < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = min (&1) (e / &4)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 /\ d <= e / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LTE_TRANS `(&2 * d) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `d * d <= d * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

let WAN_LNORM2_TRIANGLE_SUB = prove
 (`!(f:real^M->real^K) g h.
     f IN lspace (:real^M) (&2) /\ g IN lspace (:real^M) (&2) /\
     h IN lspace (:real^M) (&2)
     ==> lnorm (:real^M) (&2) (\x. f x - g x) <=
         lnorm (:real^M) (&2) (\x. f x - h x) + lnorm (:real^M) (&2) (\x. g x - h x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (f:real^M->real^K) x - g x) =
    (\x. (\x. f x - h x) x + (\x. --(g x - h x)) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
  ASM_SIMP_TAC[LSPACE_SUB; LSPACE_NEG; REAL_POS; ETA_AX; LNORM_NEG] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[]]);;

let WAN_L2C_CAUCHY_SQ = prove
 (`!(u:num->real^M->real^K) v.
     wan_l2c u v
     ==> !e. &0 < e
             ==> ?M. !m n. M <= m /\ M <= n
                           ==> drop(integral (:real^M)
                                      (\x. lift(norm(u m x - u n x) pow 2))) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l2c]) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `((\n. lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)) ---> &0)
    sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `min (&1) (e / &4)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN DISCH_THEN(LABEL_TAC "M") THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (u:num->real^M->real^K) m x - u n x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(BETA_RULE(MATCH_MP WAN_LNORM2_SQ th))]) THEN
  MATCH_MP_TAC WAN_SQ_SMALL THEN ASM_SIMP_TAC[LNORM_POS_LE] THEN
  MP_TAC(ISPECL [`(u:num->real^M->real^K) m`; `(u:num->real^M->real^K) n`;
                 `v:real^M->real^K`] WAN_LNORM2_TRIANGLE_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "M" (fun th -> MP_TAC(MP (SPEC `m:num` th) (ASSUME `M:num <= m`)) THEN
                          MP_TAC(MP (SPEC `n:num` th) (ASSUME `M:num <= n`))) THEN
  REAL_ARITH_TAC);;

let WAN_L2C_CAUCHY = prove
 (`!(u:num->real^M->real^K).
     (!n. u n IN lspace (:real^M) (&2)) /\
     (!e. &0 < e
          ==> ?M. !m n. M <= m /\ M <= n
                        ==> drop(integral (:real^M)
                                   (\x. lift(norm(u m x - u n x) pow 2))) < e)
     ==> ?v. wan_l2c u v`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c")) THEN
  MP_TAC(ISPECL [`u:num->real^M->real^K`; `&2`; `(:real^M)`] RIESZ_FISCHER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "c" (MP_TAC o SPEC `e pow 2`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN DISCH_THEN(LABEL_TAC "M") THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN STRIP_TAC THEN
    USE_THEN "M" (fun th -> MP_TAC(MP (SPECL [`m:num`; `n:num`] th)
                    (CONJ (ASSUME `M:num <= m`) (ASSUME `M:num <= n`)))) THEN
    SUBGOAL_THEN `(\x. (u:num->real^M->real^K) m x - u n x) IN lspace (:real^M) (&2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(BETA_RULE(MATCH_MP WAN_LNORM2_SQ th))]) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M->real^K` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[wan_l2c; REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[GE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)`
  MP_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    REAL_ARITH_TAC]);;

let WAN_L2C_UNIQUE = prove
 (`!(u:num->real^M->real^K) v w.
     wan_l2c u v /\ wan_l2c u w ==> negligible {x | ~(v x = w x)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_l2c] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (v:real^M->real^K) x - w x) IN lspace (:real^M) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^M)`; `&2`; `\x. (v:real^M->real^K) x - w x`] LNORM_EQ_0) THEN
  ASM_REWRITE_TAC[IN_UNIV; VECTOR_SUB_EQ; REAL_ARITH `~(&2 = &0)`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  ASM_SIMP_TAC[LNORM_POS_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `c = lnorm (:real^M) (&2) (\x. (v:real^M->real^K) x - w x)` THEN
  UNDISCH_TAC
   `((\n. lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - w x)) ---> &0)
    sequentially` THEN
  UNDISCH_TAC
   `((\n. lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)) ---> &0)
    sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `c / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `c / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `M2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M1 + M2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `M1 + M2:num`) THEN REWRITE_TAC[LE_ADD; LE_ADDR] THEN
  MP_TAC(ISPECL [`v:real^M->real^K`; `w:real^M->real^K`;
                 `(u:num->real^M->real^K) (M1 + M2)`] WAN_LNORM2_TRIANGLE_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lnorm (:real^M) (&2) (\x. (v:real^M->real^K) x - u (M1 + M2:num) x) =
    lnorm (:real^M) (&2) (\x. u (M1 + M2:num) x - v x) /\
    lnorm (:real^M) (&2) (\x. (w:real^M->real^K) x - u (M1 + M2:num) x) =
    lnorm (:real^M) (&2) (\x. u (M1 + M2:num) x - w x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LNORM_NEG] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* L^1 convergence, used to pass to the limit in integrals.                 *)
(* ------------------------------------------------------------------------- *)

let wan_l1c = new_definition
 `wan_l1c (u:num->real^M->real^K) (v:real^M->real^K) <=>
    (!n. u n absolutely_integrable_on (:real^M)) /\ v absolutely_integrable_on (:real^M) /\
    ((\n. drop(integral (:real^M) (\x. lift(norm(u n x - v x))))) ---> &0) sequentially`;;

let WAN_L1_NORM_SUB_INTEGRABLE = prove
 (`!(f:real^M->real^K) g.
     f absolutely_integrable_on (:real^M) /\ g absolutely_integrable_on (:real^M)
     ==> (\x. lift(norm(f x - g x))) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]);;

let WAN_L1C_BOUND2 = prove
 (`!(u:num->real^M->real^K) v (u1:num->real^M->real^P) v1 (w:num->real^M->real^L) z B.
     wan_l1c u v /\ wan_l1c u1 v1 /\
     (!n. w n absolutely_integrable_on (:real^M)) /\ z absolutely_integrable_on (:real^M) /\
     (!n x. norm(w n x - z x) <= B * (norm(u n x - v x) + norm(u1 n x - v1 x)))
     ==> wan_l1c w z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))) THEN
  UNDISCH_TAC `wan_l1c (u1:num->real^M->real^P) v1` THEN
  UNDISCH_TAC `wan_l1c (u:num->real^M->real^K) v` THEN
  REWRITE_TAC[wan_l1c] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. B * (drop(integral (:real^M)
                (\x. lift(norm((u:num->real^M->real^K) n x - v x)))) +
             drop(integral (:real^M)
                (\x. lift(norm((u1:num->real^M->real^P) n x - v1 x)))))` THEN
  ASM_SIMP_TAC[REALLIM_NULL_LMUL; REALLIM_NULL_ADD] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((w:num->real^M->real^L) n x - z x))) integrable_on (:real^M) /\
    (\x. lift(norm((u:num->real^M->real^K) n x - v x))) integrable_on (:real^M) /\
    (\x. lift(norm((u1:num->real^M->real^P) n x - v1 x))) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_L1_NORM_SUB_INTEGRABLE THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= drop(integral (:real^M) (\x. lift(norm((w:num->real^M->real^L) n x - z x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `B * (drop(integral (:real^M) (\x. lift(norm((u:num->real^M->real^K) n x - v x)))) +
         drop(integral (:real^M) (\x. lift(norm((u1:num->real^M->real^P) n x - v1 x))))) =
    drop(integral (:real^M)
           (\x. B % (lift(norm(u n x - v x)) + lift(norm(u1 n x - v1 x)))))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRABLE_ADD; INTEGRAL_ADD; DROP_CMUL; DROP_ADD];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_ADD; DROP_CMUL; DROP_ADD; LIFT_DROP]);;

let WAN_L1C_ADD = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l1c u v /\ wan_l1c u' v'
     ==> wan_l1c (\n x. u n x + u' n x) (\x. v x + v' x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l1c] o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l1c] o CONJUNCT2) THEN
  MATCH_MP_TAC(ISPECL [`u:num->real^M->real^K`; `v:real^M->real^K`;
                       `u':num->real^M->real^K`; `v':real^M->real^K`] WAN_L1C_BOUND2) THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ADD; ETA_AX] THEN
  REPEAT GEN_TAC THEN CONV_TAC NORM_ARITH);;

let WAN_L1C_SUB = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l1c u v /\ wan_l1c u' v'
     ==> wan_l1c (\n x. u n x - u' n x) (\x. v x - v' x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l1c] o CONJUNCT1) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[wan_l1c] o CONJUNCT2) THEN
  MATCH_MP_TAC(ISPECL [`u:num->real^M->real^K`; `v:real^M->real^K`;
                       `u':num->real^M->real^K`; `v':real^M->real^K`] WAN_L1C_BOUND2) THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_SUB; ETA_AX] THEN
  REPEAT GEN_TAC THEN CONV_TAC NORM_ARITH);;

let WAN_L1C_ZERO = prove
 (`wan_l1c (\n:num x:real^M. vec 0:real^K) (\x. vec 0)`,
  REWRITE_TAC[wan_l1c; VECTOR_SUB_REFL; NORM_0; LIFT_NUM; INTEGRAL_0; DROP_VEC;
              ABSOLUTELY_INTEGRABLE_0; REALLIM_CONST]);;

let WAN_L1C_VSUM = prove
 (`!(u:A->num->real^M->real^K) v t.
     FINITE t /\ (!i. i IN t ==> wan_l1c (u i) (v i))
     ==> wan_l1c (\n x. vsum t (\i. u i n x)) (\x. vsum t (\i. v i x))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; WAN_L1C_ZERO; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(u:A->num->real^M->real^K) a`; `(v:A->real^M->real^K) a`;
                 `\n x. vsum s (\i. (u:A->num->real^M->real^K) i n x)`;
                 `\x. vsum s (\i. (v:A->real^M->real^K) i x)`] WAN_L1C_ADD) THEN
  ASM_SIMP_TAC[]);;

let WAN_L1C_INTEGRAL = prove
 (`!(u:num->real^M->real^K) v.
     wan_l1c u v
     ==> ((\n. integral (:real^M) (u n)) --> integral (:real^M) v) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_l1c] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN REWRITE_TAC[] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. drop(integral (:real^M) (\x. lift(norm((u:num->real^M->real^K) n x - v x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `integral (:real^M) ((u:num->real^M->real^K) n) - integral (:real^M) v =
      integral (:real^M) (\x. u n x - v x)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SUB THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC WAN_L1_NORM_SUB_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX]];
    UNDISCH_TAC
     `((\n. drop(integral (:real^M) (\x. lift(norm((u:num->real^M->real^K) n x - v x)))))
       ---> &0) sequentially` THEN
    REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; LIFT_NUM]]);;

let WAN_L2C_PAIR = prove
 (`!(u:num->real^M->real^K) v (h:real^M->real) k.
     wan_l2c u v /\ (\x. lift(h x)) continuous_on (:real^M) /\ compact k /\
     (!x. ~(x IN k) ==> h x = &0)
     ==> wan_l1c (\n x. h x % u n x) (\x. h x % v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[wan_l2c] (ASSUME `wan_l2c (u:num->real^M->real^K) v`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((h:real^M->real) x)) IN lspace (:real^M) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; GSYM LIFT_NUM; LIFT_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^M->real^K. f IN lspace (:real^M) (&2)
      ==> (\x. lift(norm(lift((h:real^M->real) x)) * norm(lift(norm(f x)))))
            integrable_on (:real^M) /\
          (\x. h x % f x) absolutely_integrable_on (:real^M) /\
          drop(integral (:real^M)
                 (\x. lift(norm(lift(h x)) * norm(lift(norm(f x)))))) <=
          lnorm (:real^M) (&2) (\x. lift(h x)) * lnorm (:real^M) (&2) f`
  (LABEL_TAC "hp") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x. lift(norm((f:real^M->real^K) x))) IN lspace (:real^M) (&2)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[LSPACE_NORM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(:real^M)`; `&2`; `&2`; `\x. lift((h:real^M->real) x)`;
                   `\x. lift(norm((f:real^M->real^K) x))`] LSPACE_INTEGRABLE_PRODUCT) THEN
    MP_TAC(ISPECL [`(:real^M)`; `&2`; `&2`; `\x. lift((h:real^M->real) x)`;
                   `\x. lift(norm((f:real^M->real^K) x))`] HOELDER_INEQUALITY) THEN
    ASM_REWRITE_TAC[LNORM_NORM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC
     `\x. lift(norm(lift((h:real^M->real) x)) * norm(lift(norm((f:real^M->real^K) x))))` THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_MUL; NORM_LIFT; REAL_ABS_NORM; REAL_LE_REFL] THEN
    MATCH_MP_TAC MEASURABLE_ON_MUL THEN
    ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON] THEN
    UNDISCH_TAC `(f:real^M->real^K) IN lspace (:real^M) (&2)` THEN
    SIMP_TAC[lspace; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[wan_l1c] THEN
  SUBGOAL_THEN
   `(!n. (\x. (h:real^M->real) x % (u:num->real^M->real^K) n x)
           absolutely_integrable_on (:real^M)) /\
    (\x. h x % (v:real^M->real^K) x) absolutely_integrable_on (:real^M)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN
      USE_THEN "hp" (fun th -> MP_TAC(MATCH_MP th (SPEC `n:num`
        (ASSUME `!n. (u:num->real^M->real^K) n IN lspace (:real^M) (&2)`)))) THEN
      SIMP_TAC[];
      USE_THEN "hp" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(v:real^M->real^K) IN lspace (:real^M) (&2)`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. lnorm (:real^M) (&2) (\x. lift((h:real^M->real) x)) *
                  lnorm (:real^M) (&2) (\x. (u:num->real^M->real^K) n x - v x)` THEN
  ASM_SIMP_TAC[REALLIM_NULL_LMUL] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (u:num->real^M->real^K) n x - v x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  USE_THEN "hp" (fun th -> MP_TAC(MATCH_MP th
     (ASSUME `(\x. (u:num->real^M->real^K) n x - v x) IN lspace (:real^M) (&2)`))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift(norm((h:real^M->real) x % (u:num->real^M->real^K) n x - h x % v x))) =
    (\x. lift(norm(lift(h x)) * norm(lift(norm(u n x - v x)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM VECTOR_SUB_LDISTRIB; NORM_MUL; NORM_LIFT; REAL_ABS_NORM];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[LIFT_DROP; REAL_LE_MUL; NORM_POS_LE]);;

(* ========================================================================= *)
(* The mollifier sequence J_n = wan_moll (inv(n + 1)):                      *)
(* linearity, L^2 convergence, commutators [J_n, m] h -> 0 and Friedrichs   *)
(* convergence [d_k J_n, a] h -> (d_k a) h.                                 *)
(* ========================================================================= *)

let WAN_INV_N1_POS = prove
 (`!n. &0 < inv(&n + &1)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC);;

let WAN_SQINT_POS = prove
 (`!(f:real^M->real^K).
     f IN lspace (:real^M) (&2)
     ==> &0 <= drop(integral (:real^M) (\x. lift(norm(f x) pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2]);;

let WAN_LNORM2_POS = prove
 (`!s (f:real^M->real^K). &0 <= lnorm s (&2) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lnorm] THEN
  SPEC_TAC(`drop(integral s (\x. lift(norm((f:real^M->real^K) x) rpow &2)))`,`t:real`) THEN
  GEN_TAC THEN REWRITE_TAC[rpow] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE; REAL_LE_REFL; REAL_POS]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) o
    check (is_exists o concl)) THEN
  SUBGOAL_THEN `~(&n = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_MESON_TAC[ODD]; ALL_TAC] THEN
  SUBGOAL_THEN `&n = &2 * &m` MP_TAC THENL
   [UNDISCH_TAC `abs(inv(&2)) = &m / &n` THEN UNDISCH_TAC `~(&n = &0)` THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN DISCH_TAC THEN
  UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[ODD_MULT; ARITH_ODD]);;

let WAN_L2C_SUB0 = prove
 (`!(u:num->real^M->real^K) u' v.
     wan_l2c u v /\ wan_l2c u' v ==> wan_l2c (\n x. u n x - u' n x) (\x. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:num->real^M->real^K`; `v:real^M->real^K`;
                 `u':num->real^M->real^K`; `v:real^M->real^K`] WAN_L2C_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL]);;

let WAN_DPART_LIFT = prove
 (`!i (a:real^M->real) x.
     lift(wan_dpart i a x) = partial_derivative i (\y. lift(a y)) x`,
  REWRITE_TAC[wan_dpart; partial_derivative; LIFT_DROP]);;

let WAN_DPART_SMOOTH = prove
 (`!i (a:real^M->real).
     smooth_map_on (:real^M) (\x. lift(a x))
     ==> smooth_map_on (:real^M) (\x. lift(wan_dpart i a x)) /\
         (\x. lift(wan_dpart i a x)) continuous_on (:real^M)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WAN_DPART_LIFT; ETA_AX] THEN
  SUBGOAL_THEN `smooth_map_on (:real^M) (partial_derivative i (\y. lift((a:real^M->real) y)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

(* ------------------------------------------------------------------------- *)
(* Linearity of convolution with a test kernel.                             *)
(* ------------------------------------------------------------------------- *)

let WAN_KCONV_ADD = prove
 (`!(k:real^M->real) (u:real^M->real^K) w x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u /\ wan_lloc (:real^M) w
     ==> wan_kconv k (\y. u y + w y) x = wan_kconv k u x + wan_kconv k w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_kconv; VECTOR_ADD_LDISTRIB] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_REWRITE_TAC[]);;

let WAN_KCONV_SUB = prove
 (`!(k:real^M->real) (u:real^M->real^K) w x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u /\ wan_lloc (:real^M) w
     ==> wan_kconv k (\y. u y - w y) x = wan_kconv k u x - wan_kconv k w x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_kconv; VECTOR_SUB_LDISTRIB] THEN
  MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_REWRITE_TAC[]);;

let WAN_KCONV_CMUL = prove
 (`!(k:real^M->real) (u:real^M->real^K) c x.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> wan_kconv k (\y. c % u y) x = c % wan_kconv k u x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_kconv; VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC INTEGRAL_CMUL THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_REWRITE_TAC[]);;

let WAN_KCONV_VSUM = prove
 (`!(k:real^M->real) (u:A->real^M->real^K) t x.
     wan_test (:real^M) k /\ FINITE t /\ (!i. i IN t ==> wan_lloc (:real^M) (u i))
     ==> wan_kconv k (\y. vsum t (\i. u i y)) x = vsum t (\i. wan_kconv k (u i) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_kconv; GSYM VSUM_LMUL] THEN
  MP_TAC(ISPECL [`\i y. (k:real^M->real)(x - y) % (u:A->real^M->real^K) i y`;
                 `(:real^M)`; `t:A->bool`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[]);;

let WAN_MOLL_ADD = prove
 (`!e (u:real^M->real^K) w x.
     &0 < e /\ wan_lloc (:real^M) u /\ wan_lloc (:real^M) w
     ==> wan_moll e (\y. u y + w y) x = wan_moll e u x + wan_moll e w x`,
  SIMP_TAC[wan_moll; WAN_KCONV_ADD; WAN_MKE_TEST]);;

let WAN_MOLL_SUBL = prove
 (`!e (u:real^M->real^K) w x.
     &0 < e /\ wan_lloc (:real^M) u /\ wan_lloc (:real^M) w
     ==> wan_moll e (\y. u y - w y) x = wan_moll e u x - wan_moll e w x`,
  SIMP_TAC[wan_moll; WAN_KCONV_SUB; WAN_MKE_TEST]);;

let WAN_MOLL_CMUL = prove
 (`!e (u:real^M->real^K) c x.
     &0 < e /\ wan_lloc (:real^M) u
     ==> wan_moll e (\y. c % u y) x = c % wan_moll e u x`,
  SIMP_TAC[wan_moll; WAN_KCONV_CMUL; WAN_MKE_TEST]);;

let WAN_MOLL_VSUM = prove
 (`!e (u:A->real^M->real^K) t x.
     &0 < e /\ FINITE t /\ (!i. i IN t ==> wan_lloc (:real^M) (u i))
     ==> wan_moll e (\y. vsum t (\i. u i y)) x = vsum t (\i. wan_moll e (u i) x)`,
  SIMP_TAC[wan_moll; WAN_KCONV_VSUM; WAN_MKE_TEST]);;

(* ------------------------------------------------------------------------- *)
(* L^2 convergence of the mollifier sequence; commutators with multipliers. *)
(* ------------------------------------------------------------------------- *)

let WAN_MOLL_SEQ_L2C = prove
 (`!(u:real^M->real^K) c.
     compact c /\ (!x. ~(x IN c) ==> u x = vec 0) /\ u IN lspace (:real^M) (&2)
     ==> wan_l2c (\n. wan_moll (inv(&n + &1)) u) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WAN_L2C_SQ] THEN
  ASM_SIMP_TAC[WAN_MOLL_L2; WAN_INV_N1_POS] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^M->real^K`; `c:real^M->bool`] WAN_MOLL_L2_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[WAN_INV_N1_POS] THEN ANTS_TAC THENL
   [TRANS_TAC REAL_LET_TRANS `inv(&M)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x < e ==> abs x < e`) THEN
  MATCH_MP_TAC WAN_SQINT_POS THEN MATCH_MP_TAC LSPACE_SUB THEN
  ASM_SIMP_TAC[REAL_POS; ETA_AX; WAN_MOLL_L2; WAN_INV_N1_POS]);;

let WAN_COMM_L2C = prove
 (`!(m:real^M->real) B (h:real^M->real^K) c.
     (\x. lift(m x)) continuous_on (:real^M) /\ (!x. abs(m x) <= B) /\
     compact c /\ (!x. ~(x IN c) ==> h x = vec 0) /\ h IN lspace (:real^M) (&2)
     ==> wan_l2c (\n x. wan_moll (inv(&n + &1)) (\y. m y % h y) x -
                        m x % wan_moll (inv(&n + &1)) h x)
                 (\x. vec 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (m:real^M->real) y % (h:real^M->real^K) y) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. wan_moll (inv(&n + &1)) (\y. (m:real^M->real) y % (h:real^M->real^K) y)`;
                 `\n x. (m:real^M->real) x % wan_moll (inv(&n + &1)) (h:real^M->real^K) x`;
                 `\x. (m:real^M->real) x % (h:real^M->real^K) x`] WAN_L2C_SUB0) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `c:real^M->bool` THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO];
    MP_TAC(ISPECL [`\n. wan_moll (inv(&n + &1)) (h:real^M->real^K)`; `h:real^M->real^K`;
                   `m:real^M->real`; `B:real`] WAN_L2C_MUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `c:real^M->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Friedrichs commutators [d_k J_e, a] f.                                   *)
(* ------------------------------------------------------------------------- *)

let wan_fcomm = new_definition
 `wan_fcomm k (a:real^M->real) e (f:real^M->real^K) x =
    wan_kconv (wan_dpart k (wan_mke e)) (\y. a y % f y) x -
    a x % wan_kconv (wan_dpart k (wan_mke e)) f x`;;

let WAN_SMOOTH_C1 = prove
 (`!s (f:real^M->real^N). smooth_map_on s f ==> continuously_differentiable 1 s f`,
  SIMP_TAC[smooth_map_on]);;

let WAN_DMKE_TEST = prove
 (`!e k. &0 < e ==> wan_test (:real^M) (wan_dpart k (wan_mke e))`,
  SIMP_TAC[WAN_TEST_DPART_TEST; WAN_MKE_TEST]);;

let WAN_LNORM2_MUL_BOUND = prove
 (`!(m:real^M->real) B (f:real^M->real^K).
     (\x. lift(m x)) continuous_on (:real^M) /\ (!x. abs(m x) <= B) /\
     f IN lspace (:real^M) (&2)
     ==> (\x. m x % f x) IN lspace (:real^M) (&2) /\
         lnorm (:real^M) (&2) (\x. m x % f x) <= B * lnorm (:real^M) (&2) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^M`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (m:real^M->real) x % (f:real^M->real^K) x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS `lnorm (:real^M) (&2) (\x. B % (f:real^M->real^K) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^M->bool` THEN
    ASM_SIMP_TAC[LSPACE_CMUL; REAL_POS; NEGLIGIBLE_EMPTY] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; NOT_IN_EMPTY; NORM_MUL] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= B ==> abs B = B`];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ASM_SIMP_TAC[LNORM_MUL; REAL_ARITH `~(&2 = &0)`; REAL_ARITH `&0 <= B ==> abs B = B`]]);;

let WAN_LNORM2_TRIANGLE3 = prove
 (`!(f:real^M->real^K) g h.
     f IN lspace (:real^M) (&2) /\ g IN lspace (:real^M) (&2) /\
     h IN lspace (:real^M) (&2)
     ==> lnorm (:real^M) (&2) (\x. f x + g x + h x) <=
         lnorm (:real^M) (&2) f + lnorm (:real^M) (&2) g + lnorm (:real^M) (&2) h`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `lnorm (:real^M) (&2) (f:real^M->real^K) +
    lnorm (:real^M) (&2) (\x. (g:real^M->real^K) x + h x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_SIMP_TAC[LSPACE_ADD; REAL_POS] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= x + z`) THEN
    MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let WAN_FCOMM_SUB = prove
 (`!k (a:real^M->real) e (f:real^M->real^K) g x.
     &0 < e /\ (\x. lift(a x)) continuous_on (:real^M) /\
     wan_lloc (:real^M) f /\ wan_lloc (:real^M) g
     ==> wan_fcomm k a e (\y. f y - g y) x = wan_fcomm k a e f x - wan_fcomm k a e g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_fcomm] THEN
  SUBGOAL_THEN
   `(\y. (a:real^M->real) y % ((f:real^M->real^K) y - g y)) =
    (\y. (\y. a y % f y) y - (\y. a y % g y) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_LDISTRIB]; ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_KCONV_SUB; WAN_DMKE_TEST; WAN_LLOC_CONT_MUL; ETA_AX] THEN
  VECTOR_ARITH_TAC);;

let WAN_FCOMM_BOUND = prove
 (`!k. ?D. &0 <= D /\
           !e (a:real^M->real) L (f:real^M->real^K).
             &0 < e /\ (\x. lift(a x)) continuous_on (:real^M) /\ &0 <= L /\
             (!x y. abs(a x - a y) <= L * norm(x - y)) /\
             f IN lspace (:real^M) (&2)
             ==> wan_fcomm k a e f IN lspace (:real^M) (&2) /\
                 lnorm (:real^M) (&2) (wan_fcomm k a e f) <=
                 L * D * lnorm (:real^M) (&2) f`,
  GEN_TAC THEN
  X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC
   (ISPEC `k:num` (INST_TYPE [`:M`,`:M`; `:K`,`:K`] WAN_FRIEDRICHS)) THEN
  EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `a:real^M->real`; `L:real`; `f:real^M->real^K`]) THEN
  ASM_REWRITE_TAC[GSYM wan_fcomm; ETA_AX] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[LNORM_POS_LE; REAL_LE_MUL; ARITH_EQ] THEN
  ASM_SIMP_TAC[WAN_LNORM2_SQ; REAL_POW_MUL] THEN
  ASM_REWRITE_TAC[GSYM REAL_POW_MUL; REAL_MUL_ASSOC]);;

let WAN_KCONV_DMKE_C1 = prove
 (`!e (w:real^M->real^K) k x.
     &0 < e /\ continuously_differentiable 1 (:real^M) w
     ==> wan_kconv (wan_dpart k (wan_mke e)) w x =
         wan_moll e (\x. partial_derivative k w x) x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_wpd (:real^M) k (w:real^M->real^K) (\x. partial_derivative k w x)`
  ASSUME_TAC THENL [MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (w:real^M->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_wpd]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM WAN_MOLL_PARTIAL] THEN MATCH_MP_TAC WAN_MOLL_WPD THEN
  ASM_REWRITE_TAC[]);;

let WAN_FCOMM_SMOOTH = prove
 (`!(a:real^M->real) Ba Bd (h:real^M->real^K) c k.
     smooth_map_on (:real^M) (\x. lift(a x)) /\ (!x. abs(a x) <= Ba) /\
     (!x. abs(wan_dpart k a x) <= Bd) /\
     smooth_map_on (:real^M) h /\ compact c /\ (!x. ~(x IN c) ==> h x = vec 0)
     ==> wan_l2c (\n. wan_fcomm k a (inv(&n + &1)) h) (\x. wan_dpart k a x % h x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^M) (\y. (a:real^M->real) y % (h:real^M->real^K) y)`
  ASSUME_TAC THENL [MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. partial_derivative k (\y. (a:real^M->real) y % (h:real^M->real^K) y) z =
        a z % partial_derivative k h z + wan_dpart k a z % h z`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[wan_dpart] THEN
    MP_TAC(ISPECL [`a:real^M->real`; `h:real^M->real^K`; `k:num`; `z:real^M`]
                  WAN_PD_DROPMUL) THEN
    ASM_REWRITE_TAC[partial_derivative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((a:real^M->real) x)) continuous_on (:real^M) /\
    (\x. lift(wan_dpart k (a:real^M->real) x)) continuous_on (:real^M) /\
    (h:real^M->real^K) continuous_on (:real^M) /\
    (\x. partial_derivative k (h:real^M->real^K) x) continuous_on (:real^M) /\
    (!x. ~(x IN c) ==> partial_derivative k h x = vec 0) /\
    (\x. (a:real^M->real) x % partial_derivative k h x) continuous_on (:real^M) /\
    (\x. wan_dpart k a x % h x) continuous_on (:real^M) /\
    (!x. ~(x IN c) ==> wan_dpart k a x % h x = vec 0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; WAN_DPART_SMOOTH] THEN
    SUBGOAL_THEN
     `(\x. partial_derivative k (h:real^M->real^K) x) continuous_on (:real^M)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PEN_PSUPPORT THEN
      EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_SIMP_TAC[o_DEF; SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_SIMP_TAC[o_DEF; SMOOTH_MAP_ON_CONTINUOUS_ON; WAN_DPART_SMOOTH];
      ASM_SIMP_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. partial_derivative k (h:real^M->real^K) x) IN lspace (:real^M) (&2) /\
    (\x. wan_dpart k (a:real^M->real) x % h x) IN lspace (:real^M) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN
    EXISTS_TAC `c:real^M->bool` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. wan_moll (inv(&n + &1))
             (\y. (a:real^M->real) y % (\x. partial_derivative k (h:real^M->real^K) x) y) x -
           a x % wan_moll (inv(&n + &1)) (\x. partial_derivative k h x) x`;
    `\x:real^M. vec 0:real^K`;
    `\n. wan_moll (inv(&n + &1)) (\x. wan_dpart k (a:real^M->real) x % (h:real^M->real^K) x)`;
    `\x. wan_dpart k (a:real^M->real) x % (h:real^M->real^K) x`] WAN_L2C_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WAN_COMM_L2C THEN
      MAP_EVERY EXISTS_TAC [`Ba:real`; `c:real^M->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `c:real^M->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC WAN_L2C_EQ THEN MP_TAC th) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC(rand(rator(concl th))) THEN
                        EXISTS_TAC(rand(concl th))) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN
  ASM_SIMP_TAC[wan_fcomm; WAN_KCONV_DMKE_C1; WAN_INV_N1_POS; WAN_SMOOTH_C1] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WAN_MOLL_ADD o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WAN_INV_N1_POS] THEN CONJ_TAC THEN MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC(VECTOR_ARITH `(a + b) - c:real^N = (a - c) + b`)]);;

let WAN_DENSITY_LIMIT = prove
 (`!(p:num->real) (q:num->num->real) (r:num->real) C.
     &0 <= C /\ (r ---> &0) sequentially /\ (!m. (q m ---> &0) sequentially) /\
     (!m n. abs(p n) <= C * abs(r m) + abs(q m n))
     ==> (p ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "q") (LABEL_TAC "b")))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (&2 * (C + &1))`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (MP_TAC o SPEC `m:num`)) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `C * abs((r:num->real) m) <= e / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs((r:num->real) m) * (&2 * (C + &1)) < e` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < &2 * (C + &1)`];
      ALL_TAC] THEN
    MP_TAC(SPEC `(r:num->real) m` REAL_ABS_POS) THEN
    SUBGOAL_THEN `&0 <= C * abs((r:num->real) m)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "q" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "b" (MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REAL_ARITH_TAC);;

let WAN_FCOMM_SPLIT = prove
 (`!k (a:real^M->real) L D Bd e (f:real^M->real^K) g.
     &0 < e /\ (\x. lift(a x)) continuous_on (:real^M) /\
     (\x. lift(wan_dpart k a x)) continuous_on (:real^M) /\
     (!x. abs(wan_dpart k a x) <= Bd) /\
     (!f:real^M->real^K.
         f IN lspace (:real^M) (&2)
         ==> wan_fcomm k a e f IN lspace (:real^M) (&2) /\
             lnorm (:real^M) (&2) (wan_fcomm k a e f) <= L * D * lnorm (:real^M) (&2) f) /\
     f IN lspace (:real^M) (&2) /\ g IN lspace (:real^M) (&2)
     ==> lnorm (:real^M) (&2) (\x. wan_fcomm k a e f x - wan_dpart k a x % f x) <=
         (L * D + Bd) * lnorm (:real^M) (&2) (\x. g x - f x) +
         lnorm (:real^M) (&2) (\x. wan_fcomm k a e g x - wan_dpart k a x % g x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "fb") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `(\x. (f:real^M->real^K) x - g x) IN lspace (:real^M) (&2) /\
    (\x. (g:real^M->real^K) x - f x) IN lspace (:real^M) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  USE_THEN "fb" (fun th ->
    STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(\x. (f:real^M->real^K) x - g x) IN lspace (:real^M) (&2)`)) THEN
    STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(f:real^M->real^K) IN lspace (:real^M) (&2)`)) THEN
    STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(g:real^M->real^K) IN lspace (:real^M) (&2)`))) THEN
  MP_TAC(ISPECL [`\x. wan_dpart k (a:real^M->real) x`; `Bd:real`;
                 `\x. (g:real^M->real^K) x - f x`] WAN_LNORM2_MUL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. wan_dpart k (a:real^M->real) x % (f:real^M->real^K) x) IN lspace (:real^M) (&2) /\
    (\x. wan_dpart k (a:real^M->real) x % (g:real^M->real^K) x) IN lspace (:real^M) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `Bd:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. wan_fcomm k (a:real^M->real) e g x - wan_dpart k a x % (g:real^M->real^K) x)
      IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. wan_fcomm k (a:real^M->real) e (f:real^M->real^K) x - wan_dpart k a x % f x) =
    (\x. wan_fcomm k a e (\x. f x - g x) x +
         (\x. wan_fcomm k a e g x - wan_dpart k a x % g x) x +
         (\x. wan_dpart k a x % (g x - f x)) x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    ASM_SIMP_TAC[WAN_FCOMM_SUB; WAN_L2_LLOC] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`wan_fcomm k (a:real^M->real) e (\x. (f:real^M->real^K) x - g x)`;
    `\x. wan_fcomm k (a:real^M->real) e (g:real^M->real^K) x - wan_dpart k a x % g x`;
    `\x. wan_dpart k (a:real^M->real) x % ((g:real^M->real^K) x - f x)`]
   WAN_LNORM2_TRIANGLE3) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lnorm (:real^M) (&2) (\x. (f:real^M->real^K) x - g x) =
    lnorm (:real^M) (&2) (\x. g x - f x)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LNORM_NEG] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    let c = concl th in is_binary "real_le" c &&
      (free_in `L:real` c || free_in `Bd:real` c)))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let WAN_FCOMM_L2C = prove
 (`!(a:real^M->real) L Ba Bd (h:real^M->real^K) c k.
     smooth_map_on (:real^M) (\x. lift(a x)) /\ &0 <= L /\
     (!x y. abs(a x - a y) <= L * norm(x - y)) /\
     (!x. abs(a x) <= Ba) /\ (!x. abs(wan_dpart k a x) <= Bd) /\
     compact c /\ (!x. ~(x IN c) ==> h x = vec 0) /\ h IN lspace (:real^M) (&2)
     ==> wan_l2c (\n. wan_fcomm k a (inv(&n + &1)) h) (\x. wan_dpart k a x % h x)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `D:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fb"))
   (ISPEC `k:num` (INST_TYPE [`:M`,`:M`; `:K`,`:K`] WAN_FCOMM_BOUND)) THEN
  SUBGOAL_THEN
   `(\x. lift((a:real^M->real) x)) continuous_on (:real^M) /\
    (\x. lift(wan_dpart k (a:real^M->real) x)) continuous_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; WAN_DPART_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^M` o
      check (free_in `Bd:real` o concl)) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c1 = {x + y:real^M | x IN c /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact (c1:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. smooth_map_on (:real^M) (wan_moll (inv(&m + &1)) (h:real^M->real^K)) /\
        (!x. ~(x IN c1) ==> wan_moll (inv(&m + &1)) h x = vec 0) /\
        wan_moll (inv(&m + &1)) h IN lspace (:real^M) (&2)`
  (LABEL_TAC "hm") THENL
   [GEN_TAC THEN ASM_SIMP_TAC[WAN_MOLL_SMOOTH; WAN_L2_LLOC; WAN_INV_N1_POS; WAN_MOLL_L2] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&m + &1)`; `h:real^M->real^K`; `c:real^M->bool`]
                  WAN_MOLL_SUPPORT) THEN
    ASM_REWRITE_TAC[WAN_INV_N1_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^M) IN c1)` THEN EXPAND_TAC "c1" THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^M` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^M` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN MP_TAC(SPEC `m:num` WAN_INV_N1_BOUNDS) THEN
    MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> !f:real^M->real^K.
              f IN lspace (:real^M) (&2)
              ==> wan_fcomm k (a:real^M->real) e f IN lspace (:real^M) (&2) /\
                  lnorm (:real^M) (&2) (wan_fcomm k a e f) <=
                  L * D * lnorm (:real^M) (&2) f`
  (LABEL_TAC "fb1") THENL
   [GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "fb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. wan_dpart k (a:real^M->real) x % (h:real^M->real^K) x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `Bd:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[wan_l2c] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN USE_THEN "fb1" (MP_TAC o SPEC `inv(&n + &1)`) THEN
    REWRITE_TAC[WAN_INV_N1_POS] THEN DISCH_THEN(MP_TAC o SPEC `h:real^M->real^K`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_DENSITY_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`\m n. lnorm (:real^M) (&2)
             (\x. wan_fcomm k (a:real^M->real) (inv(&n + &1))
                    (wan_moll (inv(&m + &1)) (h:real^M->real^K)) x -
                  wan_dpart k a x % wan_moll (inv(&m + &1)) h x)`;
    `\m. lnorm (:real^M) (&2) (\x. wan_moll (inv(&m + &1)) (h:real^M->real^K) x - h x)`;
    `L * D + Bd`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL];
    MP_TAC(ISPECL [`h:real^M->real^K`; `c:real^M->bool`] WAN_MOLL_SEQ_L2C) THEN
    ASM_REWRITE_TAC[wan_l2c] THEN SIMP_TAC[];
    X_GEN_TAC `m:num` THEN
    USE_THEN "hm" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
    MP_TAC(ISPECL [`a:real^M->real`; `Ba:real`; `Bd:real`;
                   `wan_moll (inv(&m + &1)) (h:real^M->real^K)`; `c1:real^M->bool`;
                   `k:num`] WAN_FCOMM_SMOOTH) THEN
    ASM_REWRITE_TAC[wan_l2c] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    USE_THEN "hm" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ &0 <= y /\ &0 <= z /\ x <= C * y + z
      ==> abs x <= C * abs y + abs z`) THEN
    REWRITE_TAC[WAN_LNORM2_POS] THEN MATCH_MP_TAC WAN_FCOMM_SPLIT THEN
    ASM_REWRITE_TAC[WAN_INV_N1_POS] THEN
    TRY(USE_THEN "fb1" MATCH_MP_TAC THEN REWRITE_TAC[WAN_INV_N1_POS])]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of a mollifier commutator; its convergence to 0.              *)
(* ------------------------------------------------------------------------- *)

let WAN_SMOOTH_DIFFERENTIABLE = prove
 (`!(f:real^M->real^N) x. smooth_map_on (:real^M) f ==> f differentiable (at x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let WAN_MCOMM_PARTIAL = prove
 (`!e (a:real^M->real) (h:real^M->real^K) k z.
     &0 < e /\ smooth_map_on (:real^M) (\x. lift(a x)) /\ wan_lloc (:real^M) h
     ==> partial_derivative k (\x. wan_moll e (\y. a y % h y) x - a x % wan_moll e h x) z =
         wan_fcomm k a e h z - wan_dpart k a z % wan_moll e h z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^M) (\y. (a:real^M->real) y % (h:real^M->real^K) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^M) (wan_moll e (\y. (a:real^M->real) y % (h:real^M->real^K) y)) /\
    smooth_map_on (:real^M) (wan_moll e (h:real^M->real^K)) /\
    smooth_map_on (:real^M) (\x. (a:real^M->real) x % wan_moll e (h:real^M->real^K) x)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_MOLL_SMOOTH] THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN
    ASM_SIMP_TAC[WAN_MOLL_SMOOTH; ETA_AX];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_SUB o lhand o snd) THEN
  ASM_SIMP_TAC[WAN_SMOOTH_DIFFERENTIABLE; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:real^M->real`; `wan_moll e (h:real^M->real^K)`; `k:num`; `z:real^M`]
                WAN_PD_DROPMUL) THEN
  ASM_SIMP_TAC[WAN_MOLL_SMOOTH] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[WAN_MOLL_PARTIAL; wan_fcomm] THEN
  REWRITE_TAC[wan_dpart; partial_derivative] THEN
  MATCH_ACCEPT_TAC(VECTOR_ARITH `x - (y + z):real^N = (x - y) - z`));;

let WAN_MCOMM_D_L2C = prove
 (`!(a:real^M->real) L Ba Bd (h:real^M->real^K) c k.
     smooth_map_on (:real^M) (\x. lift(a x)) /\ &0 <= L /\
     (!x y. abs(a x - a y) <= L * norm(x - y)) /\
     (!x. abs(a x) <= Ba) /\ (!x. abs(wan_dpart k a x) <= Bd) /\
     compact c /\ (!x. ~(x IN c) ==> h x = vec 0) /\ h IN lspace (:real^M) (&2)
     ==> wan_l2c (\n. partial_derivative k
                        (\x. wan_moll (inv(&n + &1)) (\y. a y % h y) x -
                             a x % wan_moll (inv(&n + &1)) h x))
                 (\x. vec 0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WAN_L2C_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n x. wan_fcomm k (a:real^M->real) (inv(&n + &1)) (h:real^M->real^K) x -
           wan_dpart k a x % wan_moll (inv(&n + &1)) h x`;
    `\x:real^M. vec 0:real^K`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\n. wan_fcomm k (a:real^M->real) (inv(&n + &1)) (h:real^M->real^K)`;
                   `\n x. wan_dpart k (a:real^M->real) x %
                          wan_moll (inv(&n + &1)) (h:real^M->real^K) x`;
                   `\x. wan_dpart k (a:real^M->real) x % (h:real^M->real^K) x`]
                  WAN_L2C_SUB0) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_FCOMM_L2C THEN
      MAP_EVERY EXISTS_TAC [`L:real`; `Ba:real`; `Bd:real`; `c:real^M->bool`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\n. wan_moll (inv(&n + &1)) (h:real^M->real^K)`; `h:real^M->real^K`;
                     `wan_dpart k (a:real^M->real)`; `Bd:real`] WAN_L2C_MUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[WAN_DPART_SMOOTH; ETA_AX] THEN
      MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `c:real^M->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC WAN_MCOMM_PARTIAL THEN
    ASM_SIMP_TAC[WAN_INV_N1_POS; WAN_L2_LLOC]]);;

(* ========================================================================= *)
(* The mollified equation.  Testing the weak form                           *)
(* wan_gweak with y |-> wan_mke e (z - y) shows that J_e v solves the       *)
(* classical equation wan_ceq with explicit data.                            *)
(* ========================================================================= *)

let WAN_LLOC_VSUM = prove
 (`!(s:real^M->bool) (u:A->real^M->real^K) t.
     FINITE t /\ (!i. i IN t ==> wan_lloc s (u i))
     ==> wan_lloc s (\x. vsum t (\i. u i x))`,
  REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN ASM_SIMP_TAC[]);;

let WAN_REFLECT_PAIRING = prove
 (`!(k:real^M->real) (u:real^M->real^K) i z.
     wan_test (:real^M) k /\ wan_lloc (:real^M) u
     ==> (\y. wan_dpart i (\y. k(z - y)) y % u y) integrable_on (:real^M) /\
         integral (:real^M) (\y. wan_dpart i (\y. k(z - y)) y % u y) =
         --(wan_kconv (wan_dpart i k) u z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_test (:real^M) (\y. (k:real^M->real)(z - y))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_TEST_UNIV_REFLECT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`(:real^M)`; `\y. (k:real^M->real)(z - y)`; `u:real^M->real^K`]
                  WAN_TEST_PAIRING) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[WAN_REFLECT_DPART; VECTOR_MUL_LNEG; wan_kconv] THEN
    MATCH_MP_TAC INTEGRAL_NEG THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_TEST_DPART_TEST]]);;

let WAN_GWEAK_MOLL_EQN = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f g (v:real^(N,1)finite_sum->real^1) K H R e.
     &0 < e /\
     (!i y. H i y = vsum(1..dimindex(:N)) (\j. a y$i$j % K j y) + g i y) /\
     (!y. R y = vsum(1..dimindex(:N)) (\i. b y$i % K i y) + c y % v y + f y) /\
     wan_lloc (:real^(N,1)finite_sum) v /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_lloc (:real^(N,1)finite_sum) (H i)) /\
     wan_lloc (:real^(N,1)finite_sum) R /\
     wan_gweak a b c f g v K
     ==> !z. partial_derivative (dimindex(:N) + 1) (wan_moll e v) z =
             vsum(1..dimindex(:N)) (\i. partial_derivative i (wan_moll e (H i)) z) +
             wan_moll e R z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H")
   (CONJUNCTS_THEN2 (LABEL_TAC "R") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gw"))))))) THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN USE_THEN "gw" MP_TAC THEN
  SUBGOAL_THEN `wan_test (:real^(N,1)finite_sum) (\y. wan_mke e (z - y))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_TEST_UNIV_REFLECT; WAN_MKE_TEST]; ALL_TAC] THEN
  REWRITE_TAC[wan_gweak] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:real^(N,1)finite_sum. wan_mke e (z - y)`) THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "H" (fun th -> REWRITE_TAC[GSYM th]) THEN
  REMOVE_THEN "R" (fun th -> REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN
   `!i (u:real^(N,1)finite_sum->real^1).
      wan_lloc (:real^(N,1)finite_sum) u
      ==> (\y. wan_dpart i (\y. wan_mke e (z - y)) y % u y)
            integrable_on (:real^(N,1)finite_sum) /\
          integral (:real^(N,1)finite_sum)
            (\y. wan_dpart i (\y. wan_mke e (z - y)) y % u y) =
          --(partial_derivative i (wan_moll e u) z)`
  (LABEL_TAC "rp") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[WAN_MOLL_PARTIAL] THEN
    MATCH_MP_TAC WAN_REFLECT_PAIRING THEN ASM_SIMP_TAC[WAN_MKE_TEST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. wan_mke e (z - y) % (R:real^(N,1)finite_sum->real^1) y)
      integrable_on (:real^(N,1)finite_sum)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`(:real^(N,1)finite_sum)`; `\y:real^(N,1)finite_sum. wan_mke e (z - y)`;
                   `R:real^(N,1)finite_sum->real^1`] WAN_TEST_PAIRING) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i IN 1..dimindex(:N)
         ==> (\y. wan_dpart i (\y. wan_mke e (z - y)) y %
                  (H:num->real^(N,1)finite_sum->real^1) i y)
               integrable_on (:real^(N,1)finite_sum)) /\
    (\y. wan_dpart (dimindex(:N) + 1) (\y. wan_mke e (z - y)) y %
         (v:real^(N,1)finite_sum->real^1) y)
      integrable_on (:real^(N,1)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      USE_THEN "rp" (fun th -> MP_TAC(SPECL [`i:num`; `(H:num->real^(N,1)finite_sum->real^1) i`] th)) THEN
      ASM_SIMP_TAC[];
      USE_THEN "rp" (fun th -> MP_TAC(SPECL [`dimindex(:N) + 1`; `v:real^(N,1)finite_sum->real^1`] th)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y. wan_dpart (dimindex(:N) + 1) (\y. wan_mke e (z - y)) y %
         (v:real^(N,1)finite_sum->real^1) y -
         vsum(1..dimindex(:N))
           (\i. wan_dpart i (\y. wan_mke e (z - y)) y %
                (H:num->real^(N,1)finite_sum->real^1) i y)`;
    `\y. wan_mke e (z - y) % (R:real^(N,1)finite_sum->real^1) y`;
    `(:real^(N,1)finite_sum)`] INTEGRAL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\i y. wan_dpart i (\y. wan_mke e (z - y)) y %
                          (H:num->real^(N,1)finite_sum->real^1) i y`;
                   `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRABLE_VSUM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\y. wan_dpart (dimindex(:N) + 1) (\y. wan_mke e (z - y)) y %
         (v:real^(N,1)finite_sum->real^1) y`;
    `\y. vsum(1..dimindex(:N))
           (\i. wan_dpart i (\y. wan_mke e (z - y)) y %
                (H:num->real^(N,1)finite_sum->real^1) i y)`;
    `(:real^(N,1)finite_sum)`] INTEGRAL_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\i y. wan_dpart i (\y. wan_mke e (z - y)) y %
                          (H:num->real^(N,1)finite_sum->real^1) i y`;
                   `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRABLE_VSUM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\i y. wan_dpart i (\y. wan_mke e (z - y)) y %
                        (H:num->real^(N,1)finite_sum->real^1) i y`;
                 `(:real^(N,1)finite_sum)`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. integral (:real^(N,1)finite_sum)
             (\y. wan_dpart i (\y. wan_mke e (z - y)) y %
                  (H:num->real^(N,1)finite_sum->real^1) i y)) =
    vsum(1..dimindex(:N)) (\i. --(partial_derivative i (wan_moll e (H i)) z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    USE_THEN "rp" (fun th -> MP_TAC(SPECL [`i:num`; `(H:num->real^(N,1)finite_sum->real^1) i`] th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "rp" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP
    (SPECL [`dimindex(:N) + 1`; `v:real^(N,1)finite_sum->real^1`] th)
    (ASSUME `wan_lloc (:real^(N,1)finite_sum) (v:real^(N,1)finite_sum->real^1)`)))) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VSUM_NEG; GSYM wan_kconv; GSYM wan_moll] THEN
  MATCH_ACCEPT_TAC(VECTOR_ARITH `--x - --s + w:real^N = vec 0 ==> x = s + w`));;

let WAN_GWEAK_MOLL_CEQ = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f g (v:real^(N,1)finite_sum->real^1) K e.
     &0 < e /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\w. lift(a w$i$j)) continuous_on (:real^(N,1)finite_sum)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\w. lift(b w$i)) continuous_on (:real^(N,1)finite_sum)) /\
     (\w. lift(c w)) continuous_on (:real^(N,1)finite_sum) /\
     wan_lloc (:real^(N,1)finite_sum) v /\ wan_lloc (:real^(N,1)finite_sum) f /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_lloc (:real^(N,1)finite_sum) (g i)) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_wpd (:real^(N,1)finite_sum) j v (K j)) /\
     wan_gweak a b c f g v K
     ==> wan_ceq a b c
           (\w. wan_moll e f w +
                vsum(1..dimindex(:N))
                  (\i. wan_moll e (\y. b y$i % K i y) w - b w$i % wan_moll e (K i) w) +
                (wan_moll e (\y. c y % v y) w - c w % wan_moll e v w))
           (\i w. wan_moll e (g i) w +
                  vsum(1..dimindex(:N))
                    (\j. wan_moll e (\y. a y$i$j % K j y) w - a w$i$j % wan_moll e (K j) w))
           (wan_moll e v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_lloc (:real^(N,1)finite_sum) ((K:num->real^(N,1)finite_sum->real^1) j)`
  ASSUME_TAC THENL [ASM_MESON_TAC[wan_wpd]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> wan_lloc (:real^(N,1)finite_sum)
                 (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                      (K:num->real^(N,1)finite_sum->real^1) j y)) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum)
               (\y. (b:real^(N,1)finite_sum->real^N) y$i % K i y)) /\
    wan_lloc (:real^(N,1)finite_sum)
      (\y. (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. 1 <= i /\ i <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum)
               (\y. vsum(1..dimindex(:N))
                      (\j. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                           (K:num->real^(N,1)finite_sum->real^1) j y))) /\
    wan_lloc (:real^(N,1)finite_sum)
      (\y. vsum(1..dimindex(:N))
             (\i. (b:real^(N,1)finite_sum->real^N) y$i %
                  (K:num->real^(N,1)finite_sum->real^1) i y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_LLOC_VSUM THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
    `c:real^(N,1)finite_sum->real`; `f:real^(N,1)finite_sum->real^1`;
    `g:num->real^(N,1)finite_sum->real^1`; `v:real^(N,1)finite_sum->real^1`;
    `K:num->real^(N,1)finite_sum->real^1`;
    `\i y. vsum(1..dimindex(:N))
             (\j. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                  (K:num->real^(N,1)finite_sum->real^1) j y) +
           (g:num->real^(N,1)finite_sum->real^1) i y`;
    `\y. vsum(1..dimindex(:N))
           (\i. (b:real^(N,1)finite_sum->real^N) y$i %
                (K:num->real^(N,1)finite_sum->real^1) i y) +
         (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y +
         (f:real^(N,1)finite_sum->real^1) y`;
    `e:real`] WAN_GWEAK_MOLL_EQN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LLOC_ADD THEN ASM_SIMP_TAC[ETA_AX];
      REPEAT(MATCH_MP_TAC WAN_LLOC_ADD THEN CONJ_TAC) THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "eqn") THEN
  SUBGOAL_THEN
   `!j w. 1 <= j /\ j <= dimindex(:N)
          ==> partial_derivative j (wan_moll e (v:real^(N,1)finite_sum->real^1)) w =
              wan_moll e ((K:num->real^(N,1)finite_sum->real^1) j) w`
  (LABEL_TAC "pdj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_MOLL_WPD THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\w. vsum(1..dimindex(:N))
                   (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                        partial_derivative j (wan_moll e (v:real^(N,1)finite_sum->real^1)) w) +
                 (wan_moll e ((g:num->real^(N,1)finite_sum->real^1) i) w +
                  vsum(1..dimindex(:N))
                    (\j. wan_moll e (\y. a y$i$j % (K:num->real^(N,1)finite_sum->real^1) j y) w -
                         a w$i$j % wan_moll e (K j) w))) =
            wan_moll e (\y. vsum(1..dimindex(:N)) (\j. a y$i$j % K j y) + g i y)`
  (LABEL_TAC "S1") THENL
   [GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `w:real^(N,1)finite_sum` THEN
    SUBGOAL_THEN
     `vsum(1..dimindex(:N))
        (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
             partial_derivative j (wan_moll e (v:real^(N,1)finite_sum->real^1)) w) =
      vsum(1..dimindex(:N))
        (\j. a w$i$j % wan_moll e ((K:num->real^(N,1)finite_sum->real^1) j) w)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN USE_THEN "pdj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real`;
                   `\y. vsum(1..dimindex(:N))
                          (\j. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                               (K:num->real^(N,1)finite_sum->real^1) j y)`;
                   `(g:num->real^(N,1)finite_sum->real^1) i`;
                   `w:real^(N,1)finite_sum`] WAN_MOLL_ADD) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`e:real`;
                   `\j y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                          (K:num->real^(N,1)finite_sum->real^1) j y`;
                   `1..dimindex(:N)`; `w:real^(N,1)finite_sum`] WAN_MOLL_VSUM) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VSUM_SUB_NUMSEG] THEN
    MATCH_ACCEPT_TAC(VECTOR_ARITH `(x:real^N) + (y + (z - x)) = z + y`);
    ALL_TAC] THEN
  REWRITE_TAC[wan_ceq] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
  USE_THEN "eqn" (fun th -> REWRITE_TAC[SPEC `z:real^(N,1)finite_sum` th]) THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (\w. vsum(1..dimindex(:N))
                    (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                         partial_derivative j (wan_moll e (v:real^(N,1)finite_sum->real^1)) w) +
                  (wan_moll e ((g:num->real^(N,1)finite_sum->real^1) i) w +
                   vsum(1..dimindex(:N))
                     (\j. wan_moll e (\y. a y$i$j % (K:num->real^(N,1)finite_sum->real^1) j y) w -
                          a w$i$j % wan_moll e (K j) w))) z) =
    vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (wan_moll e (\y. vsum(1..dimindex(:N)) (\j. a y$i$j % K j y) + g i y)) z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "S1" (fun th -> REWRITE_TAC[MP (SPEC `i:num` th)
      (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`))]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. (b:real^(N,1)finite_sum->real^N) z$i %
           partial_derivative i (wan_moll e (v:real^(N,1)finite_sum->real^1)) z) =
    vsum(1..dimindex(:N))
      (\i. b z$i % wan_moll e ((K:num->real^(N,1)finite_sum->real^1) i) z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN USE_THEN "pdj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_moll e
      (\y. vsum(1..dimindex(:N))
             (\i. (b:real^(N,1)finite_sum->real^N) y$i %
                  (K:num->real^(N,1)finite_sum->real^1) i y) +
           (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y +
           (f:real^(N,1)finite_sum->real^1) y) z =
    vsum(1..dimindex(:N)) (\i. wan_moll e (\y. b y$i % K i y) z) +
    wan_moll e (\y. c y % v y) z + wan_moll e f z`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`e:real`;
                   `\y. vsum(1..dimindex(:N))
                          (\i. (b:real^(N,1)finite_sum->real^N) y$i %
                               (K:num->real^(N,1)finite_sum->real^1) i y)`;
                   `\y. (c:real^(N,1)finite_sum->real) y %
                        (v:real^(N,1)finite_sum->real^1) y +
                        (f:real^(N,1)finite_sum->real^1) y`;
                   `z:real^(N,1)finite_sum`] WAN_MOLL_ADD) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LLOC_ADD THEN ASM_REWRITE_TAC[ETA_AX];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`e:real`;
                   `\y. (c:real^(N,1)finite_sum->real) y %
                        (v:real^(N,1)finite_sum->real^1) y`;
                   `f:real^(N,1)finite_sum->real^1`;
                   `z:real^(N,1)finite_sum`] WAN_MOLL_ADD) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`e:real`;
                   `\i y. (b:real^(N,1)finite_sum->real^N) y$i %
                          (K:num->real^(N,1)finite_sum->real^1) i y`;
                   `1..dimindex(:N)`; `z:real^(N,1)finite_sum`] WAN_MOLL_VSUM) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_SUB_NUMSEG] THEN
  MATCH_ACCEPT_TAC(VECTOR_ARITH
   `(p:real^N) + (x + y + w) = p + q + r + (w + (x - q) + (y - r))`));;

(* ========================================================================= *)
(* Moving a derivative from f into g in wan_ceq, Cauchy                     *)
(* sequences from the level-0 energy estimate, weak derivatives and weak    *)
(* equations in the L^2 limit, restriction of limits to a compact set.      *)
(* ========================================================================= *)

let WAN_CEQ_MOVE = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f0 f1 g (v:real^(N,1)finite_sum->real^1) k.
     1 <= k /\ k <= dimindex(:N) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     smooth_map_on (:real^(N,1)finite_sum) v /\ smooth_map_on (:real^(N,1)finite_sum) f0 /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> smooth_map_on (:real^(N,1)finite_sum) (g i)) /\
     wan_ceq a b c (\z. partial_derivative k f0 z + f1 z) g v
     ==> wan_ceq a b c f1 (\i z. g i z + (if i = k then f0 z else vec 0)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wan_ceq (a:real^(N,1)finite_sum->real^N^N) b c
                 (\z. partial_derivative k (f0:real^(N,1)finite_sum->real^1) z + f1 z) g
                 (v:real^(N,1)finite_sum->real^1)` THEN
  REWRITE_TAC[wan_ceq] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum)
              (\w. vsum(1..dimindex(:N))
                     (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                          partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
                   (g:num->real^(N,1)finite_sum->real^1) i w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN MATCH_MP_TAC WAN_SMOOTH_VSUM THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN
    ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (\w. vsum(1..dimindex(:N))
                    (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                         partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
                  ((g:num->real^(N,1)finite_sum->real^1) i w +
                   (if i = k then (f0:real^(N,1)finite_sum->real^1) w else vec 0))) z) =
    vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (\w. vsum(1..dimindex(:N)) (\j. a w$i$j % partial_derivative j v w) + g i w) z) +
    partial_derivative k f0 z`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `!i. 1 <= i /\ i <= dimindex(:N)
          ==> partial_derivative i
               (\w. vsum(1..dimindex(:N))
                      (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                           partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
                    ((g:num->real^(N,1)finite_sum->real^1) i w +
                     (if i = k then (f0:real^(N,1)finite_sum->real^1) w else vec 0))) z =
              partial_derivative i
               (\w. vsum(1..dimindex(:N)) (\j. a w$i$j % partial_derivative j v w) + g i w) z +
              (if i = k then partial_derivative k f0 z else vec 0)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `(\w. vsum(1..dimindex(:N))
               (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                    partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
             ((g:num->real^(N,1)finite_sum->real^1) i w +
              (if i = k then (f0:real^(N,1)finite_sum->real^1) w else vec 0))) =
        (\w. (\w. vsum(1..dimindex(:N)) (\j. a w$i$j % partial_derivative j v w) + g i w) w +
             (\w. if i = k then f0 w else vec 0) w)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_ADD o lhand o snd) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC WAN_SMOOTH_DIFFERENTIABLE THEN ASM_SIMP_TAC[] THEN
        ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[ETA_AX; SMOOTH_MAP_ON_CONST];
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[ETA_AX; PARTIAL_DERIVATIVE_CONST]];
      ALL_TAC] THEN
    MATCH_MP_TAC(VECTOR_ARITH `(x:real^N) = y + z ==> x = y + z`) THEN
    TRANS_TAC EQ_TRANS
     `vsum(1..dimindex(:N))
        (\i. partial_derivative i
               (\w. vsum(1..dimindex(:N))
                      (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                           partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
                    (g:num->real^(N,1)finite_sum->real^1) i w) z +
             (if i = k then partial_derivative k (f0:real^(N,1)finite_sum->real^1) z
              else vec 0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[VSUM_ADD_NUMSEG; VSUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]];
    MATCH_ACCEPT_TAC(VECTOR_ARITH
     `(s:real^N) + b + c + p + f = (s + p) + b + c + f`)]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy sequences from the level-0 energy estimate.                       *)
(* ------------------------------------------------------------------------- *)

let WAN_SUM_TERM_LE = prove
 (`!s (f:A->real) i.
     FINITE s /\ i IN s /\ (!j. j IN s ==> &0 <= f j) ==> f i <= sum s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `s:A->bool`; `i:A`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sum (s DELETE (i:A)) f` MP_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_DELETE]; REAL_ARITH_TAC]);;

let WAN_SMALL_SQ_BOUND = prove
 (`!B s eps.
     &0 <= B /\ &0 < eps /\ &0 <= s /\ s < &2 * min (&1) (eps / (&8 * (B + &1)))
     ==> B * s pow 2 < eps`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = min (&1) (eps / (&8 * (B + &1)))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 /\ d * (&8 * (B + &1)) <= eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `(eps / (&8 * (B + &1))) * (&8 * (B + &1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ARITH `&0 <= B ==> ~(&8 * (B + &1) = &0)`;
                     REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 <= &4 * d` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&2 * d) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `d * d <= d * &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `B * s pow 2 <= B * (&4 * d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= B * d` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WAN_CAUCHY_FROM_BOUND = prove
 (`!(u:num->real^M->real^K) (e:num->real) B.
     (!n. u n IN lspace (:real^M) (&2)) /\ (e ---> &0) sequentially /\
     (!n. &0 <= e n) /\ &0 <= B /\
     (!m n. drop(integral (:real^M) (\x. lift(norm(u m x - u n x) pow 2))) <=
            B * (e m + e n) pow 2)
     ==> ?v. wan_l2c u v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MATCH_MP_TAC WAN_L2C_CAUCHY THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) (eps / (&8 * (B + &1)))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN DISCH_THEN(LABEL_TAC "M") THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  TRANS_TAC REAL_LET_TRANS `B * ((e:num->real) m + e n) pow 2` THEN
  USE_THEN "bd" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC WAN_SMALL_SQ_BOUND THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "M" (fun th -> MP_TAC(MP (SPEC `m:num` th) (ASSUME `M:num <= m`)) THEN
                          MP_TAC(MP (SPEC `n:num` th) (ASSUME `M:num <= n`))) THEN
  MP_TAC(SPEC `m:num` (ASSUME `!n. &0 <= (e:num->real) n`)) THEN
  MP_TAC(SPEC `n:num` (ASSUME `!n. &0 <= (e:num->real) n`)) THEN
  REAL_ARITH_TAC);;

let WAN_L2C_PAIR_SQ_BOUND = prove
 (`!(u:num->real^M->real^K) v m n em en.
     wan_l2c u v /\
     lnorm (:real^M) (&2) (\x. u m x - v x) <= em /\
     lnorm (:real^M) (&2) (\x. u n x - v x) <= en
     ==> drop(integral (:real^M) (\x. lift(norm(u m x - u n x) pow 2))) <= (em + en) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[wan_l2c] (ASSUME `wan_l2c (u:num->real^M->real^K) v`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (u:num->real^M->real^K) m x - u n x) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(BETA_RULE(MATCH_MP WAN_LNORM2_SQ th))]) THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[WAN_LNORM2_POS] THEN
  MP_TAC(ISPECL [`(u:num->real^M->real^K) m`; `(u:num->real^M->real^K) n`;
                 `v:real^M->real^K`] WAN_LNORM2_TRIANGLE_SUB) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let wan_e0 = new_definition
 `wan_e0 (a:real^(N,1)finite_sum->real^N^N) b c C <=>
    !(v:real^(N,1)finite_sum->real^1) f g k.
       compact k /\ smooth_map_on (:real^(N,1)finite_sum) v /\
       (!z. ~(z IN k) ==> v z = vec 0) /\
       f continuous_on (:real^(N,1)finite_sum) /\ (!z. ~(z IN k) ==> f z = vec 0) /\
       (!i. 1 <= i /\ i <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (g i) /\
                (!z. ~(z IN k) ==> g i z = vec 0)) /\
       wan_ceq a b c f g v
       ==> sum(1..dimindex(:N))
             (\i. drop(integral (:real^(N,1)finite_sum)
                        (\z. lift(norm(partial_derivative i v z) pow 2)))) <=
           C * (drop(integral (:real^(N,1)finite_sum) (\z. lift(norm(v z) pow 2))) +
                drop(integral (:real^(N,1)finite_sum) (\z. lift(norm(f z) pow 2))) +
                sum(1..dimindex(:N))
                  (\i. drop(integral (:real^(N,1)finite_sum)
                             (\z. lift(norm(g i z) pow 2)))))`;;

let WAN_ENERGY0_E0 = prove
 (`!lam Kb Kc (a:real^(N,1)finite_sum->real^N^N) b c.
     &0 < lam /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\w. lift(b w$i)) continuous_on (:real^(N,1)finite_sum)) /\
     (\w. lift(c w)) continuous_on (:real^(N,1)finite_sum) /\
     (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi)) /\
     (!z i. 1 <= i /\ i <= dimindex(:N) ==> abs(b z$i) <= Kb) /\
     (!z. abs(c z) <= Kc)
     ==> ?C. &0 < C /\ wan_e0 a b c C`,
  REWRITE_TAC[wan_e0; WAN_ENERGY0]);;

let WAN_ERR3 = prove
 (`!x y (s:num->real) N.
     &0 <= x /\ &0 <= y /\ (!i. &0 <= s i)
     ==> x <= x + y + sum(1..N) s /\ y <= x + y + sum(1..N) s /\
         !j. 1 <= j /\ j <= N ==> s j <= x + y + sum(1..N) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sum(1..N) (s:num->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`1..N`; `s:num->real`; `j:num`] WAN_SUM_TERM_LE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ASM_REAL_ARITH_TAC);;

let WAN_ENERGY0_CAUCHY = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c C (vs:num->real^(N,1)finite_sum->real^1)
    fs gs k1 v0 f0 g0 i.
     wan_e0 a b c C /\ &0 < C /\ compact k1 /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!n. smooth_map_on (:real^(N,1)finite_sum) (vs n) /\
          (!z. ~(z IN k1) ==> vs n z = vec 0) /\
          smooth_map_on (:real^(N,1)finite_sum) (fs n) /\
          (!z. ~(z IN k1) ==> fs n z = vec 0) /\
          (!i. 1 <= i /\ i <= dimindex(:N)
               ==> smooth_map_on (:real^(N,1)finite_sum) (gs n i) /\
                   (!z. ~(z IN k1) ==> gs n i z = vec 0)) /\
          wan_ceq a b c (fs n) (gs n) (vs n)) /\
     wan_l2c vs v0 /\ wan_l2c fs f0 /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2c (\n. gs n i) (g0 i)) /\
     1 <= i /\ i <= dimindex(:N)
     ==> ?U. wan_l2c (\n. partial_derivative i (vs n)) U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E0") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "seq") (CONJUNCTS_THEN2 (LABEL_TAC "vc")
   (CONJUNCTS_THEN2 (LABEL_TAC "fc") (CONJUNCTS_THEN2 (LABEL_TAC "gc")
    STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN
   `!j n. partial_derivative j ((vs:num->real^(N,1)finite_sum->real^1) n)
            IN lspace (:real^(N,1)finite_sum) (&2)`
  (LABEL_TAC "pdl") THENL
   [REPEAT GEN_TAC THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k1:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PEN_PSUPPORT THEN
      EXISTS_TAC `k1:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_CAUCHY_FROM_BOUND THEN
  EXISTS_TAC
   `\n. lnorm (:real^(N,1)finite_sum) (&2)
          (\x. (vs:num->real^(N,1)finite_sum->real^1) n x - v0 x) +
        lnorm (:real^(N,1)finite_sum) (&2)
          (\x. (fs:num->real^(N,1)finite_sum->real^1) n x - f0 x) +
        sum(1..dimindex(:N))
          (\i. lnorm (:real^(N,1)finite_sum) (&2)
                 (\x. (gs:num->num->real^(N,1)finite_sum->real^1) n i x - g0 i x))` THEN
  EXISTS_TAC `C * (&(dimindex(:N)) + &2)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "pdl" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [USE_THEN "vc" (fun th -> REWRITE_TAC[REWRITE_RULE[wan_l2c] th]);
      MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
       [USE_THEN "fc" (fun th -> REWRITE_TAC[REWRITE_RULE[wan_l2c] th]);
        MATCH_MP_TAC REALLIM_NULL_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        USE_THEN "gc" (fun th -> MP_TAC(REWRITE_RULE[wan_l2c] (MP (SPEC `j:num` th)
                                   (ASSUME `1 <= j /\ j <= dimindex(:N)`)))) THEN
        SIMP_TAC[]]];
    GEN_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REWRITE_TAC[WAN_LNORM2_POS] THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[WAN_LNORM2_POS];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  ABBREV_TAC
   `em = lnorm (:real^(N,1)finite_sum) (&2)
           (\x. (vs:num->real^(N,1)finite_sum->real^1) m x - v0 x) +
         lnorm (:real^(N,1)finite_sum) (&2)
           (\x. (fs:num->real^(N,1)finite_sum->real^1) m x - f0 x) +
         sum(1..dimindex(:N))
           (\i. lnorm (:real^(N,1)finite_sum) (&2)
                  (\x. (gs:num->num->real^(N,1)finite_sum->real^1) m i x - g0 i x))` THEN
  ABBREV_TAC
   `en = lnorm (:real^(N,1)finite_sum) (&2)
           (\x. (vs:num->real^(N,1)finite_sum->real^1) n x - v0 x) +
         lnorm (:real^(N,1)finite_sum) (&2)
           (\x. (fs:num->real^(N,1)finite_sum->real^1) n x - f0 x) +
         sum(1..dimindex(:N))
           (\i. lnorm (:real^(N,1)finite_sum) (&2)
                  (\x. (gs:num->num->real^(N,1)finite_sum->real^1) n i x - g0 i x))` THEN
  MP_TAC(ISPECL
   [`lnorm (:real^(N,1)finite_sum) (&2)
       (\x. (vs:num->real^(N,1)finite_sum->real^1) m x - v0 x)`;
    `lnorm (:real^(N,1)finite_sum) (&2)
       (\x. (fs:num->real^(N,1)finite_sum->real^1) m x - f0 x)`;
    `\i. lnorm (:real^(N,1)finite_sum) (&2)
          (\x. (gs:num->num->real^(N,1)finite_sum->real^1) m i x - g0 i x)`;
    `dimindex(:N)`] WAN_ERR3) THEN
  ASM_REWRITE_TAC[WAN_LNORM2_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vm") (CONJUNCTS_THEN2 (LABEL_TAC "fm") (LABEL_TAC "gm"))) THEN
  MP_TAC(ISPECL
   [`lnorm (:real^(N,1)finite_sum) (&2)
       (\x. (vs:num->real^(N,1)finite_sum->real^1) n x - v0 x)`;
    `lnorm (:real^(N,1)finite_sum) (&2)
       (\x. (fs:num->real^(N,1)finite_sum->real^1) n x - f0 x)`;
    `\i. lnorm (:real^(N,1)finite_sum) (&2)
          (\x. (gs:num->num->real^(N,1)finite_sum->real^1) n i x - g0 i x)`;
    `dimindex(:N)`] WAN_ERR3) THEN
  ASM_REWRITE_TAC[WAN_LNORM2_POS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vn") (CONJUNCTS_THEN2 (LABEL_TAC "fn") (LABEL_TAC "gn"))) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
  USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  USE_THEN "E0" (MP_TAC o SPECL
   [`\z. (vs:num->real^(N,1)finite_sum->real^1) m z - vs n z`;
    `\z. (fs:num->real^(N,1)finite_sum->real^1) m z - fs n z`;
    `\i z. (gs:num->num->real^(N,1)finite_sum->real^1) m i z - gs n i z`;
    `k1:real^(N,1)finite_sum->bool`] o REWRITE_RULE[wan_e0]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[VECTOR_SUB_REFL; SMOOTH_MAP_ON_SUB_OPEN; OPEN_UNIV; ETA_AX] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX];
      MATCH_MP_TAC WAN_CEQ_SUB THEN ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j z. partial_derivative j
            (\z. (vs:num->real^(N,1)finite_sum->real^1) m z - vs n z) z =
          partial_derivative j (vs m) z - partial_derivative j (vs n) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_SUB THEN
    ASM_SIMP_TAC[WAN_SMOOTH_DIFFERENTIABLE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `t <= s /\ c <= d ==> s <= c ==> t <= d`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`1..dimindex(:N)`;
      `\j. drop(integral (:real^(N,1)finite_sum)
              (\z. lift(norm(partial_derivative j
                     ((vs:num->real^(N,1)finite_sum->real^1) m) z -
                     partial_derivative j (vs n) z) pow 2)))`;
      `i:num`] WAN_SUM_TERM_LE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_SQINT_POS THEN MATCH_MP_TAC LSPACE_SUB THEN
    USE_THEN "pdl" (fun th -> REWRITE_TAC[th; REAL_POS; ETA_AX]);
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
      (\z. lift(norm((vs:num->real^(N,1)finite_sum->real^1) m z - vs n z) pow 2))) <=
    (em + en) pow 2 /\
    drop(integral (:real^(N,1)finite_sum)
      (\z. lift(norm((fs:num->real^(N,1)finite_sum->real^1) m z - fs n z) pow 2))) <=
    (em + en) pow 2 /\
    sum(1..dimindex(:N))
      (\i. drop(integral (:real^(N,1)finite_sum)
              (\z. lift(norm((gs:num->num->real^(N,1)finite_sum->real^1) m i z - gs n i z)
                         pow 2)))) <=
    &(dimindex(:N)) * (em + en) pow 2`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_L2C_PAIR_SQ_BOUND THEN EXISTS_TAC `v0:real^(N,1)finite_sum->real^1` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_L2C_PAIR_SQ_BOUND THEN EXISTS_TAC `f0:real^(N,1)finite_sum->real^1` THEN
      ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\n. (gs:num->num->real^(N,1)finite_sum->real^1) n j`;
                     `(g0:num->real^(N,1)finite_sum->real^1) j`;
                     `m:num`; `n:num`; `em:real`; `en:real`] WAN_L2C_PAIR_SQ_BOUND) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "gc" (fun th -> REWRITE_TAC[MP (SPEC `j:num` th)
                                 (ASSUME `1 <= j /\ j <= dimindex(:N)`)]) THEN
      USE_THEN "gm" (fun th -> REWRITE_TAC[MP (SPEC `j:num` th)
                                 (ASSUME `1 <= j /\ j <= dimindex(:N)`)]) THEN
      USE_THEN "gn" (fun th -> REWRITE_TAC[MP (SPEC `j:num` th)
                                 (ASSUME `1 <= j /\ j <= dimindex(:N)`)])];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Weak derivatives and weak equations in the L^2 limit.                    *)
(* ------------------------------------------------------------------------- *)

let WAN_L1C_TRANSFORM = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l1c u v ==> (!n x. u' n x = u n x) /\ (!x. v' x = v x) ==> wan_l1c u' v'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `u':num->real^M->real^K = u /\ v':real^M->real^K = v`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

let WAN_L2C_TRANSFORM = prove
 (`!(u:num->real^M->real^K) v u' v'.
     wan_l2c u v ==> (!n x. u' n x = u n x) /\ (!x. v' x = v x) ==> wan_l2c u' v'`,
  MESON_TAC[WAN_L2C_EQ]);;

let WAN_TESTW_PAIR = prove
 (`!(u:num->real^M->real^K) v phi (m:real^M->real).
     wan_l2c u v /\ wan_test (:real^M) phi /\ (\x. lift(m x)) continuous_on (:real^M)
     ==> wan_l1c (\n x. (phi x * m x) % u n x) (\x. (phi x * m x) % v x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC o
    CONJUNCT2 o REWRITE_RULE[wan_test]) THEN
  MATCH_MP_TAC WAN_L2C_PAIR THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN
  ASM_MESON_TAC[WAN_TEST_CONTINUOUS]);;

let WAN_TESTW1_PAIR = prove
 (`!(u:num->real^M->real^K) v phi.
     wan_l2c u v /\ wan_test (:real^M) phi
     ==> wan_l1c (\n x. phi x % u n x) (\x. phi x % v x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC o
    CONJUNCT2 o REWRITE_RULE[wan_test]) THEN
  MATCH_MP_TAC WAN_L2C_PAIR THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[WAN_TEST_CONTINUOUS]);;

let WAN_WPD_LIMIT = prove
 (`!(u:num->real^M->real^1) U U' i.
     (!n. smooth_map_on (:real^M) (u n)) /\
     wan_l2c u U /\ wan_l2c (\n. partial_derivative i (u n)) U'
     ==> wan_wpd (:real^M) i U U'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_wpd] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_L2_LLOC THEN ASM_MESON_TAC[WAN_L2C_MEM];
    MATCH_MP_TAC WAN_L2_LLOC THEN ASM_MESON_TAC[WAN_L2C_MEM];
    ALL_TAC] THEN
  X_GEN_TAC `phi:real^M->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:num->real^M->real^1`; `U:real^M->real^1`;
                 `wan_dpart i (phi:real^M->real)`] WAN_TESTW1_PAIR) THEN
  ASM_SIMP_TAC[WAN_TEST_DPART_TEST] THEN DISCH_THEN(MP_TAC o MATCH_MP WAN_L1C_INTEGRAL) THEN
  MP_TAC(ISPECL [`\n. partial_derivative i ((u:num->real^M->real^1) n)`; `U':real^M->real^1`;
                 `phi:real^M->real`] WAN_TESTW1_PAIR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG o MATCH_MP WAN_L1C_INTEGRAL) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. integral (:real^M) (\x. wan_dpart i phi x % (u:num->real^M->real^1) n x) =
        --(integral (:real^M) (\x. phi x % partial_derivative i (u n) x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_TEST_IBP_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. --(integral (:real^M)
            (\x. phi x % partial_derivative i ((u:num->real^M->real^1) n) x))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

let WAN_GWEAK_LIMIT = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c (fs:num->real^(N,1)finite_sum->real^1)
    (gs:num->num->real^(N,1)finite_sum->real^1) (vs:num->real^(N,1)finite_sum->real^1)
    (Ks:num->num->real^(N,1)finite_sum->real^1) f g v K.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\w. lift(a w$i$j)) continuous_on (:real^(N,1)finite_sum)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\w. lift(b w$i)) continuous_on (:real^(N,1)finite_sum)) /\
     (\w. lift(c w)) continuous_on (:real^(N,1)finite_sum) /\
     wan_l2c vs v /\ wan_l2c fs f /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_l2c (\n. Ks n j) (K j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2c (\n. gs n i) (g i)) /\
     (!n. wan_gweak a b c (fs n) (gs n) (vs n) (Ks n))
     ==> wan_gweak a b c f g v K`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gw")))))))) THEN
  REWRITE_TAC[wan_gweak] THEN
  X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. wan_test (:real^(N,1)finite_sum) (wan_dpart i phi)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_TEST_DPART_TEST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l1c
     (\n z. (wan_dpart (dimindex(:N) + 1) phi z % (vs:num->real^(N,1)finite_sum->real^1) n z -
             vsum(1..dimindex(:N))
               (\i. vsum(1..dimindex(:N))
                      (\j. (wan_dpart i phi z * (a:real^(N,1)finite_sum->real^N^N) z$i$j) %
                           (Ks:num->num->real^(N,1)finite_sum->real^1) n j z) +
                    wan_dpart i phi z % (gs:num->num->real^(N,1)finite_sum->real^1) n i z)) +
            (vsum(1..dimindex(:N))
               (\i. (phi z * (b:real^(N,1)finite_sum->real^N) z$i) % Ks n i z) +
             (phi z * (c:real^(N,1)finite_sum->real) z) % vs n z +
             phi z % (fs:num->real^(N,1)finite_sum->real^1) n z))
     (\z. (wan_dpart (dimindex(:N) + 1) phi z % (v:real^(N,1)finite_sum->real^1) z -
           vsum(1..dimindex(:N))
             (\i. vsum(1..dimindex(:N))
                    (\j. (wan_dpart i phi z * a z$i$j) %
                         (K:num->real^(N,1)finite_sum->real^1) j z) +
                  wan_dpart i phi z % (g:num->real^(N,1)finite_sum->real^1) i z)) +
          (vsum(1..dimindex(:N)) (\i. (phi z * b z$i) % K i z) +
           (phi z * c z) % v z + phi z % (f:real^(N,1)finite_sum->real^1) z))`
  (LABEL_TAC "l1") THENL
   [MATCH_MP_TAC WAN_L1C_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_L1C_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_TESTW1_PAIR THEN ASM_REWRITE_TAC[ETA_AX];
        MATCH_MP_TAC WAN_L1C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC WAN_L1C_ADD THEN CONJ_TAC THENL
         [MATCH_MP_TAC WAN_L1C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`\n. (Ks:num->num->real^(N,1)finite_sum->real^1) n j`;
                         `(K:num->real^(N,1)finite_sum->real^1) j`;
                         `wan_dpart i (phi:real^(N,1)finite_sum->real)`;
                         `\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j`] WAN_TESTW_PAIR) THEN
          ASM_SIMP_TAC[];
          MP_TAC(ISPECL [`\n. (gs:num->num->real^(N,1)finite_sum->real^1) n i`;
                         `(g:num->real^(N,1)finite_sum->real^1) i`;
                         `wan_dpart i (phi:real^(N,1)finite_sum->real)`] WAN_TESTW1_PAIR) THEN
          ASM_SIMP_TAC[]]];
      MATCH_MP_TAC WAN_L1C_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_L1C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`\n. (Ks:num->num->real^(N,1)finite_sum->real^1) n i`;
                       `(K:num->real^(N,1)finite_sum->real^1) i`;
                       `phi:real^(N,1)finite_sum->real`;
                       `\z. (b:real^(N,1)finite_sum->real^N) z$i`] WAN_TESTW_PAIR) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC WAN_L1C_ADD THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`vs:num->real^(N,1)finite_sum->real^1`;
                         `v:real^(N,1)finite_sum->real^1`;
                         `phi:real^(N,1)finite_sum->real`;
                         `c:real^(N,1)finite_sum->real`] WAN_TESTW_PAIR) THEN
          ASM_SIMP_TAC[ETA_AX];
          MATCH_MP_TAC WAN_TESTW1_PAIR THEN ASM_REWRITE_TAC[ETA_AX]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l1c
     (\n z. wan_dpart (dimindex(:N) + 1) phi z % (vs:num->real^(N,1)finite_sum->real^1) n z -
            vsum(1..dimindex(:N))
              (\i. wan_dpart i phi z %
                   (vsum(1..dimindex(:N))
                      (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                           (Ks:num->num->real^(N,1)finite_sum->real^1) n j z) +
                    (gs:num->num->real^(N,1)finite_sum->real^1) n i z)) +
            phi z % (vsum(1..dimindex(:N))
                       (\i. (b:real^(N,1)finite_sum->real^N) z$i % Ks n i z) +
                     (c:real^(N,1)finite_sum->real) z % vs n z +
                     (fs:num->real^(N,1)finite_sum->real^1) n z))
     (\z. wan_dpart (dimindex(:N) + 1) phi z % (v:real^(N,1)finite_sum->real^1) z -
          vsum(1..dimindex(:N))
            (\i. wan_dpart i phi z %
                 (vsum(1..dimindex(:N))
                    (\j. a z$i$j % (K:num->real^(N,1)finite_sum->real^1) j z) +
                  (g:num->real^(N,1)finite_sum->real^1) i z)) +
          phi z % (vsum(1..dimindex(:N)) (\i. b z$i % K i z) +
                   c z % v z + (f:real^(N,1)finite_sum->real^1) z))`
  MP_TAC THENL
   [USE_THEN "l1" (MATCH_MP_TAC o MATCH_MP WAN_L1C_TRANSFORM) THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; GSYM VSUM_LMUL; VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP WAN_L1C_INTEGRAL) THEN
  SUBGOAL_THEN
   `!n. integral (:real^(N,1)finite_sum)
         (\z. wan_dpart (dimindex(:N) + 1) phi z % (vs:num->real^(N,1)finite_sum->real^1) n z -
              vsum(1..dimindex(:N))
                (\i. wan_dpart i phi z %
                     (vsum(1..dimindex(:N))
                        (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j %
                             (Ks:num->num->real^(N,1)finite_sum->real^1) n j z) +
                      (gs:num->num->real^(N,1)finite_sum->real^1) n i z)) +
              phi z % (vsum(1..dimindex(:N))
                         (\i. (b:real^(N,1)finite_sum->real^N) z$i % Ks n i z) +
                       (c:real^(N,1)finite_sum->real) z % vs n z +
                       (fs:num->real^(N,1)finite_sum->real^1) n z)) = vec 0`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN USE_THEN "gw" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[wan_gweak] THEN
    DISCH_THEN(MP_TAC o SPEC `phi:real^(N,1)finite_sum->real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n:num. vec 0:real^1` THEN
  ASM_REWRITE_TAC[LIM_CONST; TRIVIAL_LIMIT_SEQUENTIALLY]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of an L^2 limit to a set where all approximants vanish.      *)
(* ------------------------------------------------------------------------- *)

let WAN_L2C_RESTRICT = prove
 (`!(u:num->real^M->real^K) v k.
     wan_l2c u v /\ lebesgue_measurable k /\ (!n x. ~(x IN k) ==> u n x = vec 0)
     ==> wan_l2c u (\x. if x IN k then v x else vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[wan_l2c] (ASSUME `wan_l2c (u:num->real^M->real^K) v`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(\x. if x IN k then (v:real^M->real^K) x else vec 0) IN lspace (:real^M) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:K`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `v:real^M->real^K` THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_RESTRICT THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^M->real^K) IN lspace (:real^M) (&2)` THEN
      SIMP_TAC[lspace; IN_ELIM_THM];
      GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_LE_REFL; NORM_0; NORM_POS_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2C_BOUND1 THEN
  MAP_EVERY EXISTS_TAC [`u:num->real^M->real^K`; `v:real^M->real^K`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^M->bool` THEN
  REWRITE_TAC[NEGLIGIBLE_EMPTY; IN_DIFF; IN_UNIV; NOT_IN_EMPTY; REAL_POS] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN k` THEN
    ASM_SIMP_TAC[REAL_LE_REFL; VECTOR_SUB_REFL; NORM_0; NORM_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Coefficients: smooth and constant outside a compact set.                 *)
(* ------------------------------------------------------------------------- *)

let wan_cc = new_definition
 `wan_cc (m:real^M->real) <=>
    smooth_map_on (:real^M) (\x. lift(m x)) /\
    ?k m0. compact k /\ !x. ~(x IN k) ==> m x = m0`;;

let WAN_CC_SHIFT = prove
 (`!(m:real^M->real) k m0.
     smooth_map_on (:real^M) (\x. lift(m x)) /\ compact k /\
     (!x. ~(x IN k) ==> m x = m0)
     ==> smooth_map_on (:real^M) (\x. lift(m x - m0)) /\
         !x. ~(x IN k) ==> m x - m0 = &0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_SUB_REFL] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST]);;

let WAN_CC_BOUNDED = prove
 (`!m:real^M->real. wan_cc m ==> ?B. !x. abs(m x) <= B`,
  GEN_TAC THEN REWRITE_TAC[wan_cc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `m0:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`m:real^M->real`; `k:real^M->bool`; `m0:real`] WAN_CC_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (m:real^M->real) x - m0`; `k:real^M->bool`]
                WAN_SMOOTH_SUPPORT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real` o CONJUNCT1) THEN
  EXISTS_TAC `B + abs m0` THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN REAL_ARITH_TAC);;

let WAN_CC_LIPSCHITZ = prove
 (`!m:real^M->real.
     wan_cc m ==> ?L. &0 <= L /\ !x y. abs(m x - m y) <= L * norm(x - y)`,
  GEN_TAC THEN REWRITE_TAC[wan_cc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `m0:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`m:real^M->real`; `k:real^M->bool`; `m0:real`] WAN_CC_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (m:real^M->real) x - m0`; `k:real^M->bool`]
                WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `abs B` THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  MP_TAC(ISPEC `x - y:real^M` NORM_POS_LE) THEN
  SUBGOAL_THEN `B * norm(x - y:real^M) <= abs B * norm(x - y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let WAN_CC_CONTINUOUS = prove
 (`!m:real^M->real. wan_cc m ==> (\x. lift(m x)) continuous_on (:real^M)`,
  SIMP_TAC[wan_cc; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let WAN_DPART_SUB_CONST = prove
 (`!i (m:real^M->real) c x.
     smooth_map_on (:real^M) (\x. lift(m x))
     ==> wan_dpart i (\y. m y - c) x = wan_dpart i m x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart; GSYM partial_derivative] THEN
  REWRITE_TAC[LIFT_SUB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_SUB o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_SMOOTH_DIFFERENTIABLE THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[PARTIAL_DERIVATIVE_CONST; VECTOR_SUB_RZERO]]);;

let WAN_CC_DPART = prove
 (`!i m:real^M->real. wan_cc m ==> wan_cc (wan_dpart i m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_cc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `m0:real` STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[WAN_DPART_SMOOTH] THEN
  MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `&0`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:real^M->real`; `k:real^M->bool`; `m0:real`] WAN_CC_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `m:real^M->real`; `m0:real`; `x:real^M`] WAN_DPART_SUB_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_REWRITE_TAC[]);;

let WAN_CC_CONST = prove
 (`!c. wan_cc (\x:real^M. c)`,
  GEN_TAC THEN REWRITE_TAC[wan_cc; SMOOTH_MAP_ON_CONST] THEN
  MAP_EVERY EXISTS_TAC [`{}:real^M->bool`; `c:real`] THEN REWRITE_TAC[COMPACT_EMPTY]);;

let WAN_CC_ADD = prove
 (`!m1 m2:real^M->real. wan_cc m1 /\ wan_cc m2 ==> wan_cc (\x. m1 x + m2 x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_cc] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `k2:real^M->bool` (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    MAP_EVERY EXISTS_TAC [`k1 UNION k2:real^M->bool`; `c1 + c2:real`] THEN
    ASM_SIMP_TAC[COMPACT_UNION; IN_UNION; DE_MORGAN_THM]]);;

let WAN_CC_MUL = prove
 (`!m1 m2:real^M->real. wan_cc m1 /\ wan_cc m2 ==> wan_cc (\x. m1 x * m2 x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_cc] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)))
   (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `k2:real^M->bool` (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)))) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^M)`; `\x. lift((m1:real^M->real) x)`;
                   `\x. lift((m2:real^M->real) x)`] SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; LIFT_DROP];
    MAP_EVERY EXISTS_TAC [`k1 UNION k2:real^M->bool`; `c1 * c2:real`] THEN
    ASM_SIMP_TAC[COMPACT_UNION; IN_UNION; DE_MORGAN_THM]]);;

let WAN_CC_NEG = prove
 (`!m:real^M->real. wan_cc m ==> wan_cc (\x. --(m x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. --((m:real^M->real) x)) = (\x. (\x. -- &1) x * m x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC WAN_CC_MUL THEN ASM_REWRITE_TAC[WAN_CC_CONST]]);;

let WAN_CC_SUB = prove
 (`!m1 m2:real^M->real. wan_cc m1 /\ wan_cc m2 ==> wan_cc (\x. m1 x - m2 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_sub] THEN
  MP_TAC(ISPECL [`m1:real^M->real`; `\x. --((m2:real^M->real) x)`] WAN_CC_ADD) THEN
  ASM_SIMP_TAC[WAN_CC_NEG]);;

let WAN_TEST_CC = prove
 (`!phi:real^M->real. wan_test (:real^M) phi ==> wan_cc phi`,
  GEN_TAC THEN REWRITE_TAC[wan_test; wan_cc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `&0`] THEN
  ASM_REWRITE_TAC[]);;

let WAN_FINITE_BOUND = prove
 (`!(f:A->B->real) t.
     FINITE t /\ (!i. i IN t ==> ?B. !x. abs(f i x) <= B)
     ==> ?B. !i x. i IN t ==> abs(f i x) <= B`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun ih -> DISCH_THEN(fun th -> MP_TAC(MATCH_MP ih (CONJUNCT2 th)) THEN
                                         MP_TAC(CONJUNCT1 th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN
  EXISTS_TAC `max B1 B2` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [MP_TAC(SPEC `x:B` (ASSUME `!x:B. abs((f:A->B->real) a x) <= B1`)) THEN
    REAL_ARITH_TAC;
    MP_TAC(MP (SPECL [`i:A`; `x:B`]
      (ASSUME `!i x. i IN s ==> abs((f:A->B->real) i x) <= B2`))
      (ASSUME `(i:A) IN s`)) THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The spatial regularity step.  A whole-space weak                         *)
(* solution with compactly supported L^2 data, whose divergence data g has  *)
(* spatial weak derivatives in L^2, has second spatial weak derivatives in  *)
(* L^2, and each spatial derivative solves the differentiated weak          *)
(* equation.                                                                 *)
(* ========================================================================= *)

let WAN_MOLL_SUPPORT_CBALL = prove
 (`!e (u:real^M->real^K) k0.
     &0 < e /\ e <= &1 /\ (!y. ~(y IN k0) ==> u y = vec 0)
     ==> !x. ~(x IN {x + y | x IN k0 /\ y IN cball(vec 0,&1)}) ==> wan_moll e u x = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e:real`; `u:real^M->real^K`; `k0:real^M->bool`] WAN_MOLL_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `~((x:real^M) IN {x + y | x IN k0 /\ y IN cball(vec 0,&1)})` THEN
  REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^M` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^M` THEN
  REWRITE_TAC[IN_BALL; IN_CBALL] THEN UNDISCH_TAC `e <= &1` THEN
  MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]);;

let WAN_CBALL_SUMS_COMPACT = prove
 (`!k0:real^M->bool. compact k0 ==> compact {x + y | x IN k0 /\ y IN cball(vec 0,&1)}`,
  SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL]);;

let WAN_CBALL_SUMS_SUBSET = prove
 (`!k0:real^M->bool. k0 SUBSET {x + y | x IN k0 /\ y IN cball(vec 0,&1)}`,
  GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^M`; `vec 0:real^M`] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID; CENTRE_IN_CBALL; REAL_POS]);;

let WAN_INV_N1_LE1 = prove
 (`!n. inv(&n + &1) <= &1`,
  MESON_TAC[WAN_INV_N1_BOUNDS]);;

let WAN_PSTEP_DATA = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1)
    (K:num->real^(N,1)finite_sum->real^1) e k0 Fd Gd.
     &0 < e /\ e <= &1 /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(b w$i))) /\
     smooth_map_on (:real^(N,1)finite_sum) (\w. lift(c w)) /\
     wan_lloc (:real^(N,1)finite_sum) v /\ wan_lloc (:real^(N,1)finite_sum) f /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_lloc (:real^(N,1)finite_sum) (K j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_lloc (:real^(N,1)finite_sum) (g i)) /\
     (!z. ~(z IN k0) ==> v z = vec 0) /\ (!z. ~(z IN k0) ==> f z = vec 0) /\
     (!j z. 1 <= j /\ j <= dimindex(:N) /\ ~(z IN k0) ==> K j z = vec 0) /\
     (!i z. 1 <= i /\ i <= dimindex(:N) /\ ~(z IN k0) ==> g i z = vec 0) /\
     (!w. Fd w = wan_moll e f w +
                 vsum(1..dimindex(:N))
                   (\i. wan_moll e (\y. b y$i % K i y) w - b w$i % wan_moll e (K i) w) +
                 (wan_moll e (\y. c y % v y) w - c w % wan_moll e v w)) /\
     (!i w. Gd i w = wan_moll e (g i) w +
                     vsum(1..dimindex(:N))
                       (\j. wan_moll e (\y. a y$i$j % K j y) w -
                            a w$i$j % wan_moll e (K j) w))
     ==> smooth_map_on (:real^(N,1)finite_sum) (wan_moll e v) /\
         smooth_map_on (:real^(N,1)finite_sum) Fd /\
         (!i. 1 <= i /\ i <= dimindex(:N)
              ==> smooth_map_on (:real^(N,1)finite_sum) (Gd i)) /\
         (!z. ~(z IN {x + y | x IN k0 /\ y IN cball(vec 0,&1)})
              ==> wan_moll e v z = vec 0 /\ Fd z = vec 0 /\
                  !i. 1 <= i /\ i <= dimindex(:N) ==> Gd i z = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "F") (LABEL_TAC "G"))))))))))))))) THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> wan_lloc (:real^(N,1)finite_sum)
                 (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                      (K:num->real^(N,1)finite_sum->real^1) j y)) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum)
               (\y. (b:real^(N,1)finite_sum->real^N) y$i % K i y)) /\
    wan_lloc (:real^(N,1)finite_sum)
      (\y. (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN
    ASM_SIMP_TAC[ETA_AX; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^(N,1)finite_sum->real^1.
      wan_lloc (:real^(N,1)finite_sum) u ==> smooth_map_on (:real^(N,1)finite_sum) (wan_moll e u)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_MOLL_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!(m:real^(N,1)finite_sum->real) (u:real^(N,1)finite_sum->real^1).
      smooth_map_on (:real^(N,1)finite_sum) (\w. lift(m w)) /\
      wan_lloc (:real^(N,1)finite_sum) u
      ==> smooth_map_on (:real^(N,1)finite_sum) (\w. m w % wan_moll e u w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `(Fd:real^(N,1)finite_sum->real^1) =
      (\w. wan_moll e f w +
           vsum(1..dimindex(:N))
             (\i. wan_moll e (\y. (b:real^(N,1)finite_sum->real^N) y$i %
                                  (K:num->real^(N,1)finite_sum->real^1) i y) w -
                  b w$i % wan_moll e (K i) w) +
           (wan_moll e (\y. (c:real^(N,1)finite_sum->real) y %
                            (v:real^(N,1)finite_sum->real^1) y) w -
            c w % wan_moll e v w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(Gd:num->real^(N,1)finite_sum->real^1) i =
      (\w. wan_moll e ((g:num->real^(N,1)finite_sum->real^1) i) w +
           vsum(1..dimindex(:N))
             (\j. wan_moll e (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                                  (K:num->real^(N,1)finite_sum->real^1) j y) w -
                  a w$i$j % wan_moll e (K j) w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!u:real^(N,1)finite_sum->real^1.
      (!y. ~(y IN k0) ==> u y = vec 0) ==> wan_moll e u z = vec 0`
  (LABEL_TAC "sup") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`e:real`; `u:real^(N,1)finite_sum->real^1`;
      `k0:real^(N,1)finite_sum->bool`] WAN_MOLL_SUPPORT_CBALL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_moll e (v:real^(N,1)finite_sum->real^1) z = vec 0 /\
                (!j. 1 <= j /\ j <= dimindex(:N)
                     ==> wan_moll e ((K:num->real^(N,1)finite_sum->real^1) j) z = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REPEAT STRIP_TAC] THEN USE_THEN "sup" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "F" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `wan_moll e (f:real^(N,1)finite_sum->real^1) z = vec 0 /\
      wan_moll e (\y. (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y) z =
      vec 0 /\
      vsum(1..dimindex(:N))
        (\i. wan_moll e (\y. (b:real^(N,1)finite_sum->real^N) y$i %
                             (K:num->real^(N,1)finite_sum->real^1) i y) z -
             b z$i % wan_moll e (K i) z) = vec 0`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [USE_THEN "sup" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "sup" MATCH_MP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO];
        MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
        REWRITE_TAC[] THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
        USE_THEN "sup" MATCH_MP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO]];
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN VECTOR_ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN USE_THEN "G" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(VECTOR_ARITH `x = vec 0 /\ y = vec 0 ==> x + y:real^N = vec 0`) THEN
    CONJ_TAC THENL
     [USE_THEN "sup" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
      USE_THEN "sup" MATCH_MP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO]]]);;

let WAN_PSTEP_CEQ = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1)
    (K:num->real^(N,1)finite_sum->real^1) e k Fd Gd.
     &0 < e /\ 1 <= k /\ k <= dimindex(:N) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(b w$i))) /\
     smooth_map_on (:real^(N,1)finite_sum) (\w. lift(c w)) /\
     wan_lloc (:real^(N,1)finite_sum) v /\ wan_lloc (:real^(N,1)finite_sum) f /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_lloc (:real^(N,1)finite_sum) (g i)) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> wan_wpd (:real^(N,1)finite_sum) j v (K j)) /\
     wan_gweak a b c f g v K /\
     (!w. Fd w = wan_moll e f w +
                 vsum(1..dimindex(:N))
                   (\i. wan_moll e (\y. b y$i % K i y) w - b w$i % wan_moll e (K i) w) +
                 (wan_moll e (\y. c y % v y) w - c w % wan_moll e v w)) /\
     (!i w. Gd i w = wan_moll e (g i) w +
                     vsum(1..dimindex(:N))
                       (\j. wan_moll e (\y. a y$i$j % K j y) w -
                            a w$i$j % wan_moll e (K j) w)) /\
     smooth_map_on (:real^(N,1)finite_sum) Fd /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> smooth_map_on (:real^(N,1)finite_sum) (Gd i))
     ==> wan_ceq a b c
           (\z. vsum(1..dimindex(:N))
                  (\i. drop(partial_derivative k (\w. lift(b w$i)) z) %
                       partial_derivative i (wan_moll e v) z) +
                drop(partial_derivative k (\w. lift(c w)) z) % wan_moll e v z)
           (\i z. (partial_derivative k (Gd i) z +
                   vsum(1..dimindex(:N))
                     (\j. drop(partial_derivative k (\w. lift(a w$i$j)) z) %
                          partial_derivative j (wan_moll e v) z)) +
                  (if i = k then Fd z else vec 0))
           (partial_derivative k (wan_moll e v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_ceq a b c Fd Gd (wan_moll e (v:real^(N,1)finite_sum->real^1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(Fd:real^(N,1)finite_sum->real^1) =
      (\w. wan_moll e f w +
           vsum(1..dimindex(:N))
             (\i. wan_moll e (\y. (b:real^(N,1)finite_sum->real^N) y$i %
                                  (K:num->real^(N,1)finite_sum->real^1) i y) w -
                  b w$i % wan_moll e (K i) w) +
           (wan_moll e (\y. (c:real^(N,1)finite_sum->real) y %
                            (v:real^(N,1)finite_sum->real^1) y) w -
            c w % wan_moll e v w)) /\
      (Gd:num->real^(N,1)finite_sum->real^1) =
      (\i w. wan_moll e ((g:num->real^(N,1)finite_sum->real^1) i) w +
             vsum(1..dimindex(:N))
               (\j. wan_moll e (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j % K j y) w -
                    a w$i$j % wan_moll e (K j) w))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC WAN_GWEAK_MOLL_CEQ THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
                 `c:real^(N,1)finite_sum->real`; `Fd:real^(N,1)finite_sum->real^1`;
                 `Gd:num->real^(N,1)finite_sum->real^1`;
                 `wan_moll e (v:real^(N,1)finite_sum->real^1)`; `k:num`] WAN_CEQ_DIFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_MOLL_SMOOTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
    `c:real^(N,1)finite_sum->real`; `Fd:real^(N,1)finite_sum->real^1`;
    `\z. vsum(1..dimindex(:N))
           (\i. drop(partial_derivative k (\w. lift((b:real^(N,1)finite_sum->real^N) w$i)) z) %
                partial_derivative i (wan_moll e (v:real^(N,1)finite_sum->real^1)) z) +
         drop(partial_derivative k (\w. lift((c:real^(N,1)finite_sum->real) w)) z) %
         wan_moll e v z`;
    `\i z. partial_derivative k ((Gd:num->real^(N,1)finite_sum->real^1) i) z +
           vsum(1..dimindex(:N))
             (\j. drop(partial_derivative k
                         (\w. lift((a:real^(N,1)finite_sum->real^N^N) w$i$j)) z) %
                  partial_derivative j (wan_moll e (v:real^(N,1)finite_sum->real^1)) z)`;
    `partial_derivative k (wan_moll e (v:real^(N,1)finite_sum->real^1))`; `k:num`]
   WAN_CEQ_MOVE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL; WAN_MOLL_SMOOTH] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_SIMP_TAC[OPEN_UNIV; ETA_AX; WAN_PEN_SMOOTH_PARTIAL] THEN
  MATCH_MP_TAC WAN_SMOOTH_VSUM THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC WAN_PEN_SMOOTH_DROPMUL THEN
  ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL; WAN_MOLL_SMOOTH; ETA_AX]);;

let WAN_CC_FACTS = prove
 (`!m:real^M->real.
     wan_cc m
     ==> smooth_map_on (:real^M) (\x. lift(m x)) /\
         (\x. lift(m x)) continuous_on (:real^M) /\
         (?B. !x. abs(m x) <= B) /\
         (?L. &0 <= L /\ !x y. abs(m x - m y) <= L * norm(x - y)) /\
         (!k. ?B. !x. abs(wan_dpart k m x) <= B)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[WAN_CC_CONTINUOUS; WAN_CC_BOUNDED; WAN_CC_LIPSCHITZ] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[wan_cc]; ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC WAN_CC_BOUNDED THEN ASM_SIMP_TAC[WAN_CC_DPART; ETA_AX]);;

let WAN_PSTEP_FLIM = prove
 (`!(b:real^(N,1)finite_sum->real^N) (c:real^(N,1)finite_sum->real)
    (f:real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1)
    (K:num->real^(N,1)finite_sum->real^1) k0.
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c /\
     compact k0 /\
     (!z. ~(z IN k0) ==> v z = vec 0) /\ (!z. ~(z IN k0) ==> f z = vec 0) /\
     (!j z. 1 <= j /\ j <= dimindex(:N) /\ ~(z IN k0) ==> K j z = vec 0) /\
     v IN lspace (:real^(N,1)finite_sum) (&2) /\ f IN lspace (:real^(N,1)finite_sum) (&2) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> K j IN lspace (:real^(N,1)finite_sum) (&2))
     ==> wan_l2c
           (\n w. wan_moll (inv(&n + &1)) f w +
                  vsum(1..dimindex(:N))
                    (\i. wan_moll (inv(&n + &1)) (\y. b y$i % K i y) w -
                         b w$i % wan_moll (inv(&n + &1)) (K i) w) +
                  (wan_moll (inv(&n + &1)) (\y. c y % v y) w -
                   c w % wan_moll (inv(&n + &1)) v w))
           f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `wan_l2c
     (\n w. wan_moll (inv(&n + &1)) (f:real^(N,1)finite_sum->real^1) w +
           vsum(1..dimindex(:N))
             (\i. wan_moll (inv(&n + &1))
                    (\y. (b:real^(N,1)finite_sum->real^N) y$i %
                         (K:num->real^(N,1)finite_sum->real^1) i y) w -
                  b w$i % wan_moll (inv(&n + &1)) (K i) w) +
           (wan_moll (inv(&n + &1))
              (\y. (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y) w -
            c w % wan_moll (inv(&n + &1)) v w))
     (\w. f w + (vsum(1..dimindex(:N)) (\i:num. vec 0:real^1) + vec 0))`
  (fun th -> MATCH_MP_TAC(MATCH_MP WAN_L2C_TRANSFORM th) THEN
             REWRITE_TAC[VSUM_0; VECTOR_ADD_RID]) THEN
  MATCH_MP_TAC WAN_L2C_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN
    EXISTS_TAC `k0:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2C_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_L2C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP WAN_CC_FACTS (MP (SPEC `i:num`
      (ASSUME `!i. 1 <= i /\ i <= dimindex(:N)
                   ==> wan_cc (\z. (b:real^(N,1)finite_sum->real^N) z$i)`))
      (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`)))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`\z. (b:real^(N,1)finite_sum->real^N) z$i`; `B:real`;
                   `(K:num->real^(N,1)finite_sum->real^1) i`;
                   `k0:real^(N,1)finite_sum->bool`] WAN_COMM_L2C) THEN
    RULE_ASSUM_TAC BETA_RULE THEN REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    MP_TAC(MATCH_MP WAN_CC_FACTS (ASSUME `wan_cc (c:real^(N,1)finite_sum->real)`)) THEN
    STRIP_TAC THEN MATCH_MP_TAC WAN_COMM_L2C THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `k0:real^(N,1)finite_sum->bool`] THEN
    ASM_SIMP_TAC[]]);;

let WAN_PSTEP_GLIM = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (g:num->real^(N,1)finite_sum->real^1)
    (K:num->real^(N,1)finite_sum->real^1) (w:num->num->real^(N,1)finite_sum->real^1) k0 k i.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     compact k0 /\
     (!j z. 1 <= j /\ j <= dimindex(:N) /\ ~(z IN k0) ==> K j z = vec 0) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> K j IN lspace (:real^(N,1)finite_sum) (&2)) /\
     (!z. ~(z IN k0) ==> w k i z = vec 0) /\
     w k i IN lspace (:real^(N,1)finite_sum) (&2) /\
     wan_wpd (:real^(N,1)finite_sum) k (g i) (w k i) /\
     1 <= i /\ i <= dimindex(:N)
     ==> wan_l2c
           (\n. partial_derivative k
                  (\x. wan_moll (inv(&n + &1)) (g i) x +
                       vsum(1..dimindex(:N))
                         (\j. wan_moll (inv(&n + &1)) (\y. a y$i$j % K j y) x -
                              a x$i$j % wan_moll (inv(&n + &1)) (K j) x)))
           (w k i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^(N,1)finite_sum) ((g:num->real^(N,1)finite_sum->real^1) i)`
  ASSUME_TAC THENL [ASM_MESON_TAC[wan_wpd]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum) (\z. lift((a:real^(N,1)finite_sum->real^N^N) z$i$j)) /\
            wan_lloc (:real^(N,1)finite_sum) ((K:num->real^(N,1)finite_sum->real^1) j) /\
            wan_lloc (:real^(N,1)finite_sum) (\y. a y$i$j % K j y)`
  (LABEL_TAC "aj") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP WAN_CC_FACTS (MP (SPECL [`i:num`; `j:num`]
      (ASSUME `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                     ==> wan_cc (\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j)`))
      (CONJ (ASSUME `1 <= i`) (CONJ (ASSUME `i <= dimindex(:N)`)
        (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`)))))) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `wan_lloc (:real^(N,1)finite_sum) ((K:num->real^(N,1)finite_sum->real^1) j)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LLOC_CONT_MUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l2c
     (\n x. wan_moll (inv(&n + &1)) ((w:num->num->real^(N,1)finite_sum->real^1) k i) x +
            vsum(1..dimindex(:N))
              (\j. partial_derivative k
                     (\x. wan_moll (inv(&n + &1))
                            (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                                 (K:num->real^(N,1)finite_sum->real^1) j y) x -
                          a x$i$j % wan_moll (inv(&n + &1)) (K j) x) x))
     (\x. w k i x + vsum(1..dimindex(:N)) (\j:num. vec 0:real^1))`
  (fun th -> MATCH_MP_TAC(MATCH_MP WAN_L2C_TRANSFORM th)) THENL
   [MATCH_MP_TAC WAN_L2C_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN
      EXISTS_TAC `k0:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_L2C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MP_TAC(MATCH_MP WAN_CC_FACTS (MP (SPECL [`i:num`; `j:num`]
        (ASSUME `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                       ==> wan_cc (\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j)`))
        (CONJ (ASSUME `1 <= i`) (CONJ (ASSUME `i <= dimindex(:N)`)
          (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`)))))) THEN
      REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Ba:real`) (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)
        (MP_TAC o SPEC `k:num`))))) THEN
      DISCH_THEN(X_CHOOSE_TAC `Bd:real`) THEN
      MP_TAC(ISPECL [`\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j`; `L:real`; `Ba:real`;
                     `Bd:real`; `(K:num->real^(N,1)finite_sum->real^1) j`;
                     `k0:real^(N,1)finite_sum->bool`; `k:num`] WAN_MCOMM_D_L2C) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_0; VECTOR_ADD_RID] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^(N,1)finite_sum`] THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum)
              (\x. wan_moll (inv(&n + &1))
                     (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                          (K:num->real^(N,1)finite_sum->real^1) j y) x -
                   a x$i$j % wan_moll (inv(&n + &1)) (K j) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "aj" (fun th -> MP_TAC(MP (SPEC `j:num` th)
      (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`)))) THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; WAN_MOLL_SMOOTH; WAN_INV_N1_POS; ETA_AX] THEN
    MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[WAN_MOLL_SMOOTH; WAN_INV_N1_POS; ETA_AX];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_ADD o lhand o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_SMOOTH_DIFFERENTIABLE THEN
    ASM_SIMP_TAC[WAN_MOLL_SMOOTH; WAN_INV_N1_POS; ETA_AX] THEN
    MATCH_MP_TAC WAN_SMOOTH_VSUM THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC WAN_MOLL_WPD THEN
    ASM_REWRITE_TAC[WAN_INV_N1_POS];
    W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_VSUM o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC WAN_SMOOTH_DIFFERENTIABLE THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]]);;

let WAN_DROP_PD_LIFT = prove
 (`!k (m:real^M->real) z.
     drop(partial_derivative k (\w. lift(m w)) z) = wan_dpart k m z`,
  REWRITE_TAC[GSYM WAN_DPART_LIFT; LIFT_DROP]);;

let WAN_COEFF_FACTS = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c
     ==> (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j)) /\
                    (\w. lift(a w$i$j)) continuous_on (:real^(N,1)finite_sum)) /\
         (!i. 1 <= i /\ i <= dimindex(:N)
              ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(b w$i)) /\
                  (\w. lift(b w$i)) continuous_on (:real^(N,1)finite_sum)) /\
         smooth_map_on (:real^(N,1)finite_sum) (\w. lift(c w)) /\
         (\w. lift(c w)) continuous_on (:real^(N,1)finite_sum) /\
         (?Kb. !z i. 1 <= i /\ i <= dimindex(:N) ==> abs(b z$i) <= Kb) /\
         (?Kc. !z. abs(c z) <= Kc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP WAN_CC_FACTS (MP (SPECL [`i:num`; `j:num`]
      (ASSUME `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                     ==> wan_cc (\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j)`))
      (ASSUME `1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)`))) THEN
    SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP WAN_CC_FACTS (MP (SPEC `i:num`
      (ASSUME `!i. 1 <= i /\ i <= dimindex(:N)
                   ==> wan_cc (\z. (b:real^(N,1)finite_sum->real^N) z$i)`))
      (ASSUME `1 <= i /\ i <= dimindex(:N)`))) THEN
    SIMP_TAC[];
    ASM_MESON_TAC[WAN_CC_FACTS];
    ASM_MESON_TAC[WAN_CC_FACTS];
    MP_TAC(ISPECL [`\i z. (b:real^(N,1)finite_sum->real^N) z$i`; `1..dimindex(:N)`]
                  WAN_FINITE_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(MATCH_MP WAN_CC_BOUNDED (MP (SPEC `i:num`
        (ASSUME `!i. 1 <= i /\ i <= dimindex(:N)
                     ==> wan_cc (\z. (b:real^(N,1)finite_sum->real^N) z$i)`))
        (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`)))) THEN
      REWRITE_TAC[];
      MESON_TAC[]];
    ASM_MESON_TAC[WAN_CC_BOUNDED]]);;

let WAN_PSTEP = prove
 (`!lam (a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1)
    (K:num->real^(N,1)finite_sum->real^1) (w:num->num->real^(N,1)finite_sum->real^1) k0 k.
     &0 < lam /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c /\
     (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi)) /\
     compact k0 /\
     (!z. ~(z IN k0) ==> v z = vec 0) /\ (!z. ~(z IN k0) ==> f z = vec 0) /\
     (!j z. 1 <= j /\ j <= dimindex(:N) /\ ~(z IN k0) ==> K j z = vec 0) /\
     (!i z. 1 <= i /\ i <= dimindex(:N) /\ ~(z IN k0) ==> g i z = vec 0) /\
     (!l i z. 1 <= l /\ l <= dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N) /\ ~(z IN k0)
              ==> w l i z = vec 0) /\
     v IN lspace (:real^(N,1)finite_sum) (&2) /\ f IN lspace (:real^(N,1)finite_sum) (&2) /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> K j IN lspace (:real^(N,1)finite_sum) (&2) /\
              wan_wpd (:real^(N,1)finite_sum) j v (K j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> g i IN lspace (:real^(N,1)finite_sum) (&2)) /\
     (!l i. 1 <= l /\ l <= dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N)
            ==> w l i IN lspace (:real^(N,1)finite_sum) (&2) /\
                wan_wpd (:real^(N,1)finite_sum) l (g i) (w l i)) /\
     wan_gweak a b c f g v K /\
     1 <= k /\ k <= dimindex(:N)
     ==> ?H. (!j. 1 <= j /\ j <= dimindex(:N)
                  ==> H j IN lspace (:real^(N,1)finite_sum) (&2) /\
                      wan_wpd (:real^(N,1)finite_sum) j (K k) (H j) /\
                      (!z. ~(z IN {x + y | x IN k0 /\ y IN cball(vec 0,&1)})
                           ==> H j z = vec 0)) /\
             wan_gweak a b c
               (\z. vsum(1..dimindex(:N)) (\i. wan_dpart k (\y. b y$i) z % K i z) +
                    wan_dpart k c z % v z)
               (\i z. w k i z +
                      vsum(1..dimindex(:N)) (\j. wan_dpart k (\y. a y$i$j) z % K j z) +
                      (if i = k then f z else vec 0))
               (K k) H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
                 `c:real^(N,1)finite_sum->real`] WAN_COEFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ca") (CONJUNCTS_THEN2 (LABEL_TAC "cb")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Kb:real`) (X_CHOOSE_TAC `Kc:real`)))))) THEN
  MP_TAC(ISPECL [`lam:real`; `Kb:real`; `Kc:real`; `a:real^(N,1)finite_sum->real^N^N`;
                 `b:real^(N,1)finite_sum->real^N`; `c:real^(N,1)finite_sum->real`]
                WAN_ENERGY0_E0) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `k1 = {x + y:real^(N,1)finite_sum | x IN k0 /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact (k1:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN ASM_SIMP_TAC[WAN_CBALL_SUMS_COMPACT]; ALL_TAC] THEN
  ABBREV_TAC
   `Fd = \n w. wan_moll (inv(&n + &1)) (f:real^(N,1)finite_sum->real^1) w +
               vsum(1..dimindex(:N))
                 (\i. wan_moll (inv(&n + &1))
                        (\y. (b:real^(N,1)finite_sum->real^N) y$i %
                             (K:num->real^(N,1)finite_sum->real^1) i y) w -
                      b w$i % wan_moll (inv(&n + &1)) (K i) w) +
               (wan_moll (inv(&n + &1))
                  (\y. (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y) w -
                c w % wan_moll (inv(&n + &1)) v w)` THEN
  ABBREV_TAC
   `Gd = \n i w. wan_moll (inv(&n + &1)) ((g:num->real^(N,1)finite_sum->real^1) i) w +
                 vsum(1..dimindex(:N))
                   (\j. wan_moll (inv(&n + &1))
                          (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                               (K:num->real^(N,1)finite_sum->real^1) j y) w -
                        a w$i$j % wan_moll (inv(&n + &1)) (K j) w)` THEN
  SUBGOAL_THEN
   `(!n w. (Fd:num->real^(N,1)finite_sum->real^1) n w =
           wan_moll (inv(&n + &1)) (f:real^(N,1)finite_sum->real^1) w +
           vsum(1..dimindex(:N))
             (\i. wan_moll (inv(&n + &1))
                    (\y. (b:real^(N,1)finite_sum->real^N) y$i %
                         (K:num->real^(N,1)finite_sum->real^1) i y) w -
                  b w$i % wan_moll (inv(&n + &1)) (K i) w) +
           (wan_moll (inv(&n + &1))
              (\y. (c:real^(N,1)finite_sum->real) y % (v:real^(N,1)finite_sum->real^1) y) w -
            c w % wan_moll (inv(&n + &1)) v w)) /\
    (!n i w. (Gd:num->num->real^(N,1)finite_sum->real^1) n i w =
             wan_moll (inv(&n + &1)) ((g:num->real^(N,1)finite_sum->real^1) i) w +
             vsum(1..dimindex(:N))
               (\j. wan_moll (inv(&n + &1))
                      (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j %
                           (K:num->real^(N,1)finite_sum->real^1) j y) w -
                    a w$i$j % wan_moll (inv(&n + &1)) (K j) w))`
  (CONJUNCTS_THEN2 (LABEL_TAC "Fdef") (LABEL_TAC "Gdef")) THENL
   [MAP_EVERY EXPAND_TAC ["Fd"; "Gd"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_lloc (:real^(N,1)finite_sum) (v:real^(N,1)finite_sum->real^1) /\
    wan_lloc (:real^(N,1)finite_sum) (f:real^(N,1)finite_sum->real^1) /\
    (!j. 1 <= j /\ j <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum) ((K:num->real^(N,1)finite_sum->real^1) j)) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> wan_lloc (:real^(N,1)finite_sum) ((g:num->real^(N,1)finite_sum->real^1) i))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^(N,1)finite_sum)
          (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) /\
        smooth_map_on (:real^(N,1)finite_sum) ((Fd:num->real^(N,1)finite_sum->real^1) n) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> smooth_map_on (:real^(N,1)finite_sum)
                   ((Gd:num->num->real^(N,1)finite_sum->real^1) n i)) /\
        (!z. ~(z IN (k1:real^(N,1)finite_sum->bool))
             ==> wan_moll (inv(&n + &1)) v z = vec 0 /\ Fd n z = vec 0 /\
                 !i. 1 <= i /\ i <= dimindex(:N) ==> Gd n i z = vec 0)`
  (LABEL_TAC "dat") THENL
   [GEN_TAC THEN EXPAND_TAC "k1" THEN MATCH_MP_TAC WAN_PSTEP_DATA THEN
    MAP_EVERY EXISTS_TAC
     [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
      `c:real^(N,1)finite_sum->real`; `f:real^(N,1)finite_sum->real^1`;
      `g:num->real^(N,1)finite_sum->real^1`; `K:num->real^(N,1)finite_sum->real^1`] THEN
    ASM_SIMP_TAC[WAN_INV_N1_POS; WAN_INV_N1_LE1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_ceq (a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
          (c:real^(N,1)finite_sum->real)
          (\z. vsum(1..dimindex(:N))
                 (\i. drop(partial_derivative k (\w. lift(b w$i)) z) %
                      partial_derivative i
                        (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) z) +
               drop(partial_derivative k (\w. lift(c w)) z) % wan_moll (inv(&n + &1)) v z)
          (\i z. (partial_derivative k ((Gd:num->num->real^(N,1)finite_sum->real^1) n i) z +
                  vsum(1..dimindex(:N))
                    (\j. drop(partial_derivative k (\w. lift(a w$i$j)) z) %
                         partial_derivative j (wan_moll (inv(&n + &1)) v) z)) +
                 (if i = k then (Fd:num->real^(N,1)finite_sum->real^1) n z else vec 0))
          (partial_derivative k (wan_moll (inv(&n + &1)) v))`
  (LABEL_TAC "ceq") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
                   `c:real^(N,1)finite_sum->real`; `f:real^(N,1)finite_sum->real^1`;
                   `g:num->real^(N,1)finite_sum->real^1`; `v:real^(N,1)finite_sum->real^1`;
                   `K:num->real^(N,1)finite_sum->real^1`; `inv(&n + &1)`; `k:num`;
                   `(Fd:num->real^(N,1)finite_sum->real^1) n`;
                   `(Gd:num->num->real^(N,1)finite_sum->real^1) n`] WAN_PSTEP_CEQ) THEN
    USE_THEN "dat" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[WAN_INV_N1_POS]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "Fdef" (K ALL_TAC) THEN REMOVE_THEN "Gdef" (K ALL_TAC) THEN
  ABBREV_TAC `D = \n. partial_derivative k (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1))` THEN
  ABBREV_TAC
   `F2 = \n z. vsum(1..dimindex(:N))
                 (\i. drop(partial_derivative k (\w. lift((b:real^(N,1)finite_sum->real^N) w$i)) z) %
                      partial_derivative i
                        (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) z) +
               drop(partial_derivative k (\w. lift((c:real^(N,1)finite_sum->real) w)) z) %
               wan_moll (inv(&n + &1)) v z` THEN
  ABBREV_TAC
   `G2 = \n i z. (partial_derivative k ((Gd:num->num->real^(N,1)finite_sum->real^1) n i) z +
                  vsum(1..dimindex(:N))
                    (\j. drop(partial_derivative k
                                (\w. lift((a:real^(N,1)finite_sum->real^N^N) w$i$j)) z) %
                         partial_derivative j
                           (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) z)) +
                 (if i = k then (Fd:num->real^(N,1)finite_sum->real^1) n z else vec 0)` THEN
  SUBGOAL_THEN
   `!n. wan_ceq a b c ((F2:num->real^(N,1)finite_sum->real^1) n)
                ((G2:num->num->real^(N,1)finite_sum->real^1) n)
                ((D:num->real^(N,1)finite_sum->real^1) n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["F2"; "G2"; "D"] THEN REWRITE_TAC[] THEN
    USE_THEN "ceq" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (!j z. ~(z IN k1)
               ==> partial_derivative j
                     (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) z = vec 0) /\
        (!j. smooth_map_on (:real^(N,1)finite_sum)
               (partial_derivative j (wan_moll (inv(&n + &1)) v)))`
  (LABEL_TAC "pdv") THENL
   [GEN_TAC THEN USE_THEN "dat" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WAN_PEN_PSUPPORT THEN EXISTS_TAC `k1:real^(N,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^(N,1)finite_sum) ((D:num->real^(N,1)finite_sum->real^1) n) /\
        (!z. ~(z IN k1) ==> D n z = vec 0) /\
        smooth_map_on (:real^(N,1)finite_sum) ((F2:num->real^(N,1)finite_sum->real^1) n) /\
        (!z. ~(z IN k1) ==> F2 n z = vec 0) /\
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> smooth_map_on (:real^(N,1)finite_sum)
                   ((G2:num->num->real^(N,1)finite_sum->real^1) n i) /\
                 (!z. ~(z IN k1) ==> G2 n i z = vec 0)) /\
        wan_ceq a b c (F2 n) (G2 n) (D n)`
  (LABEL_TAC "seq") THENL
   [GEN_TAC THEN USE_THEN "dat" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "pdv" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["D"; "F2"; "G2"] THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC WAN_PEN_SMOOTH_DROPMUL THEN
        USE_THEN "cb" (fun th -> ASM_SIMP_TAC[th; WAN_PEN_SMOOTH_PARTIAL; ETA_AX]);
        MATCH_MP_TAC WAN_PEN_SMOOTH_DROPMUL THEN
        ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL; ETA_AX]];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO; VSUM_0; VECTOR_ADD_RID];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
          ASM_SIMP_TAC[OPEN_UNIV; ETA_AX; WAN_PEN_SMOOTH_PARTIAL] THEN
          MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
          MATCH_MP_TAC WAN_PEN_SMOOTH_DROPMUL THEN
          USE_THEN "ca" (fun th -> ASM_SIMP_TAC[th; WAN_PEN_SMOOTH_PARTIAL; ETA_AX]);
          ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[ETA_AX; SMOOTH_MAP_ON_CONST]];
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN
         `partial_derivative k ((Gd:num->num->real^(N,1)finite_sum->real^1) n i) z = vec 0`
        SUBST1_TAC THENL
         [MATCH_MP_TAC WAN_PEN_PSUPPORT THEN EXISTS_TAC `k1:real^(N,1)finite_sum->bool` THEN
          ASM_SIMP_TAC[];
          ASM_SIMP_TAC[VECTOR_MUL_RZERO; VSUM_0; VECTOR_ADD_RID; VECTOR_ADD_LID; COND_ID]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l2c (\n. wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) v`
  (LABEL_TAC "LV") THENL
   [MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `k0:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_l2c (\n. partial_derivative j
                           (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)))
                    ((K:num->real^(N,1)finite_sum->real^1) j)`
  (LABEL_TAC "LJ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_L2C_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\n. wan_moll (inv(&n + &1)) ((K:num->real^(N,1)finite_sum->real^1) j)`;
      `(K:num->real^(N,1)finite_sum->real^1) j`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SEQ_L2C THEN EXISTS_TAC `k0:real^(N,1)finite_sum->bool` THEN
      ASM_SIMP_TAC[];
      REPEAT GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_MOLL_WPD THEN
      ASM_SIMP_TAC[WAN_INV_N1_POS];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(wan_dpart k (\y. (b:real^(N,1)finite_sum->real^N) y$i) x))
              continuous_on (:real^(N,1)finite_sum) /\
            (?B. !x. abs(wan_dpart k (\y. b y$i) x) <= B)`
  (LABEL_TAC "db") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP WAN_CC_FACTS (MATCH_MP (ISPECL [`k:num`; `\y. (b:real^(N,1)finite_sum->real^N) y$i`]
      WAN_CC_DPART) (MP (SPEC `i:num`
        (ASSUME `!i. 1 <= i /\ i <= dimindex(:N)
                     ==> wan_cc (\z. (b:real^(N,1)finite_sum->real^N) z$i)`))
        (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`))))) THEN
    REWRITE_TAC[ETA_AX] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(wan_dpart k (c:real^(N,1)finite_sum->real) x))
      continuous_on (:real^(N,1)finite_sum) /\
    (?B. !x. abs(wan_dpart k c x) <= B)`
  (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `Bc:real`)) THENL
   [MP_TAC(MATCH_MP WAN_CC_FACTS (MATCH_MP (ISPECL [`k:num`; `c:real^(N,1)finite_sum->real`]
      WAN_CC_DPART) (ASSUME `wan_cc (c:real^(N,1)finite_sum->real)`))) THEN
    REWRITE_TAC[ETA_AX] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l2c (F2:num->real^(N,1)finite_sum->real^1)
     (\z. vsum(1..dimindex(:N))
            (\i. wan_dpart k (\y. (b:real^(N,1)finite_sum->real^N) y$i) z %
                 (K:num->real^(N,1)finite_sum->real^1) i z) +
          wan_dpart k (c:real^(N,1)finite_sum->real) z % (v:real^(N,1)finite_sum->real^1) z)`
  (LABEL_TAC "LF2") THENL
   [EXPAND_TAC "F2" THEN
    SUBGOAL_THEN
     `wan_l2c
       (\n z. vsum(1..dimindex(:N))
                (\i. wan_dpart k (\y. (b:real^(N,1)finite_sum->real^N) y$i) z %
                     partial_derivative i
                       (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) z) +
              wan_dpart k (c:real^(N,1)finite_sum->real) z % wan_moll (inv(&n + &1)) v z)
       (\z. vsum(1..dimindex(:N))
              (\i. wan_dpart k (\y. b y$i) z % (K:num->real^(N,1)finite_sum->real^1) i z) +
            wan_dpart k c z % v z)`
    (fun th -> MATCH_MP_TAC(MATCH_MP WAN_L2C_TRANSFORM th) THEN
               REWRITE_TAC[WAN_DROP_PD_LIFT]) THEN
    MATCH_MP_TAC WAN_L2C_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_L2C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "db" (fun th -> MP_TAC(MP (SPEC `i:num` th)
        (CONJ (ASSUME `1 <= i`) (ASSUME `i <= dimindex(:N)`)))) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `Bb:real`)) THEN
      MP_TAC(ISPECL [`\n. partial_derivative i
                            (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1))`;
                     `(K:num->real^(N,1)finite_sum->real^1) i`;
                     `wan_dpart k (\y. (b:real^(N,1)finite_sum->real^N) y$i)`; `Bb:real`]
                    WAN_L2C_MUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "LJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\n. wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)`;
                     `v:real^(N,1)finite_sum->real^1`;
                     `wan_dpart k (c:real^(N,1)finite_sum->real)`; `Bc:real`] WAN_L2C_MUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_l2c (Fd:num->real^(N,1)finite_sum->real^1) f` (LABEL_TAC "LFd") THENL
   [EXPAND_TAC "Fd" THEN MATCH_MP_TAC WAN_PSTEP_FLIM THEN
    EXISTS_TAC `k0:real^(N,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_l2c (\n. partial_derivative k
                           ((Gd:num->num->real^(N,1)finite_sum->real^1) n i))
                    ((w:num->num->real^(N,1)finite_sum->real^1) k i)`
  (LABEL_TAC "LGd") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Gd" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_PSTEP_GLIM THEN EXISTS_TAC `k0:real^(N,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_l2c (\n. (G2:num->num->real^(N,1)finite_sum->real^1) n i)
              (\z. (w:num->num->real^(N,1)finite_sum->real^1) k i z +
                   vsum(1..dimindex(:N))
                     (\j. wan_dpart k (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j) z %
                          (K:num->real^(N,1)finite_sum->real^1) j z) +
                   (if i = k then (f:real^(N,1)finite_sum->real^1) z else vec 0))`
  (LABEL_TAC "LG2") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "G2" THEN
    SUBGOAL_THEN
     `wan_l2c
       (\n z. (partial_derivative k ((Gd:num->num->real^(N,1)finite_sum->real^1) n i) z +
               vsum(1..dimindex(:N))
                 (\j. wan_dpart k (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j) z %
                      partial_derivative j
                        (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1)) z)) +
              (if i = k then (Fd:num->real^(N,1)finite_sum->real^1) n z else vec 0))
       (\z. ((w:num->num->real^(N,1)finite_sum->real^1) k i z +
             vsum(1..dimindex(:N))
               (\j. wan_dpart k (\y. a y$i$j) z % (K:num->real^(N,1)finite_sum->real^1) j z)) +
            (if i = k then (f:real^(N,1)finite_sum->real^1) z else vec 0))`
    (fun th -> MATCH_MP_TAC(MATCH_MP WAN_L2C_TRANSFORM th) THEN
               REWRITE_TAC[WAN_DROP_PD_LIFT; VECTOR_ADD_ASSOC]) THEN
    MATCH_MP_TAC WAN_L2C_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_L2C_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN USE_THEN "LGd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC WAN_L2C_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        MP_TAC(MATCH_MP WAN_CC_FACTS (MATCH_MP
          (ISPECL [`k:num`; `\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j`] WAN_CC_DPART)
          (MP (SPECL [`i:num`; `j:num`]
            (ASSUME `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                           ==> wan_cc (\z. (a:real^(N,1)finite_sum->real^N^N) z$i$j)`))
            (CONJ (ASSUME `1 <= i`) (CONJ (ASSUME `i <= dimindex(:N)`)
              (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`))))))) THEN
        REWRITE_TAC[ETA_AX] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (X_CHOOSE_TAC `Ba:real`) ASSUME_TAC))) THEN
        MP_TAC(ISPECL [`\n. partial_derivative j
                              (wan_moll (inv(&n + &1)) (v:real^(N,1)finite_sum->real^1))`;
                       `(K:num->real^(N,1)finite_sum->real^1) j`;
                       `wan_dpart k (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j)`;
                       `Ba:real`] WAN_L2C_MUL) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "LJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[ETA_AX; WAN_L2C_ZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_l2c (D:num->real^(N,1)finite_sum->real^1) ((K:num->real^(N,1)finite_sum->real^1) k)`
  (LABEL_TAC "LD") THENL
   [EXPAND_TAC "D" THEN USE_THEN "LJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> ?U. wan_l2c (\n. partial_derivative j ((D:num->real^(N,1)finite_sum->real^1) n)) U`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_ENERGY0_CAUCHY THEN
    MAP_EVERY EXISTS_TAC
     [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
      `c:real^(N,1)finite_sum->real`; `C:real`; `F2:num->real^(N,1)finite_sum->real^1`;
      `G2:num->num->real^(N,1)finite_sum->real^1`; `k1:real^(N,1)finite_sum->bool`;
      `(K:num->real^(N,1)finite_sum->real^1) k`;
      `\z. vsum(1..dimindex(:N))
             (\i. wan_dpart k (\y. (b:real^(N,1)finite_sum->real^N) y$i) z %
                  (K:num->real^(N,1)finite_sum->real^1) i z) +
           wan_dpart k (c:real^(N,1)finite_sum->real) z % (v:real^(N,1)finite_sum->real^1) z`;
      `\i z. (w:num->num->real^(N,1)finite_sum->real^1) k i z +
             vsum(1..dimindex(:N))
               (\j. wan_dpart k (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j) z %
                    (K:num->real^(N,1)finite_sum->real^1) j z) +
             (if i = k then (f:real^(N,1)finite_sum->real^1) z else vec 0)`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "seq" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "LF2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "LG2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ca" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `U:num->real^(N,1)finite_sum->real^1` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> wan_l2c (\n. partial_derivative j ((D:num->real^(N,1)finite_sum->real^1) n))
                    (\z. if z IN k1 then (U:num->real^(N,1)finite_sum->real^1) j z else vec 0)`
  (LABEL_TAC "LH") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_L2C_RESTRICT THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; ETA_AX] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC WAN_PEN_PSUPPORT THEN EXISTS_TAC `k1:real^(N,1)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\j z. if z IN k1 then (U:num->real^(N,1)finite_sum->real^1) j z else vec 0` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "LH" (fun th -> MP_TAC(MP (SPEC `j:num` th)
      (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`)))) THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[WAN_L2C_MEM];
      MATCH_MP_TAC WAN_WPD_LIMIT THEN
      EXISTS_TAC `D:num->real^(N,1)finite_sum->real^1` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "seq" (fun th -> REWRITE_TAC[th]);
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_GWEAK_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`F2:num->real^(N,1)finite_sum->real^1`; `G2:num->num->real^(N,1)finite_sum->real^1`;
    `D:num->real^(N,1)finite_sum->real^1`;
    `\n j. partial_derivative j ((D:num->real^(N,1)finite_sum->real^1) n)`] THEN
  REWRITE_TAC[] THEN
  USE_THEN "LD" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "LF2" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "LG2" (fun th -> SIMP_TAC[th]) THEN
  USE_THEN "LH" (fun th -> SIMP_TAC[th]) THEN
  USE_THEN "ca" (fun th -> SIMP_TAC[th]) THEN
  USE_THEN "cb" (fun th -> SIMP_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC WAN_CEQ_WEAK THEN
  ASM_SIMP_TAC[] THEN USE_THEN "ca" (fun th -> SIMP_TAC[th]));;

(* ========================================================================= *)
(* Whole-space Sobolev classes wan_hd d s u (iterated weak                  *)
(* derivatives in the directions of d, all in L^2) and their algebra.       *)
(* ========================================================================= *)

let wan_hd = define
 `(wan_hd (d:num->bool) 0 (u:real^M->real^K) <=> u IN lspace (:real^M) (&2)) /\
  (wan_hd d (SUC s) u <=>
     u IN lspace (:real^M) (&2) /\
     !k. k IN d ==> ?w. wan_wpd (:real^M) k u w /\ wan_hd d s w)`;;

let WAN_HD_LSPACE = prove
 (`!d s (u:real^M->real^K). wan_hd d s u ==> u IN lspace (:real^M) (&2)`,
  GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[wan_hd]);;

let WAN_HD_MONO = prove
 (`!d s (u:real^M->real^K). wan_hd d (SUC s) u ==> wan_hd d s u`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[wan_hd]; ALL_TAC] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[wan_hd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^M->real^K` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let WAN_HD_MONO_LE = prove
 (`!d s t (u:real^M->real^K). s <= t /\ wan_hd d t u ==> wan_hd d s u`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[ARITH_RULE `s <= 0 <=> s = 0`]; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `s <= SUC t <=> s = SUC t \/ s <= t`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[WAN_HD_MONO]);;

let WAN_HD_ZERO = prove
 (`!d s. wan_hd d s (\x:real^M. vec 0:real^K)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[wan_hd; WAN_LSPACE2_ZERO] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^M. vec 0:real^K` THEN
  ASM_REWRITE_TAC[WAN_WPD_ZERO]);;

let WAN_HD_ADD = prove
 (`!d s (u:real^M->real^K) u'.
     wan_hd d s u /\ wan_hd d s u' ==> wan_hd d s (\x. u x + u' x)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[wan_hd; LSPACE_ADD; REAL_POS]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wan_hd] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LSPACE_ADD; REAL_POS] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w':real^M->real^K` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M->real^K` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
  EXISTS_TAC `\x. (w:real^M->real^K) x + w' x` THEN
  ASM_SIMP_TAC[WAN_WPD_ADD]);;

let WAN_HD_CMUL = prove
 (`!d s (u:real^M->real^K) c. wan_hd d s u ==> wan_hd d s (\x. c % u x)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [SIMP_TAC[wan_hd; LSPACE_CMUL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[wan_hd] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LSPACE_CMUL] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M->real^K` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
  EXISTS_TAC `\x. c % (w:real^M->real^K) x` THEN ASM_SIMP_TAC[WAN_WPD_CMUL]);;

let WAN_HD_NEG = prove
 (`!d s (u:real^M->real^K). wan_hd d s u ==> wan_hd d s (\x. --(u x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num->bool`; `s:num`; `u:real^M->real^K`; `-- &1`] WAN_HD_CMUL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let WAN_HD_SUB = prove
 (`!d s (u:real^M->real^K) u'.
     wan_hd d s u /\ wan_hd d s u' ==> wan_hd d s (\x. u x - u' x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB] THEN
  MP_TAC(ISPECL [`d:num->bool`; `s:num`; `u:real^M->real^K`; `\x. --((u':real^M->real^K) x)`]
                WAN_HD_ADD) THEN
  ASM_SIMP_TAC[WAN_HD_NEG]);;

let WAN_HD_VSUM = prove
 (`!d s (u:A->real^M->real^K) t.
     FINITE t /\ (!i. i IN t ==> wan_hd d s (u i))
     ==> wan_hd d s (\x. vsum t (\i. u i x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; WAN_HD_ZERO; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s':A->bool`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num->bool`; `s:num`; `(u:A->real^M->real^K) a`;
                 `\x. vsum s' (\i. (u:A->real^M->real^K) i x)`] WAN_HD_ADD) THEN
  ASM_SIMP_TAC[]);;

let WAN_HD_MUL = prove
 (`!d s (m:real^M->real) (u:real^M->real^K).
     wan_cc m /\ wan_hd d s u ==> wan_hd d s (\x. m x % u x)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[wan_hd] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WAN_CC_FACTS) THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_hd d s (u:real^M->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_HD_MONO]; ALL_TAC] THEN
  UNDISCH_TAC `wan_hd d (SUC s) (u:real^M->real^K)` THEN
  ONCE_REWRITE_TAC[wan_hd] THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP WAN_CC_FACTS) THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M->real^K` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
  EXISTS_TAC `\x. wan_dpart k (m:real^M->real) x % (u:real^M->real^K) x + m x % w x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_WPD_MUL_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    ASM_MESON_TAC[wan_cc];
    MATCH_MP_TAC WAN_HD_ADD THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[WAN_CC_DPART; ETA_AX]]);;

let WAN_LSPACE_SPIKE = prove
 (`!(u:real^M->real^K) u' t p.
     negligible t /\ (!x. ~(x IN t) ==> u' x = u x) /\ u IN lspace (:real^M) p
     ==> u' IN lspace (:real^M) p`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`u:real^M->real^K`; `u':real^M->real^K`; `t:real^M->bool`; `(:real^M)`]
                  MEASURABLE_ON_SPIKE) THEN
    ASM_SIMP_TAC[IN_DIFF; IN_UNIV];
    MP_TAC(ISPECL [`\x. lift(norm((u:real^M->real^K) x) rpow p)`;
                   `\x. lift(norm((u':real^M->real^K) x) rpow p)`; `t:real^M->bool`;
                   `(:real^M)`] INTEGRABLE_SPIKE) THEN
    ASM_SIMP_TAC[IN_DIFF; IN_UNIV]]);;

let WAN_LLOC_SPIKE = prove
 (`!(u:real^M->real^K) u' t.
     negligible t /\ (!x. ~(x IN t) ==> u' x = u x) /\ wan_lloc (:real^M) u
     ==> wan_lloc (:real^M) u'`,
  REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^M->real^K`; `u':real^M->real^K`; `t:real^M->bool`;
                 `k:real^M->bool`] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
  ASM_SIMP_TAC[IN_DIFF]);;

let WAN_WPD_SPIKE = prove
 (`!(u:real^M->real^K) w u' w' k t.
     negligible t /\ (!x. ~(x IN t) ==> u' x = u x /\ w' x = w x) /\
     wan_wpd (:real^M) k u w
     ==> wan_wpd (:real^M) k u' w'`,
  REWRITE_TAC[wan_wpd] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC WAN_LLOC_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^M->real^K`; `t:real^M->bool`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC WAN_LLOC_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`w:real^M->real^K`; `t:real^M->bool`] THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^M->real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `(x:real^N) = x' /\ (y:real^N) = y' ==> x = --y ==> x' = --y'`) THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `t:real^M->bool` THEN
    ASM_SIMP_TAC[IN_DIFF; IN_UNIV]]);;

let WAN_HD_SPIKE = prove
 (`!d s (u:real^M->real^K) u' t.
     negligible t /\ (!x. ~(x IN t) ==> u' x = u x) /\ wan_hd d s u
     ==> wan_hd d s u'`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[wan_hd] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^M->real^K`; `t:real^M->bool`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC WAN_LSPACE_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^M->real^K`; `t:real^M->bool`] THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M->real^K` STRIP_ASSUME_TAC o
      C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
    EXISTS_TAC `w:real^M->real^K` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_SPIKE THEN
    MAP_EVERY EXISTS_TAC [`u:real^M->real^K`; `w:real^M->real^K`; `t:real^M->bool`] THEN
    ASM_SIMP_TAC[]]);;

let WAN_HD_WPD = prove
 (`!d s (u:real^M->real^K) w k.
     wan_hd d (SUC s) u /\ k IN d /\ wan_wpd (:real^M) k u w ==> wan_hd d s w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_hd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w0:real^M->real^K` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
  MATCH_MP_TAC WAN_HD_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`w0:real^M->real^K`; `{x:real^M | ~((w0:real^M->real^K) x = w x)}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`(:real^M)`; `k:num`; `u:real^M->real^K`; `w0:real^M->real^K`;
                 `w:real^M->real^K`] WAN_WPD_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Weak derivatives of compactly supported functions may be taken with the  *)
(* same support.                                                             *)
(* ------------------------------------------------------------------------- *)

let WAN_WPD_RESTRICT = prove
 (`!(u:real^M->real^K) w l k0.
     compact k0 /\ (!x. ~(x IN k0) ==> u x = vec 0) /\ wan_wpd (:real^M) l u w
     ==> negligible {x | ~((\x. if x IN k0 then w x else vec 0) x = w x)} /\
         wan_wpd (:real^M) l u (\x. if x IN k0 then w x else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open((:real^M) DIFF k0)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | x IN (:real^M) DIFF k0 /\ ~((w:real^M->real^K) x = vec 0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_FUNDAMENTAL_LEMMA THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LLOC_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[wan_wpd];
      ALL_TAC] THEN
    X_GEN_TAC `phi:real^M->real` THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `kp:real^M->bool` STRIP_ASSUME_TAC o
      CONJUNCT2 o REWRITE_RULE[wan_test]) THEN
    TRANS_TAC EQ_TRANS `integral (:real^M) (\x. phi x % (w:real^M->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `kp:real^M->bool` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; VECTOR_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `wan_test (:real^M) phi` ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_TEST_SUBSET THEN EXISTS_TAC `(:real^M) DIFF k0` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    MP_TAC(ASSUME `wan_wpd (:real^M) l (u:real^M->real^K) w`) THEN
    REWRITE_TAC[wan_wpd] THEN DISCH_THEN(MP_TAC o SPEC `phi:real^M->real` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. wan_dpart l phi x % (u:real^M->real^K) x) = (\x. vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
      ASM_CASES_TAC `(x:real^M) IN k0` THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO] THEN
      SUBGOAL_THEN `wan_dpart l phi (x:real^M) = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `kp:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[wan_test]; ASM SET_TAC[]];
      REWRITE_TAC[INTEGRAL_0] THEN
      MATCH_ACCEPT_TAC(VECTOR_ARITH `vec 0 = --(x:real^N) ==> x = vec 0`)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | ~((\x. if x IN k0 then (w:real^M->real^K) x else vec 0) x = w x)} =
    {x | x IN (:real^M) DIFF k0 /\ ~(w x = vec 0)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WPD_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`u:real^M->real^K`; `w:real^M->real^K`;
                        `{x | x IN (:real^M) DIFF k0 /\ ~((w:real^M->real^K) x = vec 0)}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let WAN_HD_SUPPORT_WITNESS = prove
 (`!d s (u:real^M->real^K) k k0.
     wan_hd d (SUC s) u /\ k IN d /\ compact k0 /\ (!x. ~(x IN k0) ==> u x = vec 0)
     ==> ?w. wan_wpd (:real^M) k u w /\ wan_hd d s w /\ (!x. ~(x IN k0) ==> w x = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[wan_hd]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->real^K` STRIP_ASSUME_TAC o
    C MATCH_MP (ASSUME `(k:num) IN d`)) THEN
  MP_TAC(ISPECL [`u:real^M->real^K`; `w:real^M->real^K`; `k:num`; `k0:real^M->bool`]
                WAN_WPD_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. if x IN k0 then (w:real^M->real^K) x else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_HD_SPIKE THEN
    MAP_EVERY EXISTS_TAC
     [`w:real^M->real^K`;
      `{x | ~((\x. if x IN k0 then (w:real^M->real^K) x else vec 0) x = w x)}`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The spatial bootstrap.  Data f in H^s and g in H^(s+1)                  *)
(* (spatial Sobolev classes) give v in H^(s+2).                              *)
(* ========================================================================= *)

let WAN_PSTEP_HD = prove
 (`!lam (a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
    (g:num->real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1)
    (K:num->real^(N,1)finite_sum->real^1) k0 s.
     &0 < lam /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c /\
     (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi)) /\
     compact k0 /\
     (!z. ~(z IN k0) ==> v z = vec 0) /\ (!z. ~(z IN k0) ==> f z = vec 0) /\
     (!j z. 1 <= j /\ j <= dimindex(:N) /\ ~(z IN k0) ==> K j z = vec 0) /\
     (!i z. 1 <= i /\ i <= dimindex(:N) /\ ~(z IN k0) ==> g i z = vec 0) /\
     v IN lspace (:real^(N,1)finite_sum) (&2) /\ f IN lspace (:real^(N,1)finite_sum) (&2) /\
     (!j. 1 <= j /\ j <= dimindex(:N)
          ==> K j IN lspace (:real^(N,1)finite_sum) (&2) /\
              wan_wpd (:real^(N,1)finite_sum) j v (K j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_hd (1..dimindex(:N)) (SUC s) (g i)) /\
     wan_gweak a b c f g v K
     ==> ?w. (!l i. 1 <= l /\ l <= dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N)
                    ==> wan_wpd (:real^(N,1)finite_sum) l (g i) (w l i) /\
                        wan_hd (1..dimindex(:N)) s (w l i) /\
                        (!z. ~(z IN k0) ==> w l i z = vec 0)) /\
             !k. 1 <= k /\ k <= dimindex(:N)
                 ==> ?H. (!j. 1 <= j /\ j <= dimindex(:N)
                              ==> H j IN lspace (:real^(N,1)finite_sum) (&2) /\
                                  wan_wpd (:real^(N,1)finite_sum) j (K k) (H j) /\
                                  (!z. ~(z IN {x + y | x IN k0 /\ y IN cball(vec 0,&1)})
                                       ==> H j z = vec 0)) /\
                         wan_gweak a b c
                           (\z. vsum(1..dimindex(:N))
                                  (\i. wan_dpart k (\y. b y$i) z % K i z) +
                                wan_dpart k c z % v z)
                           (\i z. w k i z +
                                  vsum(1..dimindex(:N))
                                    (\j. wan_dpart k (\y. a y$i$j) z % K j z) +
                                  (if i = k then f z else vec 0))
                           (K k) H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l i. 1 <= l /\ l <= dimindex(:N) /\ 1 <= i /\ i <= dimindex(:N)
          ==> ?w'. wan_wpd (:real^(N,1)finite_sum) l ((g:num->real^(N,1)finite_sum->real^1) i) w' /\
                   wan_hd (1..dimindex(:N)) s w' /\ (!z. ~(z IN k0) ==> w' z = vec 0)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_SUPPORT_WITNESS THEN
    ASM_SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:num->num->real^(N,1)finite_sum->real^1` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC WAN_PSTEP THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `g:num->real^(N,1)finite_sum->real^1`] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[WAN_HD_LSPACE]);;

let WAN_PSTEP_BOOT = prove
 (`!lam (a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
    (c:real^(N,1)finite_sum->real).
     &0 < lam /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> wan_cc (\z. a z$i$j)) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_cc (\z. b z$i)) /\ wan_cc c /\
     (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi))
     ==> !s (f:real^(N,1)finite_sum->real^1) (g:num->real^(N,1)finite_sum->real^1)
           (v:real^(N,1)finite_sum->real^1) (K:num->real^(N,1)finite_sum->real^1) k0.
           compact k0 /\
           (!z. ~(z IN k0) ==> v z = vec 0) /\ (!z. ~(z IN k0) ==> f z = vec 0) /\
           (!j z. 1 <= j /\ j <= dimindex(:N) /\ ~(z IN k0) ==> K j z = vec 0) /\
           (!i z. 1 <= i /\ i <= dimindex(:N) /\ ~(z IN k0) ==> g i z = vec 0) /\
           v IN lspace (:real^(N,1)finite_sum) (&2) /\
           (!j. 1 <= j /\ j <= dimindex(:N)
                ==> K j IN lspace (:real^(N,1)finite_sum) (&2) /\
                    wan_wpd (:real^(N,1)finite_sum) j v (K j)) /\
           wan_gweak a b c f g v K /\
           wan_hd (1..dimindex(:N)) s f /\
           (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_hd (1..dimindex(:N)) (SUC s) (g i))
           ==> wan_hd (1..dimindex(:N)) (SUC(SUC s)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`lam:real`; `a:real^(N,1)finite_sum->real^N^N`;
                   `b:real^(N,1)finite_sum->real^N`; `c:real^(N,1)finite_sum->real`;
                   `f:real^(N,1)finite_sum->real^1`; `g:num->real^(N,1)finite_sum->real^1`;
                   `v:real^(N,1)finite_sum->real^1`; `K:num->real^(N,1)finite_sum->real^1`;
                   `k0:real^(N,1)finite_sum->bool`; `0`] WAN_PSTEP_HD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_HD_LSPACE THEN
      MAP_EVERY EXISTS_TAC [`1..dimindex(:N)`; `0`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num->num->real^(N,1)finite_sum->real^1`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))) THEN
    REWRITE_TAC[wan_hd; IN_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    EXISTS_TAC `(K:num->real^(N,1)finite_sum->real^1) k` THEN ASM_SIMP_TAC[] THEN
    USE_THEN "st" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (CONJ (ASSUME `1 <= k`) (ASSUME `k <= dimindex(:N)`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `H:num->real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    EXISTS_TAC `(H:num->real^(N,1)finite_sum->real^1) j` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_hd (1..dimindex(:N)) (SUC(SUC s)) (v:real^(N,1)finite_sum->real^1)`
  ASSUME_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`f:real^(N,1)finite_sum->real^1`; `g:num->real^(N,1)finite_sum->real^1`;
      `K:num->real^(N,1)finite_sum->real^1`; `k0:real^(N,1)finite_sum->bool`] THEN
    ASM_SIMP_TAC[WAN_HD_MONO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_hd (1..dimindex(:N)) (SUC s) ((K:num->real^(N,1)finite_sum->real^1) i)`
  (LABEL_TAC "KH") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_HD_WPD THEN
    MAP_EVERY EXISTS_TAC [`v:real^(N,1)finite_sum->real^1`; `i:num`] THEN
    ASM_SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `a:real^(N,1)finite_sum->real^N^N`;
                 `b:real^(N,1)finite_sum->real^N`; `c:real^(N,1)finite_sum->real`;
                 `f:real^(N,1)finite_sum->real^1`; `g:num->real^(N,1)finite_sum->real^1`;
                 `v:real^(N,1)finite_sum->real^1`; `K:num->real^(N,1)finite_sum->real^1`;
                 `k0:real^(N,1)finite_sum->bool`; `SUC s`] WAN_PSTEP_HD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_HD_LSPACE THEN
    MAP_EVERY EXISTS_TAC [`1..dimindex(:N)`; `SUC s`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->num->real^(N,1)finite_sum->real^1`
    (CONJUNCTS_THEN2 (LABEL_TAC "wd") (LABEL_TAC "st"))) THEN
  ONCE_REWRITE_TAC[wan_hd] THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  EXISTS_TAC `(K:num->real^(N,1)finite_sum->real^1) k` THEN ASM_SIMP_TAC[] THEN
  USE_THEN "st" (fun th -> MP_TAC(MP (SPEC `k:num` th)
      (CONJ (ASSUME `1 <= k`) (ASSUME `k <= dimindex(:N)`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `H:num->real^(N,1)finite_sum->real^1` STRIP_ASSUME_TAC) THEN
  USE_THEN "IH" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\z. vsum(1..dimindex(:N))
          (\i. wan_dpart k (\y. (b:real^(N,1)finite_sum->real^N) y$i) z %
               (K:num->real^(N,1)finite_sum->real^1) i z) +
        wan_dpart k (c:real^(N,1)finite_sum->real) z % (v:real^(N,1)finite_sum->real^1) z`;
    `\i z. (w:num->num->real^(N,1)finite_sum->real^1) k i z +
           vsum(1..dimindex(:N))
             (\j. wan_dpart k (\y. (a:real^(N,1)finite_sum->real^N^N) y$i$j) z %
                  (K:num->real^(N,1)finite_sum->real^1) j z) +
           (if i = k then (f:real^(N,1)finite_sum->real^1) z else vec 0)`;
    `H:num->real^(N,1)finite_sum->real^1`;
    `{x + y:real^(N,1)finite_sum | x IN k0 /\ y IN cball(vec 0,&1)}`] THEN
  ASM_SIMP_TAC[WAN_CBALL_SUMS_COMPACT] THEN
  SUBGOAL_THEN
   `!z. ~(z IN {x + y:real^(N,1)finite_sum | x IN k0 /\ y IN cball(vec 0,&1)})
        ==> ~(z IN k0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `k0:real^(N,1)finite_sum->bool` WAN_CBALL_SUMS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((z:real^(N,1)finite_sum) IN k0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((z:real^(N,1)finite_sum) IN k0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VSUM_0; VECTOR_ADD_RID];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((z:real^(N,1)finite_sum) IN k0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VSUM_0; VECTOR_ADD_RID; VECTOR_ADD_LID; COND_ID] THEN
    USE_THEN "wd" (MP_TAC o SPECL [`k:num`; `i:num`]) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC WAN_HD_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_HD_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_HD_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_CC_DPART THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC WAN_HD_MONO THEN USE_THEN "KH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC WAN_HD_MUL THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_CC_DPART] THEN
      MATCH_MP_TAC WAN_HD_MONO_LE THEN EXISTS_TAC `SUC(SUC s)` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_HD_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN USE_THEN "wd" (MP_TAC o SPECL [`k:num`; `i:num`]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC WAN_HD_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_HD_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_HD_MUL THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [MATCH_MP_TAC WAN_CC_DPART THEN ASM_SIMP_TAC[];
        USE_THEN "KH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[ETA_AX; WAN_HD_ZERO]]]);;

