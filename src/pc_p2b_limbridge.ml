(* ========================================================================= *)
(* pc_p2b_limbridge (Part 2B): two bridges between the limit notions of      *)
(* pc_p3_iface and pc_p3_defs, in a unit of their own so that they can be    *)
(* used without loading pc_p2b_t911:                                         *)
(*   P2B11_P3_SLICE: p3_flow_limit on (-Tl,0] gives p2c_slice_limit_with at  *)
(*     time 0;                                                               *)
(*   P2B11_SLICE_TO_FLOW0: p2c_slice_limit_with gives p2c_flow_limit_with    *)
(*     on J = {0} with the constant flow.                                    *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* A flow limit on (-Tl,0] gives the slice limit at time 0. *)

let P2B11_P3_SLICE = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g xl Tl.
     p3_flow_limit V x t Q (top,atlas) g xl Tl
     ==> ?W phi. p2c_slice_limit_with V x t Q (top,atlas) (g(&0)) xl W phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto")
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `ts:num->real`
    (X_CHOOSE_THEN `phi:num->B->A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ts")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dif") (LABEL_TAC "lck")))))))))))))))) THEN
  MAP_EVERY EXISTS_TAC [`W:num->B->bool`; `phi:num->B->A`] THEN
  REWRITE_TAC[p2c_slice_limit_with] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "upto" (MP_TAC o SPEC `--(Tl / &2)`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]];
    X_GEN_TAC `k:num` THEN USE_THEN "dif" (MP_TAC o SPECL [`k:num`; `&0`]) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "ts" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`K:B->bool`; `m:num`; `eta:real`] THEN STRIP_TAC THEN
    USE_THEN "lck" (MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`; `&0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
    DISCH_THEN(fun th -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `&0`))) THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID; REAL_LE_REFL]]);;

(* A slice limit is a flow limit on J = {0}. *)

let P2B11_SLICE_TO_FLOW0 = prove
 (`!(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    x t Q (top:B topology) atlas g0 xl W phi.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi
     ==> p2c_flow_limit_with V x t Q {&0} (top,atlas) (\s. g0) xl W phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_slice_limit_with; p2c_flow_limit_with; IN_SING] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `K:B->bool`; `m:num`; `eta:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`K:B->bool`; `m:num`; `eta:real`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k0:num` THEN
  DISCH_THEN(fun th -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN MP_TAC(SPEC `k:num` th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s. a <= s /\ s <= b ==> s = &0` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `real_interval[a,b] SUBSET {&0}` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_SING] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s = &0` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN ASM_SIMP_TAC[]]);;

