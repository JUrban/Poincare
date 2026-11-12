(* ========================================================================= *)
(* Unit pc_sch_b1cut: part of the one-saddle base case of the smooth         *)
(* Schoenflies induction: the bridge from the single cut                     *)
(* SCH5S_SINGLE_CUT_CHART of pc_sch_surg to the cut hypothesis               *)
(* SCHY_CUT_STATEMENT of pc_sch_b1cls, so that SCHY_DEPS reduces to the      *)
(* statements SCH_BASE0_STATEMENT, SCH_LEVEL_NECK_STATEMENT and              *)
(* SCH_LEVEL_INNERMOST_STATEMENT (SCHY_DEPS_FROM_STATEMENTS,                 *)
(* SCHY_REDUCE_U4U7A).  It needs pc_sch_b1cls first (which loads pc_sch_glue *)
(* before pc_sch_vflow).                                                     *)
(* ========================================================================= *)

needs "src/pc_sch_b1cls.ml";;
needs "src/pc_sch_surg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* SCH5S_SINGLE_CUT_CHART implies SCHY_CUT_STATEMENT (weaker hypotheses; the *)
(* crit clauses of SCH5S_SINGLE_CUT_CHART are stronger; its iff clause gives *)
(* the two clauses "one of" and "not both").                                 *)
(* ------------------------------------------------------------------------- *)

let SCHY_CUT_FROM_SURG = prove
 (`SCHY_CUT_STATEMENT`,
  REWRITE_TAC[SCHY_CUT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`;
                       `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                       `Theta':real^3->real^3`; `H:real`; `lam:real`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `H:real`; `lam:real`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                 `Theta':real^3->real^3`] SCH5S_SINGLE_CUT_CHART) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
      (X_CHOOSE_THEN `e0:real` (fun th ->
        let ths = CONJUNCTS th in
        MAP_EVERY ASSUME_TAC ths THEN LABEL_TAC "C1" (el 14 ths) THEN
        LABEL_TAC "C2" (el 15 ths) THEN LABEL_TAC "CU" (el 16 ths))))))) THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `g2:real^3->real^3`;
                        `g2':real^3->real^3`; `e0:real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "C1" (fun th -> MP_TAC(MP (SPEC `t:real^3` th)
      (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN MESON_TAC[];
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    USE_THEN "C2" (fun th -> MP_TAC(MP (SPEC `t:real^3` th)
      (ASSUME `sch_crit (g2:real^3->real^3) t`))) THEN MESON_TAC[];
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    USE_THEN "CU" (fun th -> MP_TAC(MP (SPEC `u:real^3` th)
      (ASSUME `sch_crit (g:real^3->real^3) u`))) THEN MESON_TAC[];
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    USE_THEN "CU" (fun th -> MP_TAC(MP (SPEC `u:real^3` th)
      (ASSUME `sch_crit (g:real^3->real^3) u`))) THEN MESON_TAC[]]);;

let SCHY_DEPS_FROM_STATEMENTS = prove
 (`SCH_BASE0_STATEMENT /\ SCH_LEVEL_NECK_STATEMENT /\ SCH_LEVEL_INNERMOST_STATEMENT
   ==> SCHY_DEPS`,
  SIMP_TAC[SCHY_DEPS; SCHY_CUT_FROM_SURG]);;

let SCHY_REDUCE_U4U7A = prove
 (`SCH_BASE0_STATEMENT /\ SCH_LEVEL_NECK_STATEMENT /\ SCH_LEVEL_INNERMOST_STATEMENT /\
   SCHY_CANCEL_STATEMENT
   ==> SCH_BASE1_STATEMENT`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHY_REDUCE THEN ASM_SIMP_TAC[SCHY_DEPS_FROM_STATEMENTS]);;

