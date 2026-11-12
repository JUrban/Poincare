(* ========================================================================= *)
(* Unit pc_p2b_allneck: piece (g) of COR_9_94_L, the statement               *)
(* P2B_ALL_NECK_LINE_STATEMENT of pc_p2b_c994req: for eps small, a complete  *)
(* connected manifold with apx_sphere_sep all of whose points are centres of *)
(* eps-necks is not compact and contains a line.  Headline:                  *)
(* P2BAN_ALL_NECK_LINE.                                                      *)
(*                                                                           *)
(* Route: P2HN_TWO_ENDS (pc_p2c_nsides; APX_A19 on the closure of a side of  *)
(* a neck sphere and the end separation clause of apx_tube: no side of a     *)
(* neck sphere has compact closure) gives a compact K with two different     *)
(* components of the complement whose closures are not compact; hence the    *)
(* space is not compact, and APXT_TWO_ENDS_LINE gives the line.              *)
(* ========================================================================= *)

needs "src/pc_p2b_c994req.ml";;
needs "src/pc_apx_twoends.ml";;
needs "src/pc_p2c_nsides.ml";;

prioritize_real();;
type_invention_error := true;;



(* ------------------------------------------------------------------------- *)
(* The headline.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2BAN_ALL_NECK_LINE = prove
 (`!w:B->bool. P2B_ALL_NECK_LINE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_ALL_NECK_LINE_STATEMENT] THEN
  MP_TAC(INST_TYPE [`:B`,`:A`] P2HN_TWO_ENDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "te"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?x0:B. x0 IN topspace top` (X_CHOOSE_TAC `x0:B`) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?e0:real^3->B. rfs_neck (top,atlas) (g:B->real^3^3) eps x0 e0`
  (X_CHOOSE_TAC `e0:real^3->B`) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "te" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                 `g:B->real^3^3`; `eps:real`; `x0:B`; `e0:real^3->B`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:B->bool` (X_CHOOSE_THEN `U1:B->bool`
   (X_CHOOSE_THEN `U2:B->bool` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~compact_in top (top closure_of (U1:B->bool))` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    MATCH_MP_TAC APXT_TWO_ENDS_LINE THEN
    MAP_EVERY EXISTS_TAC [`K:B->bool`; `U1:B->bool`; `U2:B->bool`] THEN
    ASM_REWRITE_TAC[]]);;

