(* ========================================================================= *)
(* pc_apx_chchart: the product chart of a one-sided infinite chain of       *)
(* eps-necks, in the form of the statement P2BT_REQ_CHAIN_CHART_STATEMENT   *)
(* of pc_p2b_tubestmts.  The construction is in pc_apx_chcore (below the    *)
(* interface files, shared with pc_apx_ncends); this unit only states the   *)
(* headline at the chain type B.                                            *)
(* ========================================================================= *)

needs "src/pc_apx_chcore.ml";;
needs "src/pc_p2b_tubestmts.ml";;

prioritize_real();;
type_invention_error := true;;


(* The headline: P2BT_REQ_CHAIN_CHART_STATEMENT (the extra hypothesis      *)
(* apx_sphere_sep of the statement is not needed).                          *)

let APXC_CHAIN_CHART = prove
 (`!w:B->bool. P2BT_REQ_CHAIN_CHART_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2BT_REQ_CHAIN_CHART_STATEMENT] THEN
  MP_TAC(MATCH_MP APXC_CHART_CORE (ISPEC `w:B->bool` SMT_PRODUCT2)) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:B->real^3^3`; `eps:real`; `x:int->B`; `e:int->real^3->B`]) THEN
  ASM_REWRITE_TAC[]);;

