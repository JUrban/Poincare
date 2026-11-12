(* ========================================================================= *)
(* Unit pc_p2b_g3 (Part 2B): the route theorem P2B_W920_G3_ROUTE of the      *)
(* statements-only unit pc_p2b_w920g: for every output of G1 the reduced     *)
(* volume of linf is the limit V of the reduced volumes of the flow          *)
(* (pc_p2b_g3a) and the weak equation p2bg_weq holds in every chart box of   *)
(* the limit (pc_p2b_g3b to pc_p2b_g3g: subsolution on boxes, partitions and *)
(* the global functional, cutoffs, slices and the limit R to infinity).      *)
(* ========================================================================= *)

needs "src/pc_p2b_g3g.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The route.                                                                *)
(* ========================================================================= *)

let P2B_W920_G3_ROUTE = prove
 (`!(u:A->bool) (w:B->bool). P2B_W920_G3_ROUTE_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_W920_G3_ROUTE_STATEMENT; P2B_W920_G3_STATEMENT] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`]
                P2BX_G3_RVOL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[p2bg_g3out] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `V:real`; `c:(B->bool)#(B->real^3)`; `om:real^(3,1)finite_sum->bool`]
                  P2BX_BOX_WEQ) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `V:real` THEN ASM_REWRITE_TAC[]]);;

