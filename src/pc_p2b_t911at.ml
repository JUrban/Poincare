(* ========================================================================= *)
(* pc_p2b_t911at (Part 2B): MT Thm 9.11 at a given base point.               *)
(* Main theorem:                                                             *)
(*   P2B_THM_9_11_AT_ROUTE |- !w. P2B_THM_9_11_AT_ROUTE_STATEMENT w         *)
(* (the inputs of THM_9_11_ROUTE ==> P2B_THM_9_11_AT_STATEMENT: the based   *)
(* form with l(q k, tau k) <= 3/2, in pc_p2b_chainstmts).  The proof of      *)
(* P2B11_THM_9_11_CORE (pc_p2b_t911) with the base point given instead of    *)
(* chosen; p2b11_flim already keeps the bound l <= 3/2.                      *)
(* ========================================================================= *)

needs "src/pc_p2b_t911.ml";;

prioritize_real();;
type_invention_error := true;;

(* T911.B19 THM_9_11 at a given base point p                             *)
(* (P2B_THM_9_11_AT_STATEMENT of pc_p2b_chainstmts): the proof of         *)
(* P2B11_THM_9_11_CORE with p given instead of chosen, exporting the bound *)
(* l(q k, tau k) <= 3/2 kept by p2b11_flim; and the AT route theorem.      *)

let P2B11_THM_9_11_AT_CORE = prove
 (`!w:B->bool.
     P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     P2B_PROP_9_20_STATEMENT w w /\ P2B_SOLITON_FROM_LINF_FIX_STATEMENT w /\
     P2B_KSOL_DRDT_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     P2C_PROP_5_14_STATEMENT w w
     ==> P2B_THM_9_11_AT_STATEMENT w`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl4") (CONJUNCTS_THEN2 (LABEL_TAC "cor")
    (CONJUNCTS_THEN2 (LABEL_TAC "p920") (CONJUNCTS_THEN2 (LABEL_TAC "sol")
    (CONJUNCTS_THEN2 (LABEL_TAC "drdt") (CONJUNCTS_THEN2 (LABEL_TAC "ac")
    (LABEL_TAC "514"))))))) THEN
  REWRITE_TAC[P2B_THM_9_11_AT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `p:B`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:B->bool`; `kappa:real`; `top:B topology`;
                 `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`]
                P2B11_FLIM_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->real` (X_CHOOSE_THEN `q:num->B`
    (X_CHOOSE_THEN `top':B topology` (X_CHOOSE_THEN `atlas':((B->bool)#(B->real^3))->bool`
    (X_CHOOSE_THEN `g':real->B->real^3^3` (X_CHOOSE_THEN `xl:B`
    (X_CHOOSE_THEN `W:num->B->bool` (X_CHOOSE_THEN `phi:num->B->B` (LABEL_TAC "flim"))))))))) THEN
  USE_THEN "flim" (STRIP_ASSUME_TAC o MATCH_MP P2B11_FLIM_FACTS) THEN
  USE_THEN "flim" (LABEL_TAC "sec" o MATCH_MP P2B11_FLIM_SEC) THEN
  USE_THEN "flim" (LABEL_TAC "rfo1" o MATCH_MP P2B11_FLIM_RFO1) THEN
  USE_THEN "flim" (LABEL_TAC "back" o MATCH_MP P2B11_FLIM_COMPLETE_BACK) THEN
  USE_THEN "flim" (STRIP_ASSUME_TAC o REWRITE_RULE[p2b11_flim]) THEN
  (* complete slices for s < 1 *)
  SUBGOAL_THEN `!s. s < &1 ==> mfd_complete (top',atlas') ((g':real->B->real^3^3) s)`
  (LABEL_TAC "comp") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN ASM_CASES_TAC `s <= &0` THENL
     [USE_THEN "back" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2B11_FLIM_COMPLETE_FWD THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `tau:num->real`;
        `q:num->B`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Prop 9.20 *)
  USE_THEN "p920" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`;
    `tau:num->real`; `q:num->B`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] o
    REWRITE_RULE[P2B_PROP_9_20_STATEMENT]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2bg_setup] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `linf:real->B->real`
    (X_CHOOSE_THEN `V:real` STRIP_ASSUME_TAC))) THEN
  (* the leaf *)
  USE_THEN "sol" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `linf:real->B->real`; `V:real`] o
    REWRITE_RULE[P2B_SOLITON_FROM_LINF_FIX_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
        NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "shr") (LABEL_TAC "nonflat")) THEN
  MAP_EVERY EXISTS_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `\s:real. (linf:real->B->real) (&1 - s)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[] THEN USE_THEN "shr" ACCEPT_TAC THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC P2B11_FLIM_P3_ON THEN
      MAP_EVERY EXISTS_TAC [`kappa:real`; `p:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      USE_THEN "flim" ACCEPT_TAC THEN NO_TAC) THEN
  REWRITE_TAC[p2b_ancflow0] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MP_TAC(ASSUME `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)`) THEN
      REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SIMP_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `xl:B` THEN ASM_REWRITE_TAC[] THEN
      NO_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(MATCH_MP_TAC P2B11_FLIM_DRDS THEN
      MAP_EVERY EXISTS_TAC [`w:B->bool`; `kappa:real`; `top:B topology`;
        `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`; `tau:num->real`;
        `q:num->B`; `xl:B`; `W:num->B->bool`; `phi:num->B->B`] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC P2B11_FLIM_KNC THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `p:B`; `tau:num->real`; `q:num->B`; `xl:B`;
    `W:num->B->bool`; `phi:num->B->B`] THEN
  CONJ_TAC THENL [USE_THEN "flim" ACCEPT_TAC; USE_THEN "comp" ACCEPT_TAC]);;

let P2B_THM_9_11_AT_ROUTE = prove
 (`!w:B->bool. P2B_THM_9_11_AT_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_THM_9_11_AT_ROUTE_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2B11_THM_9_11_AT_CORE THEN ASM_REWRITE_TAC[]);;

