(* ========================================================================= *)
(* Unit pc_p3_c1712r: the route theorem of MT Lemma 17.12 (on the history   *)
(* carrier A + num#num#real^3 with the invariant                            *)
(* p3_extra, whose second conjunct is the hypothesis p3h_plus_disc of        *)
(* P3H_LEMMA_17_12_CORE).  The route input P2_LEMMA_12_3_STATEMENT is not   *)
(* needed.                                                                   *)
(* ========================================================================= *)

needs "src/pc_p3_c1712.ml";;
needs "src/pc_p3_route.ml";;

prioritize_real();;
type_invention_error := true;;

let P3H_EXTRA_PLUS_DISC = prove
 (`!dl (hs:(A+num#num#real^3)rfs_history). p3_extra dl hs ==> p3h_plus_disc dl hs`,
  REWRITE_TAC[p3_extra; p3h_plus_disc] THEN MESON_TAC[]);;

let P3_LEMMA_17_12_ROUTE = prove
 (`!u:A->bool. P3_LEMMA_17_12_ROUTE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P3_LEMMA_17_12_ROUTE_STATEMENT; P3_LEMMA_17_12_STATEMENT] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `(:A+num#num#real^3)` P3H_LEMMA_17_12_CORE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "core") THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_THEN "core" (MP_TAC o SPEC_ALL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1712:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N"))) THEN
  EXISTS_TAC `d1712:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_THEN "N" (MP_TAC o SPEC_ALL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "cnt")) THEN EXISTS_TAC `N:num` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "cnt" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`rp:real->real`; `dl:real->real`] THEN
  ASM_SIMP_TAC[P3H_EXTRA_PLUS_DISC]);;

