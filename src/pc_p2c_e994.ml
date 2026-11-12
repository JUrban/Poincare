(* ========================================================================= *)
(* Unit pc_p2c_e994 (Part 2C): MT Thm 9.89 (2), Claim 9.90 and Prop 9.91     *)
(* with length L for compact kappa-solutions:                                *)
(* P2KC_KSOL_COMPACT_CANON_L_ROUTE proves the statement                      *)
(* P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT of pc_p2b_c994req (used for      *)
(* COR_9_94_L).  It combines P2KC_KSOL_COMPACT_FROM_ROUTES (pc_p2c_e994c)    *)
(* with the two statements of pc_p2c_e994s, proved as P2KD_CLAIM_9_90_ROUTE  *)
(* (pc_p2c_c990) and P2BLD_LARGE_DR_ROUTE (pc_p2b_largedr).                  *)
(* ========================================================================= *)

needs "src/pc_p2c_e994c.ml";;
needs "src/pc_p2c_c990.ml";;
needs "src/pc_p2b_largedr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let P2KC_KSOL_COMPACT_CANON_L_ROUTE = prove
 (`!w:B->bool. P2B_KSOL_COMPACT_CANON_L_ROUTE_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC P2KC_KSOL_COMPACT_FROM_ROUTES THEN
  REWRITE_TAC[P2KD_CLAIM_9_90_ROUTE; P2BLD_LARGE_DR_ROUTE]);;

