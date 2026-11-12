(* ========================================================================= *)
(* Unit pc_p2b_avrreq: statement only.  The route of the A6 leaf,            *)
(* P2B_AVR_ZERO_ROUTE_STATEMENT: Thm 9.59 gives the FIX form                 *)
(* P2B_AVR_ZERO_FIX_STATEMENT of the asymptotic volume ratio statement.      *)
(* Used in the chain composition of pc_p2c_chainx2; proved in pc_p2b_avrz    *)
(* (noncompact case by Thm 9.59, compact case because a large ball is the    *)
(* whole manifold).                                                          *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2b_kreq.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_AVR_ZERO_ROUTE_STATEMENT = new_definition
 `P2B_AVR_ZERO_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_THM_9_59_STATEMENT w ==> P2B_AVR_ZERO_FIX_STATEMENT w`;;

