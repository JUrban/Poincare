(* ========================================================================= *)
(* Unit pc_p2b_anccreq: statement only.  The route statement                 *)
(* P2B_ANCIENT_COMPACT_ROUTE_STATEMENT for                                   *)
(* P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (pc_p2b_defs), proved in            *)
(* pc_p2b_ancc.  P2C_THM_5_15 is for histories (compact stages, times from   *)
(* 0), so the route is the view form: the rescaled flow views at time 0 have *)
(* compact ball closures (complete slices, CMPZ_COMPLETE_CLOSURE_COMPACT)    *)
(* and derivative bounds from Shi in view form (VSHI_SHI_VIEW_CC, on         *)
(* RFA_P2_THM_3_28); Cheeger-Gromov compactness (the one hypothesis) gives a *)
(* complete slice limit at time 0; P2BU_FROM_SLICE_UPTO (pc_p2c_blowup)      *)
(* extends it to a flow limit on J, the set of s <= 0, with rfs_flow_upto a  *)
(* 0 for a < 0; P2BU_FLOW_LIMIT_OF_ON gives one subsequence for every Tl.    *)
(* In the chain the hypothesis is discharged at w = (:real^3) by             *)
(* P2CK_CG_COMPACT.                                                          *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2c_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_ANCIENT_COMPACT_ROUTE_STATEMENT = new_definition
 `P2B_ANCIENT_COMPACT_ROUTE_STATEMENT (w:B->bool) <=>
    P2C_CG_COMPACT_STATEMENT w w ==> P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w`;;

