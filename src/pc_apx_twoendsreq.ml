(* ========================================================================= *)
(* pc_apx_twoendsreq: APXT_TWO_ENDS_NO_CAP proves the statement              *)
(* P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT (pc_p2c_iface): no (C,eps)-cap in a     *)
(* complete connected 3-manifold with sec >= 0 and two ends, for eps <= eps0 *)
(* with eps0 independent of C.  The proof is the body                        *)
(* APXT_TWO_ENDS_NO_CAP_BODY of pc_apx_twoends; only this small unit loads   *)
(* the interface file pc_p2c_iface.                                          *)
(* ========================================================================= *)

needs "src/pc_apx_twoends.ml";;
needs "src/pc_p2c_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let APXT_TWO_ENDS_NO_CAP = prove
 (`!u:A->bool. P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT] THEN
  MATCH_ACCEPT_TAC APXT_TWO_ENDS_NO_CAP_BODY);;

