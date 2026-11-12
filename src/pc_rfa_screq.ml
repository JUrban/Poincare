(* ========================================================================= *)
(* Unit pc_rfa_screq: the scalar curvature statements of Part 2,             *)
(* P2A_REQ_RLOWER_STATEMENT and P2C_REQ_SCALAR_MIN_STATEMENT                 *)
(* (RFA_P2A_REQ_RLOWER, RFA_P2C_REQ_SCALAR_MIN), from the general-N theorems *)
(* of pc_rfa_scalar.  Kept separate because the two files defining the       *)
(* statements load the Part 3 stack.                                         *)
(* ========================================================================= *)

needs "src/pc_rfa_scalar.ml";;
needs "src/pc_p2a_defs.ml";;
needs "src/pc_p2c_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The two statements, real^3 instances of RFA_RLOWER_BODY and               *)
(* RFA_SCALAR_MIN_BODY (the Hausdorff hypothesis of the statements is not    *)
(* needed).                                                                  *)
(* ========================================================================= *)

let RFA_P2A_REQ_RLOWER = prove
 (`!u:A->bool. P2A_REQ_RLOWER_STATEMENT u`,
  REWRITE_TAC[P2A_REQ_RLOWER_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_RLOWER_BODY THEN ASM_REWRITE_TAC[]);;

let RFA_P2C_REQ_SCALAR_MIN = prove
 (`!u:A->bool. P2C_REQ_SCALAR_MIN_STATEMENT u`,
  REWRITE_TAC[P2C_REQ_SCALAR_MIN_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^3^3`; `t1:real`; `t2:real`;
                 `x:A`] RFA_SCALAR_MIN_BODY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

