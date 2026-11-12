(* ========================================================================= *)
(* pc_p2a_harn: the statement A9 of pc_p2c_iface                             *)
(* (P2C_REQ_HARNACK_STATEMENT), Hamilton's trace Harnack inequality          *)
(* dR/dt >= -R/(t - a) (MT Thm 4.37) for complete flows on the open          *)
(* interval (a,b) with nonnegative sectional curvature and bounded           *)
(* curvature.  Proof: the Part 2B form RFA_P2B_REQ_RFA_HARNACK               *)
(* (pc_rfa_htrace) on the interval (a,b'] with b' = (t + b) / 2, which       *)
(* is a flow up to b' (P2AE_UPTO_FROM_ON).                                   *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_rfa_htrace.ml";;

prioritize_real();;
type_invention_error := true;;

(* A flow on (a,b) is a flow up to any b' in (a,b), smooth past b'.         *)

let P2AE_UPTO_FROM_ON = prove
 (`!top atlas a b b' (g:real->A->real^3^3).
        ricci_flow_on (top,atlas) a b g /\ a < b' /\ b' < b
        ==> rfs_flow_upto (top,atlas) a b' g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[rfs_flow_upto] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`b - b'`;
      `\z:real^(1,3)finite_sum.
         (vectorize:real^3^3->real^(3,3)finite_prod)
         (metric_local atlas c ((g:real->A->real^3^3) (drop(fstcart z))) (sndcart z))`] THEN
    REWRITE_TAC[REAL_ARITH `b' + (b - b') = b:real`; FSTCART_PASTECART;
                SNDCART_PASTECART; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem (the statement P2C_REQ_HARNACK_STATEMENT of              *)
(* pc_p2c_iface).                                                            *)
(* ------------------------------------------------------------------------- *)

let P2AE_REQ_HARNACK = prove
 (`!u:A->bool. P2C_REQ_HARNACK_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_REQ_HARNACK_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `K:real`; `x:A`; `t:real`; `D:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` RFA_P2B_REQ_RFA_HARNACK) THEN
  REWRITE_TAC[P2B_REQ_RFA_HARNACK_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:real->A->real^3^3`; `a:real`; `(t + b) / &2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2AE_UPTO_FROM_ON THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `K:real` THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`; `D:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC]);;

