(* ========================================================================= *)
(* Unit pc_rfa_smppos: the statement P2C_REQ_SMP_POS_STATEMENT (A12 of       *)
(* pc_p2c_iface), proved as RFA_P2C_REQ_SMP_POS: sec >= 0 along a 3D Ricci   *)
(* flow on a connected manifold and sec > 0 at one point at the initial time *)
(* give sec > 0 everywhere at all later times.                               *)
(* ========================================================================= *)

needs "src/pc_rfa_smaxv.ml";;
needs "src/pc_rfa_secpres.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The headline theorem RFA_P2C_REQ_SMP_POS.                                 *)
(* ========================================================================= *)

(* The statement P2C_REQ_SMP_POS (A12): on a connected 3-manifold with     *)
(* sec >= 0 along the flow, sec > 0 at one point at the initial time gives *)
(* sec > 0 everywhere at all later times (strong maximum principle).        *)

let RFA_P2C_REQ_SMP_POS = prove
 (`!u:A->bool. P2C_REQ_SMP_POS_STATEMENT u`,
  REWRITE_TAC[P2C_REQ_SMP_POS_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b /\ x IN topspace top
          ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) a) x0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_SECMIN_POS THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) s) x0)
    real_continuous_on {s | a <= s /\ s < b}`
  MP_TAC THENL
   [REWRITE_TAC[RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`subtopology euclideanreal {t | a <= t /\ t < b}`;
       `subtopology (top:A topology) (topspace top)`;
       `\t x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                ((g:real->A->real^3^3) t) (x:A)`;
       `x0:A`] RFA_SLICE_CONTINUOUS_LEFT)) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
      MATCH_MP_TAC RFA_SECMIN_CONTINUOUS_GEN THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[ricci_flow_from]];
    ALL_TAC] THEN
  REWRITE_TAC[real_continuous_on; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC
    `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) a) x0 / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `t1 = a + min d (t - a) / &2` THEN
  SUBGOAL_THEN `a < t1 /\ t1 < t /\ abs(t1 - a) < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t1) x0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `t1:real`; `x0:A`] RFA_SECMIN_STRONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                ((g:real->A->real^3^3) t) x` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN
  EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

