(* ========================================================================= *)
(* pc_p2b_rmhalf (Part 2B): abs Rm <= R/2 in dimension 3 under sec >= 0, a   *)
(* separate unit so that its users (pc_p2c_stdc2, pc_p2c_blowup2 and others) *)
(* need not load pc_p2b_x0:                                                  *)
(*   P2BX0_LSEC_LE_HALF_LSCALAR (chart form: sec(u,v) <= R/2),              *)
(*   P2BX0_RM_NORM_LE_HALF_SCALAR (mfd_rm_norm <= mfd_scalar / 2).          *)
(* It needs the 3-d curvature algebra of pc_rfa_p3alg, Ric >= 0 from         *)
(* sec >= 0 of pc_cmp_bg, RFA_MFD_RM_NORM_LE of pc_rfa_doubling and          *)
(* CMPF_LOCAL_METRIC of pc_cmp_frame.                                        *)
(* ========================================================================= *)

needs "src/pc_rfa_p3alg.ml";;
needs "src/pc_rfa_doubling.ml";;
needs "src/pc_cmp_frame.ml";;
needs "src/pc_cmp_bg.ml";;

prioritize_real();;
type_invention_error := true;;

(* X0.2b In dimension 3 with nonnegative sectional curvature every         *)
(* sectional curvature is at most R/2: sec(u,v) = P(w,w) = R/2 - Ric(w,w)   *)
(* at the unit normal w (RFA_SEC_AS_PCURV, RFA_LPCURV_DIAG) and Ric >= 0    *)
(* (CMPZ_LRICCI_SEC_LOWER); hence abs Rm <= R/2.                           *)

let P2BX0_LSEC_LE_HALF_LSCALAR = prove
 (`!U (G:real^3->real^3^3) y u v.
     metric_field U G /\ y IN U /\
     (!a b. ~collinear {vec 0,a,b} ==> &0 <= lsectional G y a b) /\
     ~collinear {vec 0,u,v}
     ==> lsectional G y u v <= lscalar G y / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
                RFA_SEC_AS_PCURV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[RFA_LPCURV_DIAG; REAL_MUL_RID] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `&0`; `w:real^3`]
                CMPZ_LRICCI_SEC_LOWER) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

let P2BX0_RM_NORM_LE_HALF_SCALAR = prove
 (`!top atlas (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g x u v)
     ==> mfd_rm_norm atlas g x <= mfd_scalar atlas g x / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_MFD_RM_NORM_LE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= mfd_sectional atlas (g:A->real^3^3) x u v` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_sectional; mfd_scalar] THEN
  MATCH_MP_TAC P2BX0_LSEC_LE_HALF_LSCALAR THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[GSYM mfd_sectional]);;

