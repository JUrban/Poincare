(* ========================================================================= *)
(* The harmonic map regularity chain theorem CM_CHAIN_HM_REGULARITY.  Its    *)
(* six conclusions are CM_EPS_REG (pc_hm_reg_eps), CM_HOPF, CM_SPHERE_GAP    *)
(* and CM_CRITICAL_ISOLATED (pc_hm_reg_sph), CM_REMOVABLE (pc_hm_reg_rem),   *)
(* and CM_MINIMIZER_SMOOTH, obtained here from CM_REG01 (pc_hm_reg_smth) by  *)
(* HMRM_MINIMIZER_SMOOTH (pc_hm_reg_min).                                    *)
(* ========================================================================= *)

needs "src/pc_hm_reg_rem.ml";;
needs "src/pc_hm_reg_min.ml";;

prioritize_real();;
type_invention_error := true;;

let CM_MINIMIZER_SMOOTH = prove
 (`!kk:K->bool. CM_MINIMIZER_SMOOTH_STATEMENT kk`,
  GEN_TAC THEN MATCH_MP_TAC HMRM_MINIMIZER_SMOOTH THEN REWRITE_TAC[CM_REG01]);;

let CM_CHAIN_HM_REGULARITY = prove
 (`!kk:K->bool. CM_CHAIN_HM_REGULARITY_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_CHAIN_HM_REGULARITY_STATEMENT] THEN DISCH_TAC THEN
  REWRITE_TAC[CM_EPS_REG; CM_MINIMIZER_SMOOTH; CM_REMOVABLE; CM_HOPF; CM_SPHERE_GAP;
              CM_CRITICAL_ISOLATED]);;

let CM_CHAIN_HM_REGULARITY_UNIV = prove
 (`CM_CHAIN_HM_REGULARITY_STATEMENT (:K)`,
  REWRITE_TAC[CM_CHAIN_HM_REGULARITY]);;

