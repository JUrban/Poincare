(* ========================================================================= *)
(* Unit pc_rf_unique_a14u: A14, the uniqueness of complete Ricci flows of    *)
(* bounded curvature with the same initial metric (the statement             *)
(* P2C_REQ_UNIQ_COMPLETE_STATEMENT), at (:real^3) and without extra          *)
(* hypotheses: RFU_A14_COND of pc_rf_unique_a14 combined with MT Thm 3.29    *)
(* (Shi with initial bounds), proved as RFA_P2_THM_3_29 in pc_rfa_shi329.    *)
(* Kept separate from pc_rf_unique_a14 because pc_rfa_shi329 adds about 2.7  *)
(* MB to the load closure.                                                   *)
(* ========================================================================= *)

needs "src/pc_rf_unique_a14.ml";;
needs "src/pc_rfa_shi329.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The theorem RFU_A14: A14 at (:real^3).                                    *)
(* ========================================================================= *)

let RFU_A14 = prove
 (`!top atlas a b g g' phi C.
       hausdorff_space (top:(real^3)topology) /\
       ricci_flow_from (top,atlas:((real^3->bool)#(real^3->real^3))->bool) a b g /\
       ricci_flow_from (top,atlas) a b g' /\
       (!x. x IN topspace top ==> g' a x = g a x) /\
       (!t. a <= t /\ t < b ==> mfd_complete (top,atlas) (g t) /\
                                mfd_complete (top,atlas) (g' t)) /\
       (!b1. b1 < b
             ==> ?K. !t x. a <= t /\ t <= b1 /\ x IN topspace top
                           ==> mfd_rm_norm atlas (g t) x <= K /\
                               mfd_rm_norm atlas (g' t) x <= K) /\
       (!l. ?Cl. !x. x IN topspace top
                     ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) (g a))
                                         (SND(chart_at atlas x) x) <= Cl) /\
       mfd_smooth atlas (lift o phi) /\
       (!c. compact_in top {x | x IN topspace top /\ phi x <= c}) /\
       (!x. x IN topspace top
            ==> p2c_fgrad2 atlas (g a) phi x <= C /\ abs(p2c_flap atlas (g a) phi x) <= C) /\
       (!s v. mfd_has_volume (top,atlas) (g a) {x | x IN topspace top /\ phi x <= s} v
              ==> v <= C * exp(C * s))
       ==> !t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x`,
  MATCH_ACCEPT_TAC(MATCH_MP RFU_A14_COND (ISPEC `(:real^3)` RFA_P2_THM_3_29)));;

