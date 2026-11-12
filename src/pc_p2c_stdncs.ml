(* ========================================================================= *)
(* Unit pc_p2c_stdncs (Part 2C): the statement of the kappa-noncollapsing of *)
(* partial standard flows (MT Prop 12.13 = Thm 12.5 (6)), proved in          *)
(* pc_p2c_stdnc1-3 and used for Thms 12.28 and 12.29 (pc_p2c_stdc1,          *)
(* pc_p2c_stdc2; P2C_THM_11_8_VIEW needs p3_noncoll_at for the flow view of  *)
(* the standard solution: p2c_vblowup_seq, p2c_vblowup_back).  For t outside *)
(* [0,te) or r^2 > t the predicate p3_noncoll_at is vacuous (no parabolic    *)
(* neighbourhood), as in MT's definition.                                    *)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statement constant.                                                  *)
(* ------------------------------------------------------------------------- *)

let P2C_STD_NONCOLL_STATEMENT = new_definition
 `P2C_STD_NONCOLL_STATEMENT <=>
    !g0 A0 te G.
       p3_std_initial g0 A0 /\ p3_partial_std g0 te G
       ==> ?kappa r0. &0 < kappa /\ &0 < r0 /\
             !x t. p3_noncoll_at
                     (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                    {s | &0 <= s /\ s < te} G)
                     kappa r0 x t`;;

