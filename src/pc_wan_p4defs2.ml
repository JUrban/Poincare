(* ========================================================================= *)
(* pc_wan_p4defs2: one more statement constant of the weak analysis part for *)
(* Part 4, WAN_REMOVABLE_POINT_WEAK_STATEMENT (used by CM_REMOVABLE in       *)
(* pc_hm_regularity, with n := (:2)), and a sanity check. The statement is   *)
(* proved in pc_wan_sob2.                                                    *)
(* ========================================================================= *)

needs "src/pc_wan_p4defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A weak first-order equation  sum_i int A_i . d_i phi = int f . phi  that   *)
(* holds for the vector test maps supported away from a point a holds for    *)
(* all vector test maps, in dimension N >= 2, for L^2_loc coefficients A_i  *)
(* and an L^1_loc right-hand side f (points have zero W^(1,2) capacity).     *)
(* ------------------------------------------------------------------------- *)

let WAN_REMOVABLE_POINT_WEAK_STATEMENT = new_definition
 `WAN_REMOVABLE_POINT_WEAK_STATEMENT (n:N->bool) (kk:K->bool) <=>
    !(s:real^N->bool) (a:real^N) (A:num->real^N->real^K) (f:real^N->real^K).
       open s /\ 2 <= dimindex(:N) /\
       (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2loc s (A i)) /\ wan_lloc s f /\
       (!phi. wan_vtest (s DIFF {a}) phi
              ==> sum(1..dimindex(:N))
                     (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
                  drop(integral s (\x. lift(f x dot phi x))))
       ==> !phi. wan_vtest s phi
                 ==> sum(1..dimindex(:N))
                        (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
                     drop(integral s (\x. lift(f x dot phi x)))`;;

(* ------------------------------------------------------------------------- *)
(* Sanity: vector test maps on a subset are vector test maps on the whole    *)
(* set, so the conclusion of the statement implies its hypothesis (the       *)
(* statement says the two conditions are equivalent).                        *)
(* ------------------------------------------------------------------------- *)

let WAN_VTEST_SUBSET = prove
 (`!(s:real^N->bool) t (phi:real^N->real^K).
     wan_vtest t phi /\ t SUBSET s ==> wan_vtest s phi`,
  REWRITE_TAC[wan_vtest] THEN MESON_TAC[SUBSET_TRANS]);;

let WAN_REMOVABLE_POINT_WEAK_CONVERSE = prove
 (`!(s:real^N->bool) (a:real^N) (A:num->real^N->real^K) (f:real^N->real^K).
     (!phi. wan_vtest s phi
            ==> sum(1..dimindex(:N))
                   (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
                drop(integral s (\x. lift(f x dot phi x))))
     ==> !phi. wan_vtest (s DIFF {a}) phi
               ==> sum(1..dimindex(:N))
                      (\i. drop(integral s (\x. lift(A i x dot partial_derivative i phi x)))) =
                   drop(integral s (\x. lift(f x dot phi x)))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC WAN_VTEST_SUBSET THEN EXISTS_TAC `s DIFF {a:real^N}` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

