(* ========================================================================= *)
(* Unit pc_cmr_defs: S^2 energy vocabulary for pc_cm_replacement             *)
(* (CM_TIGHTEN, CM 2008 Thm 2.1).                                            *)
(*   cmr_cone E       : the part of wan_shell over a set E of directions;   *)
(*   cmr_dens G u     : the G-energy density of the radial extension of u;  *)
(*   cmr_sen_on G u E : the G-energy of u on E (cm_sen G u is the case      *)
(*                      E = S^2);                                           *)
(*   cmr_chart Q      : the inverse of cm_capmap Q off the pole Q e3.       *)
(* The replacement vocabulary is defined in pc_cmr_rep.                      *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;

prioritize_real();;
type_invention_error := true;;

let cmr_cone = new_definition
 `cmr_cone (E:real^3->bool) = {z:real^3 | z IN wan_shell /\ inv(norm z) % z IN E}`;;

let cmr_dens = new_definition
 `cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) (z:real^3) =
    sum(1..3) (\j. wan_wd wan_shell j (wan_rext u) z dot
                   (G(wan_rext u z) ** wan_wd wan_shell j (wan_rext u) z))`;;

let cmr_sen_on = new_definition
 `cmr_sen_on (G:real^K->real^K^K) (u:real^3->real^K) (E:real^3->bool) =
    drop(integral (cmr_cone E) (\z. lift(cmr_dens G u z))) / &3`;;

let cmr_chart = new_definition
 `cmr_chart (Q:real^3^3) (y:real^3) = stereo2_n(transp Q ** y)`;;

