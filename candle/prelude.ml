(* ========================================================================= *)
(* Candle-specific set-up, loaded after hol.ml and before Multivariate.      *)
(* candle/compute.ml overloads +, -, * (and friends) with the cval           *)
(* operations Cexp_*; remove these so that ordinary arithmetic terms parse   *)
(* as in HOL Light.                                                          *)
(* ========================================================================= *)

the_interface :=
  filter (fun (_,(c,_)) ->
            let n = String.length c in
            not (n >= 5 && String.sub c 0 5 = "Cexp_"))
         (!the_interface);;
