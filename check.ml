(* ========================================================================= *)
(* Load the development and print its main results.  Each headline theorem  *)
(* must have no hypotheses and conclude exactly its statement constant      *)
(* applied to the universe (:A) of a TYPE VARIABLE A (such a theorem holds  *)
(* at every type by type instantiation; an instance at a particular type    *)
(* could hold vacuously), and the only axioms must be HOL Light's three     *)
(* standard ones (ETA_AX, SELECT_AX, INFINITY_AX).                           *)
(* ========================================================================= *)

loadt "make.ml";;

POINCARE_TOP;;
POINCARE_SMOOTH;;
POINCARE_EMBEDDED;;
MOI_SST_HEADLINE;;

let poincare_univ_of_tyvar tm =
  is_const tm && fst(dest_const tm) = "UNIV" &&
  (match dest_type(type_of tm) with
     "fun",[a;b] -> is_vartype a && b = bool_ty
   | _ -> false);;

let poincare_check (name,th,stmt) =
  let ok = try let c,u = dest_comb(concl th) in
               is_const c && fst(dest_const c) = stmt && poincare_univ_of_tyvar u
           with Failure _ -> false in
  Printf.printf "%-18s hypotheses %d  conclusion is %s (:A), A a type variable: %b\n"
    name (List.length (hyp th)) stmt ok;;

List.iter poincare_check
  ["POINCARE_TOP", POINCARE_TOP, "POINCARE_STATEMENT";
   "POINCARE_SMOOTH", POINCARE_SMOOTH, "POINCARE_SMOOTH_STATEMENT";
   "POINCARE_EMBEDDED", POINCARE_EMBEDDED, "POINCARE_EMBEDDED_STATEMENT"];;

let poincare_moise_ok =
  try let v,b = dest_forall(concl MOI_SST_HEADLINE) in
      let c,x = dest_comb b in
      x = v && is_const c && fst(dest_const c) = "MOISE_SMOOTHING_STATEMENT" &&
      (match dest_type(type_of v) with
         "fun",[a;bb] -> is_vartype a && bb = bool_ty
       | _ -> false)
  with Failure _ -> false;;

Printf.printf "%-18s hypotheses %d  conclusion is !u:A->bool. MOISE_SMOOTHING_STATEMENT u: %b\n"
  "MOI_SST_HEADLINE" (List.length (hyp MOI_SST_HEADLINE)) poincare_moise_ok;;

Printf.printf "AXIOMS_COUNT %d\n" (List.length (axioms()));;
List.iter (fun th -> print_string ("AXIOM " ^ string_of_term (concl th) ^ "\n")) (axioms());;
print_string "POINCARE_CHECK_DONE\n";;
