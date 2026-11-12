(* ========================================================================= *)
(* The checks of check.ml on Candle (which has no Printf): each headline     *)
(* theorem must have no hypotheses and conclude exactly its statement        *)
(* constant applied to the universe (:A) of a type variable A, and the only  *)
(* axioms must be the three standard ones.                                   *)
(* ========================================================================= *)

POINCARE_TOP;;
POINCARE_SMOOTH;;
POINCARE_EMBEDDED;;
MOI_SST_HEADLINE;;

let poincare_is_tyvar_set ty =
  try let s, args = dest_type ty in
      s = "fun" && length args = 2 && is_vartype (hd args) && hd (tl args) = bool_ty
  with Failure _ -> false;;

let poincare_univ_of_tyvar tm =
  is_const tm && fst(dest_const tm) = "UNIV" && poincare_is_tyvar_set (type_of tm);;

let poincare_check (name,th,stmt) =
  let ok = try let c,u = dest_comb(concl th) in
               is_const c && fst(dest_const c) = stmt && poincare_univ_of_tyvar u
           with Failure _ -> false in
  print_string (name ^ " hypotheses " ^ string_of_int (length (hyp th)) ^
                "  conclusion is " ^ stmt ^ " (:A), A a type variable: " ^
                string_of_bool ok ^ "\n");;

do_list poincare_check
  [("POINCARE_TOP", POINCARE_TOP, "POINCARE_STATEMENT");
   ("POINCARE_SMOOTH", POINCARE_SMOOTH, "POINCARE_SMOOTH_STATEMENT");
   ("POINCARE_EMBEDDED", POINCARE_EMBEDDED, "POINCARE_EMBEDDED_STATEMENT")];;

let poincare_moise_ok =
  try let v,b = dest_forall(concl MOI_SST_HEADLINE) in
      let c,x = dest_comb b in
      x = v && is_const c && fst(dest_const c) = "MOISE_SMOOTHING_STATEMENT" &&
      poincare_is_tyvar_set (type_of v)
  with Failure _ -> false;;

print_string ("MOI_SST_HEADLINE hypotheses " ^
              string_of_int (length (hyp MOI_SST_HEADLINE)) ^
              "  conclusion is !u:A->bool. MOISE_SMOOTHING_STATEMENT u: " ^
              string_of_bool poincare_moise_ok ^ "\n");;

print_string ("AXIOMS_COUNT " ^ string_of_int (length (axioms())) ^ "\n");;
do_list (fun th -> print_string ("AXIOM " ^ string_of_term (concl th) ^ "\n"))
        (axioms());;
check_axioms ();;
print_string "POINCARE_CHECK_DONE\n";;
