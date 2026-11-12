(* ========================================================================= *)
(* Fully typed printing of types and terms, for comparing sessions.          *)
(* ========================================================================= *)

let rec dump_ty ty =
  if is_vartype ty then dest_vartype ty else
  let (n,args) = dest_type ty in
  "(" ^ n ^ itlist (fun t s -> " " ^ dump_ty t ^ s) args "" ^ ")";;

let rec dump_tm tm =
  if is_var tm then
    let (n,ty) = dest_var tm in "(V " ^ n ^ " " ^ dump_ty ty ^ ")"
  else if is_const tm then
    let (n,ty) = dest_const tm in "(C " ^ n ^ " " ^ dump_ty ty ^ ")"
  else if is_comb tm then
    let (f,x) = dest_comb tm in "(A " ^ dump_tm f ^ " " ^ dump_tm x ^ ")"
  else
    let (v,b) = dest_abs tm in "(L " ^ dump_tm v ^ " " ^ dump_tm b ^ ")";;
