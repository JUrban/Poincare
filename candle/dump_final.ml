(* ========================================================================= *)
(* In the session that proves the theorems (no instrumentation): the         *)
(* definitions made with new_definition in src/poincare_statement.ml,         *)
(* src/pc_interfaces.ml and audit/poincare_blind.ml, in the form in which    *)
(* the kernel recorded them (rebuilt from the theorems as new_definition     *)
(* builds them; see basic_definition_of), the theorems of the two constants  *)
(* defined with define, and all constants and type operators, as             *)
(* candle/dump_defs.ml prints them.  Run after the audit.                    *)
(* Self-contained, so that no nested load precedes the output.               *)
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

(* new_definition (pair.ml) gives the kernel fn = \g1 .. gn. r', where each   *)
(* argument is replaced by a fresh variable gi (and the components of a       *)
(* tuple by FST and SND of it); rebuild that from |- !avs. fn args = r.  The  *)
(* names of the fresh variables differ, but compare_defs.py renames them.     *)

let basic_definition_of th =
  let depair arg =
    let rec depair gv arg =
      try let l,r = dest_pair arg in
          (depair (list_mk_icomb "FST" [gv]) l) @
          (depair (list_mk_icomb "SND" [gv]) r)
      with Failure _ -> [gv,arg] in
    let gv = genvar(type_of arg) in
    gv,depair gv arg in
  let _,bod = strip_forall (concl th) in
  let l,r = dest_eq bod in
  let fn,args = strip_comb l in
  let gargs,reps = (I F_F unions) (unzip(map depair args)) in
  mk_eq(fn, list_mk_abs(gargs, subst reps r));;

do_list (fun th -> print_string ("DEFDUMP " ^ dump_tm (basic_definition_of th) ^ "\n"))
  [smooth_map_on;
   simply_connected_space;
   locally_euclidean_space;
   smooth_manifold_atlas;
   smooth_immersion_into;
   POINCARE_STATEMENT;
   POINCARE_SMOOTH_STATEMENT;
   POINCARE_EMBEDDED_STATEMENT;
   MOISE_SMOOTHING_STATEMENT;
   blind_locally_euclidean_3;
   blind_topological_3_manifold;
   blind_closed_topological_3_manifold;
   blind_simply_connected_space;
   blind_smooth_on;
   blind_chart_3;
   blind_smoothly_compatible_3;
   blind_smooth_atlas_3;
   blind_smooth_3_manifold;
   blind_closed_smooth_3_manifold;
   blind_smooth_map_3;
   blind_diffeomorphic_3;
   blind_sphere3;
   blind_sphere3_topology;
   blind_stereo_north;
   blind_stereo_south;
   blind_sphere3_atlas;
   BLIND_POINCARE_TOP;
   BLIND_POINCARE_SMOOTH];;
(* The constants defined with define: the theorems define returned (the     *)
(* last binding of each name; continuously_differentiable is defined again,   *)
(* identically, in src/ns_smooth.ml).                                         *)

do_list (fun (n,th) -> print_string ("DEFTHMDUMP " ^ n ^ " " ^ dump_tm (concl th) ^ "\n"))
  [("continuously_differentiable", continuously_differentiable);
   ("blind_ck", blind_ck)];;
do_list (fun (n,ty) -> print_string ("CONSTDUMP " ^ n ^ " " ^ dump_ty ty ^ "\n"))
        (constants());;
do_list (fun (n,k) ->
           print_string ("TYPEDUMP " ^ n ^ " " ^ string_of_int k ^ "\n"))
        (types());;
print_string "DUMP_DONE\n";;
