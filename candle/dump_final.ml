(* ========================================================================= *)
(* In the session that proves the theorems (no instrumentation): the         *)
(* definitions made with new_definition in src/poincare_statement.ml,         *)
(* src/pc_interfaces.ml and audit/poincare_blind.ml, in the form in which    *)
(* the kernel recorded them (c = \x1 .. xn. t, rebuilt from the theorem     *)
(* |- !x1 .. xn. c x1 .. xn = t as new_definition builds it), and all        *)
(* constants and type operators, as candle/dump_defs.ml prints them.  Left   *)
(* out: smooth_map_on, whose name is bound again by the identical            *)
(* redefinition in src/ns_smooth.ml, with other variable names.  Run after   *)
(* the audit.  Self-contained, so that no nested load precedes the output.   *)
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

let basic_definition_of th =
  let _,bod = strip_forall (concl th) in
  let l,r = dest_eq bod in
  let c,args = strip_comb l in
  mk_eq(c, list_mk_abs(args, r));;

do_list (fun th -> print_string ("DEFDUMP " ^ dump_tm (basic_definition_of th) ^ "\n"))
  [simply_connected_space;
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
do_list (fun (n,ty) -> print_string ("CONSTDUMP " ^ n ^ " " ^ dump_ty ty ^ "\n"))
        (constants());;
do_list (fun (n,k) ->
           print_string ("TYPEDUMP " ^ n ^ " " ^ string_of_int k ^ "\n"))
        (types());;
print_string "DUMP_DONE\n";;
