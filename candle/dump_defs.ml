(* ========================================================================= *)
(* Print every definition of the session, and the constants and type         *)
(* operators, in a fully typed form, for comparing two sessions (see         *)
(* candle/compare_defs.py).  Needs definitions (), which Candle's kernel     *)
(* wrapper does not have; see candle/tools/candle_recorder.patch.  HOL Light *)
(* needs a pc symlink to this repository in its own directory, because its   *)
(* loads is relative to that directory.                                      *)
(* ========================================================================= *)

loads "pc/candle/dump_terms.ml";;

do_list (fun th -> print_string ("DEFDUMP " ^ dump_tm (concl th) ^ "\n"))
        (definitions());;
do_list (fun (n,ty) -> print_string ("CONSTDUMP " ^ n ^ " " ^ dump_ty ty ^ "\n"))
        (constants());;
do_list (fun (n,k) ->
           print_string ("TYPEDUMP " ^ n ^ " " ^ string_of_int k ^ "\n"))
        (types());;
print_string "DUMP_DONE\n";;
