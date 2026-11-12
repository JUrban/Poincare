(* ========================================================================= *)
(* Print every type definition theorem of the session, for comparing two     *)
(* sessions (see candle/compare_defs.py).  Needs tydefs (), which neither    *)
(* kernel has; candle/REPORT.md describes the recorders.                     *)
(* ========================================================================= *)

loads "pc/candle/dump_terms.ml";;

do_list (fun th -> print_string ("TYDEFDUMP " ^ dump_tm (concl th) ^ "\n"))
        (tydefs());;
print_string "DUMP_DONE\n";;
