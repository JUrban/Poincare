(* ========================================================================= *)
(* Print the hypothesis counts and statements of the results that check.ml  *)
(* and audit/check.ml check, in a fully typed form, for comparing two        *)
(* sessions (see candle/compare_defs.py).  Run after the audit, which        *)
(* defines poincare_sanity.                                                  *)
(* ========================================================================= *)

loads "pc/candle/dump_terms.ml";;

do_list (fun (n,th) ->
           print_string ("THMDUMP " ^ n ^ " " ^ string_of_int (length (hyp th)) ^
                         " " ^ dump_tm (concl th) ^ "\n"))
  ([("POINCARE_TOP", POINCARE_TOP);
    ("POINCARE_SMOOTH", POINCARE_SMOOTH);
    ("POINCARE_EMBEDDED", POINCARE_EMBEDDED);
    ("MOI_SST_HEADLINE", MOI_SST_HEADLINE);
    ("POINCARE_TOP_BLIND_EQUIV", POINCARE_TOP_BLIND_EQUIV);
    ("POINCARE_SMOOTH_BLIND_EQUIV", POINCARE_SMOOTH_BLIND_EQUIV);
    ("BLIND_POINCARE_TOP_PROVED", BLIND_POINCARE_TOP_PROVED);
    ("BLIND_POINCARE_SMOOTH_PROVED", BLIND_POINCARE_SMOOTH_PROVED)] @ poincare_sanity);;
print_string "THMDUMP_DONE\n";;
