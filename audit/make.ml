(* ========================================================================= *)
(* The statement audit: an independent formalization of the Poincare         *)
(* conjecture (audit/poincare_blind.ml) and the proof that it is equivalent  *)
(* to the statements of src/poincare_statement.ml.  Loads make.ml first.     *)
(* ========================================================================= *)

loadt "make.ml";;

needs "audit/pc_audit_equiv.ml";;
needs "audit/pc_audit_blind_proved.ml";;
