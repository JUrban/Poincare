(* ========================================================================= *)
(* The statement files and the audit's independent statements, after the    *)
(* library, in the order in which a proving session first loads them: the   *)
(* first files of make.ml, then the prerequisites of audit/pc_audit_equiv.ml *)
(* and audit/poincare_blind.ml.  For the short sessions that compare the     *)
(* statements' definitions between systems (see candle/REPORT.md).  Uses     *)
(* needs, which both systems have (the proving session loads                 *)
(* poincare_blind.ml with loadt, or loads in Candle).  Candle: after hol.ml, *)
(* prelude.ml, the library and compat.ml.                                    *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/pc_interfaces.ml";;
needs "src/poincare_statement_sanity.ml";;
needs "src/ns_smooth_elem.ml";;
needs "src/pc_mfd_examples.ml";;
needs "audit/poincare_blind.ml";;
