(* ========================================================================= *)
(* audit/make.ml and audit/check.ml for Candle: the audit files, then their  *)
(* results (candle/audit_results.ml).  Run after candle/make.ml (or          *)
(* candle/check.ml) in the same session.                                     *)
(* ========================================================================= *)

needs "audit/pc_audit_equiv.ml";;
needs "audit/pc_audit_blind_proved.ml";;
loads "pc/candle/audit_results.ml";;
