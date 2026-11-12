(* ========================================================================= *)
(* pc_moi_s34_op1bstmt: the intermediate statement that splits s34_op1b    *)
(* (Moise Sec 34, p.241, Operation 1 with the compressing disk outside the *)
(* face ball) into a clean and an unclean case.                            *)
(*   moi_s4v_pocket c d j q e e' : the pocket data of an outside disk d    *)
(*     with rim j: e, e' the two disks of the frontier sphere of c cut by  *)
(*     j, q the ball bounded by d UNION e meeting c exactly in e, and      *)
(*     c UNION q the ball bounded by d UNION e';                           *)
(*   moi_s4v_clean tt kk f1 s q : DG's clean pocket (its interior misses   *)
(*     the frontier of the face torus, it misses the foreign vertex balls); *)
(*   MOI_S4V_UNCLEAN : Schoenflies ==> Operation 1 outside, for a pocket   *)
(*     that is not clean (UNCLEAN in pc_moi_s34_op1bu.ml, shell and        *)
(*     tunnel; DG Section34CompressionOutsideTube);                        *)
(*   pc_moi_s34_op1b proves OP1_OUT_FROM_UNCLEAN :                         *)
(*     |- MOI_S4V_UNCLEAN ==> MOI_S34_OP1_OUT (theta lemma, clean case);   *)
(*   MOI_S4V_UNCLEAN_FROM_OUT : |- MOI_S34_OP1_OUT ==> MOI_S4V_UNCLEAN     *)
(*     (sanity: MOI_S4V_UNCLEAN only adds hypotheses to MOI_S34_OP1_OUT).  *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The pocket, the clean condition, the statement MOI_S4V_UNCLEAN          *)
(* and the sanity theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Pocket data for a ball c and a disk d with rim j meeting c only in j:   *)
(* e, e' are the two disks into which j cuts the frontier sphere of c; q is *)
(* the ball bounded by d UNION e, meeting c exactly in e; c UNION q is the  *)
(* ball bounded by d UNION e'.                                              *)

let moi_s4v_pocket = new_definition
 `moi_s4v_pocket (c:real^3->bool) (d:real^3->bool) (j:real^3->bool)
                 (q:real^3->bool) (e:real^3->bool) (e':real^3->bool) <=>
    pl_cell_with_boundary 2 e j /\ pl_cell_with_boundary 2 e' j /\
    e UNION e' = frontier c /\ e INTER e' = j /\
    pl_ball 3 q /\ frontier q = d UNION e /\ q INTER c = e /\
    pl_ball 3 (c UNION q) /\ frontier (c UNION q) = d UNION e'`;;

(* DG's clean pocket (Section34CompressionLeaf): the interior of the pocket *)
(* misses the frontier of the face torus, and the pocket misses the vertex  *)
(* balls of the vertices not in s.                                          *)

let moi_s4v_clean = new_definition
 `moi_s4v_clean (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (f1:real^N->real^3) (s:real^N->bool) (q:real^3->bool) <=>
    DISJOINT (interior q) (frontier (IMAGE f1 (moi_s34_ft tt kk s))) /\
    (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT q (IMAGE f1 (moi_s34_vb tt kk w)))`;;

(* The unclean-pocket case of Operation 1 outside the ball, proved in       *)
(* pc_moi_s34_op1bu.ml (shell and tunnel, DG Section34CompressionOutsideTube) *)

let MOI_S4V_UNCLEAN =
  let hyp = list_mk_conj
    [MOI_S34_OP_HYP;
     `moi_s34_op1w (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                   (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool)
                   (s:real^N->bool) (v:real^N) (d:real^3->bool) (j:real^3->bool)`;
     `DISJOINT ((d:real^3->bool) DIFF (j:real^3->bool))
               ((cb:(real^N->bool)->real^3->bool) (s:real^N->bool))`;
     `moi_s4v_pocket ((cb:(real^N->bool)->real^3->bool) (s:real^N->bool))
                     (d:real^3->bool) (j:real^3->bool)
                     (q:real^3->bool) (e:real^3->bool) (e':real^3->bool)`;
     `~moi_s4v_clean (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                     (f1:real^N->real^3) (s:real^N->bool) (q:real^3->bool)`] in
  mk_imp(`PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT`,
         list_mk_forall(MOI_S34_OP_VARS @
                        [`v:real^N`; `d:real^3->bool`; `j:real^3->bool`;
                         `q:real^3->bool`; `e:real^3->bool`; `e':real^3->bool`],
                        mk_imp(hyp,MOI_S34_OP_CONCL)));;

(* Sanity: MOI_S34_OP1_OUT implies MOI_S4V_UNCLEAN (which only adds        *)
(* hypotheses).                                                            *)

let MOI_S4V_UNCLEAN_FROM_OUT = prove
 (mk_imp(MOI_S34_OP1_OUT,MOI_S4V_UNCLEAN),
  DISCH_THEN(LABEL_TAC "out") THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REMOVE_THEN "out" (MP_TAC o SPECL
    [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
     `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
     `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`; `v:real^N`;
     `d:real^3->bool`; `j:real^3->bool`] o
    C MP (ASSUME `PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT`)) THEN
  ASM_REWRITE_TAC[]);;

Printf.printf "OP1BSTMT_SANITY %b\n%!"
  (aconv (concl MOI_S4V_UNCLEAN_FROM_OUT) (mk_imp(MOI_S34_OP1_OUT,MOI_S4V_UNCLEAN)) &&
   hyp MOI_S4V_UNCLEAN_FROM_OUT = [] && frees MOI_S4V_UNCLEAN = []);;

