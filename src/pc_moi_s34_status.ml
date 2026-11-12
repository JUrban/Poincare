(* ========================================================================= *)
(* pc_moi_s34_status: Moise Sec 34 assembled.  MOI_S34ST_PROD :             *)
(* |- MOI_PROD_34_EXT, from the glue MOI_S4D_PROD_34_EXT of                 *)
(* pc_moi_s34_stmt.ml and the unit theorems loaded below: LF_FINE, SRC,     *)
(* SCELL_A, SCELL_B, MARGIN, LEMMA4, FBALL, L910, RECOG_A, RECOG_B, EXT,    *)
(* TRACE, FDISK, OP1_IN, OUTER (TOUTER), OP2, OP1_OUT (OP1_OUT_FROM_UNCLEAN *)
(* with UNCLEAN), CELLNB (CELLNB_FND with SIMPLEX_SMALL_CELL of             *)
(* pc_moi_fnd_rnsc), RESID (MOI_S4X_GLUE with RESID_A, RESID_B), and SHELL, *)
(* FRAME from the foundation MOI_FND_SOLID_TORUS_TRIANGLE, which is         *)
(* GRAPH_TUBE_TRIANGLE_SOLID_TORUS of pc_moi_fnd_tubec.                     *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_moi_s34_fine.ml";;
needs "src/pc_moi_s34_src.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_s34_scellb.ml";;
needs "src/pc_moi_s34_margin.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_s34_fball.ml";;
needs "src/pc_moi_s34_l910.ml";;
needs "src/pc_moi_s34_recoga.ml";;
needs "src/pc_moi_s34_recogb.ml";;
needs "src/pc_moi_s34_ext.ml";;
needs "src/pc_moi_s34_shell.ml";;
needs "src/pc_moi_s34_frame.ml";;
needs "src/pc_moi_s34_trace.ml";;
needs "src/pc_moi_s34_fdisk.ml";;
needs "src/pc_moi_s34_cellnb.ml";;
needs "src/pc_moi_s34_op1a.ml";;
needs "src/pc_moi_fnd_rnsc.ml";;
needs "src/pc_moi_s34_touter.ml";;
needs "src/pc_moi_s34_resida.ml";;
needs "src/pc_moi_s34_residb.ml";;
needs "src/pc_moi_fnd_tubec.ml";;
needs "src/pc_moi_s34_op1b.ml";;
needs "src/pc_moi_s34_op1bu.ml";;
needs "src/pc_moi_s34_op2b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The assembly.  The foundation MOI_FND_SOLID_TORUS_TRIANGLE is             *)
(* GRAPH_TUBE_TRIANGLE_SOLID_TORUS (pc_moi_fnd_tubec), OP1_OUT is            *)
(* OP1_OUT_FROM_UNCLEAN (pc_moi_s34_op1b) applied to UNCLEAN                 *)
(* (pc_moi_s34_op1bu), and OP2 is proved in pc_moi_s34_op2b, so              *)
(* MOI_PROD_34_EXT is a theorem.  The list MOI_S34ST_OPEN is empty.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S34ST_OPEN = ([]:term list);;

let MOI_S34ST_PROVED =
  [LF_FINE; SRC; SCELL_A; SCELL_B; MARGIN; LEMMA4; FBALL; L910; RECOG_A; RECOG_B; EXT;
   TRACE; FDISK; OP1_IN; TOUTER; GRAPH_TUBE_TRIANGLE_SOLID_TORUS; OP2;
   MP OP1_OUT_FROM_UNCLEAN UNCLEAN];;

let MOI_S34ST_PROD = prove
 (MOI_PROD_34_EXT,
  let fnd = GRAPH_TUBE_TRIANGLE_SOLID_TORUS in
  let all = MOI_S34ST_PROVED @
            [MP SHELL_FND fnd; MP FRAME_FND fnd;
             MP CELLNB_FND SIMPLEX_SMALL_CELL;
             MP (MP MOI_S4X_GLUE RESID_A) RESID_B] in
  MATCH_MP_TAC MOI_S4D_PROD_34_EXT THEN
  REPEAT CONJ_TAC THEN
  FIRST(map (fun t -> ACCEPT_TAC t ORELSE (MATCH_ACCEPT_TAC t)) all));;

Printf.printf "S34ST_PROD %b %d %d\n%!"
  (aconv (concl MOI_S34ST_PROD) MOI_PROD_34_EXT && hyp MOI_S34ST_PROD = [] &&
   frees (concl MOI_S34ST_PROD) = [])
  (length MOI_S34ST_OPEN) (length MOI_S34ST_PROVED);;

