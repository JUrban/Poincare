(* ========================================================================= *)
(* pc_moi_fnd_stmt4: the regular-neighbourhood term of dimension at most 2.  *)
(* The consumers of MOI_FND_DERIVED_NBHD_BALL (pc_moi_fnd_stmt.ml) use only  *)
(* PL balls of dimension at most 2 and trees (DISK_CHART and NULL_POLYGON of *)
(* the pc_moi_s3032 files, the neighbourhood N(d) of pc_moi_fnd_split, and   *)
(* pc_moi_s34_cellnba through the simplex case), never the case of           *)
(* triangulated 3-balls.                                                     *)
(*   MOI_FND_DERIVED_NBHD_BALL_2 : the text of MOI_FND_DERIVED_NBHD_BALL     *)
(*     with n <= 2 in place of n <= 3 (tree disjunct kept);                  *)
(*   MOI_FS4_BALL_2 : |- MOI_FND_DERIVED_NBHD_BALL ==> ..._BALL_2 (so the   *)
(*     restricted term is no stronger than the general one).                 *)
(* pc_moi_fnd_rnb2 proves it (DERIVED_NBHD_BALL_2) by collapsing the ball or *)
(* tree, over the simplex case of pc_moi_fnd_rnsc.  The statements of the    *)
(* pc_moi_s3032 files restated with this term are in pc_moi_s3032_stmt2.ml.  *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_FND_DERIVED_NBHD_BALL_2 =
 `!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ FINITE l /\
     (!v. {v} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     ((?n. n <= 2 /\ pl_ball n (UNIONS l)) \/
      ((!s. s IN l ==> aff_dim s <= &1) /\ connected (UNIONS l) /\
       ~(UNIONS l = {}) /\
       CARD {v | {v} IN l} = CARD {e | e IN l /\ aff_dim e = &1} + 1))
     ==> pl_cell_with_boundary 3 (derived_nbhd t l) (derived_frontier t l)`;;

let MOI_FS4_BALL_2 = prove
 (mk_imp(MOI_FND_DERIVED_NBHD_BALL,MOI_FND_DERIVED_NBHD_BALL_2),
  DISCH_THEN(LABEL_TAC "ball") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
  STRIP_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(DISJ1_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC));;

Printf.printf "FS4 %b\n%!"
  (aconv (concl MOI_FS4_BALL_2) (mk_imp(MOI_FND_DERIVED_NBHD_BALL,MOI_FND_DERIVED_NBHD_BALL_2)) &&
   hyp MOI_FS4_BALL_2 = [] && frees MOI_FND_DERIVED_NBHD_BALL_2 = []);;

