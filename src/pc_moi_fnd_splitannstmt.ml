(* ========================================================================= *)
(* pc_moi_fnd_splitannstmt: the statement term MOI_FSN_ANNULUS_NBHD, which   *)
(* divides the proof of MOI_FND_SPLIT_ANNULUS_R3 into two parts.             *)
(* MOI_FSN_ANNULUS_NBHD: the second-derived neighbourhood N of an annulus   *)
(* la in the interior of a finite combinatorial 3-manifold t, meeting a     *)
(* closed surface lm exactly in its rims j1, j2.  Its trace on M = |lm| is   *)
(* two disjoint annuli a1, a2 around j1, j2, whose ends are the four        *)
(* circles of F INTER M (F the derived frontier).  F is the union of four   *)
(* annuli: b1, b2 joining the rims (the parallel copies of the annulus) and *)
(* c1, c2 around the rims, meeting only in those circles.                    *)
(* pc_moi_fnd_splitann proves SPLIT_ANNULUS_R3_COND :                        *)
(*   |- MOI_FSN_ANNULUS_NBHD ==> MOI_FND_SPLIT_ANNULUS_R3                    *)
(* and pc_moi_fnd_annnbhd proves ANNULUS_NBHD : |- MOI_FSN_ANNULUS_NBHD.     *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_FSN_ANNULUS_NBHD =
 `!(t:(real^3->bool)->bool) la lm j1 j2.
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     simplicial_subcomplex la t /\ simplicial_subcomplex lm t /\
     FINITE lm /\ combinatorial_manifold 2 lm /\
     pl_annulus_with_ends (UNIONS la) j1 j2 /\
     UNIONS la INTER UNIONS lm = j1 UNION j2 /\
     DISJOINT (derived_nbhd t la) (complex_boundary t)
     ==> ?a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
           derived_nbhd t la INTER UNIONS lm = a1 UNION a2 /\ DISJOINT a1 a2 /\
           pl_annulus_with_ends a1 k11 k12 /\ pl_annulus_with_ends a2 k21 k22 /\
           j1 SUBSET a1 DIFF (k11 UNION k12) /\ j2 SUBSET a2 DIFF (k21 UNION k22) /\
           derived_frontier t la INTER UNIONS lm = k11 UNION k12 UNION k21 UNION k22 /\
           derived_frontier t la = b1 UNION b2 UNION c1 UNION c2 /\
           pl_annulus_with_ends b1 k11 k21 /\ pl_annulus_with_ends b2 k12 k22 /\
           pl_annulus_with_ends c1 k11 k12 /\ pl_annulus_with_ends c2 k21 k22 /\
           DISJOINT b1 b2 /\ DISJOINT c1 c2 /\
           b1 INTER c1 = k11 /\ b1 INTER c2 = k21 /\
           b2 INTER c1 = k12 /\ b2 INTER c2 = k22`;;

let moi_fsn_stmt_ok =
  type_of MOI_FSN_ANNULUS_NBHD = bool_ty && frees MOI_FSN_ANNULUS_NBHD = [];;

if not moi_fsn_stmt_ok then failwith "moi_fsn_stmt_ok";;

Printf.printf "SPLITANNSTMT %b\n%!" moi_fsn_stmt_ok;;

