(* ========================================================================= *)
(* pc_moi_s35_all: the composed 35.1 producer.  Loads every unit proving a   *)
(* statement of MOI_S35_UNIT_TARGETS_R3 (pc_moi_s35_stmt_r3.ml) and the two  *)
(* foundation statements, and derives MOI_PROD_351 (pc_moi_core_stmt.ml)     *)
(* through MOI_S5D_PROD_351_R3: the theorem MOI_S35_ALL_PROD_351.            *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_s35_triple.ml";;
needs "src/pc_moi_s35_mark.ml";;
needs "src/pc_moi_s35_deg.ml";;
needs "src/pc_moi_s35_ext.ml";;
needs "src/pc_moi_s35_ext2.ml";;
needs "src/pc_moi_s35_slab.ml";;
needs "src/pc_moi_s35_charts.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_s35_apxsep3.ml";;
needs "src/pc_moi_s35_mina.ml";;
needs "src/pc_moi_s35_minb.ml";;
needs "src/pc_moi_s35_minc.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s35_comb.ml";;
needs "src/pc_moi_s35_fina.ml";;
needs "src/pc_moi_s35_finb2.ml";;
needs "src/pc_moi_s35_stmt_r3.ml";;

prioritize_real();;
type_invention_error := true;;

(* Lemma 3 of 35.1 (annulus swap) from its split form and the sphere split  *)
(* of pc_moi_sch3_s2.                                                       *)

let MOI_S35_ALL_ANNULUS_SWAP = MP MOI_S5C_ANNULUS_SWAP_SPLIT SPHERE_SPLIT;;

(* The 19 unit theorems in the order of MOI_S35_UNIT_TARGETS_R3.            *)

let MOI_S35_ALL_TARGETS =
  [TUBE_TRIPLE; MARKER; CELL_341; FILL; LOCAL_SIGN; CLOSE_SIGN; ONE_DISK_EXT;
   TWO_DISK_EXT; SLAB_PRODUCT; CHARTS; SOURCE; APPROX_R3; LEMMA1; SINGLE_FROM_ONE;
   DISK_SWAP; MOI_S35_ALL_ANNULUS_SWAP; COMBINE; FINAL_CELLS; MOI_S5P_FINAL_R3];;

let MOI_S35_ALL_TARGETS_OK =
  List.length MOI_S35_ALL_TARGETS = List.length MOI_S35_UNIT_TARGETS_R3 &&
  List.for_all2 (fun th tm -> aconv (concl th) tm && hyp th = [])
    MOI_S35_ALL_TARGETS MOI_S35_UNIT_TARGETS_R3;;

let MOI_S35_ALL_PROD_351 =
  MP MOI_S5D_PROD_351_R3
     (end_itlist CONJ (DERIVED_NBHD_BASIC :: GRAPH_TUBE_DUAL_CELLS :: MOI_S35_ALL_TARGETS));;

