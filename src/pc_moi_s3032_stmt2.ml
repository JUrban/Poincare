(* ========================================================================= *)
(* pc_moi_s3032_stmt2: two statements of pc_moi_s3032_stmt.ml restated on    *)
(* the regular-neighbourhood term of dimension at most 2.  The bodies are    *)
(* the consequents of the original statements (moi_std_csq, not retyped);    *)
(* only the antecedent moi_n3 MOI_FND_DERIVED_NBHD_BALL becomes moi_n3       *)
(* MOI_FND_DERIVED_NBHD_BALL_2 (pc_moi_fnd_stmt4.ml), which the composition  *)
(* can discharge without the 3-ball case.  The _2 forms are proved (in       *)
(* pc_moi_s30_cut_a.ml and pc_moi_s31_link.ml); the bridges give the         *)
(* original texts.                                                           *)
(*   MOI_S30_DISK_CHART_2, MOI_S31_NULL_POLYGON_2;                           *)
(*   MOI_S3S2_DISK_CHART_BRIDGE : |- DISK_CHART_2 ==> MOI_S30_DISK_CHART;    *)
(*   MOI_S3S2_NULL_POLYGON_BRIDGE : |- NULL_POLYGON_2 ==> MOI_S31_NULL_POLYGON. *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_stmt4.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_S30_DISK_CHART_2 =
  mk_imp(list_mk_conj [`PL_SCHOENFLIES_3_STATEMENT`; moi_n3 MOI_FND_DERIVED_NBHD_BALL_2;
                       moi_std_csq MOI_S30_ANNULUS_2D],
         moi_std_csq MOI_S30_DISK_CHART);;

let MOI_S31_NULL_POLYGON_2 =
  mk_imp(list_mk_conj [moi_n3 MOI_S31_MV_POLY; MOI_FND_POLYGON_SOLID_TORUS_3;
                       moi_n3 MOI_FND_DERIVED_NBHD_BALL_2],
         moi_std_csq MOI_S31_NULL_POLYGON);;

let MOI_S3S2_DISK_CHART_BRIDGE = prove
 (mk_imp(MOI_S30_DISK_CHART_2,MOI_S30_DISK_CHART),
  DISCH_THEN(LABEL_TAC "new") THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  USE_THEN "new" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MOI_FS4_BALL_2) THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3S2_NULL_POLYGON_BRIDGE = prove
 (mk_imp(MOI_S31_NULL_POLYGON_2,MOI_S31_NULL_POLYGON),
  DISCH_THEN(LABEL_TAC "new") THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  USE_THEN "new" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC (INST_TYPE [`:3`,`:N`] MOI_FS4_BALL_2) THEN FIRST_ASSUM ACCEPT_TAC]);;

Printf.printf "S3S2 %b %b\n%!"
  (aconv (concl MOI_S3S2_DISK_CHART_BRIDGE) (mk_imp(MOI_S30_DISK_CHART_2,MOI_S30_DISK_CHART)) &&
   hyp MOI_S3S2_DISK_CHART_BRIDGE = [] && frees MOI_S30_DISK_CHART_2 = [])
  (aconv (concl MOI_S3S2_NULL_POLYGON_BRIDGE) (mk_imp(MOI_S31_NULL_POLYGON_2,MOI_S31_NULL_POLYGON)) &&
   hyp MOI_S3S2_NULL_POLYGON_BRIDGE = [] && frees MOI_S31_NULL_POLYGON_2 = []);;

