(* ========================================================================= *)
(* pc_moi_core_status: the Moise PL core,                                    *)
(*   MOI_CORE_STATUS : |- MOISE_352_COMPLEX_STATEMENT (:7).                  *)
(* The closure theorem MOI_CD_BLUEPRINT_CLOSURE of pc_moi_core_stmt.ml       *)
(* reduces the PL core to its producers, glue implications and leaves        *)
(* (results of Moise Secs 25-35, the Schoenflies theorems and the loop       *)
(* theorem); each of them is proved in the files loaded below, and the       *)
(* theorems MOI_CST_ below instantiate them at the types of the core.        *)
(* MOI_CORE_PROVED lists them all; the lists MOI_CORE_REMAINING_IMPLS and    *)
(* MOI_CORE_REMAINING_LEAVES of conjuncts not in that list are empty, which  *)
(* the file checks, so MOI_CORE_STATUS has no antecedent.                    *)
(* ========================================================================= *)

needs "src/pc_moi_cglue.ml";;
needs "src/pc_moi_s30sep.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_s27.ml";;
needs "src/pc_moi_p305.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_s308.ml";;
needs "src/pc_moi_s35_all.ml";;
needs "src/pc_moi_sch3_all.ml";;
needs "src/pc_moi_s288_cov.ml";;
needs "src/pc_moi_s2810.ml";;
needs "src/pc_moi_s26_sep.ml";;
needs "src/pc_moi_fnd_sides.ml";;
needs "src/pc_moi_s34_status.ml";;
needs "src/pc_moi_s3032_stmt5.ml";;
needs "src/pc_moi_s30_cut_a.ml";;
needs "src/pc_moi_s30_cut_b.ml";;
needs "src/pc_moi_fnd_rnb2.ml";;
needs "src/pc_moi_sch3_amb2.ml";;
needs "src/pc_moi_s26_three.ml";;
needs "src/pc_moi_s26_surf.ml";;
needs "src/pc_moi_s286.ml";;
needs "src/pc_moi_loop_status.ml";;
needs "src/pc_moi_s3032_stmt4.ml";;
needs "src/pc_moi_s31_rev.ml";;
needs "src/pc_moi_s31_cross.ml";;
needs "src/pc_moi_fnd_gpb.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_s30_tame.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_s35_charts.ml";;
needs "src/pc_moi_s35_triple.ml";;
needs "src/pc_moi_s32_handles.ml";;
needs "src/pc_moi_fnd_tubeb.ml";;
needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_s32_cap_a.ml";;
needs "src/pc_moi_s32_cap_b.ml";;
needs "src/pc_moi_s30_z2c.ml";;
needs "src/pc_moi_s33_z2a.ml";;
needs "src/pc_moi_s33_z2b.ml";;
needs "src/pc_moi_fnd_surfb.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s30_shell.ml";;
needs "src/pc_moi_s30_init.ml";;
needs "src/pc_moi_s30_comp.ml";;
needs "src/pc_moi_fnd_split.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_s30_bound.ml";;
needs "src/pc_moi_s26_nbhd.ml";;
needs "src/pc_moi_s26_cut.ml";;
needs "src/pc_moi_s26_fill.ml";;
needs "src/pc_moi_s26_level.ml";;
needs "src/pc_moi_s26_ext.ml";;
needs "src/pc_moi_s28_tria.ml";;
needs "src/pc_moi_fnd_bicol.ml";;
needs "src/pc_moi_s26_cross.ml";;
needs "src/pc_moi_s26_local.ml";;
needs "src/pc_moi_fnd_nb2f.ml";;
needs "src/pc_moi_fnd_sptrace.ml";;
needs "src/pc_moi_lt_fill.ml";;
needs "src/pc_moi_s3032_stmt6.ml";;
needs "src/pc_moi_s32_chart.ml";;
needs "src/pc_moi_s32_tower.ml";;
needs "src/pc_moi_s32_init3.ml";;
needs "src/pc_moi_s32_iter3.ml";;
needs "src/pc_moi_s32_level.ml";;
needs "src/pc_moi_s32_iter.ml";;
needs "src/pc_moi_s32_classify3.ml";;
needs "src/pc_moi_s32_steps.ml";;
needs "src/pc_moi_s32_cell.ml";;
needs "src/pc_moi_s32_sides.ml";;
needs "src/pc_moi_fnd_cbicol.ml";;
needs "src/pc_moi_s31_axis.ml";;
needs "src/pc_moi_s31_carrier.ml";;
needs "src/pc_moi_s31_mv.ml";;
needs "src/pc_moi_s31_link.ml";;
needs "src/pc_moi_fnd_tubep.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_s30_tor_a.ml";;
needs "src/pc_moi_s30_cst.ml";;
needs "src/pc_moi_fnd_tubed.ml";;
needs "src/pc_moi_s30_tor_b.ml";;
needs "src/pc_moi_s35_ext2.ml";;
needs "src/pc_moi_s35_ext.ml";;
needs "src/pc_moi_s35_deg.ml";;
needs "src/pc_moi_fnd_surfc.ml";;
needs "src/pc_moi_fnd_splitann.ml";;
needs "src/pc_moi_fnd_annnbhd.ml";;
needs "src/pc_moi_s33_frame.ml";;
needs "src/pc_moi_s33_x2.ml";;
needs "src/pc_moi_s33_char.ml";;
needs "src/pc_moi_s33_traces.ml";;
needs "src/pc_moi_s33_conn.ml";;
needs "src/pc_moi_s33_push.ml";;
needs "src/pc_moi_s33_ltd7.ml";;
needs "src/pc_moi_s33_l8.ml";;
needs "src/pc_moi_s33_l9stmt.ml";;
needs "src/pc_moi_s33_gp.ml";;
needs "src/pc_moi_s33_l9.ml";;
needs "src/pc_moi_s33_l10.ml";;
needs "src/pc_moi_s33_l12.ml";;
needs "src/pc_moi_s33_hext.ml";;
needs "src/pc_moi_s33_sorient.ml";;
needs "src/pc_moi_s33_msides.ml";;
needs "src/pc_moi_s33_match.ml";;
needs "src/pc_moi_s33_ext.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_dn.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_CST_PROD_302 = prove
 (MOI_PROD_302,
  DISCH_THEN(K(ACCEPT_TAC MOISE_302)));;

let MOI_CST_341_NBHD = prove
 (MOI_CORE_GLUE_341_NBHD,
  MATCH_MP_TAC MOI_CGL_341_NBHD THEN ACCEPT_TAC BALL_TRIANGULATION_IN_OPEN);;

(* 35.1 at the core's type (:7): pc_moi_s35_all proves MOI_PROD_351 with no *)
(* hypotheses (MOI_S35_ALL_PROD_351, type variable N).                      *)

let MOI_CST_PROD_351 = prove
 (n7 MOI_PROD_351,
  ACCEPT_TAC(INST_TYPE [`:7`,`:N`] MOI_S35_ALL_PROD_351));;

(* 26.6 and 26.8 (leaves): 26.6 by the rule MOI_S26_SEP from the three 26.6 *)
(* chain theorems; 26.8 by MOI_FD_268_GLUE from the orientation of closed   *)
(* surfaces in real^3 (fnd_sides) and 26.6.                                 *)

let MOI_CST_266 = prove
 (`MOISE_266_STATEMENT`,
  ACCEPT_TAC(MP SEP_266 (CONJ EVEN_CROSSING (CONJ LOCAL_TRI LOCAL_EDGE))));;

let MOI_CST_268 = prove
 (`MOISE_268_STATEMENT`,
  ACCEPT_TAC(MP MOI_FD_268_GLUE (CONJ SURFACE_SIDES_ORIENTABLE_3 MOI_CST_266)));;

(* Sec 34: MOI_PROD_34_EXT at the two types of the core.                    *)

let MOI_CST_34EXT_7 = prove
 (n7 MOI_PROD_34_EXT, ACCEPT_TAC(INST_TYPE [`:7`,`:N`] MOI_S34ST_PROD));;

let MOI_CST_34EXT_3 = prove
 (n3 MOI_PROD_34_EXT, ACCEPT_TAC(INST_TYPE [`:3`,`:N`] MOI_S34ST_PROD));;

(* 30.3 by the s3032 glue of pc_moi_s3032_stmt5.                             *)

let MOI_CST_303 = prove
 (`MOISE_303_STATEMENT`,
  MATCH_MP_TAC MOI_S3S5_303 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
    [CUTCAP; MOI_SCH3_ALL_SCHOENFLIES; ANNULUS_2D; MATCH_MP MOI_SCD_AMB2 AMB2_VERTEX;
     DISK_CHART_2; INST_TYPE [`:3`,`:N`] DERIVED_NBHD_BALL_2]));;

(* 26.7 from 26.6 and the s26 units (rule MOI_S26_THREE).                   *)

let MOI_CST_267 = prove
 (`MOISE_267_STATEMENT`,
  MATCH_MP_TAC THREE_267 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
    [MOI_CST_266; MOI_S6G_SURF_GLUE_BODY; INT_CONNECTED; LOCAL_TRI]));;

(* 31.1 and 32.3 by the s3032 glue from the theorems of their files (at     *)
(* their own types and at :3).                                              *)

let moi_cst_pool8 =
  let ths = [REV_SHELL; RECROSS; GENERAL_POSITION_SURFACES_3; PL_SOLID_TORUS_BASIC;
             PL_TORUS_COMPLEX; SURFACE_TRIANG; SURF_LOCAL; COMPLEX_EULER_VALUES;
             GRAPH_TUBE_DUAL_CELLS; CHARTS; TUBE_TRIPLE; SLAB_W; HANDLES;
             GRAPH_TUBE_FRONTIER_3; DERIVED_NBHD_BASIC] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1;;

let MOI_CST_311 = prove
 (MOI_PROD_311,
  MATCH_MP_TAC MOI_STD_311 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool8));;

let MOI_CST_323 = prove
 (MOI_PROD_323,
  MATCH_MP_TAC MOI_S3S4_323 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool8));;

(* 32.4 (leaf) by the s3032 glue MOI_S3S5_324; the character count with      *)
(* boundary from the s33 glue MOI_S3D_CHAR_COUNT_BD.                         *)

let moi_cst_cc_bd = MP (INST_TYPE [`:3`,`:N`] MOI_S3D_CHAR_COUNT_BD)
   (CONJ (INST_TYPE [`:3`,`:N`] Z2_COUNT_BD) (INST_TYPE [`:3`,`:N`] Z2_CHAR));;

let moi_cst_pool324 =
  let ths = [CAP_SETUP; CAP_SURGERY; GENERAL_POSITION_SURFACES_3; SURFACE_TRIANG; SURF_LOCAL;
             POLY_DISK; Z2_SC_BOUNDARY; moi_cst_cc_bd; SURFACE_EULER_PLANAR; DISK_CHART_2;
             MOI_SCH3_ALL_SCHOENFLIES; DERIVED_NBHD_BALL_2; ANNULUS_2D;
             MATCH_MP MOI_SCD_AMB2 AMB2_VERTEX; SPHERE_SPLIT] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1;;

let MOI_CST_324 = prove
 (`MOISE_324_STATEMENT`,
  MATCH_MP_TAC MOI_S3S5_324 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool324));;

(* 30.4 (producer) by MOI_STD_304 and 26.4 (producer, = MOI_CORE_GLUE_264)  *)
(* by the s2628 glue MOI_SDD_PROD_264; the split along a disk from          *)
(* fnd_split with BALL_2 and the sptrace annulus.                           *)

let moi_cst_split_disk =
  MP SPLIT_SURFACE_DISK_3
     (CONJ DERIVED_NBHD_BALL_2
           (MP SPLIT_TRACE_ANNULUS (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_POLYGON_2)));;

let moi_cst_cc = MP (INST_TYPE [`:3`,`:N`] MOI_S3D_CHAR_COUNT)
   (CONJ (INST_TYPE [`:3`,`:N`] Z2_COUNT) (INST_TYPE [`:3`,`:N`] Z2_CHAR));;

let moi_cst_pool304 =
  let ths = [moi_cst_split_disk; SPHERICAL_SHELL_FACTS; INIT_SURFACE; DERIVED_NBHD_COMBINATORIAL;
             COMPRESS; MP SEP_266 (CONJ EVEN_CROSSING (CONJ LOCAL_TRI LOCAL_EDGE));
             SURFACE_EULER_SPHERE; BOUNDS; COMPACT_NBHD; CUT; SPHERE_SPLIT;
             COMPLEX_EULER_PL_INVARIANT; SPLIT_ESSENTIAL;
             SPEC `(:3)` (INST_TYPE [`:3`,`:N`] MOISE_273); DISK_COMPLEMENT; Z2_SC_CLOSED;
             moi_cst_cc; EULER_NAT; EVEN_CROSSING; LOCAL_TRI; LOCAL_EDGE; SEP_266;
             PL_FILL; LEVEL_CIRCLES; S26_EXT; SURF_CHARTS; SURF_LOCAL; SURF_INVARIANT;
             SURFACE_BICOLLAR_R3] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1 @ map (INST_TYPE [`:3`,`:N`; `:3`,`:M`]) ths1;;

let MOI_CST_304 = prove
 (MOI_PROD_304,
  MATCH_MP_TAC MOI_STD_304 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool304));;

let MOI_CST_264 = prove
 (MOI_PROD_264,
  MATCH_MP_TAC MOI_SDD_PROD_264 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool304));;

(* 32.2 (cells) and 31.4 by the s3032 glue from the s32 and s31 files.      *)

let moi_cst_pool322 =
  let ths = [CHART; MODEL_V; TOWER; RECROSS; GENERAL_POSITION_SURFACES_3; PL_SOLID_TORUS_BASIC;
             PL_TORUS_COMPLEX; SURFACE_TRIANG; SURF_LOCAL; COMPLEX_EULER_VALUES; INITIAL_3;
             ITERATE_3; LEVEL_3; MOI_CST_268; CURVE_BICOLLAR_ORIENTABLE; LIMIT; CLASSIFY_3;
             SURFACE_EULER_PLANAR; COMPLEX_EULER_UNION; PL_HOLED_DISK_1_ANNULUS; STEPS24; CELL;
             SIDES; DISK_COMPLEMENT; SPHERE_SPLIT; SPINES; TRANSFER; REV_SHELL; CARRIER; MV_POLY;
             NULL_POLYGON_2; POLYGON_NBHD_SOLID_TORUS; DERIVED_NBHD_BALL_2;
             SPINE_HOMOLOGY_ISOMORPHISM; SOLID_TORUS_MODEL_NULLHOMOTOPIC_WINDING] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1;;

let MOI_CST_322 = prove
 (MOI_PROD_322_CELLS,
  MATCH_MP_TAC MOI_S3S6_322 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool322));;

let MOI_CST_314 = prove
 (MOI_PROD_314,
  MATCH_MP_TAC MOI_S3S5_314 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool322));;

(* 30.7 by the s3032 glue MOI_STD_307 from s30_tor_b (HANDLE_SOLID_TORUS),  *)
(* s30_tor_a, s30_cst, the s35 disk extensions and the units of 30.4.       *)

let moi_cst_pool307 =
  let ths = [PL_TORUS_COMPLEX; SURFACE_TRIANG; SURF_LOCAL; COMPLEX_EULER_VALUES; BOUNDS;
             COMPACT_NBHD; DERIVED_NBHD_COMBINATORIAL; CUT; SPHERE_SPLIT;
             COMPLEX_EULER_PL_INVARIANT; TORUS_REGION; TORUS_LOOP; S307_OUTSIDE;
             moi_cst_split_disk; SURFACE_EULER_SPHERE; SPLIT_ESSENTIAL;
             SPEC `(:3)` (INST_TYPE [`:3`,`:N`] MOISE_273); DISK_COMPLEMENT; EULER_EVEN;
             SHELL_CORE_ESSENTIAL; S307_INSIDE; HANDLE_SOLID_TORUS; LOCAL_SIGN; ONE_DISK_EXT;
             TWO_DISK_EXT; DISK_UNION] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1 @ map (INST_TYPE [`:3`,`:N`; `:3`,`:M`]) ths1;;

let MOI_CST_307 = prove
 (MOI_PROD_307,
  MATCH_MP_TAC MOI_STD_307 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool307));;

(* 30.6 by the s3032 glue MOI_STD_306 from fnd_surfc (SURFACE_EULER_TORUS), *)
(* s30_shell, s30_z2c, fnd_tubed and the 30.4 pool.                          *)

let moi_cst_pool306 =
  let ths = [TOROIDAL_SHELL_FACTS; Z2_TORUS_BOUND; SHELL_NO_SPHERE; EULER_EVEN;
             SURFACE_EULER_TORUS; MOI_CST_268] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1 @ moi_cst_pool304;;

let MOI_CST_306 = prove
 (MOI_PROD_306,
  MATCH_MP_TAC MOI_STD_306 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool306));;

(* 33.1 by the glue MOI_S3D_PROD_331 of pc_moi_s33_stmt from the Sec 33     *)
(* files; TRACES through the annulus split (stage 1 COND and stage 2        *)
(* ANNULUS_NBHD), L9 through the l9 split glue MOI_S39D_L9.                 *)

let moi_cst_traces =
  MP MOI_S3TR_TRACES_ANN (MP SPLIT_ANNULUS_R3_COND ANNULUS_NBHD);;

let moi_cst_l9 = MP MOI_S39D_L9 (CONJ S39_GP (CONJ S39_PUSH S39_L9_FROM));;

let moi_cst_pool331 =
  let ths = [TUBE_FACTS; X2; DISK_RECOG; HOLED_RECOG; CHAR_TRANSFER; CHAR_HOMEO;
             CHAR_PRODUCT; POLY_PC; Z2_COUNT; Z2_COUNT_BD; Z2_CHAR; moi_cst_traces;
             S33_L5; S33_L6; LTD_STEP; S33_L8; moi_cst_l9; S33_SURJ; S33_EULER;
             HOLED_EXT; MATCH; S33_EXT; TUBE_TRIPLE; SURFACE_EULER_SPHERE;
             BOUNDARY_COMPLEX_SURFACE; COMPLEX_BOUNDARY_FRONTIER_3;
             GRAPH_NBHD_BOUNDARY_EULER; DERIVED_NBHD_BASIC] in
  let ths1 = flat (map (fun th -> th :: CONJUNCTS th) ths) in
  ths1 @ map (INST_TYPE [`:3`,`:N`]) ths1 @ map (INST_TYPE [`:2`,`:N`]) ths1 @
  map (INST_TYPE [`:2`,`:M`; `:3`,`:N`]) ths1;;

let MOI_CST_331 = prove
 (MOI_PROD_331,
  MATCH_MP_TAC MOI_S3D_PROD_331 THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC moi_cst_pool331));;

(* The loop producer n7 MOI_CORE_GLUE_LOOPN from lt_fill, lt_nsys and fnd_m3b *)
(* through MOI_LTD_LOOPN.                                                    *)

let MOI_CST_LOOPN = prove
 (n7 MOI_CORE_GLUE_LOOPN,
  MATCH_MP_TAC (INST_TYPE [`:7`,`:N`; `:7`,`:M`] MOI_LTD_LOOPN) THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC [LT_FILL; NSYS; COMBINATORIAL_WB_BARYCENTRIC]));;

(* The conjuncts of the closure not in MOI_CORE_PROVED: producers and glue   *)
(* (first list) and leaves (second list); both lists are empty.              *)

let MOI_CORE_REMAINING_IMPLS =
  ([]:term list);;

let MOI_CORE_REMAINING_LEAVES = ([]:term list);;

let MOI_CORE_REMAINING = MOI_CORE_REMAINING_IMPLS @ MOI_CORE_REMAINING_LEAVES;;

let MOI_CORE_PROVED =
  [MOI_CGL_352; MOI_CGL_341; MOI_CGL_LOOP3; MOI_CST_PROD_302; MOISE_301;
   MOISE_CELL_ASSEMBLY_ON; MOISE_273; MOI_PROD_305_THM; MOI_CST_341_NBHD;
   MOISE_308; MOI_CST_PROD_351; MOI_SCH3_ALL_SCHOENFLIES;
   MOI_SCH3_ALL_SCHOENFLIES_AMBIENT; MOISE_288; MOISE_2810; MOI_CST_266; MOI_CST_268;
   MOI_CST_34EXT_7; MOI_CST_34EXT_3; MOI_CST_303; MOI_CST_267; MOISE_286;
   MOI_CST_311; MOI_CST_323; MOI_LTST_PROD_LOOP_NS; MOI_LTST_SPHERE;
   MOI_LTST_DOUBLE_COVER; MOI_CST_324; MOI_CST_304; MOI_CST_264; MOI_CST_LOOPN;
   MOI_CST_322; MOI_CST_314; MOI_LTST_DESCENT; MOI_CST_307; MOI_CST_306;
   MOI_CST_331];;

if not (MOI_CORE_REMAINING = []) then failwith "rev 10: open items left";;

let MOI_CORE_STATUS = prove
 (`MOISE_352_COMPLEX_STATEMENT (:7)`,
  MATCH_MP_TAC MOI_CD_BLUEPRINT_CLOSURE THEN
  REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC MOI_CORE_PROVED));;

(length MOI_CORE_REMAINING_IMPLS, length MOI_CORE_REMAINING_LEAVES,
 length (hyp MOI_CORE_STATUS));;

