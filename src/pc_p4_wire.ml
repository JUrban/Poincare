(* ========================================================================= *)
(* Unit pc_p4_wire: the wiring of the Colding-Minicozzi core into Part 4.    *)
(* The seven chain theorems of the statement file pc_cm_stmts, the           *)
(* harmonic-map theorems of pc_hm_reg_eps, pc_hm_reg_rem, pc_hm_reg_sph and  *)
(* pc_hm_regularity, the Sobolev and potential theory of the pc_wan units    *)
(* and the topology of pc_top_p4 give                                        *)
(*   FINITE_EXTINCTION          |- FINITE_EXTINCTION_STATEMENT (:A)          *)
(*   FINITE_EXTINCTION_ALL      |- !u:A->bool. FINITE_EXTINCTION_STATEMENT u *)
(*   P4_EXTINCTION_FROM_CUTCAP                                               *)
(*     |- RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3)    *)
(*        ==> P4_EXTINCTION_STATEMENT (:A)                                   *)
(* The Part 3 form has the single hypothesis RFS_CUTCAP_SC_STATEMENT         *)
(* (pc_rfs_top), proved in pc_rfs_ccsc and discharged in pc_p4_final;        *)
(* FINITE_EXTINCTION has none.                                               *)
(* ========================================================================= *)

needs "src/pc_p4_align.ml";;
needs "src/pc_p4_pinch.ml";;
needs "src/pc_top_p4.ml";;
needs "src/pc_cm_width.ml";;
needs "src/pc_cm_lemma122.ml";;
needs "src/pc_cm_replacement.ml";;
needs "src/pc_cm_compactness.ml";;
needs "src/pc_hm_dirichlet.ml";;
needs "src/pc_hm_convexity.ml";;
needs "src/pc_hm_regularity.ml";;
needs "src/pc_hm_reg_eps.ml";;
needs "src/pc_hm_reg_rem.ml";;
needs "src/pc_hm_reg_sph.ml";;
needs "src/pc_wan_weak.ml";;
needs "src/pc_wan_sob2.ml";;
needs "src/pc_wan_sob2b.ml";;
needs "src/pc_wan_sob2c.ml";;
needs "src/pc_wan_sob2p.ml";;
needs "src/pc_wan_sob2r.ml";;
needs "src/pc_wan_sob2s.ml";;
needs "src/pc_wan_sob2v.ml";;
needs "src/pc_wan_lap2a.ml";;
needs "src/pc_wan_lap2e.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The CM core in the ambient dimension K = 7 (MFD_EMBEDDING_EXISTS).        *)
(* ------------------------------------------------------------------------- *)

(* Harmonic-map regularity, removable singularities, Hopf, the energy gap   *)
(* and isolatedness of harmonic spheres.                                     *)

let P4W_CM_REGULARITY7 = prove
 (`CM_EPS_REG_STATEMENT (:7) /\ CM_MINIMIZER_SMOOTH_STATEMENT (:7) /\
   CM_REMOVABLE_STATEMENT (:7) /\ CM_HOPF_STATEMENT (:7) /\
   CM_SPHERE_GAP_STATEMENT (:7) /\ CM_CRITICAL_ISOLATED_STATEMENT (:7)`,
  REWRITE_TAC[CM_EPS_REG; CM_MINIMIZER_SMOOTH; CM_REMOVABLE; CM_HOPF; CM_SPHERE_GAP;
              CM_CRITICAL_ISOLATED]);;

(* CM_CHAIN_HM_CONVEXITY (pc_hm_convexity).                                   *)

let P4W_CM_CONVEXITY7 = prove
 (`CM_CONVEXITY_STATEMENT (:7)`,
  MP_TAC(ISPEC `(:7)` CM_CHAIN_HM_CONVEXITY) THEN
  REWRITE_TAC[CM_CHAIN_HM_CONVEXITY_STATEMENT; WAN_HARDY_BALL; WAN_CHAIN_W12; WAN_W12_C1;
              WAN_W120_CONT; P4W_CM_REGULARITY7]);;

(* CM_CHAIN_HM_DIRICHLET (pc_hm_dirichlet).                                   *)

let P4W_CM_REPLACEMENT7 = prove
 (`CM_REPLACEMENT_STATEMENT (:7)`,
  MP_TAC(ISPEC `(:7)` CM_CHAIN_HM_DIRICHLET) THEN
  REWRITE_TAC[CM_CHAIN_HM_DIRICHLET_STATEMENT; WAN_RELLICH0; WAN_GDIR_LSC;
              WAN_WEAK_PARTIALS_CONV; WAN_RADON_RIESZ_G; WAN_W120_CONT; WAN_CHAIN_W12;
              WAN_CHAIN_LIP_W12; WAN_GLUE_W12; WAN_COURANT_LEBESGUE;
              WAN_COURANT_LEBESGUE_BDRY; WAN_POISSON_ENERGY; WAN_MAX_PRINCIPLE_DISC_BALL;
              P4W_CM_REGULARITY7; P4W_CM_CONVEXITY7]);;

(* CM_CHAIN_CM_REPLACEMENT (pc_cm_replacement): CM Thm 2.1.                   *)

let P4W_CM_TIGHTEN7 = prove
 (`CM_TIGHTEN_STATEMENT (:7)`,
  MP_TAC(ISPEC `(:7)` CM_CHAIN_CM_REPLACEMENT) THEN
  REWRITE_TAC[CM_CHAIN_CM_REPLACEMENT_STATEMENT; P4W_CM_REPLACEMENT7; P4W_CM_CONVEXITY7;
              P4W_CM_REGULARITY7; WAN_WIRTINGER_VEC; WAN_POLAR_DIR; WAN_CIRCLE_ACL;
              WAN_GLUE_W12; WAN_MUL_W12; WAN_CHAIN_W12; WAN_W120_CONT; WAN_W12_DIFFEO;
              WAN_DIR_CONFORMAL_2D; WAN_S2_STEREO]);;

(* CM_CHAIN_CM_COMPACTNESS (pc_cm_compactness): CM Thm B.1.                   *)

let P4W_CM_COMPACTNESS7 = prove
 (`CM_COMPACTNESS_STATEMENT (:7)`,
  MP_TAC(ISPEC `(:7)` CM_CHAIN_CM_COMPACTNESS) THEN
  REWRITE_TAC[CM_CHAIN_CM_COMPACTNESS_STATEMENT; P4W_CM_REGULARITY7; P4W_CM_REPLACEMENT7;
              P4W_CM_CONVEXITY7; WAN_RELLICH_LOC; WAN_WEAK_PARTIALS_CONV; WAN_POINCARE0;
              WAN_WIRTINGER_VEC; WAN_POLAR_DIR; WAN_CIRCLE_ACL; WAN_REMOVABLE_POINT;
              WAN_W12_DIFFEO; WAN_DIR_CONFORMAL_2D; WAN_S2_STEREO]);;

(* ------------------------------------------------------------------------- *)
(* The top statement CM_GOOD_SWEEPOUT of Part 4 (from CM_CHAIN_CM_WIDTH of   *)
(* pc_cm_width); the other one, CM_HARMONIC_SPHERE, is CML_HARMONIC_SPHERE   *)
(* of pc_cm_lemma122.                                                        *)
(* ------------------------------------------------------------------------- *)

let P4W_GOOD_SWEEPOUT = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A)`,
  MP_TAC CM_CHAIN_CM_WIDTH THEN
  REWRITE_TAC[CM_CHAIN_CM_WIDTH_STATEMENT; P4W_CM_TIGHTEN7; P4W_CM_COMPACTNESS7;
              P4W_CM_REPLACEMENT7; P4W_CM_REGULARITY7; WAN_W12_C1; WAN_CHAIN_W12;
              WAN_CHAIN_LIP_W12; WAN_S2_STEREO; WAN_DIR_CONFORMAL_2D]);;

(* ------------------------------------------------------------------------- *)
(* Finite extinction (MT Thm 18.1 in the form FINITE_EXTINCTION_STATEMENT of *)
(* pc_p4_top) with no hypothesis, and the Part 3 form P4_EXTINCTION from     *)
(* RFS_CUTCAP_SC.                                                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_EXTINCTION = prove
 (`FINITE_EXTINCTION_STATEMENT (:A)`,
  MATCH_MP_TAC P4_FINITE_EXTINCTION_CM2 THEN
  REWRITE_TAC[P4W_GOOD_SWEEPOUT; CML_HARMONIC_SPHERE; ATOP_P4_DEGREE_ONE_PROVED;
              ATOP_P4_SC_DEGREE_ONE_PROVED; ATOP_P4_SMOOTHING_PROVED]);;

let FINITE_EXTINCTION_ALL = prove
 (`!u:A->bool. FINITE_EXTINCTION_STATEMENT u`,
  MP_TAC FINITE_EXTINCTION THEN REWRITE_TAC[FINITE_EXTINCTION_STATEMENT]);;

let P4_EXTINCTION_FROM_CUTCAP = prove
 (`RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3)
   ==> P4_EXTINCTION_STATEMENT (:A)`,
  DISCH_TAC THEN MATCH_MP_TAC P4_EXTINCTION_CM3 THEN
  ASM_REWRITE_TAC[P4W_GOOD_SWEEPOUT; CML_HARMONIC_SPHERE; ATOP_P4_DEGREE_ONE_PROVED;
                  ATOP_P4_SC_DEGREE_ONE_PROVED; ATOP_P4_SMOOTHING_PROVED]);;

