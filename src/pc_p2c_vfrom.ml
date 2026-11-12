(* ========================================================================= *)
(* Unit pc_p2c_vfrom (Part 2C): from-smoothness of views.  For W open in   *)
(* the slice at a and persisting over (a,b], the identity is a diffeo from  *)
(* the slice at a to the slice at b.  This is conjunct 5 of               *)
(* p2c_regular_view (without it Prop 5.14 at a least element 0 of J does    *)
(* not follow); the predicate p2cz_from_smooth has literally that conjunct  *)
(* as its body.  Flow views satisfy it (P2CZ_FLOW_VIEW_FROM_SMOOTH);        *)
(* histories by P2CY_HIST_FROM_SMOOTH of unit pc_p2c_hreg.                  *)
(* ========================================================================= *)

needs "src/pc_p2c_fview.ml";;

prioritize_real();;
type_invention_error := true;;

let p2cz_from_smooth = new_definition
 `p2cz_from_smooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) <=>
    (!W a b. a < b /\ open_in (rfs_vtop V a) W /\ rfs_persists V W a b
             ==> mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W
                            (rfs_vtop V b) (rfs_vatlas V b) W (\y:A. y) (\y. y))`;;

let P2CZ_FLOW_VIEW_FROM_SMOOTH = prove
 (`!top atlas J (g:real->A->real^3^3).
     p2cz_from_smooth (rfs_flow_view (top,atlas) J g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2cz_from_smooth] THEN
  MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
  ASM_CASES_TAC `W:A->bool = {}` THEN ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `J:real->bool`; `g:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                P2CF_FLOW_PERSIST_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
  UNDISCH_TAC `open_in (rfs_vtop (rfs_flow_view (top,atlas) J (g:real->A->real^3^3)) a) W` THEN
  REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `J:real->bool`; `W:A->bool`; `a:real`]
                P2CF_FLOW_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]);;

