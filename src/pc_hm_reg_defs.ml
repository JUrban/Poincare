(* ========================================================================= *)
(* Unit pc_hm_reg_defs (definitions for the harmonic map regularity chain of *)
(* pc_hm_regularity): the class cm_wharmonic and the statement               *)
(* CM_REG01_STATEMENT.  cm_wharmonic is the class of continuous W^{1,2} maps *)
(* into S whose energy is critical for the variations                        *)
(* closest_point S (u + e phi) (the variational condition of                 *)
(* cm_harmonic without smoothness); CM_REG01_STATEMENT says that such maps   *)
(* are smooth harmonic maps.  It is proved as CM_REG01 in pc_hm_reg_smth,    *)
(* from the C^(1,al) regularity of pc_hm_reg_c1a; pc_hm_reg_rem and          *)
(* pc_hm_reg_min state their results against this statement.                 *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The class cm_wharmonic, the statement constant CM_REG01_STATEMENT and the *)
(* inclusion of smooth harmonic maps.                                        *)
(* ========================================================================= *)

let cm_wharmonic = new_definition
 `cm_wharmonic (S:real^K->bool) (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) <=>
    wan_w12 s u /\ u continuous_on s /\ (!x. x IN s ==> u x IN S) /\
    !(phi:real^2->real^K) s'.
       open s' /\ bounded s' /\ closure s' SUBSET s /\ wan_vtest s' phi
       ==> ((\e. cm_gen G s' (\x. closest_point S (u x + e % phi x))) has_real_derivative &0)
           (atreal (&0))`;;

let CM_REG01_STATEMENT = new_definition
 `CM_REG01_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> !s (u:real^2->real^K). open s /\ cm_wharmonic S G s u ==> cm_harmonic S G s u`;;

let CM_HARMONIC_IMP_WHARMONIC = prove
 (`!S (G:real^K->real^K^K) s (u:real^2->real^K).
     cm_harmonic S G s u /\ wan_w12 s u ==> cm_wharmonic S G s u`,
  REWRITE_TAC[cm_harmonic; cm_wharmonic] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

