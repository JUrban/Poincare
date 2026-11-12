(* ========================================================================= *)
(* pc_moi_s32_init3: Moise Sec 32 Lemmas 1-3 with the member invariant of   *)
(* pc_moi_s3032_stmt6.  Main theorem INITIAL_3 |- MOI_S32_INITIAL_3.  The   *)
(* family of INITIAL (pc_moi_s32_init): the components of the L_i; each     *)
(* lies in T''_(2i+1), so it is its own history witness                     *)
(* (MOI_S3S6_HIST_TORUS).                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_s32_init.ml";;
needs "src/pc_moi_s3032_stmt6.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The members with their witnesses, and INITIAL_3.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_S3J3_MEMBER = prove
 (`!(g:real^3->real^3) v pp dd s2 i c.
     (!c:(real^3->bool)->bool.
        lf_simplicial_complex c /\
        (!y. y IN UNIONS c
             ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)
        ==> combinatorial_manifold_with_boundary 2 c /\
            surface_boundary c = {y | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y} /\
            (surface_boundary c = {} ==> combinatorial_manifold 2 c)) /\
     (!s:real^3->bool.
        pl_solid_torus s
        ==> ?(f:real^(2,2)finite_sum->real^3) h.
              pl_homeomorphism (pl_torus_model,frontier s) (f,h)) /\
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     c IN components (moi_s3i2_lsurf s2 i)
     ==> ?cc. (c SUBSET moi_s32_lvl g dd i /\
               FINITE cc /\ combinatorial_manifold_with_boundary 2 cc /\
               UNIONS cc = c /\ connected c /\ ~(c = {}) /\
               surface_boundary cc = c INTER moi_s32_evens s2 /\
               c INTER moi_s32_evens s2 SUBSET
                 frontier (s2 (&2 * i)) UNION frontier (s2 (&2 * i + &2))) /\
              moi_s32_hist s2 i cc c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3I2_MEMBER) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `cc:(real^3->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3S6_HIST_TORUS THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`moi_s3i2_lsurf s2 i`; `c:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s3i2_lsurf] THEN SET_TAC[]);;

let INITIAL_3 = prove
 (MOI_S32_INITIAL_3,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (LABEL_TAC "tb" o CONJUNCT2)) THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                       `dd:int->real^3->bool`; `s2:int->real^3->bool`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `{c:real^3->bool | ?i. c IN components (moi_s3i2_lsurf s2 i)}` THEN
  SUBGOAL_THEN
   `moi_s32_set g s2 {c:real^3->bool | ?i. c IN components (moi_s3i2_lsurf s2 i)} =
    moi_s32_evens s2 UNION
    (UNIONS {frontier (s2 (&2 * i + &1)) | i IN (:int)} DIFF
     UNIONS {interior (s2 (&2 * i)) | i IN (:int)}) UNION {g (vec 0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_set; MOI_S3I2_FAM_UNIONS] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3I2_L_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s32_state3; NOT_IN_EMPTY; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3I2_FAM_DISJOINT THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                          `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `c:real^3->bool` THEN DISCH_THEN(X_CHOOSE_TAC `i:int`) THEN
    EXISTS_TAC `i:int` THEN MATCH_MP_TAC MOI_S3J3_MEMBER THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:int` THEN MATCH_MP_TAC MOI_S3I2_FAM_FINITE THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3I2_M1_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3I2_M1_SEP THEN
    MAP_EVERY EXISTS_TAC [`v:real^3->bool`; `pp:int->real^3`; `dd:int->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;

