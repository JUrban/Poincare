(* ========================================================================= *)
(* pc_geo_param: the local inverse function theorem into a manifold         *)
(* (MFD_LOCAL_PARAM, used by the comparison layer): a smooth map from an     *)
(* open set of real^N with injective differential at v is a smooth           *)
(* parametrization near v.                                                   *)
(* ========================================================================= *)

needs "src/pc_geo_defs.ml";;
(* MFD_PARAM_CHART_INV, MFD_PARAM_PRECOMPOSE, MFD_PARAM_EQ *)
needs "src/pc_smt_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* A smooth map from an open set of real^N read in one chart. *)

let GEOP_CHART_REP = prove
 (`!top atlas (Fm:real^N->A) U (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ open U /\
        continuous_map (subtopology euclidean U,top) Fm /\
        mfd_smooth_map (open_set_atlas (:real^N)) atlas U Fm /\ c IN atlas
        ==> open {u | u IN U /\ Fm u IN FST c} /\
            smooth_map_on {u | u IN U /\ Fm u IN FST c} (\u. SND c (Fm u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^N),(\y:real^N. y)) IN open_set_atlas (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^N),(\y:real^N. y))`; `c:(A->bool)#(A->real^N)`;
                 `U:real^N->bool`; `Fm:real^N->A`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`((:real^N),(\y:real^N. y))`; `c:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((A->bool)#(A->real^N))->bool)
                      W (f:real^N->A)`) (concl th))) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID; IN_UNIV]);;

(* The local inverse function theorem into M. *)

let MFD_LOCAL_PARAM = prove
 (`!top atlas (Fm:real^N->A) U v.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       open U /\ v IN U /\ continuous_map (subtopology euclidean U,top) Fm /\
       mfd_smooth_map (open_set_atlas (:real^N)) atlas U Fm /\
       (!h. mfd_differential (open_set_atlas (:real^N)) atlas Fm v h = vec 0
            ==> h = vec 0)
       ==> ?V. open V /\ v IN V /\ V SUBSET U /\ mfd_param top atlas V Fm`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Fm:real^N->A) v IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean U,top) (Fm:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(Fm:real^N->A) v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((Fm:real^N->A) v)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Fm:real^N->A`; `U:real^N->bool`; `c0:(A->bool)#(A->real^N)`]
    GEOP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S0 = {u | u IN U /\ (Fm:real^N->A) u IN FST (c0:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `phi = \u. SND (c0:(A->bool)#(A->real^N)) ((Fm:real^N->A) u)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN S0` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the differential is the derivative of phi and is invertible *)
  SUBGOAL_THEN
   `!h. frechet_derivative (phi:real^N->real^N) (at v) h = vec 0 ==> h = vec 0`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `!h. mfd_differential (open_set_atlas (:real^N))
            (atlas:((A->bool)#(A->real^N))->bool) (Fm:real^N->A) v h = vec 0
          ==> h = vec 0` THEN
    ASM_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN EXPAND_TAC "phi" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (phi:real^N->real^N) (at v))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^N->real^N`; `S0:real^N->bool`; `v:real^N`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DET_MATRIX_EQ_0_LEFT] THEN
    MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `psi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    check (fun th -> can (term_match []
      `diffeomorphism_on (t:real^N->bool) u (phi:real^N->real^N) psi`) (concl th))) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S0" THEN SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!w. w IN t
        ==> (Fm:real^N->A) w IN FST (c0:(A->bool)#(A->real^N)) /\
            chart_inv c0 ((phi:real^N->real^N) w) = Fm w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN S0` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S0" THEN EXPAND_TAC "phi" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
      `IMAGE (phi:real^N->real^N) t = u`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `chart_inv (c0:(A->bool)#(A->real^N)) o (phi:real^N->real^N)` THEN
  ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`;
                        `u:real^N->bool`; `psi:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
    MFD_PARAM_CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR]);;

