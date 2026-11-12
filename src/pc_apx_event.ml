(* ========================================================================= *)
(* pc_apx_event: the topology of one surgery event (MT Prop 15.3, separating *)
(* case) down to the Appendix statements, and the manifold bookkeeping it    *)
(* needs (restricted atlases, transport of listed pieces, capping by two    *)
(* balls).                                                                   *)
(* ========================================================================= *)

needs "src/pc_apx_defs.ml";;
needs "src/pc_smt_radial.ml";;
needs "src/pc_mfd_cut.ml";;
needs "src/pc_mfd_diff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Restricted atlases.  Smoothness of maps and parametrizations              *)
(* does not see the restriction to open sets containing them; consequences:  *)
(* E7 (diffeomorphisms of open subsets are diffeomorphisms of the open       *)
(* submanifolds), E8 (parametrizations transfer and restrict), E6 (twisted   *)
(* charts of open subsets), E9 (round components are space forms).          *)
(* ------------------------------------------------------------------------- *)

let APX_SMOOTH_MAP_RESTRICT = prove
 (`!top atlas top' atlas' W0 W0' S (f:A->B).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W0 /\ S SUBSET W0 /\ IMAGE f S SUBSET W0'
        ==> (mfd_smooth_map (restrict_atlas atlas W0) (restrict_atlas atlas' W0') S f <=>
             mfd_smooth_map atlas atlas' S f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM; IN_RESTRICT_ATLAS; FST; SND] THEN
  SUBGOAL_THEN
   `!U (phi:A->real^N) V (psi:B->real^M).
        (U,phi) IN atlas
        ==> (smooth_map_on
               (IMAGE phi {x | x IN (U INTER W0) INTER S /\ f x IN V INTER W0'})
               (psi o f o chart_inv (U INTER W0,phi)) <=>
             smooth_map_on (IMAGE phi {x | x IN U INTER S /\ f x IN V})
               (psi o f o chart_inv (U,phi)))`
  (LABEL_TAC "eqv") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `IMAGE (phi:A->real^N)
        {x | x IN (U INTER W0) INTER S /\ (f:A->B) x IN V INTER W0'} =
      IMAGE phi {x | x IN U INTER S /\ f x IN V}`
    SUBST1_TAC THENL [AP_TERM_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `W0:A->bool`; `x:A`]
                  MFDR_CHART_INV_RESTRICT) THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_THEN(LABEL_TAC "hyp") THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:B->bool`; `psi:B->real^M`] THEN
    STRIP_TAC THEN
    USE_THEN "eqv" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`; `V:B->bool`;
                                    `psi:B->real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    USE_THEN "hyp" MATCH_MP_TAC THEN
    CONJ_TAC THENL [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:B->bool`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U0:A->bool`; `phi:A->real^N`; `V0:B->bool`; `psi:B->real^M`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `V:B->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "eqv" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`; `V:B->bool`;
                                    `psi:B->real^M`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Diffeomorphisms of open subsets W, W' do not see restrictions of the two  *)
(* manifolds to open sets W0, W0' containing them.                           *)

let APX_MFD_DIFFEO_RESTRICT = prove
 (`!top atlas W0 top' atlas' W0' W W' (f:A->B) g.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W0 /\ open_in top' W0' /\ W SUBSET W0 /\ W' SUBSET W0'
        ==> (mfd_diffeo (subtopology top W0) (restrict_atlas atlas W0) W
                        (subtopology top' W0') (restrict_atlas atlas' W0') W' f g <=>
             mfd_diffeo top atlas W top' atlas' W' f g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `W0 INTER W:A->bool = W /\ W0' INTER W':B->bool = W'`
   (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `open_in top (W:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `open_in top' (W':B->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `homeomorphic_maps (subtopology top W,subtopology top' W') (f:A->B,g)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (f:A->B) W SUBSET W0' /\ IMAGE (g:B->A) W' SUBSET W0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `homeomorphic_maps (subtopology top W,subtopology top' W') (f:A->B,g)` THEN
    REWRITE_TAC[homeomorphic_maps] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE)
      (MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o CONJUNCT1)) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (W:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (W':B->bool)`)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC APX_SMOOTH_MAP_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`];
    MATCH_MP_TAC APX_SMOOTH_MAP_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `top:A topology`]] THEN
  ASM_REWRITE_TAC[]);;

(* Only the target restricted (W0' an open set of the target manifold). *)

let APX_MFD_DIFFEO_RESTRICT_TARGET = prove
 (`!top atlas W top' atlas' W0' W' (f:A->B) g.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top' W0' /\ W' SUBSET W0'
        ==> (mfd_diffeo top atlas W (subtopology top' W0')
                        (restrict_atlas atlas' W0') W' f g <=>
             mfd_diffeo top atlas W top' atlas' W' f g)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `open_in top (W:A->bool)` THENL
   [ALL_TAC; ASM_REWRITE_TAC[mfd_diffeo]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^M))->bool`; `W0':B->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `g:B->A`]
                APX_MFD_DIFFEO_RESTRICT) THEN
  ASM_SIMP_TAC[OPEN_IN_TOPSPACE; OPEN_IN_SUBSET; SUBTOPOLOGY_TOPSPACE;
               RESTRICT_ATLAS_TOPSPACE]);;

(* E7. *)

let APX_DIFFEO_SUBSPACE = prove
 (`!w:A->bool w':B->bool. APX_DIFFEO_SUBSPACE_STATEMENT w w'`,
  REWRITE_TAC[APX_DIFFEO_SUBSPACE_STATEMENT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_diffeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:A->B`; `f':B->A`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mfd_diffeo]) THEN
  SUBGOAL_THEN `topspace (subtopology top W) = W:A->bool /\
                topspace (subtopology top' W') = W':B->bool`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (W:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (W':B->bool)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `W':B->bool`;
                 `W:A->bool`; `W':B->bool`; `f:A->B`; `f':B->A`]
                APX_MFD_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* E8. *)

let APX_PARAM_TRANSFER = prove
 (`!w:A->bool w':B->bool. APX_PARAM_TRANSFER_STATEMENT w w'`,
  REWRITE_TAC[APX_PARAM_TRANSFER_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `W:A->bool`; `W':B->bool`; `f':B->A`] THEN
  ASM_REWRITE_TAC[]);;

let APX_PARAM_RESTRICT_EQ = prove
 (`!top atlas W s (e:real^N->A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\ IMAGE e s SUBSET W
        ==> (mfd_param (subtopology top W) (restrict_atlas atlas W) s e <=>
             mfd_param top atlas s e)`,
  REWRITE_TAC[mfd_param] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC APX_MFD_DIFFEO_RESTRICT_TARGET THEN
  ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS]);;

let APX_PARAM_FROM_RESTRICT = prove
 (`!top atlas W s (e:real^N->A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\
        mfd_param (subtopology top W) (restrict_atlas atlas W) s e
        ==> mfd_param top atlas s e /\ IMAGE e s SUBSET W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (e:real^N->A) s SUBSET W` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W`;
                   `s:real^N->bool`; `e:real^N->A`; `s:real^N->bool`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `s:real^N->bool`; `e:real^N->A`]
                APX_PARAM_RESTRICT_EQ) THEN
  ASM_MESON_TAC[]);;

let APX_PARAM_RESTRICT = prove
 (`!w:A->bool. APX_PARAM_RESTRICT_STATEMENT w`,
  REWRITE_TAC[APX_PARAM_RESTRICT_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC APX_PARAM_RESTRICT_EQ THEN ASM_REWRITE_TAC[]);;

(* E6. *)

let APX_TWISTED_MONO = prove
 (`!w:A->bool. APX_TWISTED_MONO_STATEMENT w`,
  REWRITE_TAC[APX_TWISTED_MONO_STATEMENT; rfs_has_twisted; rfs_twisted_chart] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `p:real^3->A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `ball(y:real^3,r)`; `p:real^3->A`]
                APX_PARAM_FROM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W':A->bool`; `ball(y:real^3,r)`; `p:real^3->A`]
                APX_PARAM_RESTRICT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* Components of a smooth manifold are open (from                          *)
(* GEO_MANIFOLD_LOCALLY_PATH_CONNECTED of pc_mfd_diff and the library).     *)

let APX_COMPONENT_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) U.
        smooth_manifold_atlas top atlas /\ U IN connected_components_of top
        ==> open_in top U`,
  MESON_TAC[GEO_MANIFOLD_LOCALLY_PATH_CONNECTED;
            LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE;
            OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE]);;

(* E9. *)

let APX_ROUND_SPACE_FORM = prove
 (`!w:A->bool. APX_ROUND_SPACE_FORM_STATEMENT w`,
  REWRITE_TAC[APX_ROUND_SPACE_FORM_STATEMENT; rfs_round_component;
              rfs_space_form] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`] APX_COMPONENT_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  EXISTS_TAC `restrict_metric atlas U (g1:A->real^3^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `g1:A->real^3^3`; `x:A`]
                MFDR_SECTIONAL_SET_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC
    `mfd_sectional (restrict_atlas atlas U) (restrict_metric atlas U g1)
                   (x:A) (u:real^3) v`) THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* E5. Transport of twisted charts, space forms and S^2-bundles along a     *)
(* diffeomorphism fd (inverse gd) of the whole manifolds.                  *)

let APX_TWISTED_CHART_DIFFEO = prove
 (`!top atlas top' atlas' (fd:A->B) gd p.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') fd gd /\
        rfs_twisted_chart top atlas p
        ==> rfs_twisted_chart top' atlas' (fd o p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_twisted_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "loc"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN
   `!y. y IN annulus (&1 / &4) (&4) ==> (p:real^3->A) y IN topspace top`
  (LABEL_TAC "top") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(y:real^3,r)`; `p:real^3->A`; `ball(y:real^3,r)`]
                  MFD_PARAM_IMAGE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(fd:A->B) ((p:real^3->A) y) = fd (p z) <=> p y = p z`
    SUBST1_TAC THENL
     [EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      DISCH_THEN(MP_TAC o AP_TERM `gd:B->A`) THEN
      USE_THEN "top" (MP_TAC o SPEC `y:real^3`) THEN
      USE_THEN "top" (MP_TAC o SPEC `z:real^3`) THEN
      ASM_SIMP_TAC[];
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `topspace top:A->bool`; `topspace top':B->bool`;
                          `gd:B->A`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `ball(y:real^3,r)`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let APX_SPACE_FORM_DIFFEO = prove
 (`!top atlas top' atlas' (fd:A->B) gd.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') fd gd /\
        rfs_space_form top atlas
        ==> rfs_space_form top' atlas'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_space_form] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `g:A->real^3^3` STRIP_ASSUME_TAC))))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN
  EXISTS_TAC `mfd_pullback_metric atlas' atlas (gd:B->A) (g:A->real^3^3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `gd:B->A`; `fd:A->B`; `g:A->real^3^3`]
                        RIEMANNIAN_METRIC_PULLBACK) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `mfd_pullback_metric atlas' atlas (gd:B->A) (g:A->real^3^3)`;
                         `g:A->real^3^3`; `gd:B->A`; `fd:A->B`; `&1`]
                        MFD_ISOMETRY_SECTIONAL_CONST) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[]]);;

let APX_S2_BUNDLE_DIFFEO = prove
 (`!top atlas top' atlas' (fd:A->B) gd.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
        mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') fd gd /\
        rfs_s2_bundle top atlas
        ==> rfs_s2_bundle top' atlas'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_s2_bundle; mfd_neck_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:real^3->A`; `E:real^3->A`; `f:real^3->real^3`;
                       `f':real^3->real^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MAP_EVERY EXISTS_TAC [`(fd:A->B) o (e:real^3->A)`; `(fd:A->B) o (E:real^3->A)`;
                        `f:real^3->real^3`; `f':real^3->real^3`] THEN
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top /\
    IMAGE (E:real^3->A) (annulus (&1) (&4)) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `topspace top:A->bool`; `topspace top':B->bool`;
                          `gd:B->A`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `topspace top:A->bool`; `topspace top':B->bool`;
                          `gd:B->A`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1)) =
                 IMAGE (E:real^3->A) (annulus (&1) (&4))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `IMAGE (fd:A->B) (topspace top) = topspace top'` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!x. x IN topspace top ==> (gd:B->A) ((fd:A->B) x) = x` THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET topspace top` THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` THEN
    SET_TAC[]]);;

let APX_LISTED_DIFFEO = prove
 (`!w:A->bool w':B->bool. APX_LISTED_DIFFEO_STATEMENT w w'`,
  REWRITE_TAC[APX_LISTED_DIFFEO_STATEMENT] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[mfd_diffeomorphic]) THEN
  DISCH_THEN(X_CHOOSE_THEN `fd:A->B` (X_CHOOSE_TAC `gd:B->A`)) THEN
  SUBGOAL_THEN
   `rfs_has_twisted top (atlas:((A->bool)#(A->real^3))->bool)
    ==> rfs_has_twisted top' (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[rfs_has_twisted] THEN DISCH_THEN(X_CHOOSE_TAC `p:real^3->A`) THEN
    EXISTS_TAC `(fd:A->B) o (p:real^3->A)` THEN
    MATCH_MP_TAC APX_TWISTED_CHART_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `gd:B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_listed_piece] THEN
  MATCH_MP_TAC(TAUT `(a ==> a') /\ (b ==> b') /\ (c ==> c') /\ (d ==> d')
                     ==> a \/ b \/ c \/ d ==> a' \/ b' \/ c' \/ d'`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                         `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                         `subtopology euclidean (sphere(vec 0:real^4,&1))`;
                         `sphere3_atlas`] MFD_DIFFEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[SPHERE3_ATLAS] THEN
    MATCH_MP_TAC MFD_DIFFEOMORPHIC_SYM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC APX_SPACE_FORM_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `fd:A->B`; `gd:B->A`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC APX_S2_BUNDLE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `fd:A->B`; `gd:B->A`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* E4, capping a product by two balls gives S^3 (from M2).                   *)
(* The ball chart b1 of M2 is c on ball(0,a), E on annulus(1,L) and b2 o hh  *)
(* on annulus(b,2L) (hh x = (L / |x|) f(x / |x|), an inversion followed by   *)
(* a scaling and the radial extension of f), rescaled by L.                  *)
(* ------------------------------------------------------------------------- *)

let APX_FLIP_EQ = prove
 (`!(f:real^N->real^N) L x.
        &0 < L /\ ~(x = vec 0)
        ==> (radial_ext f o (\x. L % x) o (\x. inv(norm x pow 2) % x)) x =
            (L / norm x) % f(inv(norm x) % x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM; radial_ext] THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(L % inv(norm x pow 2) % (x:real^N)) = L / norm x`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`] THEN
    UNDISCH_TAC `&0 < norm(x:real^N)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < L` THEN UNDISCH_TAC `&0 < norm(x:real^N)` THEN
  CONV_TAC REAL_FIELD);;

let APX_FLIP_NORM = prove
 (`!(f:real^N->real^N) f' L x.
        sphere_diffeo f f' /\ &0 < L /\ ~(x = vec 0)
        ==> norm((L / norm x) % f(inv(norm x) % x)) = L / norm x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((f:real^N->real^N)(inv(norm x) % x)) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `sphere_diffeo (f:real^N->real^N) f'` THEN
    REWRITE_TAC[sphere_diffeo] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(norm x) % (x:real^N)` o last o CONJUNCTS) THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`]);;

let APX_FLIP_DIFFEO = prove
 (`!(f:real^N->real^N) f' L b.
        sphere_diffeo f f' /\ &0 < L /\ &0 < b /\ b <= &2 * L
        ==> diffeomorphism_on (annulus b (&2 * L))
              (annulus (L * inv(&2 * L)) (L * inv b))
              (radial_ext f o (\x. L % x) o (\x. inv(norm x pow 2) % x))
              (((\x. inv(norm x pow 2) % x) o (\x. inv L % x)) o radial_ext f')`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (L * inv(&2 * L)) (L * inv b):real^N->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (inv(&2 * L)) (inv b):real^N->bool` THEN
    ASM_SIMP_TAC[SMT_DIFFEO_INVERSION_ANNULUS; SMT_DIFFEO_SCALING_ANNULUS];
    MATCH_MP_TAC SMT_DIFFEO_RADIAL_EXT_ANNULUS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                 REAL_ARITH `&0 < L ==> &0 <= &2 * L`]]);;

let APX_GLUE_CAPPED = prove
 (`!w:A->bool. SMT_TWISTED_SPHERE_STATEMENT w ==> APX_GLUE_CAPPED_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[SMT_TWISTED_SPHERE_STATEMENT; APX_GLUE_CAPPED_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "M2") THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`;
    `E:real^3->A`; `L:real`; `b2:real^3->A`; `f:real^3->real^3`;
    `f':real^3->real^3`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `a = min (&3 / &2) L` THEN
  ABBREV_TAC `b = (&3 * L + &1) / &4` THEN
  SUBGOAL_THEN
   `&1 < a /\ a <= &3 / &2 /\ a <= L /\ &1 <= b /\ L / &2 <= b /\
    b < L /\ &0 < L /\ &0 < b /\ b <= &2 * L /\ L * inv b <= &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN annulus (&1) (&3 / &2) ==> (E:real^3->A) x = c x`
  (LABEL_TAC "Ec") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN annulus (L / &2) L
               ==> (E:real^3->A) x =
                   (b2:real^3->A)((L / norm x) % (f:real^3->real^3)(inv(norm x) % x))`
  (LABEL_TAC "Eb") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `hh = radial_ext (f:real^3->real^3) o (\x. L % x) o
                   (\x. inv(norm x pow 2) % x)` THEN
  SUBGOAL_THEN
   `!x:real^3. ~(x = vec 0)
               ==> (hh:real^3->real^3) x = (L / norm x) % f(inv(norm x) % x) /\
                   norm(hh x) = L / norm x`
  (LABEL_TAC "hh") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `L:real`; `x:real^3`] APX_FLIP_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "hh" THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_FLIP_NORM THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = \x:real^3. if norm x < a then (c:real^3->A) x
                             else if norm x < L then (E:real^3->A) x
                             else (b2:real^3->A) ((hh:real^3->real^3) x)` THEN
  SUBGOAL_THEN
   `!x:real^3. norm x < L
               ==> (norm x <= &1 ==> (C:real^3->A) x = c x) /\
                   (&1 < norm x ==> C x = E x)`
  (LABEL_TAC "C1") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `norm(x:real^3) < a` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "Ec" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3. b < norm x /\ norm x < &2 * L
               ==> (C:real^3->A) x = b2((hh:real^3->real^3) x)`
  (LABEL_TAC "C2") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "hh" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `norm(x:real^3) < a` THEN ASM_REWRITE_TAC[] THENL
     [TRANS_TAC EQ_TRANS `(E:real^3->A) x` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "Ec" MATCH_MP_TAC;
        USE_THEN "Eb" MATCH_MP_TAC] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "Eb" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. norm(x:real^3) <= &1 /\ &1 < norm(z:real^3) /\ norm z < L
          ==> ~((c:real^3->A) x = E z)`
  (LABEL_TAC "D1") THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (c:real^3->A) (cball(vec 0,&1)))
                          (IMAGE (E:real^3->A) (annulus (&1) L))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. norm(x:real^3) <= &1 /\ norm(z:real^3) <= &1
          ==> ~((c:real^3->A) x = b2 z)`
  (LABEL_TAC "D2") THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (c:real^3->A) (cball(vec 0,&1)))
                          (IMAGE (b2:real^3->A) (cball(vec 0,&1)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_CBALL_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. &1 < norm(x:real^3) /\ norm x < L /\ norm(z:real^3) <= &1
          ==> ~((E:real^3->A) x = b2 z)`
  (LABEL_TAC "D3") THENL
   [UNDISCH_TAC `DISJOINT (IMAGE (E:real^3->A) (annulus (&1) L))
                          (IMAGE (b2:real^3->A) (cball(vec 0,&1)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY;
                IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x z. norm(x:real^3) < L /\ norm(z:real^3) <= &1
          ==> ~((C:real^3->A) x = b2 z)`
  (LABEL_TAC "G2") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `norm(x:real^3) <= &1` THENL
     [DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "D3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(vec 0:real^3,&2 * L)) (C:real^3->A)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_param top atlas (ball(vec 0:real^3,a)) (c:real^3->A)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
      REWRITE_TAC[GSYM mfd_ball_chart; OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param top atlas (annulus b (&2 * L)) ((b2:real^3->A) o (hh:real^3->real^3))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `ball(vec 0:real^3,&2)`; `b2:real^3->A`;
                     `annulus b (&2 * L):real^3->bool`;
                     `annulus (L * inv(&2 * L)) (L * inv b):real^3->bool`;
                     `hh:real^3->real^3`;
                     `((\x:real^3. inv(norm x pow 2) % x) o (\x. inv L % x)) o
                      radial_ext (f':real^3->real^3)`]
                    MFD_PARAM_PRECOMPOSE) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[GSYM mfd_ball_chart] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "hh" THEN MATCH_MP_TAC APX_FLIP_DIFFEO THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param top atlas (ball(vec 0:real^3,a) UNION annulus (&1) L)
                (C:real^3->A)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_UNION THEN
      MAP_EVERY EXISTS_TAC [`c:real^3->A`; `E:real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_BALL_0] THEN EXPAND_TAC "C" THEN SIMP_TAC[];
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
        STRIP_TAC THEN USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_IMAGE] THEN
          X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
          REWRITE_TAC[IN_IMAGE; IN_INTER; IN_BALL_0; annulus; IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `&1 < norm(x:real^3)` ASSUME_TAC THENL
           [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
            USE_THEN "D1" (MP_TAC o SPECL [`x:real^3`; `z:real^3`]) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
            ALL_TAC] THEN
          EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL
           [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
          REWRITE_TAC[IN_INTER; IN_IMAGE; IN_BALL_0; annulus; IN_ELIM_THM] THEN
          X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THEN
          EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THENL
           [EXPAND_TAC "C" THEN ASM_REWRITE_TAC[];
            USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
            ASM_REWRITE_TAC[]]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_param top atlas
        ((ball(vec 0:real^3,a) UNION annulus (&1) L) UNION annulus b (&2 * L))
        (C:real^3->A)`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_UNION THEN
      MAP_EVERY EXISTS_TAC [`C:real^3->A`; `(b2:real^3->A) o (hh:real^3->real^3)`] THEN
      ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        USE_THEN "C2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `x:real^3` THEN
        REWRITE_TAC[IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `norm(x:real^3) < L` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE; o_THM; IN_INTER; IN_UNION; IN_BALL_0; annulus;
                    IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        ASM_CASES_TAC `norm(z:real^3) < L` THENL
         [EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [CONV_TAC SYM_CONV THEN USE_THEN "C2" MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[];
            ASM_REAL_ARITH_TAC];
          USE_THEN "G2" (MP_TAC o SPECL [`x:real^3`; `(hh:real^3->real^3) z`]) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
             [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            USE_THEN "hh" (MP_TAC o SPEC `z:real^3`) THEN
            ANTS_TAC THENL
             [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
            ASM_SIMP_TAC[REAL_LE_LDIV_EQ; NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
            ASM_REWRITE_TAC[]]];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `x:real^3` THEN
          ASM_REWRITE_TAC[] THEN USE_THEN "C2" MATCH_MP_TAC THEN
          UNDISCH_TAC `(x:real^3) IN annulus b (&2 * L)` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM]]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "M2" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `(C:real^3->A) o (\x. L % x)`; `b2:real^3->A`; `f:real^3->real^3`;
    `f':real^3->real^3`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `!x:real^3. L % inv L % x = x /\ norm(inv L % x) = norm x / L /\
               norm(L % x) = L * norm x`
  (LABEL_TAC "sc") THENL
   [GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 REAL_ARITH `&0 < L ==> abs L = L`] THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,&2 * L)`; `C:real^3->A`;
                   `ball(vec 0:real^3,&2)`; `ball(vec 0:real^3,L * &2)`;
                   `\x:real^3. L % x`; `\x:real^3. inv L % x`]
                  MFD_PARAM_PRECOMPOSE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_DIFFEO_SCALING_BALL] THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNION_SUBSET; SUBSET_UNION] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0] THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        REWRITE_TAC[IN_IMAGE; o_THM; IN_CBALL_0] THEN
        EXISTS_TAC `inv L % x:real^3` THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
          ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; DISCH_THEN(MATCH_MP_TAC o CONJUNCT1)] THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
        REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        REWRITE_TAC[IN_IMAGE; o_THM; IN_CBALL_0] THEN
        EXISTS_TAC `inv L % x:real^3` THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
         [CONV_TAC SYM_CONV THEN USE_THEN "C1" (MP_TAC o SPEC `x:real^3`) THEN
          ANTS_TAC THENL
           [ASM_REAL_ARITH_TAC; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL_0; o_THM] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(L % x:real^3) < L` THENL
     [USE_THEN "C1" (MP_TAC o SPEC `L % x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `norm(L % x:real^3) <= &1` THENL
       [DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `~(L % x:real^3 = vec 0)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "C2" (MP_TAC o SPEC `L % x:real^3`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `~(norm(L % x:real^3) < L)` THEN
        USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * &1` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC]];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_CBALL_0] THEN
      USE_THEN "hh" (MP_TAC o SPEC `L % x:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      UNDISCH_TAC `~(norm(L % x:real^3) < L)` THEN
      USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < L * norm(x:real^3)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SET_RULE
     `DISJOINT (IMAGE (f:real^3->A) s) (IMAGE (g:real^3->A) t) <=>
      !x y. x IN s /\ y IN t ==> ~(f x = g y)`] THEN
    REWRITE_TAC[IN_BALL_0; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "G2" MATCH_MP_TAC THEN
    USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `L * &1` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `&2` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(x:real^3) /\ ~(L % x:real^3 = vec 0)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN
      USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "C2" (MP_TAC o SPEC `L % x:real^3`) THEN
    ANTS_TAC THENL
     [USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `L * &1` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `L * &2` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    USE_THEN "hh" (MP_TAC o SPEC `L % x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    USE_THEN "sc" (fun th -> REWRITE_TAC[th]) THEN
    BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
                     AP_THM_TAC THEN AP_TERM_TAC] THEN
    UNDISCH_TAC `&0 < norm(x:real^3)` THEN UNDISCH_TAC `&0 < L` THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* E3, the point-set structure of a discarded component of Z.                *)
(* General facts first: a nonempty connected clopen set is a component;     *)
(* removing pairwise separated cores K i (each inside an open Q i with      *)
(* connected nonempty collar Q i DIFF K i) keeps a set connected; the unit  *)
(* sphere lies in the closure of annulus(1,2); images of connected sets     *)
(* under parametrizations are connected; the identity cut-and-cap data.     *)
(* ------------------------------------------------------------------------- *)

let APX_CLOPEN_COMPONENT = prove
 (`!top c:A->bool.
        connected_in top c /\ open_in top c /\ closed_in top c /\ ~(c = {})
        ==> c IN connected_components_of top`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `c = connected_component_of top (x:A)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `connected_component_of top (x:A)`;
                     `c:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
      ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN
      MATCH_MP_TAC(SET_RULE
       `(x:A) IN s /\ x IN c ==> (s SUBSET c \/ DISJOINT s c ==> s SUBSET c)`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
      ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL]];
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF]]);;

let APX_SPHERE_CLOSURE_ANNULUS = prove
 (`sphere(vec 0:real^N,&1) SUBSET closure(annulus (&1) (&2))`,
  REWRITE_TAC[SUBSET; IN_SPHERE_0; CLOSURE_APPROACHABLE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  EXISTS_TAC `(&1 + min d (&1) / &2) % u:real^N` THEN
  ASM_REWRITE_TAC[NORM_MUL; dist;
                  VECTOR_ARITH `(&1 + b) % u - u:real^N = b % u`] THEN
  ASM_REAL_ARITH_TAC);;

let APX_PARAM_CONNECTED_IMAGE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s t (e:real^N->A).
        mfd_param top atlas s e /\ connected t /\ t SUBSET s
        ==> connected_in top (IMAGE e t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN]);;

let APX_CONNECTED_ANNULUS3 = prove
 (`!r1 r2. connected(annulus r1 r2:real^3->bool)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`]
                (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus]);;

let APX_CONNECTED_REMOVE = prove
 (`!top U P (ix:num->bool) (Q:num->A->bool) (kc:num->A->bool).
        connected_in top U /\ open_in top P /\
        P = U DIFF UNIONS {kc i | i IN ix} /\
        (!i. i IN ix
             ==> open_in top (Q i) /\ Q i SUBSET U /\ kc i SUBSET Q i /\
                 connected_in top (Q i DIFF kc i) /\ ~(Q i DIFF kc i = {})) /\
        (!i j. i IN ix /\ j IN ix /\ ~(i = j) ==> DISJOINT (Q i) (Q j))
        ==> connected_in top P`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "U") (CONJUNCTS_THEN2 (LABEL_TAC "Po")
    (CONJUNCTS_THEN2 (LABEL_TAC "P") (CONJUNCTS_THEN2 (LABEL_TAC "Q")
      (LABEL_TAC "D"))))) THEN
  SUBGOAL_THEN `!j x. j IN ix /\ (x:A) IN P ==> x IN U /\ ~(x IN (kc:num->A->bool) j)`
  (LABEL_TAC "PK") THENL
   [REPEAT GEN_TAC THEN USE_THEN "P" SUBST1_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN ix ==> (Q:num->A->bool) i DIFF kc i SUBSET P`
  (LABEL_TAC "QP") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "Q" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "P" SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:A->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    ASM_CASES_TAC `j:num = i` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "D" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    USE_THEN "Q" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IN] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:A->bool` (X_CHOOSE_THEN `e2:A->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i. i IN ix ==> (Q:num->A->bool) i DIFF kc i SUBSET e1 \/
                   Q i DIFF kc i SUBSET e2`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "Q" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "QP" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `connected_in top ((Q:num->A->bool) i DIFF kc i)` THEN
    REWRITE_TAC[CONNECTED_IN] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:A->bool`; `e2:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "U" (MP_TAC o REWRITE_RULE[CONNECTED_IN]) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`(e1 INTER P) UNION
     UNIONS {(Q:num->A->bool) i | i | i IN ix /\ Q i DIFF kc i SUBSET e1}`;
    `(e2 INTER P) UNION
     UNIONS {(Q:num->A->bool) i | i | i IN ix /\ Q i DIFF kc i SUBSET e2}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "Q" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "Q" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(x:A) IN P` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?i. i IN ix /\ (x:A) IN (kc:num->A->bool) i` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:A) IN P)` THEN USE_THEN "P" SUBST1_TAC THEN
      REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "Q" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "side" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THENL
     [DISJ1_TAC THEN DISJ2_TAC; DISJ2_TAC THEN DISJ2_TAC] THEN
    EXISTS_TAC `(Q:num->A->bool) i` THEN
    (CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]);
    REWRITE_TAC[SET_RULE
     `(a UNION b) INTER (c UNION d) INTER (u:A->bool) = {} <=>
      a INTER c INTER u = {} /\ a INTER d INTER u = {} /\
      b INTER c INTER u = {} /\ b INTER d INTER u = {}`] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      USE_THEN "PK" (MP_TAC o SPECL [`i:num`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      USE_THEN "PK" (MP_TAC o SPECL [`i:num`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `t1:A->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC))
       (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `t2:A->bool` (CONJUNCTS_THEN2
             (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC))
          ASSUME_TAC)) THEN
      ASM_CASES_TAC `j:num = i` THENL
       [USE_THEN "Q" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        USE_THEN "QP" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        UNDISCH_TAC `j:num = i` THEN DISCH_THEN SUBST_ALL_TAC THEN
        ASM SET_TAC[];
        USE_THEN "D" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN ASM SET_TAC[]]];
    USE_THEN "P" (fun th -> MP_TAC th) THEN ASM SET_TAC[];
    USE_THEN "P" (fun th -> MP_TAC th) THEN ASM SET_TAC[]]);;

(* The cut-and-cap data with identity maps: X minus the cut spheres and Z   *)
(* minus the cores are the same open subspace; the collar identities.       *)

let APX_CUTCAP_ID = prove
 (`!topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm.
        mfd_cut_cap topX (atlasX:((A->bool)#(A->real^3))->bool) topZ atlasZ
                    J e cp cm (\x. x) (\x. x)
        ==> topspace topX DIFF mfd_cut_spheres J e =
            topspace topZ DIFF mfd_cut_cores J cp cm /\
            subtopology topX (topspace topX DIFF mfd_cut_spheres J e) =
            subtopology topZ (topspace topZ DIFF mfd_cut_cores J cp cm) /\
            open_in topX (topspace topX DIFF mfd_cut_spheres J e) /\
            open_in topZ (topspace topZ DIFF mfd_cut_cores J cp cm) /\
            (!i x. i IN J /\ x IN annulus (&1) (&2) ==> e i x = cp i x) /\
            (!i x. i IN J /\ x IN annulus (&1 / &2) (&1)
                   ==> e i x = cm i (inv(norm x pow 2) % x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_cut_cap; mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `topspace:A topology->A->bool` o
    check (is_eq o concl)) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

(* Images of differences under a parametrization (injective on its domain). *)

let APX_PARAM_IMAGE_DIFF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s t u (e:real^N->A).
        mfd_param top atlas s e /\ t SUBSET s /\ u SUBSET s
        ==> IMAGE e t DIFF IMAGE e u = IMAGE e (t DIFF u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN s /\ y IN s /\ (e:real^N->A) x = e y ==> x = y`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `s:real^N->bool`; `e:real^N->A`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* E3. *)

let APX_CUTCAP_PIECE = prove
 (`!w:A->bool. APX_CUTCAP_PIECE_STATEMENT w`,
  REWRITE_TAC[APX_CUTCAP_PIECE_STATEMENT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "cut") (CONJUNCTS_THEN2 (LABEL_TAC "XK")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "caps")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "JU") (LABEL_TAC "P")))))))))))))))) THEN
  USE_THEN "cut" (STRIP_ASSUME_TAC o MATCH_MP APX_CUTCAP_ID) THEN
  USE_THEN "cut" (MP_TAC o REWRITE_RULE[mfd_cut_cap]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
   (CONJUNCTS_THEN2 (LABEL_TAC "dE") (CONJUNCTS_THEN2 (LABEL_TAC "dQ")
    (K ALL_TAC))))) THEN
  USE_THEN "cut" (MP_TAC o MATCH_MP APX_CUTCAP_ID) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "XZ") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
   (CONJUNCTS_THEN2 (LABEL_TAC "Xo") (CONJUNCTS_THEN2 (LABEL_TAC "Zo")
   (CONJUNCTS_THEN2 (LABEL_TAC "colp") (LABEL_TAC "colm")))))) THEN
  SUBGOAL_THEN
   `open_in topZ (U:A->bool) /\ closed_in topZ U /\ connected_in topZ U /\
    U SUBSET topspace topZ /\ ~(U = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`] APX_COMPONENT_OPEN) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF;
      MATCH_MP_TAC CONNECTED_IN_CONNECTED_COMPONENTS_OF;
      MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET;
      MATCH_MP_TAC NONEMPTY_CONNECTED_COMPONENTS_OF THEN
      EXISTS_TAC `topZ:A topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> mfd_param topX atlasX (annulus (&1 / &2) (&2))
                      ((e:num->real^3->A) i) /\
            mfd_param topZ atlasZ (ball(vec 0,&2)) ((cp:num->real^3->A) i) /\
            mfd_param topZ atlasZ (ball(vec 0,&2)) ((cm:num->real^3->A) i)`
  (LABEL_TAC "par") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "charts" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[mfd_neck_chart; mfd_ball_chart]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> open_in topZ (IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2))) /\
            connected_in topZ (IMAGE (cp i) (ball(vec 0,&2))) /\
            connected_in topZ (IMAGE ((cm:num->real^3->A) i) (ball(vec 0,&2))) /\
            connected_in topZ (IMAGE (cp i) (annulus (&1) (&2))) /\
            IMAGE (cp i) (ball(vec 0,&2)) SUBSET topspace topZ /\
            IMAGE (cm i) (ball(vec 0,&2)) SUBSET topspace topZ /\
            IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) SUBSET
            topspace topX /\
            open_in topX (IMAGE (e i) (annulus (&1 / &2) (&2)))`
  (LABEL_TAC "img") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `annulus (&1) (&2) SUBSET ball(vec 0:real^3,&2)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`;
                            `annulus (&1 / &2) (&2):real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`;
                            `annulus (&1 / &2) (&2):real^3->bool`] THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS; SUBSET_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J /\ ~DISJOINT U (IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2)))
        ==> i IN JU`
  (LABEL_TAC "cpU") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topZ:A topology`;
                   `IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2))`;
                   `U:A->bool`] CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "JU" SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN JU
        ==> i IN J /\ IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2)) SUBSET U`
  (LABEL_TAC "JUQ") THENL
   [GEN_TAC THEN USE_THEN "JU" SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "img" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `topZ:A topology` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `(cp:num->real^3->A) i (vec 0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "JU" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!i. i IN J ==> DISJOINT U (IMAGE ((cm:num->real^3->A) i) (ball(vec 0,&2)))`
  (LABEL_TAC "cmU") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "caps" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_CASES_TAC
     `DISJOINT (U:A->bool) (IMAGE ((cm:num->real^3->A) i) (ball(vec 0,&2)))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topZ:A topology`;
                   `IMAGE ((cm:num->real^3->A) i) (ball(vec 0,&2))`;
                   `U:A->bool`] CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(cm:num->real^3->A) i (vec 0) IN IMAGE (cm i) (cball(vec 0,&1)) /\
      cm i (vec 0) IN IMAGE (cm i) (ball(vec 0,&2))`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[CENTRE_IN_BALL; CENTRE_IN_CBALL] THEN REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN J
        ==> DISJOINT (IMAGE ((cp:num->real^3->A) i) (annulus (&1) (&2)))
                     (mfd_cut_cores J cp cm)`
  (LABEL_TAC "collarK") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "par" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_MFD_CUT_CORES;
                IN_IMAGE; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC))) THENL
     [ASM_CASES_TAC `j:num = i` THENL
       [UNDISCH_TAC `j:num = i` THEN DISCH_THEN SUBST_ALL_TAC THEN
        SUBGOAL_THEN `x:real^3 = z` SUBST_ALL_TAC THENL
         [MATCH_MP_TAC(ISPECL [`topZ:A topology`;
                               `atlasZ:((A->bool)#(A->real^3))->bool`;
                               `ball(vec 0:real^3,&2)`; `(cp:num->real^3->A) i`]
                              MFD_PARAM_INJ) THEN
          ASM_REWRITE_TAC[IN_BALL_0] THEN
          REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN ASM_MESON_TAC[];
          ASM_REAL_ARITH_TAC];
        USE_THEN "dQ" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE;
                    IN_BALL_0] THEN
        DISCH_THEN(MP_TAC o SPEC `y:A`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXISTS_TAC `x:real^3`; EXISTS_TAC `z:real^3`] THEN
        CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC];
      USE_THEN "dQ" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE;
                  IN_BALL_0] THEN
      DISCH_THEN(MP_TAC o SPEC `y:A`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^3`; EXISTS_TAC `z:real^3`] THEN
      CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i x. i IN J /\ norm(x:real^3) = &1
          ==> (e:num->real^3->A) i x IN topspace topX /\
              ~(e i x IN topspace topZ)`
  (LABEL_TAC "SZ") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "img" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(e:num->real^3->A) i x IN topspace topX` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE ((e:num->real^3->A) i) (annulus (&1 / &2) (&2)) SUBSET
                   topspace topX` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:num->real^3->A) i x IN mfd_cut_spheres J e` ASSUME_TAC THENL
     [REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "XK" MP_TAC THEN USE_THEN "XZ" MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `P SUBSET topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A) /\
    P SUBSET (U:A->bool)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "P" SUBST1_TAC THEN USE_THEN "XZ" (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i v. i IN J /\ v IN annulus (&1 / &2) (&2) /\ (e:num->real^3->A) i v IN P
          ==> &1 < norm v /\ i IN JU /\ e i v = cp i v`
  (LABEL_TAC "trich") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(norm(v:real^3) = &1)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(e:num->real^3->A) i v IN mfd_cut_spheres J e` MP_TAC THENL
       [REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
        MAP_EVERY EXISTS_TAC [`i:num`; `v:real^3`] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `P SUBSET topspace topX DIFF mfd_cut_spheres J
                       (e:num->real^3->A)` THEN
        UNDISCH_TAC `(e:num->real^3->A) i v IN P` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 < norm(v:real^3)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(v:real^3) < &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "colm" (MP_TAC o SPECL [`i:num`; `v:real^3`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[annulus; IN_ELIM_THM]; DISCH_TAC] THEN
      USE_THEN "cmU" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE;
                  IN_BALL_0] THEN
      DISCH_THEN(MP_TAC o SPEC `(e:num->real^3->A) i v`) THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `inv(norm v pow 2) % v:real^3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN
      SUBGOAL_THEN `&1 / norm(v:real^3) < &2` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_LDIV_EQ; NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div; REAL_MUL_LID]];
      ALL_TAC] THEN
    USE_THEN "colp" (MP_TAC o SPECL [`i:num`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[annulus; IN_ELIM_THM]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "cpU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `(cp:num->real^3->A) i v` THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN JU
        ==> IMAGE ((e:num->real^3->A) i) (annulus (&1) (&2)) =
            IMAGE ((cp:num->real^3->A) i) (annulus (&1) (&2)) /\
            IMAGE (cp i) (annulus (&1) (&2)) SUBSET P`
  (LABEL_TAC "colP") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN s ==> (f:real^3->A) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      REPEAT STRIP_TAC THEN USE_THEN "colp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "P" SUBST1_TAC THEN
      USE_THEN "collarK" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN
       `IMAGE ((cp:num->real^3->A) i) (annulus (&1) (&2)) SUBSET
        IMAGE (cp i) (ball(vec 0,&2))`
      MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_BALL_0] THEN SIMP_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `U = P UNION UNIONS {IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) | i IN JU}`
  (LABEL_TAC "Ub") THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNION] THEN
      ASM_CASES_TAC `(y:A) IN mfd_cut_cores J cp cm` THENL
       [DISJ2_TAC THEN
        UNDISCH_TAC `(y:A) IN mfd_cut_cores J cp cm` THEN
        REWRITE_TAC[IN_MFD_CUT_CORES] THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `z:real^3`
          STRIP_ASSUME_TAC)) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THENL
         [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
          EXISTS_TAC `IMAGE ((cp:num->real^3->A) j) (cball(vec 0,&1))` THEN
          CONJ_TAC THENL
           [EXISTS_TAC `j:num` THEN REWRITE_TAC[] THEN
            USE_THEN "cpU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
            REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY;
                        NOT_FORALL_THM] THEN
            EXISTS_TAC `(cp:num->real^3->A) j z` THEN ASM_REWRITE_TAC[] THEN
            MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN
            ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0]];
          USE_THEN "cmU" (MP_TAC o SPEC `j:num`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `(cm:num->real^3->A) j z`) THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_BALL_0] THEN
          ASM_REAL_ARITH_TAC];
        DISJ1_TAC THEN USE_THEN "P" SUBST1_TAC THEN ASM SET_TAC[]];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REMOVE_THEN "P" (LABEL_TAC "P" o SYM) THEN
  REMOVE_THEN "Ub" (LABEL_TAC "Ub" o SYM) THEN
  SUBGOAL_THEN `open_in topZ (P:A->bool)` (LABEL_TAC "PoZ") THENL
   [USE_THEN "P" (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `U DIFF mfd_cut_cores J cp cm =
      U INTER (topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->A) cm)`
    SUBST1_TAC THENL
     [ASM SET_TAC[]; MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->bool) SUBSET topspace topZ DIFF mfd_cut_cores J cp cm`
  ASSUME_TAC THENL
   [USE_THEN "XZ" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX (P:A->bool)` (LABEL_TAC "PoX") THENL
   [SUBGOAL_THEN
     `open_in (subtopology topZ (topspace topZ DIFF mfd_cut_cores J cp cm))
              (P:A->bool)`
    MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY];
      USE_THEN "sub" (fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(annulus (&1) (&2):real^3->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; annulus; IN_ELIM_THM] THEN
    EXISTS_TAC `(&3 / &2) % basis 1:real^3` THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in topZ (P:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CONNECTED_REMOVE THEN
    MAP_EVERY EXISTS_TAC
     [`U:A->bool`; `JU:num->bool`;
      `\i. IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2))`;
      `\i. IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1))`] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `u = p UNION k /\ p INTER k = {} ==> p = u DIFF (k:A->bool)`) THEN
      CONJ_TAC THENL [USE_THEN "Ub" (ACCEPT_TAC o SYM); ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `y:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:A->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
      USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(y:A) IN mfd_cut_cores J cp cm` MP_TAC THENL
       [UNDISCH_TAC `(y:A) IN t` THEN ASM_REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[IN_MFD_CUT_CORES] THEN
        MAP_EVERY EXISTS_TAC [`i:num`; `z:real^3`] THEN ASM_REWRITE_TAC[];
        USE_THEN "P" (fun th -> MP_TAC th) THEN ASM SET_TAC[]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "img" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "par" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2)) DIFF
        IMAGE (cp i) (cball(vec 0,&1)) = IMAGE (cp i) (annulus (&1) (&2))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                       `ball(vec 0:real^3,&2)`; `ball(vec 0:real^3,&2)`;
                       `cball(vec 0:real^3,&1)`; `(cp:num->real^3->A) i`]
                      APX_PARAM_IMAGE_DIFF) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[SUBSET_REFL; SUBSET; IN_BALL_0; IN_CBALL_0] THEN
          REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN
        REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; annulus;
                    IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "JUQ" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "dQ" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in topX (P:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `connected_in (subtopology topZ (topspace topZ DIFF mfd_cut_cores J cp cm))
                   (P:A->bool)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
      USE_THEN "sub" (fun th -> REWRITE_TAC[GSYM th]) THEN
      SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) | i IN {}} = {} /\
                {IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) | i IN {}} = {}`
  (LABEL_TAC "emp") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(P:A->bool = {})` ASSUME_TAC THENL
   [ASM_CASES_TAC `JU:num->bool = {}` THENL
     [UNDISCH_TAC `~(U:A->bool = {})` THEN
      USE_THEN "Ub" (SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN
      USE_THEN "emp" (fun th -> REWRITE_TAC[th; UNIONS_0; UNION_EMPTY]);
      FIRST_X_ASSUM(X_CHOOSE_TAC `i:num` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
      USE_THEN "colP" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `IMAGE ((cp:num->real^3->A) i) (annulus (&1) (&2)) SUBSET P` THEN
      UNDISCH_TAC `~(annulus (&1) (&2):real^3->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topX closure_of P =
    P UNION UNIONS {IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)) | i IN JU}`
  (LABEL_TAC "clo") THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:A) IN topspace topX` ASSUME_TAC THENL
       [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN
      ASM_CASES_TAC `(y:A) IN mfd_cut_spheres J e` THENL
       [DISJ2_TAC THEN
        UNDISCH_TAC `(y:A) IN mfd_cut_spheres J e` THEN
        REWRITE_TAC[IN_MFD_CUT_SPHERES] THEN
        DISCH_THEN(X_CHOOSE_THEN `j:num` (X_CHOOSE_THEN `u:real^3`
          STRIP_ASSUME_TAC)) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "img" (MP_TAC o SPEC `j:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        UNDISCH_TAC `(e:num->real^3->A) j u IN topX closure_of P` THEN
        REWRITE_TAC[IN_CLOSURE_OF] THEN
        DISCH_THEN(MP_TAC o SPEC
          `IMAGE ((e:num->real^3->A) j) (annulus (&1 / &2) (&2))` o CONJUNCT2) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC))) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "trich" (MP_TAC o SPECL [`j:num`; `v:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]];
        DISJ1_TAC THEN
        SUBGOAL_THEN
         `closed_in (subtopology topX (topspace topX DIFF
                       mfd_cut_spheres J (e:num->real^3->A))) (P:A->bool)`
        MP_TAC THENL
         [USE_THEN "sub" (fun th -> REWRITE_TAC[th]) THEN
          SUBGOAL_THEN
           `P = (topspace topZ DIFF mfd_cut_cores J cp cm) INTER (U:A->bool)`
          SUBST1_TAC THENL
           [USE_THEN "P" (SUBST1_TAC o SYM) THEN ASM SET_TAC[];
            MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED THEN ASM_REWRITE_TAC[]];
          REWRITE_TAC[GSYM CLOSURE_OF_EQ] THEN
          ASM_SIMP_TAC[CLOSURE_OF_SUBTOPOLOGY_OPEN] THEN
          UNDISCH_TAC `(y:A) IN topX closure_of P` THEN ASM SET_TAC[]]];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "par" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "colP" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `annulus (&1 / &2) (&2):real^3->bool`;
                     `(e:num->real^3->A) i`] MFD_PARAM_MAPS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC
       `topX closure_of (IMAGE ((e:num->real^3->A) i) (annulus (&1) (&2)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC
         `IMAGE ((e:num->real^3->A) i)
            ((subtopology euclidean (annulus (&1 / &2) (&2))) closure_of
             (annulus (&1) (&2)))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; EUCLIDEAN_CLOSURE_OF] THEN
          SUBGOAL_THEN
           `annulus (&1 / &2) (&2) INTER annulus (&1) (&2) =
            annulus (&1) (&2):real^3->bool`
          SUBST1_TAC THENL
           [REWRITE_TAC[EXTENSION; IN_INTER; annulus; IN_ELIM_THM] THEN
            GEN_TAC THEN REAL_ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC[SUBSET_INTER; APX_SPHERE_CLOSURE_ANNULUS] THEN
          REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
          GEN_TAC THEN REAL_ARITH_TAC;
          MATCH_MP_TAC CONTINUOUS_MAP_IMAGE_CLOSURE_SUBSET THEN
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(P:A->bool) IN connected_components_of topX` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_CLOPEN_COMPONENT THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM CLOSURE_OF_EQ] THEN USE_THEN "clo" SUBST1_TAC THEN
      UNDISCH_TAC `JU:num->bool = {}` THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "emp" (fun th -> REWRITE_TAC[th; UNIONS_0; UNION_EMPTY]);
      ALL_TAC] THEN
    SUBGOAL_THEN `P:A->bool = U` ASSUME_TAC THENL
     [USE_THEN "Ub" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      UNDISCH_TAC `JU:num->bool = {}` THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "emp" (fun th -> REWRITE_TAC[th; UNIONS_0; UNION_EMPTY]);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(P:A->bool) IN connected_components_of topX` THEN
      ASM_REWRITE_TAC[]];
    USE_THEN "Ub" (ACCEPT_TAC o SYM);
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    USE_THEN "clo" ACCEPT_TAC;
    USE_THEN "clo" SUBST1_TAC THEN REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_DIFF] THEN
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      USE_THEN "SZ" (MP_TAC o SPECL [`i:num`; `u:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "JUQ" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "colP" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `y:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "trich" (MP_TAC o SPECL [`i:num`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      EXISTS_TAC `v:real^3` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^3) IN annulus (&1 / &2) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
        GEN_TAC THEN REAL_ARITH_TAC]];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "trich" (MP_TAC o SPECL [`i:num`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* T0b (sphere separation passes to open subsets) and N5                     *)
(* (a compact set in a product chart with frontier in a section has empty   *)
(* interior).                                                                *)
(* ------------------------------------------------------------------------- *)

let APX_SEP_OPEN = prove
 (`!w:A->bool. APX_SEP_OPEN_STATEMENT w`,
  REWRITE_TAC[APX_SEP_OPEN_STATEMENT; apx_sphere_sep; mfd_neck_chart] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `annulus (&1 / &2) (&2):real^3->bool`;
                 `e:real^3->A`] APX_PARAM_FROM_RESTRICT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^3->A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[apx_separates; TOPSPACE_SUBTOPOLOGY; IN_DIFF; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "nc"))) THEN
  SUBGOAL_THEN
   `(e:real^3->A)(&3 / &4 % basis 1) IN W /\ e(&4 / &3 % basis 1) IN W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (&1 / &2) (&2)) SUBSET W` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; connected_component_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "nc" MP_TAC THEN REWRITE_TAC[connected_component_of] THEN
  EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONNECTED_IN_SUBTOPOLOGY]) THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

(* N5 helpers: rays and sections in real^3. *)

let APX_RADIAL_SECTION_POINT = prove
 (`!(u:real^3->real) x t.
        (!x. x IN sphere(vec 0,&1) ==> &0 < u x) /\
        x IN sphere(vec 0,&1) /\ &0 < t
        ==> (t % x IN IMAGE (\x. u x % x) (sphere(vec 0,&1)) <=> t = u x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (u:real^3->real) z` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t = (u:real^3->real) z` ASSUME_TAC THENL
   [UNDISCH_TAC `t % x = (u:real^3->real) z % z` THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
    UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
    UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^3 = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
  UNDISCH_TAC `t % x = (u:real^3->real) z % z` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ]);;

let APX_SEGMENT_RAY = prove
 (`!x:real^3 a b.
        ~(x = vec 0) /\ a < b
        ==> segment(a % x,b % x) = {s % x | a < s /\ s < b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN
  SUBGOAL_THEN `~(a % x:real^3 = b % x)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(&1 - v) * a + v * b` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < v * (b - a) /\ &0 < (&1 - v) * (b - a)
      ==> a < (&1 - v) * a + v * b /\ (&1 - v) * a + v * b < b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(s - a) / (b - a)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `a < b` THEN CONV_TAC REAL_FIELD]);;

(* N5 (with a nonnegative inner radius): a compact K in the image of a      *)
(* product chart E whose frontier lies in an E-section has empty interior.  *)
(* A point of the interior off the section lies on a ray segment from the    *)
(* section to an end of the annulus that misses the section; that segment   *)
(* would lie in K, so its far end would lie in the compact set E^-1(K)      *)
(* inside the open annulus.                                                  *)

let APX_SECTION_NOT_BOUNDING_POS = prove
 (`!top atlas (E:real^3->A) r1 r2 S Kc.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        &0 <= r1 /\
        mfd_param top atlas (annulus r1 r2) E /\ apx_section E r1 r2 S /\
        compact_in top Kc /\ Kc SUBSET IMAGE E (annulus r1 r2) /\
        top frontier_of Kc SUBSET S
        ==> top interior_of Kc = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par")
   (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  REWRITE_TAC[apx_section] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "ur") SUBST_ALL_TAC))) THEN
  USE_THEN "par" (X_CHOOSE_THEN `E':A->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `!x. x IN sphere(vec 0,&1) ==> &0 < (u:real^3->real) x`
  (LABEL_TAC "upos") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "ur" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN annulus r1 r2 /\
        (E:real^3->A) z IN IMAGE (\x. E((u:real^3->real) x % x)) (sphere(vec 0,&1))
        ==> z IN IMAGE (\x. u x % x) (sphere(vec 0,&1))`
  (LABEL_TAC "SE") THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^3->real) x % x IN annulus r1 r2` ASSUME_TAC THENL
     [USE_THEN "ur" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0; NORM_MUL; REAL_MUL_RID] THEN
      DISCH_TAC THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `E':A->real^3` o
      check (fun th -> is_eq(concl th) && lhs(concl th) = `(E:real^3->A) z`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (IMAGE (E':A->real^3) Kc) /\ IMAGE E' Kc SUBSET annulus r1 r2 /\
    !z. z IN annulus r1 r2 /\ (E:real^3->A) z IN Kc ==> z IN IMAGE E' Kc`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology top (IMAGE (E:real^3->A) (annulus r1 r2))` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(E:real^3->A) z` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `top interior_of Kc SUBSET (Kc:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_OF_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?y0. y0 IN annulus r1 r2 /\ (E:real^3->A) y0 = p`
  (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `Kc SUBSET IMAGE (E:real^3->A) (annulus r1 r2)` THEN
    UNDISCH_TAC `top interior_of Kc SUBSET (Kc:A->bool)` THEN
    UNDISCH_TAC `(p:A) IN top interior_of Kc` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN annulus r1 r2 /\ (E:real^3->A) z IN top interior_of Kc}`
  ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_IN_INTERIOR_OF];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{z | z IN annulus r1 r2 /\ (E:real^3->A) z IN top interior_of Kc}`
               OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(y0:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN annulus r1 r2` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x0 = inv(norm y0) % (y0:real^3)` THEN
  SUBGOAL_THEN `(x0:real^3) IN sphere(vec 0,&1) /\ norm y0 % x0 = y0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
                VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x0:real^3) = &1 /\ ~(x0 = vec 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^3) IN sphere(vec 0,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t. &0 < t /\ t % x0 IN annulus r1 r2 /\ (E:real^3->A)(t % x0) IN Kc /\
        ~(t = (u:real^3->real) x0)`
  (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
   [ASM_CASES_TAC `norm(y0:real^3) = (u:real^3->real) x0` THENL
     [EXISTS_TAC `norm(y0:real^3) + ep / &2` THEN
      SUBGOAL_THEN
       `(norm(y0:real^3) + ep / &2) % x0 IN
        {z | z IN annulus r1 r2 /\ (E:real^3->A) z IN top interior_of Kc}`
      MP_TAC THENL
       [UNDISCH_TAC
         `ball(y0,ep) SUBSET
          {z | z IN annulus r1 r2 /\ (E:real^3->A) z IN top interior_of Kc}` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[IN_BALL] THEN
        UNDISCH_TAC `norm(y0:real^3) % x0 = y0` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                               [SYM th]) THEN
        REWRITE_TAC[dist; GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
        ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]; ASM_REAL_ARITH_TAC]];
      EXISTS_TAC `norm(y0:real^3)` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. r1 <= a /\ a < b /\ b <= r2 /\
          (!s. a < s /\ s < b ==> ~(s = (u:real^3->real) x0)) /\
          a < t /\ t < b
          ==> a % x0 IN annulus r1 r2 /\ b % x0 IN annulus r1 r2`
  (LABEL_TAC "segK") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x0:real^3`; `a:real`; `b:real`] APX_SEGMENT_RAY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `segment(a % x0,b % (x0:real^3)) SUBSET annulus r1 r2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; annulus; IN_ELIM_THM; NORM_MUL] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(t % x0:real^3) IN segment(a % x0,b % x0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (E:real^3->A) (segment(a % x0,b % x0)) SUBSET Kc`
    ASSUME_TAC THENL
     [ASM_CASES_TAC
       `IMAGE (E:real^3->A) (segment(a % x0,b % x0)) DIFF Kc = {}` THENL
       [UNDISCH_TAC
         `IMAGE (E:real^3->A) (segment(a % x0,b % x0)) DIFF Kc = {}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`;
                     `IMAGE (E:real^3->A) (segment(a % x0,b % x0))`;
                     `Kc:A->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
          MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                                `annulus r1 r2:real^3->bool`] THEN
          REWRITE_TAC[CONNECTED_SEGMENT] THEN
          CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          EXISTS_TAC `(E:real^3->A)(t % x0)` THEN CONJ_TAC THENL
           [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM ACCEPT_TAC];
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:A` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `(z:real^3) IN segment(a % x0,b % x0)` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "SE" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `segment(a % x0,b % (x0:real^3)) SUBSET annulus r1 r2` THEN
          ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `s:real` THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `top frontier_of Kc SUBSET
             IMAGE (\x. (E:real^3->A)((u:real^3->real) x % x))
                   (sphere(vec 0,&1))` THEN
          UNDISCH_TAC `(q:A) IN top frontier_of Kc` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`u:real^3->real`; `x0:real^3`; `s:real`]
                    APX_RADIAL_SECTION_POINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
        is_neg(rand(snd(dest_forall(concl th)))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[a % x0,b % x0] SUBSET IMAGE (E':A->real^3) Kc`
    MP_TAC THENL
     [SUBGOAL_THEN `~(a % x0:real^3 = b % x0)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`a % x0:real^3`; `b % x0:real^3`]
                    (CONJUNCT2 CLOSURE_SEGMENT)) THEN
      REWRITE_TAC[ASSUME `~(a % x0:real^3 = b % x0)`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC] THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `E':A->real^3`)) (concl th))) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `segment(a % x0,b % (x0:real^3)) SUBSET annulus r1 r2` THEN
        UNDISCH_TAC `(z:real^3) IN segment(a % x0,b % x0)` THEN SET_TAC[];
        UNDISCH_TAC `IMAGE (E:real^3->A) (segment(a % x0,b % x0)) SUBSET Kc` THEN
        UNDISCH_TAC `(z:real^3) IN segment(a % x0,b % x0)` THEN SET_TAC[]];
      UNDISCH_TAC `IMAGE (E':A->real^3) Kc SUBSET annulus r1 r2` THEN
      MP_TAC(ISPECL [`a % x0:real^3`; `b % x0:real^3`] ENDS_IN_SEGMENT) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `r1 < (u:real^3->real) x0 /\ u x0 < r2 /\ r1 < t /\ t < r2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ur" (MP_TAC o SPEC `x0:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `t % x0:real^3 IN annulus r1 r2` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(u:real^3->real) x0 < t` THENL
   [USE_THEN "segK" (MP_TAC o SPECL [`(u:real^3->real) x0`; `r2:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    USE_THEN "segK" (MP_TAC o SPECL [`r1:real`; `(u:real^3->real) x0`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC]);;

let APX_SECTION_NOT_BOUNDING = prove
 (`!w:A->bool. APX_SECTION_NOT_BOUNDING_STATEMENT w`,
  REWRITE_TAC[APX_SECTION_NOT_BOUNDING_STATEMENT] THEN
  MESON_TAC[APX_SECTION_NOT_BOUNDING_POS]);;

(* ------------------------------------------------------------------------- *)
(* E2 from its leaves (REGION, A25, EXCLUDE, M2) and E3-E9 (proved above).   *)
(* Helpers: the four kinds of canonical neighbourhood; open subsets          *)
(* of X minus the cut spheres are open submanifolds of Z, with the identity  *)
(* a diffeomorphism; parametrizations move from X to Z.                      *)
(* ------------------------------------------------------------------------- *)

let APX_CANONICAL_CASES = prove
 (`!top atlas (g:A->real^3^3) C eps x W.
        rfs_canonical_nbhd (top,atlas) g C eps x W
        ==> apx_neck_or_core (top,atlas) g C eps x \/
            (x IN W /\ rfs_c_component (top,atlas) g C W) \/
            (x IN W /\ rfs_round_component (top,atlas) g eps W)`,
  REWRITE_TAC[rfs_canonical_nbhd; apx_neck_or_core] THEN MESON_TAC[]);;

let APX_CUT_SUBDIFFEO = prove
 (`!topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm V.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        open_in topX V /\ V SUBSET topspace topX DIFF mfd_cut_spheres J e
        ==> open_in topZ V /\
            mfd_diffeo topX atlasX V topZ atlasZ V (\x. x) (\x. x) /\
            mfd_diffeomorphic (subtopology topX V) (restrict_atlas atlasX V)
                              (subtopology topZ V) (restrict_atlas atlasZ V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_diffeo topX (atlasX:((A->bool)#(A->real^3))->bool) V
                  topZ (atlasZ:((A->bool)#(A->real^3))->bool) V
                  (\x:A. x) (\x. x)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_cut_cap topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm
                   (\x. x) (\x. x)` THEN
    REWRITE_TAC[mfd_cut_cap] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->A) cm`;
                   `\x:A. x`; `\x:A. x`; `V:A->bool`] MFD_DIFFEO_RESTRICT) THEN
    ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:A->bool`; `V:A->bool`] APX_DIFFEO_SUBSPACE) THEN
  REWRITE_TAC[APX_DIFFEO_SUBSPACE_STATEMENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\x:A. x`; `\x:A. x`] THEN ASM_REWRITE_TAC[]);;

let APX_CUT_PARAM = prove
 (`!topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm s E.
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        mfd_param topX atlasX s E /\
        IMAGE E s SUBSET topspace topX DIFF mfd_cut_spheres J e
        ==> mfd_param topZ atlasZ s E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(E:real^3->A) = (\x. x) o E` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `topspace topX DIFF mfd_cut_spheres J (e:num->real^3->A)`;
    `topspace topZ DIFF mfd_cut_cores J (cp:num->real^3->A) cm`;
    `\x:A. x`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_cut_cap topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm
                 (\x. x) (\x. x)` THEN
  SIMP_TAC[mfd_cut_cap]);;

(* Listed pieces of open subsets of X minus the cut spheres are listed      *)
(* pieces of the same open subsets of Z.                                     *)

let APX_CUT_LISTED = prove
 (`!topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm V.
        hausdorff_space topX /\ hausdorff_space topZ /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        smooth_manifold_atlas topZ atlasZ /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm (\x. x) (\x. x) /\
        open_in topX V /\ V SUBSET topspace topX DIFF mfd_cut_spheres J e
        ==> (rfs_has_twisted (subtopology topX V) (restrict_atlas atlasX V)
             ==> rfs_has_twisted (subtopology topZ V) (restrict_atlas atlasZ V)) /\
            (rfs_listed_piece (subtopology topX V) (restrict_atlas atlasX V)
             ==> rfs_listed_piece (subtopology topZ V) (restrict_atlas atlasZ V))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`; `V:A->bool`] APX_CUT_SUBDIFFEO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:A->bool`; `V:A->bool`] APX_LISTED_DIFFEO) THEN
  REWRITE_TAC[APX_LISTED_DIFFEO_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT]);;

(* E3 in the cut situation, with JU and P given by their definitions.       *)

let APX_SITUATION_PIECE = prove
 (`!topX atlasX (g:A->real^3^3) C eps dl topZ atlasZ J e cp cm D U.
        apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ) J e cp cm D /\
        U IN connected_components_of topZ /\ U SUBSET D
        ==> let JU = {i | i IN J /\ cp i (vec 0) IN U} in
            let P = U DIFF mfd_cut_cores J cp cm in
            P SUBSET topspace topX DIFF mfd_cut_spheres J e /\
            P SUBSET U /\
            (JU = {} ==> P = U /\ U IN connected_components_of topX) /\
            U = P UNION UNIONS {IMAGE (cp i) (cball(vec 0,&1)) | i IN JU} /\
            open_in topX P /\ connected_in topX P /\ ~(P = {}) /\
            compact_in topX (topX closure_of P) /\
            topX closure_of P =
            P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN JU} /\
            topX closure_of P SUBSET topspace topX DIFF (topspace topZ DIFF D) /\
            (!i. i IN JU
                 ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                     IMAGE (e i) (annulus (&1) (&2))) /\
            (!i. i IN J /\ ~(i IN JU)
                 ==> DISJOINT P (IMAGE (e i) (annulus (&1 / &2) (&2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_cut_situation] THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                   `cm:num->real^3->A`] APX_CUTCAP_ID) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`topZ:A topology`; `U:A->bool`]
                  CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `U:A->bool` APX_CUTCAP_PIECE) THEN
  REWRITE_TAC[APX_CUTCAP_PIECE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
    `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
    `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`;
    `{i | i IN J /\ (cp:num->real^3->A) i (vec 0) IN U}`;
    `U DIFF mfd_cut_cores J (cp:num->real^3->A) cm`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* E2, the case of a component U of Z without plus caps: U is a component of *)
(* X, a C-component, a round component or (A.25) two balls or a twisted     *)
(* chart.                                                                    *)

let APX_PIECES_EMPTY_CASE = prove
 (`!topX atlasX (g:A->real^3^3) C eps dl topZ atlasZ J e cp cm D U.
        apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ) J e cp cm D /\
        U IN connected_components_of topZ /\ U SUBSET D /\
        {i | i IN J /\ cp i (vec 0) IN U} = {} /\
        (!V. V IN connected_components_of topX /\ compact_in topX V /\
             (!x. x IN V ==> apx_neck_or_core (topX,atlasX) g C eps x)
             ==> apx_two_balls (subtopology topX V) (restrict_atlas atlasX V) \/
                 rfs_has_twisted (subtopology topX V) (restrict_atlas atlasX V)) /\
        SMT_TWISTED_SPHERE_STATEMENT (U:A->bool)
        ==> rfs_listed_piece (subtopology topZ U) (restrict_atlas atlasZ U)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sit") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "A25") (LABEL_TAC "M2")))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`]
                APX_SITUATION_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `U DIFF mfd_cut_cores J (cp:num->real^3->A) cm = U`)) THEN
  USE_THEN "sit" (STRIP_ASSUME_TAC o REWRITE_RULE[apx_cut_situation]) THEN
  SUBGOAL_THEN `compact_in topX (U:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_SIMP_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `rfs_listed_piece (subtopology topX U) (restrict_atlas atlasX (U:A->bool))`
  MP_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                   `cm:num->real^3->A`; `U:A->bool`] APX_CUT_LISTED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]] THEN
  ASM_CASES_TAC
   `!x. x IN U ==> apx_neck_or_core (topX,atlasX) (g:A->real^3^3) C eps x`
  THENL
   [USE_THEN "A25" (MP_TAC o SPEC `U:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfs_listed_piece] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b1:real^3->A` (X_CHOOSE_THEN `b2:real^3->A`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) o
      REWRITE_RULE[apx_two_balls]) THEN
    USE_THEN "M2" (MP_TAC o REWRITE_RULE[SMT_TWISTED_SPHERE_STATEMENT]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`b1:real^3->A`; `b2:real^3->A`; `f:real^3->real^3`;
                          `f':real^3->real^3`] THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "rfs_canonical_nbhd")) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool`
    (MP_TAC o MATCH_MP APX_CANONICAL_CASES)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `W:A->bool = U` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `W:A->bool`; `U:A->bool`]
                    CONNECTED_COMPONENTS_OF_OVERLAP) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[rfs_c_component]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_c_component]) THEN
    REWRITE_TAC[rfs_listed_piece] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `W:A->bool = U` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`topX:A topology`; `W:A->bool`; `U:A->bool`]
                    CONNECTED_COMPONENTS_OF_OVERLAP) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[rfs_round_component]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[rfs_listed_piece] THEN DISJ2_TAC THEN DISJ1_TAC THEN
    MP_TAC(ISPEC `U:A->bool` APX_ROUND_SPACE_FORM) THEN
    REWRITE_TAC[APX_ROUND_SPACE_FORM_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `eps:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* Plus caps with centre in U lie in U and are ball charts of Z|U.          *)

let APX_SITUATION_CAP = prove
 (`!topX atlasX (g:A->real^3^3) C eps dl topZ atlasZ J e cp cm D U i.
        apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ) J e cp cm D /\
        U IN connected_components_of topZ /\ i IN J /\ cp i (vec 0) IN U
        ==> IMAGE (cp i) (ball(vec 0,&2)) SUBSET U /\
            mfd_ball_chart (subtopology topZ U) (restrict_atlas atlasZ U) (cp i) /\
            IMAGE (cp i) (cball(vec 0,&1)) SUBSET mfd_cut_cores J cp cm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_cut_situation] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_cut_cap topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm
                 (\x. x) (\x. x)` THEN
  REWRITE_TAC[mfd_cut_cap] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart"))
        (concl th))) THEN
  ASM_REWRITE_TAC[mfd_ball_chart] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2)) SUBSET U`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `topZ:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlasZ:((A->bool)#(A->real^3))->bool`;
                            `ball(vec 0:real^3,&2)`] THEN
      ASM_REWRITE_TAC[CONNECTED_BALL; SUBSET_REFL];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `(cp:num->real^3->A) i (vec 0)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `ball(vec 0:real^3,&2)`; `(cp:num->real^3->A) i`]
                  APX_PARAM_RESTRICT_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`] APX_COMPONENT_OPEN) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_MFD_CUT_CORES; IN_CBALL_0] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `x:real^3`] THEN ASM_REWRITE_TAC[]]);;

(* Parametrizations of X with image in P = U minus the cores are those of   *)
(* Z|U.                                                                      *)

let APX_SITUATION_PARAM = prove
 (`!topX atlasX (g:A->real^3^3) C eps dl topZ atlasZ J e cp cm D U s E.
        apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ) J e cp cm D /\
        U IN connected_components_of topZ /\
        mfd_param topX atlasX s E /\
        IMAGE E s SUBSET U DIFF mfd_cut_cores J cp cm
        ==> mfd_param (subtopology topZ U) (restrict_atlas atlasZ U) s E`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_cut_situation] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`] APX_CUTCAP_ID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topZ:A topology`; `U:A->bool`]
                CONNECTED_COMPONENTS_OF_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `s:real^3->bool`; `E:real^3->A`]
                APX_PARAM_RESTRICT_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`] APX_COMPONENT_OPEN) THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC APX_CUT_PARAM THEN
  MAP_EVERY EXISTS_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
    `cm:num->real^3->A`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* With a plus cap in U, every point of the closure of P is a neck centre   *)
(* or in a cap core: a C-component or round component through such a point *)
(* would contain the centre of a dl-neck (the closure is connected and      *)
(* contains the cut spheres of the caps in U), which EXCLUDE forbids.       *)

let APX_SITUATION_NECK_OR_CORE = prove
 (`!topX atlasX (g:A->real^3^3) C eps dl topZ atlasZ J e cp cm D U.
        apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ) J e cp cm D /\
        U IN connected_components_of topZ /\ U SUBSET D /\
        ~({i | i IN J /\ cp i (vec 0) IN U} = {}) /\
        (!x e' W. rfs_neck (topX,atlasX) g dl x e' /\ x IN W
                  ==> ~rfs_c_component (topX,atlasX) g C W /\
                      ~rfs_round_component (topX,atlasX) g eps W)
        ==> !x. x IN topX closure_of (U DIFF mfd_cut_cores J cp cm)
                ==> apx_neck_or_core (topX,atlasX) g C eps x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sit") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "X"))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`]
                APX_SITUATION_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  USE_THEN "sit" (STRIP_ASSUME_TAC o REWRITE_RULE[apx_cut_situation]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `i:num` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> is_neg(concl th) &&
      can (find_term (fun t -> t = `vec 0:real^3`)) (concl th))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  SUBGOAL_THEN `?y. rfs_neck (topX,atlasX) (g:A->real^3^3) dl y ((e:num->real^3->A) i)`
  (X_CHOOSE_TAC `y:A`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck"))
          (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:A) IN topX closure_of (U DIFF mfd_cut_cores J (cp:num->real^3->A) cm)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closure_of"))
          (lhs(concl th)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1))` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `rfs_neck (topX,atlasX) (g:A->real^3^3) dl y
                     ((e:num->real^3->A) i)` THEN
      SIMP_TAC[rfs_neck]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "rfs_canonical_nbhd")) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (MP_TAC o MATCH_MP APX_CANONICAL_CASES)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `topX closure_of (U DIFF mfd_cut_cores J (cp:num->real^3->A) cm) SUBSET W`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `topX:A topology` THEN
    ASM_SIMP_TAC[CONNECTED_IN_CLOSURE_OF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_c_component; rfs_round_component]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    USE_THEN "X" (MP_TAC o SPECL [`y:A`; `(e:num->real^3->A) i`; `W:A->bool`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `topX:A topology` THEN
    ASM_SIMP_TAC[CONNECTED_IN_CLOSURE_OF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[rfs_c_component; rfs_round_component]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    USE_THEN "X" (MP_TAC o SPECL [`y:A`; `(e:num->real^3->A) i`; `W:A->bool`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]]]);;

(* E2, the case of a component U of Z containing plus caps: REGION gives a  *)
(* twisted chart of P (it passes to Z|U) or a product capped by cp_i and a  *)
(* ball of P or a second plus cap; E4 closes it up to S^3.                  *)

let APX_PIECES_NONEMPTY_CASE = prove
 (`!topX atlasX (g:A->real^3^3) C eps dl topZ atlasZ J e cp cm D U.
        apx_cut_situation (topX,atlasX) g C eps dl (topZ,atlasZ) J e cp cm D /\
        U IN connected_components_of topZ /\ U SUBSET D /\
        ~({i | i IN J /\ cp i (vec 0) IN U} = {}) /\
        (!x e' W. rfs_neck (topX,atlasX) g dl x e' /\ x IN W
                  ==> ~rfs_c_component (topX,atlasX) g C W /\
                      ~rfs_round_component (topX,atlasX) g eps W) /\
        (!J' P. FINITE J' /\ ~(J' = {}) /\
                (!i:num. i IN J' ==> ?y. rfs_neck (topX,atlasX) g dl y (e i)) /\
                (!i j. i IN J' /\ j IN J' /\ ~(i = j)
                       ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                                    (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
                open_in topX P /\ connected_in topX P /\
                compact_in topX (topX closure_of P) /\
                topX closure_of P =
                P UNION UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN J'} /\
                (!i. i IN J'
                     ==> P INTER IMAGE (e i) (annulus (&1 / &2) (&2)) =
                         IMAGE (e i) (annulus (&1) (&2))) /\
                (!x. x IN topX closure_of P
                     ==> apx_neck_or_core (topX,atlasX) g C eps x)
                ==> rfs_has_twisted (subtopology topX P) (restrict_atlas atlasX P) \/
                    ?i E L f f' b2.
                       i IN J' /\ &1 < L /\ sphere_diffeo f f' /\
                       mfd_param topX atlasX (annulus (&1) L) E /\
                       (!x. x IN annulus (&1) (&3 / &2) ==> E x = e i x) /\
                       (!x. x IN annulus (L / &2) L
                            ==> E x = b2((L / norm x) % f(inv(norm x) % x))) /\
                       ((J' = {i} /\ mfd_ball_chart topX atlasX b2 /\
                         IMAGE b2 (ball(vec 0,&2)) SUBSET P /\
                         P = IMAGE E (annulus (&1) L) UNION
                             IMAGE b2 (cball(vec 0,&1)) /\
                         DISJOINT (IMAGE E (annulus (&1) L))
                                  (IMAGE b2 (cball(vec 0,&1)))) \/
                        (?j. j IN J' /\ ~(j = i) /\ J' = {i,j} /\ b2 = e j /\
                             P = IMAGE E (annulus (&1) L)))) /\
        SMT_TWISTED_SPHERE_STATEMENT (U:A->bool)
        ==> rfs_listed_piece (subtopology topZ U) (restrict_atlas atlasZ U)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sit") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "X") (CONJUNCTS_THEN2 (LABEL_TAC "R")
    (LABEL_TAC "M2"))))))) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`]
                APX_SITUATION_NECK_OR_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`]
                APX_SITUATION_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `JU = {i | i IN J /\ (cp:num->real^3->A) i (vec 0) IN U}` THEN
  ABBREV_TAC `P = U DIFF mfd_cut_cores J (cp:num->real^3->A) cm` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "Ub" o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `U:A->bool`)) THEN
  USE_THEN "sit" (STRIP_ASSUME_TAC o REWRITE_RULE[apx_cut_situation]) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`] APX_CUTCAP_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "XZ") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
   (CONJUNCTS_THEN2 (LABEL_TAC "Xo") (CONJUNCTS_THEN2 (LABEL_TAC "Zo")
   (CONJUNCTS_THEN2 (LABEL_TAC "colp") (LABEL_TAC "colm")))))) THEN
  MP_TAC(ASSUME `mfd_cut_cap topX atlasX topZ atlasZ J (e:num->real^3->A) cp cm
                   (\x. x) (\x. x)`) THEN
  REWRITE_TAC[mfd_cut_cap] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "charts")
   (CONJUNCTS_THEN2 (LABEL_TAC "dE") (CONJUNCTS_THEN2 (LABEL_TAC "dQ")
    (K ALL_TAC))))) THEN
  SUBGOAL_THEN `(JU:num->bool) SUBSET J /\ FINITE JU /\
                (!i. i IN JU ==> (cp:num->real^3->A) i (vec 0) IN U)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `JU:num->bool`)) THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `J:num->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topZ (U:A->bool) /\ U SUBSET topspace topZ`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`] APX_COMPONENT_OPEN) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONNECTED_COMPONENTS_OF_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "R" (MP_TAC o SPECL [`JU:num->bool`; `P:A->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck"))
            (concl th))) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(JU:num->bool) SUBSET J` THEN
        UNDISCH_TAC `(i:num) IN JU` THEN SET_TAC[];
        SIMP_TAC[]];
      REPEAT STRIP_TAC THEN USE_THEN "dE" MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `(JU:num->bool) SUBSET J` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                   `cm:num->real^3->A`; `P:A->bool`] APX_CUT_SUBDIFFEO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                   `cm:num->real^3->A`; `P:A->bool`] APX_CUT_LISTED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    REWRITE_TAC[rfs_listed_piece] THEN DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    MP_TAC(ISPEC `U:A->bool` APX_TWISTED_MONO) THEN
    REWRITE_TAC[APX_TWISTED_MONO_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `P:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `E:real^3->A`
    (X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `f':real^3->real^3` (X_CHOOSE_THEN `b2:real^3->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Ec") (CONJUNCTS_THEN2 (LABEL_TAC "Eb")
     (LABEL_TAC "alt"))))))))))))) THEN
  SUBGOAL_THEN `(i:num) IN J /\ (cp:num->real^3->A) i (vec 0) IN U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(JU:num->bool) SUBSET J` THEN
      UNDISCH_TAC `(i:num) IN JU` THEN SET_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `vec 0:real^3`)) (concl th) &&
        is_forall(concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`;
                 `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                 `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                 `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`; `i:num`]
                APX_SITUATION_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN annulus (&1) (&3 / &2) ==> (E:real^3->A) x = (cp:num->real^3->A) i x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "Ec" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "colp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN annulus (&1) (&3 / &2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (subtopology topZ (U:A->bool)) /\
    smooth_manifold_atlas (subtopology topZ U)
      (restrict_atlas (atlasZ:((A->bool)#(A->real^3))->bool) U)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; SMOOTH_MANIFOLD_ATLAS_RESTRICT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `U:A->bool` APX_GLUE_CAPPED) THEN
  USE_THEN "M2" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[APX_GLUE_CAPPED_STATEMENT] THEN
  USE_THEN "alt" MP_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `JU:num->bool`)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `P:A->bool`)) THEN
    SUBGOAL_THEN
     `mfd_ball_chart (subtopology topZ U)
        (restrict_atlas (atlasZ:((A->bool)#(A->real^3))->bool) U) (b2:real^3->A) /\
      mfd_param (subtopology topZ U) (restrict_atlas atlasZ U)
        (annulus (&1) L) (E:real^3->A)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[mfd_ball_chart] THEN CONJ_TAC THEN
      MATCH_MP_TAC APX_SITUATION_PARAM THEN
      MAP_EVERY EXISTS_TAC
       [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`;
        `e:num->real^3->A`; `cp:num->real^3->A`; `cm:num->real^3->A`;
        `D:A->bool`] THEN
      ASM_REWRITE_TAC[GSYM mfd_ball_chart] THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (annulus (&1) L) UNION
                   IMAGE (b2:real^3->A) (cball(vec 0,&1)) = P` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `topspace (subtopology topZ U) =
      IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) UNION
      IMAGE (E:real^3->A) (annulus (&1) L) UNION
      IMAGE (b2:real^3->A) (cball(vec 0,&1)) /\
      DISJOINT (IMAGE (cp i) (cball(vec 0,&1))) (IMAGE E (annulus (&1) L)) /\
      DISJOINT (IMAGE (cp i) (cball(vec 0,&1))) (IMAGE b2 (cball(vec 0,&1)))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      UNDISCH_TAC `(U:A->bool) SUBSET topspace topZ` THEN
      USE_THEN "Ub" (MP_TAC o REWRITE_RULE[SET_RULE
        `UNIONS {(f:num->A->bool) k | k IN {i}} = f i`]) THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (annulus (&1) L) UNION
                   IMAGE (b2:real^3->A) (cball(vec 0,&1)) = P` THEN
      UNDISCH_TAC `IMAGE (b2:real^3->A) (ball(vec 0,&2)) SUBSET P` THEN
      UNDISCH_TAC `IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) SUBSET
                   mfd_cut_cores J cp cm` THEN
      UNDISCH_TAC `U DIFF mfd_cut_cores J (cp:num->real^3->A) cm = P` THEN
      SUBGOAL_THEN `IMAGE (b2:real^3->A) (cball(vec 0,&1)) SUBSET
                    IMAGE b2 (ball(vec 0,&2))` MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`subtopology topZ (U:A->bool)`;
      `restrict_atlas (atlasZ:((A->bool)#(A->real^3))->bool) U`;
      `(cp:num->real^3->A) i`; `E:real^3->A`; `L:real`; `b2:real^3->A`;
      `f:real^3->real^3`; `f':real^3->real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[rfs_listed_piece] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(j:num) IN J /\ (cp:num->real^3->A) j (vec 0) IN U`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(JU:num->bool) SUBSET J` THEN
        UNDISCH_TAC `(j:num) IN JU` THEN SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `vec 0:real^3`)) (concl th) &&
          is_forall(concl th))) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `JU:num->bool`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `b2:real^3->A`)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `P:A->bool`)) THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`;
                   `topZ:A topology`; `atlasZ:((A->bool)#(A->real^3))->bool`;
                   `J:num->bool`; `e:num->real^3->A`; `cp:num->real^3->A`;
                   `cm:num->real^3->A`; `D:A->bool`; `U:A->bool`; `j:num`]
                  APX_SITUATION_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `mfd_param (subtopology topZ U)
        (restrict_atlas (atlasZ:((A->bool)#(A->real^3))->bool) U)
        (annulus (&1) L) (E:real^3->A)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC APX_SITUATION_PARAM THEN
      MAP_EVERY EXISTS_TAC
       [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`;
        `e:num->real^3->A`; `cp:num->real^3->A`; `cm:num->real^3->A`;
        `D:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (annulus (&1) L) = P` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN annulus (L / &2) L
          ==> (E:real^3->A) x =
              (cp:num->real^3->A) j ((L / norm x) % f(inv(norm x) % x))`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "Eb" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "colp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < L /\ &0 < norm(x:real^3)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN annulus (L / &2) L` THEN
        UNDISCH_TAC `&1 < L` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `L:real`;
                     `x:real^3`] APX_FLIP_NORM) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; DISCH_TAC] THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
      UNDISCH_TAC `(x:real^3) IN annulus (L / &2) L` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `topspace (subtopology topZ U) =
      IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) UNION
      IMAGE (E:real^3->A) (annulus (&1) L) UNION
      IMAGE (cp j) (cball(vec 0,&1)) /\
      DISJOINT (IMAGE (cp i) (cball(vec 0,&1))) (IMAGE E (annulus (&1) L)) /\
      DISJOINT (IMAGE (cp i) (cball(vec 0,&1))) (IMAGE (cp j) (cball(vec 0,&1))) /\
      DISJOINT (IMAGE E (annulus (&1) L)) (IMAGE (cp j) (cball(vec 0,&1)))`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "dQ" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      UNDISCH_TAC `(U:A->bool) SUBSET topspace topZ` THEN
      USE_THEN "Ub" (MP_TAC o REWRITE_RULE[SET_RULE
        `UNIONS {(f:num->A->bool) k | k IN {i,j}} = f i UNION f j`]) THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (annulus (&1) L) = P` THEN
      UNDISCH_TAC `IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) SUBSET
                   mfd_cut_cores J cp cm` THEN
      UNDISCH_TAC `IMAGE ((cp:num->real^3->A) j) (cball(vec 0,&1)) SUBSET
                   mfd_cut_cores J cp cm` THEN
      UNDISCH_TAC `U DIFF mfd_cut_cores J (cp:num->real^3->A) cm = P` THEN
      UNDISCH_TAC `DISJOINT (IMAGE ((cp:num->real^3->A) i) (ball(vec 0,&2)))
                            (IMAGE (cp j) (ball(vec 0,&2)))` THEN
      SUBGOAL_THEN
       `IMAGE ((cp:num->real^3->A) i) (cball(vec 0,&1)) SUBSET
        IMAGE (cp i) (ball(vec 0,&2)) /\
        IMAGE (cp j) (cball(vec 0,&1)) SUBSET IMAGE (cp j) (ball(vec 0,&2))`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`subtopology topZ (U:A->bool)`;
      `restrict_atlas (atlasZ:((A->bool)#(A->real^3))->bool) U`;
      `(cp:num->real^3->A) i`; `E:real^3->A`; `L:real`;
      `(cp:num->real^3->A) j`; `f:real^3->real^3`; `f':real^3->real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[rfs_listed_piece] THEN ASM_REWRITE_TAC[]]);;

(* E2 from its leaves. *)

let APX_EVENT_PIECES_FROM_LEAVES = prove
 (`!w:A->bool.
        APX_REGION_STATEMENT w /\ APX_A25_STATEMENT w /\
        APX_EXCLUDE_STATEMENT w /\ SMT_TWISTED_SPHERE_STATEMENT w
        ==> APX_EVENT_PIECES_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[APX_REGION_STATEMENT; APX_A25_STATEMENT; APX_EXCLUDE_STATEMENT;
              APX_EVENT_PIECES_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "R")))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A")))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "X")))
        (LABEL_TAC "M2")))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`] THEN STRIP_TAC THEN
  USE_THEN "R" (MP_TAC o SPECL [`C:real`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "R1"))) THEN
  USE_THEN "X" (MP_TAC o SPECL [`C:real`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "X1"))) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `dl:real`; `topZ:A topology`;
    `atlasZ:((A->bool)#(A->real^3))->bool`; `J:num->bool`;
    `e:num->real^3->A`; `cp:num->real^3->A`; `cm:num->real^3->A`;
    `D:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sit"))) THEN
  X_GEN_TAC `U:A->bool` THEN STRIP_TAC THEN
  USE_THEN "sit" (STRIP_ASSUME_TAC o REWRITE_RULE[apx_cut_situation]) THEN
  ASM_CASES_TAC `{i | i IN J /\ (cp:num->real^3->A) i (vec 0) IN U} = {}` THENL
   [MATCH_MP_TAC APX_PIECES_EMPTY_CASE THEN
    MAP_EVERY EXISTS_TAC
     [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`;
      `e:num->real^3->A`; `cp:num->real^3->A`; `cm:num->real^3->A`;
      `D:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `V:A->bool` THEN STRIP_TAC THEN
      USE_THEN "A" (MP_TAC o SPECL [`C:real`; `eps:real`; `topX:A topology`;
        `atlasX:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `V:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "M2" MP_TAC THEN REWRITE_TAC[SMT_TWISTED_SPHERE_STATEMENT]];
    MATCH_MP_TAC APX_PIECES_NONEMPTY_CASE THEN
    MAP_EVERY EXISTS_TAC
     [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `C:real`; `eps:real`; `dl:real`; `J:num->bool`;
      `e:num->real^3->A`; `cp:num->real^3->A`; `cm:num->real^3->A`;
      `D:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:A`; `e':real^3->A`; `W:A->bool`] THEN STRIP_TAC THEN
      USE_THEN "X1" (MP_TAC o SPECL [`topX:A topology`;
        `atlasX:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `dl:real`;
        `x:A`; `e':real^3->A`; `W:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`J':num->bool`; `P:A->bool`] THEN STRIP_TAC THEN
      USE_THEN "R1" (MP_TAC o SPECL [`topX:A topology`;
        `atlasX:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `dl:real`;
        `J':num->bool`; `e:num->real^3->A`; `P:A->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "M2" MP_TAC THEN REWRITE_TAC[SMT_TWISTED_SPHERE_STATEMENT]]]);;

(* ------------------------------------------------------------------------- *)
(* E1 from its leaves (STRONG_NECK_EARLIER N8 and the sphere                 *)
(* separation T0).  Helpers: event times increase strictly; the slab of a    *)
(* time between two event times; a finite family of positive radii has a   *)
(* common positive lower bound.                                              *)
(* ------------------------------------------------------------------------- *)

let APX_HS_TIME_MONO = prove
 (`!hs:(A)rfs_history m n.
        rfs_history_ok hs /\ m < n /\ n <= hs_count hs + 1
        ==> hs_time hs m < hs_time hs n`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) n < hs_time hs (SUC n)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN
    REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[ADD1] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `SUC n <= hs_count (hs:(A)rfs_history) + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `m:num = n` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_HS_TIME_LE = prove
 (`!hs:(A)rfs_history m n.
        rfs_history_ok hs /\ m <= n /\ n <= hs_count hs + 1
        ==> hs_time hs m <= hs_time hs n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:num = n` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC APX_HS_TIME_MONO THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let APX_RFS_SLAB = prove
 (`!hs:(A)rfs_history k t.
        rfs_history_ok hs /\ k <= hs_count hs /\
        hs_time hs k <= t /\ t < hs_time hs (k + 1)
        ==> rfs_slab hs t = k /\ rfs_live hs t /\
            rfs_top_at hs t = hs_top hs k /\
            rfs_atlas_at hs t = hs_atlas hs k /\
            rfs_metric_at hs t = hs_metric hs k t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_slab (hs:(A)rfs_history) t = k` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_slab] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `j:num` THEN BETA_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `~(j < k) /\ ~(k < j:num) ==> j = k`) THEN
      CONJ_TAC THEN DISCH_TAC THENL
       [MP_TAC(ISPECL [`hs:(A)rfs_history`; `j + 1`; `k:num`] APX_HS_TIME_LE);
        MP_TAC(ISPECL [`hs:(A)rfs_history`; `k + 1`; `j:num`] APX_HS_TIME_LE)] THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) t` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_live] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hs_time (hs:(A)rfs_history) k` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_HS_TIME_POS THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `hs_time (hs:(A)rfs_history) (k + 1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_HS_TIME_LE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at]);;

let APX_FINITE_DELTA = prove
 (`!J:num->bool (P:num->real->bool).
        FINITE J /\ (!i. i IN J ==> ?d. &0 < d /\ P i d) /\
        (!i d d'. i IN J /\ P i d /\ &0 < d' /\ d' <= d ==> P i d')
        ==> ?d. &0 < d /\ !i. i IN J ==> P i d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) (LABEL_TAC "dn"))) THEN
  DISCH_THEN(X_CHOOSE_TAC `dd:num->real`) THEN
  ASM_CASES_TAC `J:num->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inf (IMAGE (dd:num->real) J)` THEN
  ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "dn" MATCH_MP_TAC THEN EXISTS_TAC `(dd:num->real) i` THEN
  ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
               FORALL_IN_IMAGE; REAL_INF_LE_FINITE; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* N8 applied to a cut neck: the strong dl-neck of the pre-surgery view at  *)
(* the event time is a K dl-neck of the old stage at all slightly earlier   *)
(* times (the preview slices there are the old stage, the neck chart is a   *)
(* parametrization of it by E8).                                             *)

let APX_SLICE_NECKS = prove
 (`!(hs:(A)rfs_history) kK dl k i y.
        rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
        &0 < dl /\ kK * dl <= &1 / &2 /\
        (!TM AT G dl y t e top atlas t0.
            &0 < dl /\ kK * dl <= &1 / &2 /\ t0 < t /\
            rfs_strong_neck (TM,AT,G) dl y t (e:real^3->A) /\
            (!s. t0 < s /\ s < t
                 ==> TM s = top /\ AT s = atlas /\ riemannian_metric atlas (G s) /\
                     mfd_param top atlas (rfs_neck_dom dl) e)
            ==> ?d. &0 < d /\
                    !s. t - d < s /\ s < t ==> rfs_neck (top,atlas) (G s) (kK * dl) y e) /\
        rfs_strong_neck (rfs_preview hs k) dl y (hs_time hs k)
                        (ev_neck(hs_event hs k) i)
        ==> ?d. &0 < d /\
                !s. hs_time hs k - d < s /\ s < hs_time hs k
                    ==> rfs_neck (hs_top hs (k - 1),hs_atlas hs (k - 1))
                                 (hs_metric hs (k - 1) s) (kK * dl) y
                                 (ev_neck(hs_event hs k) i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hok") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "N8")
    (LABEL_TAC "sn"))))))) THEN
  SUBGOAL_THEN `k - 1 + 1 = k /\ k - 1 <= hs_count (hs:(A)rfs_history)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "hok" (MP_TAC o REWRITE_RULE[rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (MP_TAC o SPEC `k - 1`) (MP_TAC o SPEC `k:num`)))) THEN
  ASM_REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k - 1) < hs_time hs k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param (hs_top hs (k - 1)) (hs_atlas hs (k - 1)) (rfs_neck_dom dl)
              (ev_neck(hs_event (hs:(A)rfs_history) k) i)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`hs_top (hs:(A)rfs_history) (k - 1)`;
                   `hs_atlas (hs:(A)rfs_history) (k - 1)`;
                   `ev_omega(hs_event (hs:(A)rfs_history) k)`;
                   `rfs_neck_dom dl`; `ev_neck(hs_event (hs:(A)rfs_history) k) i`]
                  APX_PARAM_FROM_RESTRICT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sn" (MP_TAC o REWRITE_RULE[rfs_strong_neck]) THEN
    REWRITE_TAC[rfs_preview; rfs_evolving_neck] THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  USE_THEN "N8" (MP_TAC o SPECL
   [`FST(rfs_preview (hs:(A)rfs_history) k)`;
    `FST(SND(rfs_preview (hs:(A)rfs_history) k))`;
    `SND(SND(rfs_preview (hs:(A)rfs_history) k))`; `dl:real`; `y:A`;
    `hs_time (hs:(A)rfs_history) k`; `ev_neck(hs_event (hs:(A)rfs_history) k) i`;
    `hs_top (hs:(A)rfs_history) (k - 1)`; `hs_atlas (hs:(A)rfs_history) (k - 1)`;
    `hs_time (hs:(A)rfs_history) (k - 1)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PAIR] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[rfs_preview] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NE] THEN
    UNDISCH_TAC `ricci_flow_from (hs_top hs (k - 1),hs_atlas hs (k - 1))
                   (hs_time hs (k - 1)) (hs_time hs k)
                   (hs_metric (hs:(A)rfs_history) (k - 1))` THEN
    REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (hs_time (hs:(A)rfs_history) k - hs_time hs (k - 1))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck"))
        (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `s:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[rfs_preview] THEN ASM_SIMP_TAC[REAL_LT_IMP_NE]);;

(* A strong canonical neighbourhood of the view at a time of the slab k - 1 *)
(* is a canonical neighbourhood of stage k - 1 with its metric at that time. *)

let APX_SLICE_CANONICAL = prove
 (`!(hs:(A)rfs_history) C eps k t x U.
        rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
        hs_time hs (k - 1) <= t /\ t < hs_time hs k /\
        rfs_strong_canonical (rfs_view hs) C eps x t U
        ==> rfs_canonical_nbhd (hs_top hs (k - 1),hs_atlas hs (k - 1))
                               (hs_metric hs (k - 1) t) C eps x U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `k - 1`; `t:real`] APX_RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  UNDISCH_TAC `rfs_strong_canonical (rfs_view (hs:(A)rfs_history)) C eps x t U` THEN
  REWRITE_TAC[rfs_view; rfs_strong_canonical; rfs_strong_neck; rfs_evolving_neck;
              rfs_canonical_nbhd] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* E1 from its leaves. *)

let APX_EVENT_SLICE_FROM_LEAVES = prove
 (`!w:A->bool.
        APX_STRONG_NECK_EARLIER_STATEMENT w /\ APX_SC_SPHERE_SEP_STATEMENT w
        ==> APX_EVENT_SLICE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[APX_STRONG_NECK_EARLIER_STATEMENT; APX_SC_SPHERE_SEP_STATEMENT;
              APX_EVENT_SLICE_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `kK:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N8")))
    (LABEL_TAC "T0")) THEN
  EXISTS_TAC `kK:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`;
                       `rp:real->real`; `dl:real->real`; `kp:real->real`;
                       `h:real->real`; `k:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hok") (CONJUNCTS_THEN2 (LABEL_TAC "par")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "Kdl") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sok")
    (LABEL_TAC "sc"))))))))) THEN
  SUBGOAL_THEN `k - 1 + 1 = k /\ k - 1 <= hs_count (hs:(A)rfs_history)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= hs_time (hs:(A)rfs_history) k /\ hs_time hs (k - 1) < hs_time hs k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_HS_TIME_POS THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC APX_HS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < dl(hs_time (hs:(A)rfs_history) k) /\
    kK * dl(hs_time hs k) <= &1 / &2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "par" (MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k` o
                    CONJUNCT1 o REWRITE_RULE[rfs_params]) THEN
    USE_THEN "Kdl" (MP_TAC o SPEC `hs_time (hs:(A)rfs_history) k`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "sok" (MP_TAC o REWRITE_RULE[rfs_surgery_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM;
                                                     SKOLEM_THM])
    (X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "can"))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `yy:num->A` (LABEL_TAC "yy")) THEN
  USE_THEN "hok" (MP_TAC o REWRITE_RULE[rfs_history_ok]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (MP_TAC o SPEC `k - 1`) (MP_TAC o SPEC `k:num`)))) THEN
  ASM_REWRITE_TAC[rfs_event_ok] THEN
  DISCH_THEN(LABEL_TAC "ev") THEN DISCH_THEN(LABEL_TAC "st") THEN
  SUBGOAL_THEN `FINITE(ev_index(hs_event (hs:(A)rfs_history) k))` ASSUME_TAC THENL
   [USE_THEN "ev" (MP_TAC o CONJUNCT1 o REWRITE_RULE[mfd_cut_cap] o
      CONJUNCT1 o funpow 5 CONJUNCT2) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ev_index(hs_event (hs:(A)rfs_history) k)`;
    `\i d. !s. hs_time (hs:(A)rfs_history) k - d < s /\ s < hs_time hs k
               ==> rfs_neck (hs_top hs (k - 1),hs_atlas hs (k - 1))
                            (hs_metric hs (k - 1) s) (kK * dl(hs_time hs k))
                            ((yy:num->A) i) (ev_neck(hs_event hs k) i)`]
   APX_FINITE_DELTA) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC APX_SLICE_NECKS THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "yy" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nd"))) THEN
  ABBREV_TAC `t' = (max t1 (hs_time (hs:(A)rfs_history) k - d) + hs_time hs k) / &2` THEN
  SUBGOAL_THEN
   `t1 < t' /\ hs_time (hs:(A)rfs_history) k - d < t' /\ t' < hs_time hs k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `t':real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[apx_cut_situation] THEN USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "st" (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "st" (MP_TAC o SPEC `t':real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT1 o REWRITE_RULE[ricci_flow_from; ricci_flow_on] o last o
      CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    USE_THEN "T0" MATCH_MP_TAC THEN USE_THEN "st" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sc" (ACCEPT_TAC o REWRITE_RULE[rfs_components_sc]);
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
    CONJ_TAC THENL
     [USE_THEN "ev" (MP_TAC o SPEC `i:num` o CONJUNCT1 o funpow 11 CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      EXISTS_TAC `(yy:num->A) i` THEN
      USE_THEN "nd" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "can" (MP_TAC o SPECL [`t':real`; `x:A`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ev" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      UNDISCH_TAC `(x:A) IN topspace (hs_top (hs:(A)rfs_history) (k - 1)) DIFF
                   (topspace (ev_ztop (hs_event hs k)) DIFF ev_disc (hs_event hs k))` THEN
      SET_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `U:A->bool`)] THEN
    EXISTS_TAC `U:A->bool` THEN MATCH_MP_TAC APX_SLICE_CANONICAL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* MT Prop 15.3 (separating case) from the leaves of the event chain. *)

let APX_EVENT_TOPOLOGY_FROM_LEAVES = prove
 (`!w:A->bool.
        APX_STRONG_NECK_EARLIER_STATEMENT w /\ APX_SC_SPHERE_SEP_STATEMENT w /\
        APX_REGION_STATEMENT w /\ APX_A25_STATEMENT w /\
        APX_EXCLUDE_STATEMENT w /\ SMT_TWISTED_SPHERE_STATEMENT w
        ==> EVENT_TOPOLOGY_STATEMENT w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC APX_EVENT_TOPOLOGY_FROM_PARTS THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC APX_EVENT_SLICE_FROM_LEAVES;
    MATCH_MP_TAC APX_EVENT_PIECES_FROM_LEAVES] THEN
  ASM_REWRITE_TAC[]);;

