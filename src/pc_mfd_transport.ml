(* ========================================================================= *)
(* pc_mfd_transport: transport of a smooth manifold, its atlas and a         *)
(* Riemannian metric along an injection f with a left inverse f' on the      *)
(* topological space (for example INL and OUTL from A to A + num#num#real^3, *)
(* the carrier of surgery histories): the image topology, the image atlas,   *)
(* the pullback metric, the diffeomorphism and the isometry, the invariants  *)
(* (Hausdorff, compact, simply connected, orientable) and the transfer of    *)
(* the curvature norm, balls, volumes and rfs_normalized along isometries.   *)
(* ========================================================================= *)

needs "src/pc_mfd_restrict.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_rfs_geom.ml";;
needs "src/pc_audit_sanity.ml";;
needs "src/pc_rf_extend.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The image topology of an injection with a left inverse.                   *)
(* ------------------------------------------------------------------------- *)

let MTR_ISTOPOLOGY = prove
 (`!(top:A topology) (f:A->B) f'.
     (!x. x IN topspace top ==> f'(f x) = x)
     ==> istopology {IMAGE f U | open_in top U}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[istopology; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN REWRITE_TAC[OPEN_IN_EMPTY; IMAGE_CLAUSES];
    MAP_EVERY X_GEN_TAC [`s:B->bool`; `t:B->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U INTER V:A->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET)) THEN ASM SET_TAC[];
    X_GEN_TAC `k:(B->bool)->bool` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
    EXISTS_TAC `UNIONS {U:A->bool | open_in top U /\ IMAGE (f:A->B) U IN k}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNIONS THEN SIMP_TAC[IN_ELIM_THM];
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `y:B` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `s:B->bool` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:B->bool`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(y:B) IN IMAGE (f:A->B) U` MP_TAC THENL
         [ASM_MESON_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `U:A->bool` THEN
        ASM_MESON_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC))) THEN
        EXISTS_TAC `IMAGE (f:A->B) U` THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
        ASM_MESON_TAC[]]]]);;

let MTR_TOPOLOGY = prove
 (`!(top:A topology) (f:A->B) f'.
     (!x. x IN topspace top ==> f'(f x) = x)
     ==> ?top'. (!V. open_in top' V <=> ?U. open_in top U /\ V = IMAGE f U) /\
                topspace top' = IMAGE f (topspace top) /\
                homeomorphic_maps (top,top') (f,f')`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `topology {IMAGE (f:A->B) U | open_in top U}` THEN
  SUBGOAL_THEN
   `!V. open_in (topology {IMAGE (f:A->B) U | open_in top U}) V <=>
        ?U. open_in top U /\ V = IMAGE f U`
  (LABEL_TAC "op") THENL
   [SUBGOAL_THEN
     `open_in (topology {IMAGE (f:A->B) U | open_in top U}) =
      {IMAGE (f:A->B) U | open_in top U}`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
      MATCH_MP_TAC MTR_ISTOPOLOGY THEN EXISTS_TAC `f':B->A` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace (topology {IMAGE (f:A->B) U | open_in top U}) = IMAGE f (topspace top)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [topspace] THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:B` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:B->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))
        ASSUME_TAC)) THEN
      UNDISCH_TAC `(y:B) IN s` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `!(f:A->B) s t y. s SUBSET t ==> y IN IMAGE f s ==> y IN IMAGE f t`) THEN
      ASM_SIMP_TAC[OPEN_IN_SUBSET];
      DISCH_TAC THEN EXISTS_TAC `IMAGE (f:A->B) (topspace top)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `topspace top:A->bool` THEN
      REWRITE_TAC[OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[homeomorphic_maps; continuous_map] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:B->bool` THEN DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{x | x IN topspace top /\ (f:A->B) x IN u} = U` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The image atlas (charts (IMAGE f U, phi o f')) of a smooth atlas along a  *)
(* homeomorphism (f,f'); f and f' are inverse diffeomorphisms.               *)
(* (MOI_SMOOTH_ATLAS_TRANSPORT of pc_moi_assembly states only the existence  *)
(* of some transported atlas; the diffeomorphism needs the explicit one.)    *)
(* ------------------------------------------------------------------------- *)

let MTR_ATLAS_IN = prove
 (`!(f:A->B) (f':B->A) (atlas:((A->bool)#(A->real^N))->bool) V psi.
        (V,psi) IN IMAGE (\c. IMAGE f (FST c),SND c o f') atlas <=>
        ?U phi. (U,phi) IN atlas /\ V = IMAGE f U /\ psi = phi o f'`,
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MTR_SMOOTH_ATLAS = prove
 (`!(top:A topology) (top':B topology) (atlas:((A->bool)#(A->real^N))->bool) f f'.
     smooth_manifold_atlas top atlas /\ homeomorphic_maps (top,top') (f,f')
     ==> smooth_manifold_atlas top' (IMAGE (\c. IMAGE f (FST c),SND c o f') atlas)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP o
    ONCE_REWRITE_RULE[HOMEOMORPHIC_MAPS_SYM]) THEN
  SUBGOAL_THEN `IMAGE (f:A->B) (topspace top) SUBSET topspace top' /\
                IMAGE (f':B->A) (topspace top') SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  SUBGOAL_THEN `!U:A->bool. open_in top U ==> U SUBSET topspace top /\
                            IMAGE (f':B->A) (IMAGE (f:A->B) U) = U`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[smooth_manifold_atlas; MTR_ATLAS_IN] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    SUBGOAL_THEN
     `open_in top (U:A->bool) /\ open (IMAGE (phi:A->real^N) U) /\
      homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U)) phi`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\
                  IMAGE (f':B->A) (IMAGE (f:A->B) U) = U` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((phi:A->real^N) o (f':B->A)) (IMAGE (f:A->B) U) = IMAGE phi U`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:A->B`; `top:A topology`; `top':B topology`; `U:A->bool`]
        HOMEOMORPHIC_MAP_OPENNESS) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f':B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?(U:A->bool) (phi:A->real^N). (U,phi) IN atlas /\ (f':B->A) y IN U`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (f:A->B) U`; `(phi:A->real^N) o (f':B->A)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(f':B->A) y` THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`V1:B->bool`; `psi1:B->real^N`;
                         `V2:B->bool`; `psi2:B->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))
     (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    SUBGOAL_THEN
     `?g:real^N->real^N.
        smooth_map_on (IMAGE (phi1:A->real^N) (U1 INTER U2)) g /\
        !x. x IN U1 INTER U2 ==> g(phi1 x) = (phi2:A->real^N) x`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `g:real^N->real^N` THEN
    SUBGOAL_THEN `(U1:A->bool) SUBSET topspace top /\ U2 SUBSET topspace top`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE ((phi1:A->real^N) o (f':B->A)) (IMAGE (f:A->B) U1 INTER IMAGE f U2) =
      IMAGE phi1 (U1 INTER U2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; o_THM] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; o_THM] THEN X_GEN_TAC `y:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x1:A` STRIP_ASSUME_TAC) (X_CHOOSE_THEN `x2:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x1:A) = x2` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[IN_INTER] THEN ASM SET_TAC[]]);;

let MTR_DIFFEO = prove
 (`!(top:A topology) (top':B topology) (atlas:((A->bool)#(A->real^N))->bool) f f'.
     smooth_manifold_atlas top atlas /\ homeomorphic_maps (top,top') (f,f')
     ==> mfd_diffeo top atlas (topspace top)
                    top' (IMAGE (\c. IMAGE f (FST c),SND c o f') atlas) (topspace top')
                    f f'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `atlas' = IMAGE (\c. IMAGE (f:A->B) (FST c),SND c o (f':B->A))
                             (atlas:((A->bool)#(A->real^N))->bool)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "atlas'" THEN MATCH_MP_TAC MTR_SMOOTH_ATLAS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  SUBGOAL_THEN `IMAGE (f:A->B) (topspace top) SUBSET topspace top' /\
                IMAGE (f':B->A) (topspace top') SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE]; ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`] MFD_SMOOTH_MAP_ID) THEN
  ASM_REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM] THEN
  DISCH_THEN(LABEL_TAC "id") THEN EXPAND_TAC "atlas'" THEN
  REWRITE_TAC[MTR_ATLAS_IN] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:B->bool`; `psi:B->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `phi':A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    REWRITE_TAC[FST; SND] THEN
    REMOVE_THEN "id" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`;
                                      `U':A->bool`; `phi':A->real^N`]) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ U' SUBSET topspace top`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{x | x IN U INTER topspace top /\ (f:A->B) x IN IMAGE f U'} =
      {x | x IN U INTER topspace top /\ x IN U'}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(phi':A->real^N) o (\x:A. x) o chart_inv (U:A->bool,phi:A->real^N)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`; `U'':A->bool`; `phi'':A->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))
      ASSUME_TAC) THEN
    REWRITE_TAC[FST; SND] THEN
    REMOVE_THEN "id" (MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`;
                                      `U'':A->bool`; `phi'':A->real^N`]) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace top /\ U'' SUBSET topspace top`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE ((phi:A->real^N) o (f':B->A))
        {y | y IN IMAGE (f:A->B) U INTER topspace top' /\ f' y IN U''} =
      IMAGE phi {x | x IN U INTER topspace top /\ x IN U''}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(phi'':A->real^N) o (\x:A. x) o chart_inv (U:A->bool,phi:A->real^N)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `IMAGE (f:A->B) U`; `(phi:A->real^N) o (f':B->A)`] CHART_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "atlas'" THEN REWRITE_TAC[MTR_ATLAS_IN] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:A->B) x` o CONJUNCT1) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM; SUBSET]]);;

let MTR_DIFFEO_INV = prove
 (`!(top:A topology) (top':B topology) (atlas:((A->bool)#(A->real^N))->bool) f f'.
     smooth_manifold_atlas top atlas /\ homeomorphic_maps (top,top') (f,f')
     ==> mfd_diffeo top' (IMAGE (\c. IMAGE f (FST c),SND c o f') atlas) (topspace top')
                    top atlas (topspace top) f' f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
  MATCH_MP_TAC MTR_DIFFEO THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The pullback metric along the inverse map is a Riemannian metric for      *)
(* which f is an isometry; isometries are insensitive to changes of the      *)
(* target metric off the space; curvature norms, least sectional curvatures, *)
(* balls and rfs_normalized transfer along isometries.                       *)
(* ------------------------------------------------------------------------- *)

let MTR_PULLBACK_ISOMETRY = prove
 (`!(top:A topology) atlas (top':B topology) atlas' f f' (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f' /\
     riemannian_metric atlas g
     ==> riemannian_metric atlas' (mfd_pullback_metric atlas' atlas f' g) /\
         mfd_isometry (top,atlas) g (top',atlas') (mfd_pullback_metric atlas' atlas f' g)
                      f f'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MFD_DIFFEO_SYM) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `top:A topology`; `f:A->B`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_ISOMETRY_INVERSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_ISOMETRY_PULLBACK THEN ASM_REWRITE_TAC[]]);;

let MTR_ISOMETRY_CONG = prove
 (`!(top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g1 g2 f f'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     mfd_isometry (top,atlas) g (top',atlas') g1 f f' /\
     (!y. y IN topspace top' ==> g2 y = g1 y)
     ==> mfd_isometry (top,atlas) g (top',atlas') g2 f f'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_isometry] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`] THEN
  STRIP_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`]) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c':(B->bool)#(B->real^N)`; `g2:B->real^N^N`; `g1:B->real^N^N`]
                PDE_METRIC_LOCAL_CONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
    `(SND(c':(B->bool)#(B->real^N)) o (f:A->B) o chart_inv (c:(A->bool)#(A->real^N)))
     (SND c x)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let MTR_ISOMETRY_SECTIONAL_SET = prove
 (`!(top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g' f f' x
    (q:real->real).
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
     ==> {q(mfd_sectional atlas g x u v) | u,v | ~collinear {vec 0,u,v}} =
         {q(mfd_sectional atlas' g' (f x) u v) | u,v | ~collinear {vec 0,u,v}}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`]
    MFD_ISOMETRY_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g:A->real^N^N`; `g':B->real^N^N`; `f:A->B`; `f':B->A`; `x:A`]
    MFDR_ISOMETRY_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `t':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `h = SND(chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)) o f o
                  chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)` THEN
  ABBREV_TAC `y0 = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x` THEN
  MP_TAC(ISPECL [`t':real^N->bool`; `t:real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y0:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative (h:real^N->real^N) (at y0)` THEN
  SUBGOAL_THEN `?K:real^N->real^N. (!v. K((D:real^N->real^N) v) = v) /\ (!w. D(K w) = w)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^N->real^N)(vec 0) = vec 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!w1 w2:real^N. (D:real^N->real^N) w1 = D w2 ==> w1 = w2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^N. ~collinear {vec 0,u,v} ==> ~collinear {vec 0,(D:real^N->real^N) u,D v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`D:real^N->real^N`; `{vec 0:real^N,u,v}`] COLLINEAR_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^N. ~collinear {vec 0,u,v} ==> ~collinear {vec 0,(K:real^N->real^N) u,K v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`D:real^N->real^N`; `{vec 0:real^N,(K:real^N->real^N) u,K v}`]
      COLLINEAR_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `s:real` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(D:real^N->real^N) u`; `(D:real^N->real^N) v`] THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(K:real^N->real^N) u`; `(K:real^N->real^N) v`] THEN
    ASM_SIMP_TAC[]]);;

let MTR_ISOMETRY_RM_NORM = prove
 (`!(top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g' f f' x.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
     ==> mfd_rm_norm atlas' g' (f x) = mfd_rm_norm atlas g x /\
         mfd_sec_min atlas' g' (f x) = mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm; mfd_sec_min] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `f:A->B`; `f':B->A`; `x:A`; `abs:real->real`]
      MTR_ISOMETRY_SECTIONAL_SET) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                   `f:A->B`; `f':B->A`; `x:A`; `\s:real. s`]
      MTR_ISOMETRY_SECTIONAL_SET)) THEN
    ASM_REWRITE_TAC[]]);;

let MTR_ISOMETRY_BALL = prove
 (`!(top:A topology) atlas (g:A->real^N^N) (top':B topology) atlas' g' f f' x r.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\ x IN topspace top
     ==> mfd_ball (top',atlas') g' (f x) r = IMAGE f (mfd_ball (top,atlas) g x r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`] MFD_DIST_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_ball; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top'` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `(f':B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `(f':B->A) y` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `(f':B->A) y`]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:A->B) ((f':B->A) y) = y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `z:A`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_MESON_TAC[]]);;

let MTR_ISOMETRY_NORMALIZED = prove
 (`!(top:A topology) atlas (g:A->real^3^3) (top':B topology) atlas' g' f f'.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
     rfs_normalized (top,atlas) g
     ==> rfs_normalized (top',atlas') g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_normalized] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN CONJ_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f':B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                   `f:A->B`; `f':B->A`; `(f':B->A) y`] MTR_ISOMETRY_RM_NORM) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`y:B`; `r:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f':B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(f':B->A) y`; `r:real`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `mfd_ball (top',atlas') (g':B->real^3^3) y r =
      IMAGE (f:A->B) (mfd_ball (top,atlas) (g:A->real^3^3) ((f':B->A) y) r)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                     `f:A->B`; `f':B->A`; `(f':B->A) y`; `r:real`] MTR_ISOMETRY_BALL) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_ball (top,atlas) (g:A->real^3^3) ((f':B->A) y) r SUBSET topspace top`
    ASSUME_TAC THENL
     [REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                   `f:A->B`; `f':B->A`;
                   `mfd_ball (top,atlas) (g:A->real^3^3) ((f':B->A) y) r`; `v:real`]
      MFD_HAS_VOLUME_ISOMETRY) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Orientability of the image atlas, and the transport package: along an     *)
(* injection f with left inverse f' a smooth manifold with a Riemannian      *)
(* metric goes to the image topology and atlas, f and f' are inverse         *)
(* diffeomorphisms, f is an isometry onto the pullback metric along f', and  *)
(* Hausdorffness, compactness, simple connectivity and orientability are     *)
(* preserved.                                                                *)
(* ------------------------------------------------------------------------- *)

let MTR_ORIENTED_ATLAS = prove
 (`!(top:A topology) (top':B topology) (O:((A->bool)#(A->real^N))->bool) f f'.
     smooth_manifold_atlas top O /\ homeomorphic_maps (top,top') (f,f') /\
     mfd_oriented_atlas O
     ==> mfd_oriented_atlas (IMAGE (\c. IMAGE f (FST c),SND c o f') O)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `O' = IMAGE (\c. IMAGE (f:A->B) (FST c),SND c o (f':B->A))
                         (O:((A->bool)#(A->real^N))->bool)` THEN
  SUBGOAL_THEN `smooth_manifold_atlas top' (O':((B->bool)#(B->real^N))->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "O'" THEN MATCH_MP_TAC MTR_SMOOTH_ATLAS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  UNDISCH_TAC `mfd_oriented_atlas (O:((A->bool)#(A->real^N))->bool)` THEN
  REWRITE_TAC[mfd_oriented_atlas; FORALL_PAIR_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`V1:B->bool`; `psi1:B->real^N`; `V2:B->bool`; `psi2:B->real^N`;
                       `y:B`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `?U1 phi1. (U1,phi1) IN (O:((A->bool)#(A->real^N))->bool) /\
              V1 = IMAGE (f:A->B) U1 /\ psi1 = phi1 o (f':B->A)`
  (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST_ALL_TAC)))) THENL
   [ASM_MESON_TAC[MTR_ATLAS_IN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?U2 phi2. (U2,phi2) IN (O:((A->bool)#(A->real^N))->bool) /\
              V2 = IMAGE (f:A->B) U2 /\ psi2 = phi2 o (f':B->A)`
  (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST_ALL_TAC)))) THENL
   [ASM_MESON_TAC[MTR_ATLAS_IN]; ALL_TAC] THEN
  REWRITE_TAC[FST; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `x2:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(U1:A->bool) SUBSET topspace top /\ U2 SUBSET topspace top /\
                open (IMAGE (phi1:A->real^N) U1)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x2:A) = x` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(f:A->B) x`)) THEN
  SUBGOAL_THEN
   `chart_jac (IMAGE (f:A->B) U1,(phi1:A->real^N) o (f':B->A))
              (IMAGE f U2,(phi2:A->real^N) o f') (f x) =
    chart_jac (U1,phi1) (U2,phi2) x`
  SUBST1_TAC THENL
   [REWRITE_TAC[chart_jac; chart_trans; o_THM] THEN
    SUBGOAL_THEN `(f':B->A) ((f:A->B) x) = x` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `IMAGE (phi1:A->real^N) U1` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `O:((A->bool)#(A->real^N))->bool`;
                   `U1:A->bool`; `phi1:A->real^N`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `O':((B->bool)#(B->real^N))->bool`;
                   `IMAGE (f:A->B) U1`; `(phi1:A->real^N) o (f':B->A)`] CHART_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "O'" THEN REWRITE_TAC[MTR_ATLAS_IN] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:A->B) z` o CONJUNCT1) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM] THEN
    SUBGOAL_THEN `(f':B->A) ((f:A->B) z) = z` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(f':B->A) ((f:A->B) z) = z` (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]);;

let MTR_ORIENTABLE = prove
 (`!(top:A topology) (top':B topology) (atlas:((A->bool)#(A->real^N))->bool) f f'.
     smooth_manifold_atlas top atlas /\ homeomorphic_maps (top,top') (f,f') /\
     mfd_orientable top atlas
     ==> mfd_orientable top' (IMAGE (\c. IMAGE f (FST c),SND c o f') atlas)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_orientable] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `O:((A->bool)#(A->real^N))->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (\c. IMAGE (f:A->B) (FST c),SND c o (f':B->A))
                    (O:((A->bool)#(A->real^N))->bool)` THEN
  REWRITE_TAC[GSYM IMAGE_UNION] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MTR_SMOOTH_ATLAS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MTR_SMOOTH_ATLAS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MTR_ORIENTED_ATLAS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`] THEN
    ASM_REWRITE_TAC[]]);;

let MTR_MANIFOLD = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
    (f:A->B) f'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. x IN topspace top ==> f'(f x) = x)
     ==> ?top' atlas'.
           topspace top' = IMAGE f (topspace top) /\
           homeomorphic_maps (top,top') (f,f') /\
           smooth_manifold_atlas top' atlas' /\
           mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f' /\
           mfd_diffeo top' atlas' (topspace top') top atlas (topspace top) f' f /\
           (hausdorff_space top' <=> hausdorff_space top) /\
           (compact_space top' <=> compact_space top) /\
           (simply_connected_space top' <=> simply_connected_space top) /\
           (mfd_orientable top atlas ==> mfd_orientable top' atlas') /\
           riemannian_metric atlas' (mfd_pullback_metric atlas' atlas f' g) /\
           mfd_isometry (top,atlas) g (top',atlas')
                        (mfd_pullback_metric atlas' atlas f' g) f f'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->B`; `f':B->A`] MTR_TOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `top':B topology` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `atlas' = IMAGE (\c. IMAGE (f:A->B) (FST c),SND c o (f':B->A))
                             (atlas:((A->bool)#(A->real^N))->bool)` THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "atlas'" THEN MATCH_MP_TAC MTR_SMOOTH_ATLAS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
               top' (atlas':((B->bool)#(B->real^N))->bool) (topspace top') f f'`
  ASSUME_TAC THENL
   [EXPAND_TAC "atlas'" THEN MATCH_MP_TAC MTR_DIFFEO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(top:A topology) homeomorphic_space (top':B topology)` ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic_space] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_HAUSDORFF_SPACE];
    ASM_MESON_TAC[HOMEOMORPHIC_COMPACT_SPACE];
    ASM_MESON_TAC[SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC];
    DISCH_TAC THEN EXPAND_TAC "atlas'" THEN MATCH_MP_TAC MTR_ORIENTABLE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `f':B->A`; `g:A->real^N^N`] MTR_PULLBACK_ISOMETRY) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `f':B->A`; `g:A->real^N^N`] MTR_PULLBACK_ISOMETRY) THEN
    ASM_SIMP_TAC[]]);;

