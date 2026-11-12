(* ========================================================================= *)
(* pc_mfd_diff: differentials of maps between smooth manifolds in preferred  *)
(* coordinates (used by the geodesics layer and by the smooth topology       *)
(* files).  Atlases, charts and smooth maps are those of pc_mfd_base.ml and  *)
(* pc_mfd_maps.ml.                                                           *)
(*                                                                           *)
(* The definition and its form for the identity atlas of an open set of      *)
(* real^N; smooth manifolds are locally path connected                       *)
(* (GEO_MANIFOLD_LOCALLY_PATH_CONNECTED); smoothness of maps is local; the   *)
(* inverse function theorem in charts; a bijective smooth map with           *)
(* invertible differentials is a diffeomorphism                              *)
(* (GEO_BIJECTIVE_LOCAL_DIFFEO).  The general topology unit pc_top_cover     *)
(* supplies TOPC_CONTINUOUS_MAP_LOCAL.                                       *)
(* ========================================================================= *)

needs "src/pc_mfd_maps.ml";;
needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* The differential of f at x in preferred coordinates on both sides (for   *)
(* the identity atlas open_set_atlas (:real^N) of real^N this is the        *)
(* Frechet derivative, MFD_DIFFERENTIAL_OPEN_SET_ATLAS).                     *)

let mfd_differential = new_definition
 `mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^M))->bool) (f:A->B) (x:A) =
    frechet_derivative
      (\y. SND(chart_at atlas' (f x)) (f(chart_inv (chart_at atlas x) y)))
      (at (SND(chart_at atlas x) x))`;;

let MFDD_OPEN_SET_CHART_AT = prove
 (`!U (x:real^N). x IN U ==> chart_at (open_set_atlas U) x = (U,(\x. x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_at; open_set_atlas; IN_SING] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST] THEN ASM_MESON_TAC[]);;

let MFD_DIFFERENTIAL_OPEN_SET_ATLAS = prove
 (`!(atlas:((B->bool)#(B->real^M))->bool) (f:real^N->B) v.
        mfd_differential (open_set_atlas (:real^N)) atlas f v =
        frechet_derivative (\y. SND(chart_at atlas (f v)) (f y)) (at v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_differential] THEN
  SIMP_TAC[MFDD_OPEN_SET_CHART_AT; IN_UNIV] THEN
  SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV] THEN REWRITE_TAC[ETA_AX]);;

(* ========================================================================= *)
(* Smooth manifolds are locally path connected; smoothness of maps is local; *)
(* a bijective smooth map with invertible differentials is a diffeomorphism  *)
(* (the smooth inverse function theorem SMOOTH_INVERSE_FUNCTION_THEOREM of   *)
(* src/ns_smooth.ml in charts).                                              *)
(* ========================================================================= *)

(* Manifolds are locally path connected: charts are homeomorphisms onto    *)
(* open subsets of real^N.                                                  *)

let GEO_MANIFOLD_LOCALLY_PATH_CONNECTED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas ==> locally_path_connected_space top`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE] THEN
  MAP_EVERY X_GEN_TAC [`v:A->bool`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `locally_path_connected_space (subtopology top (U:A->bool))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                   `subtopology euclidean (IMAGE (phi:A->real^N) U)`]
      HOMEOMORPHIC_LOCALLY_PATH_CONNECTED_SPACE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[homeomorphic_space] THEN ASM_MESON_TAC[HOMEOMORPHIC_MAP_MAPS];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE_SUBTOPOLOGY_EUCLIDEAN] THEN
      MATCH_MP_TAC OPEN_IMP_LOCALLY_PATH_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE] THEN
  DISCH_THEN(MP_TAC o SPECL [`v INTER (U:A->bool)`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u:A->bool` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY];
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* Chart inverses are continuous (the same fact as GRGD_CHART_INV_CONTINUOUS *)
(* of pc_grg_dist, which this unit does not load).                          *)

let MFDD_CHART_INV_CONTINUOUS = prove
 (`!top atlas (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> continuous_map (subtopology euclidean (IMAGE (SND c) (FST c)),top)
                           (chart_inv c)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
  PURE_REWRITE_TAC[FST; SND] THEN
  SPEC_TAC(`SND(c:(A->bool)#(A->real^N))`,`phi:A->real^N`) THEN
  SPEC_TAC(`FST(c:(A->bool)#(A->real^N))`,`U:A->bool`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:real^N->A` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) (phi x) = x`
    SUBST1_TAC THENL
     [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[]]);;

(* Charts are continuous into real^N on their domains. *)

let MFDD_CHART_CONTINUOUS = prove
 (`!top atlas (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> continuous_map (subtopology top (FST c),euclidean) (SND c)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
  PURE_REWRITE_TAC[FST; SND] THEN
  SPEC_TAC(`SND(c:(A->bool)#(A->real^N))`,`phi:A->real^N`) THEN
  SPEC_TAC(`FST(c:(A->bool)#(A->real^N))`,`U:A->bool`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o last o CONJUNCTS) THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]);;

(* Smoothness of maps depends only on the values on the set. *)

let MFDD_SMOOTH_MAP_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool)
    (atlas':((B->bool)#(B->real^M))->bool) W (f:A->B) g.
        smooth_manifold_atlas top atlas /\
        (!x. x IN W ==> f x = g x) /\ mfd_smooth_map atlas atlas' W f
        ==> mfd_smooth_map atlas atlas' W g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN FST c INTER W /\ (g:A->B) x IN FST (c':(B->bool)#(B->real^M))} =
    {x | x IN FST (c:(A->bool)#(A->real^N)) INTER W /\ (f:A->B) x IN FST c'}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `SND (c':(B->bool)#(B->real^M)) o (f:A->B) o
              chart_inv (c:(A->bool)#(A->real^N))` THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[]);;

(* Smoothness of maps is local. *)

let MFDD_SMOOTH_MAP_LOCAL = prove
 (`!top atlas top' atlas' W (f:A->B).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        (!x. x IN W
             ==> ?w. open_in top w /\ x IN w /\ w SUBSET W /\
                     mfd_smooth_map atlas atlas' w f)
        ==> mfd_smooth_map atlas atlas' W f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "loc"))))) THEN
  REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC
   [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN W`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                {z | z IN FST c INTER w /\
                     (f:A->B) z IN FST (c':(B->bool)#(B->real^M))}` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                   `w:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^M))->bool) w (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* The inverse function theorem in a pair of charts: near a point where     *)
(* the chart representative F = SND c' o f o chart_inv c has an invertible  *)
(* derivative, a smooth G on an open set u inverts it, and f maps the       *)
(* points chart_inv c (G (SND c' y)) back to y.                              *)

let MFDD_LOCAL_INVERSE_CHART = prove
 (`!top atlas top' atlas' (f:A->B) c c' x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
        continuous_map (top,top') f /\
        mfd_smooth_map atlas atlas' (topspace top) f /\
        c IN atlas /\ c' IN atlas' /\ x IN topspace top /\ x IN FST c /\
        f x IN FST c' /\
        ~(det(matrix(frechet_derivative (SND c' o f o chart_inv c)
                                        (at (SND c x)))) = &0)
        ==> ?u G. open u /\ smooth_map_on u G /\
                  SND c' (f x) IN u /\ G(SND c' (f x)) = SND c x /\
                  !y. y IN FST c' /\ SND c' y IN u
                      ==> chart_inv c (G(SND c' y)) IN FST c /\
                          chart_inv c (G(SND c' y)) IN topspace top /\
                          SND c (chart_inv c (G(SND c' y))) = G(SND c' y) /\
                          f(chart_inv c (G(SND c' y))) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c':(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N)))
                    {z | z IN FST c INTER topspace top /\
                         (f:A->B) z IN FST (c':(B->bool)#(B->real^N))}` THEN
  SUBGOAL_THEN `open (D:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                   `topspace top:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D (SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
                     chart_inv (c:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^N))->bool) (topspace top) (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) x IN D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
                  chart_inv (c:(A->bool)#(A->real^N))`;
                 `D:real^N->bool`; `SND (c:(A->bool)#(A->real^N)) x`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `G:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[o_THM] o
    GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `G:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND (c':(B->bool)#(B->real^N)) ((f:A->B) x) IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `(SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
                  chart_inv (c:(A->bool)#(A->real^N))) (SND c x) IN u` THEN
    ASM_REWRITE_TAC[o_THM];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MP_TAC(MATCH_MP
     (ASSUME `!x. x IN t
                  ==> (G:real^N->real^N)
                        (SND (c':(B->bool)#(B->real^N))
                          ((f:A->B) (chart_inv (c:(A->bool)#(A->real^N)) x))) = x`)
     (ASSUME `SND (c:(A->bool)#(A->real^N)) x IN t`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^N->real^N)(SND (c':(B->bool)#(B->real^N)) y) IN D`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `chart_inv (c:(A->bool)#(A->real^N))
      ((G:real^N->real^N)(SND (c':(B->bool)#(B->real^N)) y)) = z`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND (c':(B->bool)#(B->real^N)) ((f:A->B) z) = SND c' y`
  ASSUME_TAC THENL
   [MP_TAC(MATCH_MP
     (ASSUME `!y. y IN u
                  ==> SND (c':(B->bool)#(B->real^N))
                        ((f:A->B) (chart_inv (c:(A->bool)#(A->real^N))
                                     ((G:real^N->real^N) y))) = y`)
     (ASSUME `SND (c':(B->bool)#(B->real^N)) y IN u`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
  MAP_EVERY EXISTS_TAC
   [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
    `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* A smooth map with invertible differential at x has a continuous smooth   *)
(* local right inverse k near f x with k(f x) = x.                           *)

let MFDD_LOCAL_INVERSE = prove
 (`!top atlas top' atlas' (f:A->B) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
        continuous_map (top,top') f /\
        mfd_smooth_map atlas atlas' (topspace top) f /\
        x IN topspace top /\
        ~(det(matrix(mfd_differential atlas atlas' f x)) = &0)
        ==> ?w k. open_in top' w /\ f x IN w /\ k(f x) = x /\
                  continuous_map (subtopology top' w,top) k /\
                  (!y. y IN w ==> k y IN topspace top /\ f(k y) = y) /\
                  mfd_smooth_map atlas' atlas w k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) x` THEN
  ABBREV_TAC `c' = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)` THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN atlas /\ x IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':(B->bool)#(B->real^N)) IN atlas' /\ (f:A->B) x IN FST c'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                 `x:A`] MFDD_LOCAL_INVERSE_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(det(matrix(mfd_differential
                   (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x)) = &0)` THEN
    ASM_REWRITE_TAC[mfd_differential; o_DEF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `G:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "inv"))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c':(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the open set w and the continuity of k *)
  SUBGOAL_THEN
   `open_in top' {y | y IN FST (c':(B->bool)#(B->real^N)) /\
                      SND c' y IN (u:real^N->bool)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN] THEN MATCH_MP_TAC MFDD_CHART_CONTINUOUS THEN
    EXISTS_TAC `atlas':((B->bool)#(B->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
      (subtopology top' {y | y IN FST (c':(B->bool)#(B->real^N)) /\
                             SND c' y IN (u:real^N->bool)},top)
      (chart_inv (c:(A->bool)#(A->real^N)) o (G:real^N->real^N) o SND c')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean
                  (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MFDD_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean
                  (IMAGE (SND (c':(B->bool)#(B->real^N)))
                         {y | y IN FST c' /\ SND c' y IN (u:real^N->bool)})` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `FST (c':(B->bool)#(B->real^N))` THEN
        CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
        MATCH_MP_TAC MFDD_CHART_CONTINUOUS THEN
        EXISTS_TAC `atlas':((B->bool)#(B->real^N))->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `y:B` THEN DISCH_TAC THEN
        USE_THEN "inv" (fun th -> MP_TAC(MATCH_MP th (ASSUME
          `(y:B) IN FST (c':(B->bool)#(B->real^N)) /\
           SND c' y IN (u:real^N->bool)`))) THEN
        STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N))
                      ((G:real^N->real^N) (SND (c':(B->bool)#(B->real^N)) y))` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `{y | y IN FST (c':(B->bool)#(B->real^N)) /\
                   SND c' y IN (u:real^N->bool)}` THEN
  EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) o (G:real^N->real^N) o
              SND (c':(B->bool)#(B->real^N))` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "inv" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(y:B) IN FST (c':(B->bool)#(B->real^N)) /\
       SND c' y IN (u:real^N->bool)`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* smoothness: in charts, k is a composite of transition maps and G *)
  REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC
   [`c1:(B->bool)#(B->real^N)`; `c2:(A->bool)#(A->real^N)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `SND (c2:(A->bool)#(A->real^N)) o
    (chart_inv (c:(A->bool)#(A->real^N)) o (G:real^N->real^N) o
     SND (c':(B->bool)#(B->real^N))) o
    chart_inv (c1:(B->bool)#(B->real^N)) =
    chart_trans c c2 o G o chart_trans c1 c'`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c1:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `E = IMAGE (SND (c1:(B->bool)#(B->real^N)))
          {x | x IN FST c1 INTER
                    {y | y IN FST (c':(B->bool)#(B->real^N)) /\
                         SND c' y IN (u:real^N->bool)} /\
               (chart_inv (c:(A->bool)#(A->real^N)) o (G:real^N->real^N) o SND c') x
               IN FST (c2:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (E:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c1:(B->bool)#(B->real^N)`; `c2:(A->bool)#(A->real^N)`;
                   `{y | y IN FST (c':(B->bool)#(B->real^N)) /\
                         SND c' y IN (u:real^N->bool)}`;
                   `chart_inv (c:(A->bool)#(A->real^N)) o (G:real^N->real^N) o
                    SND (c':(B->bool)#(B->real^N))`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN E
        ==> ?y. y IN FST (c1:(B->bool)#(B->real^N)) /\
                y IN FST (c':(B->bool)#(B->real^N)) /\
                SND c' y IN (u:real^N->bool) /\
                chart_inv (c:(A->bool)#(A->real^N)) ((G:real^N->real^N) (SND c' y))
                IN FST (c2:(A->bool)#(A->real^N)) /\
                z = SND c1 y`
  (LABEL_TAC "E") THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN FST (c1:(B->bool)#(B->real^N))
        ==> chart_trans c1 (c':(B->bool)#(B->real^N)) (SND c1 y) = SND c' y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                    (FST c INTER FST (c2:(A->bool)#(A->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST (c:(A->bool)#(A->real^N))`; `SND (c:(A->bool)#(A->real^N))`;
                   `FST (c2:(A->bool)#(A->real^N))`; `SND (c2:(A->bool)#(A->real^N))`]
      CHART_OVERLAP_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "E" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^N) IN E`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    USE_THEN "inv" (fun th -> MP_TAC(MATCH_MP th (CONJ
      (ASSUME `(y:B) IN FST (c':(B->bool)#(B->real^N))`)
      (ASSUME `SND (c':(B->bool)#(B->real^N)) y IN (u:real^N->bool)`)))) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N))
                  ((G:real^N->real^N) (SND (c':(B->bool)#(B->real^N)) y))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      USE_THEN "E" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^N) IN E`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N)))
                        (FST c1 INTER FST (c':(B->bool)#(B->real^N)))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        USE_THEN "E" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^N) IN E`))) THEN
        DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_INTER];
        MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                       `FST (c1:(B->bool)#(B->real^N))`;
                       `SND (c1:(B->bool)#(B->real^N))`;
                       `FST (c':(B->bool)#(B->real^N))`;
                       `SND (c':(B->bool)#(B->real^N))`] CHART_TRANS_SMOOTH) THEN
        ASM_REWRITE_TAC[PAIR]]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST (c:(A->bool)#(A->real^N))`; `SND (c:(A->bool)#(A->real^N))`;
                   `FST (c2:(A->bool)#(A->real^N))`; `SND (c2:(A->bool)#(A->real^N))`]
      CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR]]);;

(* A bijective smooth map with invertible differentials everywhere is a     *)
(* diffeomorphism.                                                          *)

let GEO_BIJECTIVE_LOCAL_DIFFEO = prove
 (`!top atlas top' atlas' (f:A->B).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^N))->bool) /\
        continuous_map (top,top') f /\
        mfd_smooth_map atlas atlas' (topspace top) f /\
        IMAGE f (topspace top) = topspace top' /\
        (!x y. x IN topspace top /\ y IN topspace top /\ f x = f y ==> x = y) /\
        (!x. x IN topspace top
             ==> ~(det(matrix(mfd_differential atlas atlas' f x)) = &0))
        ==> ?f'. mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y. ?x. y IN topspace top' ==> x IN topspace top /\ (f:A->B) x = y`
  MP_TAC THENL
   [X_GEN_TAC `y:B` THEN ASM_CASES_TAC `(y:B) IN topspace top'` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:A->B) (topspace top) = topspace top'` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM]] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN EXISTS_TAC `g:B->A` THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> (f:A->B) x IN topspace top'`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> (g:B->A)((f:A->B) x) = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN topspace top /\ y IN topspace top /\
                                (f:A->B) x = f y ==> x = y`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* locally, g is a continuous smooth local inverse *)
  SUBGOAL_THEN
   `!y. y IN topspace top'
        ==> ?w. open_in top' w /\ y IN w /\
                continuous_map (subtopology top' w,top) (g:B->A) /\
                mfd_smooth_map (atlas':((B->bool)#(B->real^N))->bool)
                               (atlas:((A->bool)#(A->real^N))->bool) w g`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `(g:B->A) y`] MFDD_LOCAL_INVERSE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:B->bool` (X_CHOOSE_THEN `k:B->A`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(w:B->bool) SUBSET topspace top'` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `!z:B. z IN w ==> (k:B->A) z = g z` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN topspace top /\ y IN topspace top /\
                                  (f:A->B) x = f y ==> x = y`) (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `w:B->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `k:B->A` THEN
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
      MATCH_MP_TAC MFDD_SMOOTH_MAP_EQ THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `k:B->A`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top',top) (g:B->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:B) IN topspace top'`))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE;
              homeomorphic_maps] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `top:A topology`] THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:B) IN topspace top'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:B->bool` THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]);;

