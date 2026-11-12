(* ========================================================================= *)
(* pc_mfd_base: charts of smooth manifolds.  Chart inverses, preferred       *)
(* charts, images of open sets, transition maps, their smoothness and their  *)
(* derivatives (chain rule, identity, inverse).  Atlases are those of        *)
(* poincare_statement.ml (smooth_manifold_atlas).                            *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* The inverse of a chart (U,phi) on its image. *)

let chart_inv = new_definition
 `chart_inv (c:(A->bool)#(A->real^N)) (y:real^N) =
    @x. x IN FST c /\ SND c x = y`;;

(* The preferred chart of an atlas at a point (any chart containing it). *)

let chart_at = new_definition
 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A) =
    @c. c IN atlas /\ x IN FST c`;;

let SMOOTH_MANIFOLD_ATLAS_CHART = prove
 (`!top atlas (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> open_in top U /\ open (IMAGE phi U) /\
            homeomorphic_map (subtopology top U,
                              subtopology euclidean (IMAGE phi U)) phi`,
  REWRITE_TAC[smooth_manifold_atlas] THEN MESON_TAC[]);;

let SMOOTH_MANIFOLD_ATLAS_CHART_INJ = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) x y.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        x IN U /\ y IN U /\ phi x = phi y
        ==> x = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[homeomorphic_map] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM SET_TAC[]);;

let CHART_INV = prove
 (`!top atlas (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> (!x. x IN U ==> chart_inv (U,phi) (phi x) = x) /\
            (!y. y IN IMAGE phi U
                 ==> chart_inv (U,phi) y IN U /\
                     phi(chart_inv (U,phi) y) = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[chart_inv] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `z:A` THEN BETA_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `U:A->bool`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\z:A. z IN U /\ (phi:A->real^N) z = phi x`; `x:A`]
                  SELECT_AX) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[]]);;

let CHART_AT = prove
 (`!top atlas (x:A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        x IN topspace top
        ==> chart_at atlas x IN atlas /\ x IN FST(chart_at atlas x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[chart_at] THEN
  FIRST_X_ASSUM(MP_TAC o el 1 o CONJUNCTS o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\c:(A->bool)#(A->real^N). c IN atlas /\ x IN FST c`;
                 `(U:A->bool,phi:A->real^N)`] SELECT_AX) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[]);;

(* Images of open subsets of a chart domain are open. *)

let CHART_IMAGE_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        open_in top W /\ W SUBSET U
        ==> open (IMAGE phi W)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_OPEN_MAP) THEN
  REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]);;

let CHART_OVERLAP_IMAGE_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> open (IMAGE phi (U INTER V))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
  ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]);;

(* Transition maps between charts, and their smoothness. *)

let chart_trans = new_definition
 `chart_trans (c:(A->bool)#(A->real^N)) (c':(A->bool)#(A->real^N)) =
    \y. SND c' (chart_inv c y)`;;

let CHART_TRANS_SMOOTH = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> smooth_map_on (IMAGE phi (U INTER V))
                          (chart_trans (U,phi) (V,psi))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `g:real^N->real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; chart_trans] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[]);;

(* The derivative of a transition map at the chart point of x. *)

let chart_jac = new_definition
 `chart_jac (c:(A->bool)#(A->real^N)) (c':(A->bool)#(A->real^N)) (x:A) =
    frechet_derivative (chart_trans c c') (at (SND c x))`;;

let CHART_TRANS_AT = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ x IN U
        ==> chart_trans (U,phi) (V,psi) (phi x) = psi x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_trans] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_SIMP_TAC[]);;

let CHART_TRANS_HAS_DERIVATIVE = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ x IN U INTER V
        ==> (chart_trans (U,phi) (V,psi) has_derivative
             chart_jac (U,phi) (V,psi) x) (at (phi x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_jac; SND] THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  ASM_MESON_TAC[CHART_TRANS_SMOOTH; CHART_OVERLAP_IMAGE_OPEN]);;

let CHART_JAC_CHAIN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi W chi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ (W,chi) IN atlas /\ x IN U INTER V INTER W
        ==> chart_jac (V,psi) (W,chi) x o chart_jac (U,phi) (V,psi) x =
            chart_jac (U,phi) (W,chi) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC
   [`chart_trans (U:A->bool,phi:A->real^N) (W,chi)`; `(phi:A->real^N) x`] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC
   [`chart_trans (V:A->bool,psi:A->real^N) (W,chi) o
     chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `IMAGE (phi:A->real^N) (U INTER V INTER W)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    REPEAT(MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC) THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:A` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`] CHART_TRANS_AT) THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `V:A->bool`; `psi:A->real^N`] CHART_TRANS_AT) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                    `x:A`] CHART_TRANS_AT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

let CHART_JAC_SELF = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ x IN U
        ==> chart_jac (U,phi) (U,phi) x = (\h. h)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC
   [`chart_trans (U:A->bool,phi:A->real^N) (U,phi)`; `(phi:A->real^N) x`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `IMAGE (phi:A->real^N) U`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; HAS_DERIVATIVE_ID] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHART_TRANS_AT THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

let CHART_JAC_INVERSE = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ x IN U INTER V
        ==> chart_jac (V,psi) (U,phi) x o chart_jac (U,phi) (V,psi) x =
            (\h. h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `U:A->bool`; `phi:A->real^N`; `x:A`] CHART_JAC_CHAIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC CHART_JAC_SELF THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transition maps are diffeomorphisms between the images of the overlap.    *)
(* ------------------------------------------------------------------------- *)

let CHART_TRANS_DIFFEO = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> diffeomorphism_on (IMAGE phi (U INTER V)) (IMAGE psi (U INTER V))
                              (chart_trans (U,phi) (V,psi))
                              (chart_trans (V,psi) (U,phi))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  SUBGOAL_THEN
   `(!x. x IN U INTER V
         ==> chart_trans (U:A->bool,phi:A->real^N) (V,psi) (phi x) = psi x) /\
    (!x. x IN U INTER V
         ==> chart_trans (V:A->bool,psi:A->real^N) (U,phi) (psi x) = phi x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN];
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    ASM_SIMP_TAC[o_THM];
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    ASM_SIMP_TAC[o_THM];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[CHART_TRANS_SMOOTH];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_MESON_TAC[CHART_TRANS_SMOOTH]]);;

(* ------------------------------------------------------------------------- *)
(* Smooth maps from a manifold to real^K: smooth in every chart.  The        *)
(* existential form is the one used in the main statement                    *)
(* (poincare_statement.ml).                                                  *)
(* ------------------------------------------------------------------------- *)

let mfd_smooth = new_definition
 `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) <=>
    !c. c IN atlas ==> smooth_map_on (IMAGE (SND c) (FST c)) (f o chart_inv c)`;;

let MFD_SMOOTH_ALT = prove
 (`!top atlas (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)
        ==> (mfd_smooth atlas f <=>
             !U phi. (U,phi) IN atlas
                     ==> ?g. smooth_map_on (IMAGE phi U) g /\
                             !x. x IN U ==> g(phi x) = f x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_smooth; FORALL_PAIR_THM; FST; SND] THEN
  EQ_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISCH_TAC THEN
    EXISTS_TAC `(f:A->real^K) o chart_inv (U:A->bool,phi:A->real^N)` THEN
    ASM_SIMP_TAC[o_THM];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^K` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `g:real^N->real^K` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[]]);;

