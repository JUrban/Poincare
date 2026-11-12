(* ========================================================================= *)
(* pc_mfd_maps: smooth maps and diffeomorphisms between (open subsets of)    *)
(* smooth manifolds, smooth parametrizations of open sets of real^N (ball    *)
(* and neck charts), open submanifolds, orientation, functions without       *)
(* critical points, chart representatives of vector fields.  Atlases are     *)
(* those of poincare_statement.ml; charts, chart inverses and transition     *)
(* maps are those of pc_mfd_base.ml; open subsets of real^N carry the        *)
(* identity chart open_set_atlas of pc_mfd_examples.ml.                      *)
(*                                                                           *)
(* First: the definitions.                                                   *)
(* ========================================================================= *)

needs "src/pc_mfd_base.ml";;
needs "src/pc_mfd_examples.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Open annuli in real^N.  S^2 x (a,b) is the annulus exp(a) < |x| < exp(b)  *)
(* via x = exp(s) theta, and the cylinder metric is |dx|^2 / |x|^2 there.    *)
(* ------------------------------------------------------------------------- *)

let annulus = new_definition
 `annulus (r1:real) (r2:real) = {x:real^N | r1 < norm x /\ norm x < r2}`;;

(* ------------------------------------------------------------------------- *)
(* Smooth real^K-valued maps on an open subset W of a manifold (for         *)
(* W = topspace this is mfd_smooth of pc_mfd_base.ml).                       *)
(* ------------------------------------------------------------------------- *)

let mfd_smooth_on = new_definition
 `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool) (f:A->real^K) <=>
    !c. c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c INTER W)) (f o chart_inv c)`;;

(* Smooth maps between manifolds on an open subset W: smooth in charts on    *)
(* both sides (continuity is required separately, e.g. in mfd_diffeo).      *)

let mfd_smooth_map = new_definition
 `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                 (atlas':((B->bool)#(B->real^M))->bool) (W:A->bool) (f:A->B) <=>
    !c c'. c IN atlas /\ c' IN atlas'
           ==> smooth_map_on
                 (IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'})
                 (SND c' o f o chart_inv c)`;;

(* Diffeomorphisms between open subsets W, W' of two manifolds, with         *)
(* inverse g.                                                                *)

let mfd_diffeo = new_definition
 `mfd_diffeo (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool)
             (top':B topology) (atlas':((B->bool)#(B->real^M))->bool) (W':B->bool)
             (f:A->B) (g:B->A) <=>
    open_in top W /\ open_in top' W' /\
    homeomorphic_maps (subtopology top W,subtopology top' W') (f,g) /\
    mfd_smooth_map atlas atlas' W f /\ mfd_smooth_map atlas' atlas W' g`;;

let mfd_diffeomorphic = new_definition
 `mfd_diffeomorphic (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
                    (top':B topology) (atlas':((B->bool)#(B->real^M))->bool) <=>
    ?f g. mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f g`;;

(* ------------------------------------------------------------------------- *)
(* Smooth parametrizations of open sets s of real^N (inverse charts of the   *)
(* maximal atlas), ball charts (s = ball(0,2), core cball(0,1), collar       *)
(* annulus 1 2) and neck charts (s = annulus 1/2 2).                         *)
(* ------------------------------------------------------------------------- *)

let mfd_param = new_definition
 `mfd_param (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
            (s:real^N->bool) (e:real^N->A) <=>
    ?e'. mfd_diffeo euclidean (open_set_atlas (:real^N)) s top atlas (IMAGE e s)
                    e e'`;;

let mfd_ball_chart = new_definition
 `mfd_ball_chart (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
                 (b:real^N->A) <=>
    mfd_param top atlas (ball(vec 0,&2)) b`;;

let mfd_neck_chart = new_definition
 `mfd_neck_chart (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
                 (e:real^N->A) <=>
    mfd_param top atlas (annulus (&1 / &2) (&2)) e`;;

(* Open submanifolds: the restricted atlas. *)

let restrict_atlas = new_definition
 `restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool) =
    {(U INTER W,phi) | (U,phi) IN atlas}`;;

(* ------------------------------------------------------------------------- *)
(* Orientation: oriented atlases (positive Jacobian determinants of all      *)
(* transitions) and orientability (an oriented atlas compatible with the     *)
(* given one).                                                               *)
(* ------------------------------------------------------------------------- *)

let mfd_oriented_atlas = new_definition
 `mfd_oriented_atlas (atlas:((A->bool)#(A->real^N))->bool) <=>
    !c c' x. c IN atlas /\ c' IN atlas /\ x IN FST c INTER FST c'
             ==> &0 < det(matrix(chart_jac c c' x))`;;

let mfd_orientable = new_definition
 `mfd_orientable (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) <=>
    ?atlas'. smooth_manifold_atlas top atlas' /\
             smooth_manifold_atlas top (atlas UNION atlas') /\
             mfd_oriented_atlas atlas'`;;

(* Real functions without critical points on an open set W. *)

let mfd_regular_on = new_definition
 `mfd_regular_on (atlas:((A->bool)#(A->real^N))->bool) (W:A->bool) (f:A->real) <=>
    !c x. c IN atlas /\ x IN FST c INTER W
          ==> ~(frechet_derivative (\y. lift(f(chart_inv c y))) (at (SND c x)) =
                (\h. vec 0))`;;

(* The representative in the chart c of a vector field X, given by its       *)
(* coordinate vectors X x in the preferred charts chart_at atlas x.          *)

let mfd_vrep = new_definition
 `mfd_vrep (atlas:((A->bool)#(A->real^N))->bool) (X:A->real^N)
           (c:(A->bool)#(A->real^N)) =
    \y. chart_jac (chart_at atlas (chart_inv c y)) c (chart_inv c y)
                  (X (chart_inv c y))`;;

(* ------------------------------------------------------------------------- *)
(* Smoothness is local and depends only on the values on the set; charts in  *)
(* pair-free form; smooth maps between open sets of real^N; the link with    *)
(* mfd_smooth; identity and composition of smooth maps.                      *)
(* ------------------------------------------------------------------------- *)

let MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ = prove
 (`!n s (f:real^M->real^N) g.
        (!x. x IN s ==> f x = g x) /\ continuously_differentiable n s f
        ==> continuously_differentiable n s g`,
  INDUCT_TAC THEN REWRITE_TAC[continuously_differentiable] THENL
   [MESON_TAC[CONTINUOUS_ON_EQ];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `f':real^M->real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `&1`] THEN
    ASM_SIMP_TAC[REAL_LT_01]]);;

let SMOOTH_MAP_ON_EQ = prove
 (`!s (f:real^M->real^N) g.
        (!x. x IN s ==> f x = g x) /\ smooth_map_on s f ==> smooth_map_on s g`,
  REWRITE_TAC[smooth_map_on] THEN
  MESON_TAC[MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ]);;

let SMOOTH_MAP_ON_LOCAL = prove
 (`!s (f:real^M->real^N).
        open s /\
        (!x. x IN s ==> ?t. open t /\ x IN t /\ smooth_map_on t f)
        ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`; `f:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s INTER t:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `t:real^M->bool` THEN REWRITE_TAC[INTER_SUBSET] THEN
  ASM_MESON_TAC[smooth_map_on]);;

(* Charts in pair-free form. *)

let MFDM_CHART = prove
 (`!top atlas c:(A->bool)#(A->real^N).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> open_in top (FST c) /\ open (IMAGE (SND c) (FST c)) /\
            (!x. x IN FST c ==> chart_inv c (SND c x) = x) /\
            (!y. y IN IMAGE (SND c) (FST c)
                 ==> chart_inv c y IN FST c /\ SND c (chart_inv c y) = y)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; CHART_INV]);;

let MFDM_CHART_IMAGE_OPEN = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) W.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        open_in top W /\ W SUBSET FST c
        ==> open (IMAGE (SND c) W)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN MESON_TAC[CHART_IMAGE_OPEN]);;

let MFDM_OPEN_IN_PREIMAGE = prove
 (`!top top' W (f:A->B) V.
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        open_in top' V
        ==> open_in top {x | x IN W /\ f x IN V}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:A->B`; `subtopology top (W:A->bool)`; `top':B topology`;
                 `V:B->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topspace top` MP_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; SET_TAC[]]);;

(* The chart domains of a continuous map are open. *)

let MFDM_CHART_DOMAIN_OPEN = prove
 (`!top atlas top' atlas' (c:(A->bool)#(A->real^N)) (c':(B->bool)#(B->real^M))
    W (f:A->B).
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        c IN atlas /\ c' IN atlas' /\
        open_in top W /\ continuous_map (subtopology top W,top') f
        ==> open_in top {x | x IN FST c INTER W /\ f x IN FST c'} /\
            open (IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x | x IN FST c INTER W /\ (f:A->B) x IN FST(c':(B->bool)#(B->real^M))} =
      FST(c:(A->bool)#(A->real^N)) INTER {x | x IN W /\ f x IN FST c'}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top':B topology` THEN
    ASM_MESON_TAC[MFDM_CHART];
    DISCH_TAC THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Open subsets of real^N with the identity chart.                           *)
(* ------------------------------------------------------------------------- *)

let MFDM_CHART_INV_ID = prove
 (`!U (y:real^N). y IN U ==> chart_inv (U,(\x. x)) y = y`,
  REWRITE_TAC[chart_inv; FST; SND] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

let MFD_SMOOTH_MAP_OPEN_SET_ATLAS = prove
 (`!U V W (f:real^M->real^N).
        mfd_smooth_map (open_set_atlas U) (open_set_atlas V) W f <=>
        smooth_map_on {x | x IN U INTER W /\ f x IN V} f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID] THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  SIMP_TAC[IN_ELIM_THM; IN_INTER; o_THM; MFDM_CHART_INV_ID]);;

(* Maps into real^K with the identity chart are the mfd_smooth_on maps. *)

let MFD_SMOOTH_MAP_INTO_EUCLIDEAN = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) W (f:A->real^K).
        mfd_smooth_map atlas (open_set_atlas (:real^K)) W f <=>
        mfd_smooth_on atlas W f`,
  REWRITE_TAC[mfd_smooth_map; mfd_smooth_on; open_set_atlas; IN_SING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[FST; SND; IN_UNIV; SET_RULE `{x:A | x IN s} = s`] THEN
  REWRITE_TAC[o_DEF; ETA_AX]);;

(* The link with mfd_smooth of pc_mfd_base.ml. *)

let MFD_SMOOTH_ON_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K).
        smooth_manifold_atlas top atlas
        ==> (mfd_smooth_on atlas (topspace top) f <=> mfd_smooth atlas f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth_on; mfd_smooth] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `(c:(A->bool)#(A->real^N)) IN atlas` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[SET_RULE `(s:A->bool) INTER t = s <=> s SUBSET t`] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_MESON_TAC[MFDM_CHART]);;

(* Restriction of smooth maps to smaller sets. *)

let MFD_SMOOTH_MAP_SUBSET = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (atlas':((B->bool)#(B->real^M))->bool)
    V W (f:A->B).
        mfd_smooth_map atlas atlas' W f /\ V SUBSET W
        ==> mfd_smooth_map atlas atlas' V f`,
  REWRITE_TAC[mfd_smooth_map] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                {x | x IN FST c INTER W /\
                     (f:A->B) x IN FST(c':(B->bool)#(B->real^M))}` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let MFD_SMOOTH_ON_SUBSET = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) V W (f:A->real^K).
        mfd_smooth_on atlas W f /\ V SUBSET W ==> mfd_smooth_on atlas V f`,
  REWRITE_TAC[GSYM MFD_SMOOTH_MAP_INTO_EUCLIDEAN; MFD_SMOOTH_MAP_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Identity and composition.                                                 *)
(* ------------------------------------------------------------------------- *)

let MFD_SMOOTH_MAP_ID = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W.
        smooth_manifold_atlas top atlas
        ==> mfd_smooth_map atlas atlas W (\x. x)`,
  REWRITE_TAC[mfd_smooth_map; FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `W:A->bool`] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(psi:A->real^N) o (\x:A. x) o chart_inv (U,phi) =
                chart_trans (U,phi) (V,psi)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans; SND]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
  CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[CHART_TRANS_SMOOTH]]);;

(* The local step of the composition: in charts c1, c2, c3 around a point.  *)

let MFDM_SMOOTH_MAP_COMPOSE_LOCAL = prove
 (`!top1 atlas1 top2 atlas2 top3 atlas3 W1 W2 (f:A->B) (g:B->C) c1 c2 c3.
        smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^M))->bool) /\
        smooth_manifold_atlas top2 (atlas2:((B->bool)#(B->real^N))->bool) /\
        smooth_manifold_atlas top3 (atlas3:((C->bool)#(C->real^P))->bool) /\
        open_in top1 W1 /\ open_in top2 W2 /\ IMAGE f W1 SUBSET W2 /\
        continuous_map (subtopology top1 W1,top2) f /\
        continuous_map (subtopology top2 W2,top3) g /\
        mfd_smooth_map atlas1 atlas2 W1 f /\ mfd_smooth_map atlas2 atlas3 W2 g /\
        c1 IN atlas1 /\ c2 IN atlas2 /\ c3 IN atlas3
        ==> open (IMAGE (SND c1) {x | x IN FST c1 INTER W1 /\
                                      f x IN FST c2 /\ g(f x) IN FST c3}) /\
            smooth_map_on
              (IMAGE (SND c1) {x | x IN FST c1 INTER W1 /\
                                   f x IN FST c2 /\ g(f x) IN FST c3})
              (SND c3 o (g o f) o chart_inv c1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^M))->bool`;
                 `c1:(A->bool)#(A->real^M)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top2:B topology`; `atlas2:((B->bool)#(B->real^N))->bool`;
                 `c2:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top2:B topology`; `atlas2:((B->bool)#(B->real^N))->bool`;
                 `top3:C topology`; `atlas3:((C->bool)#(C->real^P))->bool`;
                 `c2:(B->bool)#(B->real^N)`; `c3:(C->bool)#(C->real^P)`;
                 `W2:B->bool`; `g:B->C`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `open_in top1 {x | x IN FST(c1:(A->bool)#(A->real^M)) INTER W1 /\
                      (f:A->B) x IN FST(c2:(B->bool)#(B->real^N)) /\
                      (g:B->C)(f x) IN FST(c3:(C->bool)#(C->real^P))}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{x | x IN FST(c1:(A->bool)#(A->real^M)) INTER W1 /\
           (f:A->B) x IN FST(c2:(B->bool)#(B->real^N)) /\
           (g:B->C)(f x) IN FST(c3:(C->bool)#(C->real^P))} =
      FST(c1:(A->bool)#(A->real^M)) INTER
      {x | x IN W1 /\ f x IN {z | z IN FST c2 INTER W2 /\ g z IN FST c3}}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top2:B topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND(c1:(A->bool)#(A->real^M)))
           {x | x IN FST c1 INTER W1 /\
                (f:A->B) x IN FST(c2:(B->bool)#(B->real^N)) /\
                (g:B->C)(f x) IN FST(c3:(C->bool)#(C->real^P))})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top1:A topology`; `atlas1:((A->bool)#(A->real^M))->bool`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(SND(c3:(C->bool)#(C->real^P)) o (g:B->C) o
               chart_inv(c2:(B->bool)#(B->real^N))) o
              (SND c2 o (f:A->B) o chart_inv(c1:(A->bool)#(A->real^M)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND(c2:(B->bool)#(B->real^N)))
                {z | z IN FST c2 INTER W2 /\
                     (g:B->C) z IN FST(c3:(C->bool)#(C->real^P))}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c1:(A->bool)#(A->real^M)))
                  {x | x IN FST c1 INTER W1 /\
                       (f:A->B) x IN FST(c2:(B->bool)#(B->real^N))}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_smooth_map (atlas1:((A->bool)#(A->real^M))->bool)
                   (atlas2:((B->bool)#(B->real^N))->bool) W1 (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `mfd_smooth_map (atlas2:((B->bool)#(B->real^N))->bool)
                   (atlas3:((C->bool)#(C->real^P))->bool) W2 (g:B->C)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MFD_SMOOTH_MAP_COMPOSE = prove
 (`!top1 atlas1 top2 atlas2 top3 atlas3 W1 W2 (f:A->B) (g:B->C).
        smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^M))->bool) /\
        smooth_manifold_atlas top2 (atlas2:((B->bool)#(B->real^N))->bool) /\
        smooth_manifold_atlas top3 (atlas3:((C->bool)#(C->real^P))->bool) /\
        open_in top1 W1 /\ open_in top2 W2 /\ IMAGE f W1 SUBSET W2 /\
        continuous_map (subtopology top1 W1,top2) f /\
        continuous_map (subtopology top2 W2,top3) g /\
        mfd_smooth_map atlas1 atlas2 W1 f /\ mfd_smooth_map atlas2 atlas3 W2 g
        ==> mfd_smooth_map atlas1 atlas3 W1 (g o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c1:(A->bool)#(A->real^M)`; `c3:(C->bool)#(C->real^P)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology top1 W1,top3) ((g:B->C) o (f:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top2 (W2:B->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^M))->bool`;
                   `top3:C topology`; `atlas3:((C->bool)#(C->real^P))->bool`;
                   `c1:(A->bool)#(A->real^M)`; `c3:(C->bool)#(C->real^P)`;
                   `W1:A->bool`; `(g:B->C) o (f:A->B)`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top2:B topology`; `W2:B->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?c2. c2 IN (atlas2:((B->bool)#(B->real^N))->bool) /\
                     (f:A->B) x IN FST c2`
  (X_CHOOSE_THEN `c2:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^M))->bool`;
                 `top2:B topology`; `atlas2:((B->bool)#(B->real^N))->bool`;
                 `top3:C topology`; `atlas3:((C->bool)#(C->real^P))->bool`;
                 `W1:A->bool`; `W2:B->bool`; `f:A->B`; `g:B->C`;
                 `c1:(A->bool)#(A->real^M)`; `c2:(B->bool)#(B->real^N)`;
                 `c3:(C->bool)#(C->real^P)`] MFDM_SMOOTH_MAP_COMPOSE_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (SND(c1:(A->bool)#(A->real^M)))
                {y | y IN FST c1 INTER W1 /\
                     (f:A->B) y IN FST(c2:(B->bool)#(B->real^N)) /\
                     (g:B->C)(f y) IN FST(c3:(C->bool)#(C->real^P))}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]);;

(* ------------------------------------------------------------------------- *)
(* Diffeomorphisms (identity, inverse, composition, restriction, the link    *)
(* with diffeomorphism_on), diffeomorphic manifolds, open submanifolds.      *)
(* ------------------------------------------------------------------------- *)

let MFD_DIFFEO_MAPS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W
    top' (atlas':((B->bool)#(B->real^M))->bool) W' f g.
        mfd_diffeo top atlas W top' atlas' W' f g
        ==> continuous_map (subtopology top W,top') f /\ IMAGE f W SUBSET W' /\
            continuous_map (subtopology top' W',top) g /\ IMAGE g W' SUBSET W /\
            (!x. x IN W ==> g(f x) = x) /\ (!y. y IN W' ==> f(g y) = y) /\
            IMAGE f W = W' /\ IMAGE g W' = W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
  MP_TAC(ISPECL [`top':B topology`; `W':B->bool`] OPEN_IN_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `topspace top INTER W = (W:A->bool) /\
                topspace top' INTER W' = (W':B->bool)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE (f:A->B) s SUBSET t /\ IMAGE (g:B->A) t SUBSET s /\
    (!x. x IN s ==> g(f x) = x) /\ (!y. y IN t ==> f(g y) = y)
    ==> IMAGE f s = t /\ IMAGE g t = s`) THEN
  ASM_REWRITE_TAC[]);;

let MFD_DIFFEO_ID = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W.
        smooth_manifold_atlas top atlas /\ open_in top W
        ==> mfd_diffeo top atlas W top atlas W (\x. x) (\x. x)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mfd_diffeo; HOMEOMORPHIC_MAPS_ID] THEN
  ASM_MESON_TAC[MFD_SMOOTH_MAP_ID]);;

let MFD_DIFFEO_SYM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W
    top' (atlas':((B->bool)#(B->real^M))->bool) W' f g.
        mfd_diffeo top atlas W top' atlas' W' f g
        ==> mfd_diffeo top' atlas' W' top atlas W g f`,
  REWRITE_TAC[mfd_diffeo] THEN MESON_TAC[HOMEOMORPHIC_MAPS_SYM]);;

let MFD_DIFFEO_COMPOSE = prove
 (`!top1 atlas1 W1 top2 atlas2 W2 top3 atlas3 W3 (f:A->B) g (h:B->C) k.
        smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^M))->bool) /\
        smooth_manifold_atlas top2 (atlas2:((B->bool)#(B->real^N))->bool) /\
        smooth_manifold_atlas top3 (atlas3:((C->bool)#(C->real^P))->bool) /\
        mfd_diffeo top1 atlas1 W1 top2 atlas2 W2 f g /\
        mfd_diffeo top2 atlas2 W2 top3 atlas3 W3 h k
        ==> mfd_diffeo top1 atlas1 W1 top3 atlas3 W3 (h o f) (g o k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^M))->bool`;
                 `W1:A->bool`; `top2:B topology`;
                 `atlas2:((B->bool)#(B->real^N))->bool`; `W2:B->bool`;
                 `f:A->B`; `g:B->A`] MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top2:B topology`; `atlas2:((B->bool)#(B->real^N))->bool`;
                 `W2:B->bool`; `top3:C topology`;
                 `atlas3:((C->bool)#(C->real^P))->bool`; `W3:C->bool`;
                 `h:B->C`; `k:C->B`] MFD_DIFFEO_MAPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_diffeo]) THEN
  ASM_REWRITE_TAC[mfd_diffeo] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
    EXISTS_TAC `subtopology top2 (W2:B->bool)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`top1:A topology`; `top2:B topology`;
      `atlas2:((B->bool)#(B->real^N))->bool`; `top3:C topology`;
      `W2:B->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`top3:C topology`; `top2:B topology`;
      `atlas2:((B->bool)#(B->real^N))->bool`; `top1:A topology`;
      `W2:B->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let MFD_DIFFEO_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W
    top' (atlas':((B->bool)#(B->real^M))->bool) W' f g V.
        mfd_diffeo top atlas W top' atlas' W' f g /\
        open_in top V /\ V SUBSET W
        ==> mfd_diffeo top atlas V top' atlas' (IMAGE f V) f g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_diffeo]) THEN ASM_REWRITE_TAC[mfd_diffeo] THEN
  MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
  MP_TAC(ISPECL [`top':B topology`; `W':B->bool`] OPEN_IN_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (f:A->B) V SUBSET W'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top' (IMAGE (f:A->B) V)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `W':B->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:A->B`; `subtopology top (W:A->bool)`;
                   `subtopology top' (W':B->bool)`; `V:A->bool`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (W:A->bool)`;
                   `subtopology top' (W':B->bool)`; `f:A->B`; `g:B->A`;
                   `V:A->bool`; `IMAGE (f:A->B) V`]
                  HOMEOMORPHIC_MAPS_SUBTOPOLOGIES) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `W INTER V = (V:A->bool) /\ W' INTER IMAGE (f:A->B) V = IMAGE f V`
     (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN EXISTS_TAC `W:A->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN EXISTS_TAC `W':B->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* Diffeomorphic manifolds. *)

let MFD_DIFFEOMORPHIC_REFL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas ==> mfd_diffeomorphic top atlas top atlas`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_diffeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`\x:A. x`; `\x:A. x`] THEN
  ASM_SIMP_TAC[MFD_DIFFEO_ID; OPEN_IN_TOPSPACE]);;

let MFD_DIFFEOMORPHIC_SYM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) top' (atlas':((B->bool)#(B->real^M))->bool).
        mfd_diffeomorphic top atlas top' atlas' ==> mfd_diffeomorphic top' atlas' top atlas`,
  REWRITE_TAC[mfd_diffeomorphic] THEN MESON_TAC[MFD_DIFFEO_SYM]);;

let MFD_DIFFEOMORPHIC_TRANS = prove
 (`!top1 atlas1 top2 atlas2 top3 atlas3.
        smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^M))->bool) /\
        smooth_manifold_atlas top2 (atlas2:((B->bool)#(B->real^N))->bool) /\
        smooth_manifold_atlas top3 (atlas3:((C->bool)#(C->real^P))->bool) /\
        mfd_diffeomorphic top1 atlas1 top2 atlas2 /\
        mfd_diffeomorphic top2 atlas2 top3 atlas3
        ==> mfd_diffeomorphic top1 atlas1 top3 atlas3`,
  REWRITE_TAC[mfd_diffeomorphic] THEN MESON_TAC[MFD_DIFFEO_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Open subsets of real^N: the link with diffeomorphism_on.                  *)
(* ------------------------------------------------------------------------- *)

let MFD_DIFFEO_OPEN_SET_ATLAS = prove
 (`!U V s t (f:real^M->real^N) g.
        open U /\ open V /\ s SUBSET U /\ t SUBSET V
        ==> (mfd_diffeo (subtopology euclidean U) (open_set_atlas U) s
                        (subtopology euclidean V) (open_set_atlas V) t f g <=>
             diffeomorphism_on s t f g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in euclidean (U:real^M->bool) /\
                open_in euclidean (V:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN]; ALL_TAC] THEN
  ASM_SIMP_TAC[mfd_diffeo; OPEN_IN_OPEN_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY;
               MFD_SMOOTH_MAP_OPEN_SET_ATLAS;
               SET_RULE `(s:real^M->bool) SUBSET u ==> u INTER s = s`;
               SET_RULE `(t:real^N->bool) SUBSET v ==> v INTER t = t`] THEN
  REWRITE_TAC[OPEN_IN_EUCLIDEAN; homeomorphic_maps; CONTINUOUS_MAP_EUCLIDEAN2;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; diffeomorphism_on] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN V} = s /\
                  {y | y IN t /\ (g:real^N->real^M) y IN U} = t`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN V} = s /\
                  {y | y IN t /\ (g:real^N->real^M) y IN U} = t`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM SET_TAC[]]);;

let MFD_DIFFEO_EUCLIDEAN = prove
 (`!s t (f:real^M->real^N) g.
        mfd_diffeo euclidean (open_set_atlas (:real^M)) s
                   euclidean (open_set_atlas (:real^N)) t f g <=>
        diffeomorphism_on s t f g`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `(:real^N)`; `s:real^M->bool`; `t:real^N->bool`;
                 `f:real^M->real^N`; `g:real^N->real^M`]
                MFD_DIFFEO_OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Open submanifolds.                                                        *)
(* ------------------------------------------------------------------------- *)

let IN_RESTRICT_ATLAS = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) W V psi.
        (V,psi) IN restrict_atlas atlas W <=>
        ?U. (U,psi) IN atlas /\ V = U INTER W`,
  REWRITE_TAC[restrict_atlas; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MFDM_RESTRICT_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W U phi.
        smooth_manifold_atlas top atlas /\ open_in top W /\ (U,phi) IN atlas
        ==> open_in (subtopology top W) (U INTER W) /\
            open (IMAGE phi (U INTER W)) /\
            homeomorphic_map (subtopology (subtopology top W) (U INTER W),
                              subtopology euclidean (IMAGE phi (U INTER W))) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (U INTER W:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_INTER]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; INTER_SUBSET];
    MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `subtopology (subtopology top W) (U INTER W) =
    subtopology (subtopology top U) (U INTER W:A->bool) /\
    subtopology euclidean (IMAGE (phi:A->real^N) (U INTER W)) =
    subtopology (subtopology euclidean (IMAGE phi U)) (IMAGE phi (U INTER W))`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  UNDISCH_TAC `(U:A->bool) SUBSET topspace top` THEN SET_TAC[]);;

let SMOOTH_MANIFOLD_ATLAS_RESTRICT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) W.
        smooth_manifold_atlas top atlas /\ open_in top W
        ==> smooth_manifold_atlas (subtopology top W) (restrict_atlas atlas W)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[smooth_manifold_atlas; IN_RESTRICT_ATLAS] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MFDM_RESTRICT_CHART THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`U INTER W:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC
     [`V1:A->bool`; `phi:A->real^N`; `V2:A->bool`; `psi:A->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `U1:A->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `U2:A->bool` STRIP_ASSUME_TAC)) THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPECL
     [`U1:A->bool`; `phi:A->real^N`; `U2:A->bool`; `psi:A->real^N`] o
      CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:real^N->real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) (U1 INTER U2)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]]);;

