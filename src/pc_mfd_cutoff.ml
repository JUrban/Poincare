(* ========================================================================= *)
(* pc_mfd_cutoff: smooth cutoff functions on Hausdorff smooth manifolds.     *)
(* For K compact inside W open there is a smooth chi with values in [0,1],   *)
(* equal to 1 on an open set containing K and vanishing off a compact subset *)
(* of W (MFD_SMOOTH_CUTOFF): finitely many chart bumps (smooth_bump of the   *)
(* vendored Navier-Stokes ns_cutoff.ml), combined as 1 - prod (1 - b_i).     *)
(*                                                                           *)
(* First: chart inverses are continuous, compact sets in charts, the chart   *)
(* bump.                                                                     *)
(* ========================================================================= *)

needs "src/pc_mfd_maps.ml";;
needs "src/ns_cutoff.ml";;

prioritize_real();;
type_invention_error := true;;

let MFDC_CHART_INV_CONTINUOUS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> continuous_map (subtopology euclidean (IMAGE phi U),subtopology top U)
                           (chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:real^N->A` ASSUME_TAC))) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:real^N->A` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[homeomorphic_maps]] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (U,phi) ((phi:A->real^N) x) = x` SUBST1_TAC THENL
   [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let MFDC_CHART_COMPACT = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) k.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        compact k /\ k SUBSET IMAGE phi U
        ==> compact_in top {x | x IN U /\ phi x IN k}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | x IN U /\ (phi:A->real^N) x IN k} =
                IMAGE (chart_inv (U,phi)) k`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(phi:A->real^N) x` THEN ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[COMPACT_IN_SUBTOPOLOGY]
   `compact_in (subtopology top (U:A->bool)) s ==> compact_in top s`) THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN
  ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY_EUCLIDEAN] THEN
  ASM_MESON_TAC[MFDC_CHART_INV_CONTINUOUS]);;

(* The chart bump: 1 near phi^-1(cball(y0,r)), 0 off phi^-1(cball(y0,2r)). *)

let MFDC_BUMP_SMOOTH = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) y0 r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        (U,phi) IN atlas /\ &0 < r /\ cball(y0,&2 * r) SUBSET IMAGE phi U
        ==> mfd_smooth atlas
              (\x. lift(if x IN U then smooth_bump r (&2 * r) (phi x - y0)
                        else &0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed_in top {x | x IN U /\ (phi:A->real^N) x IN cball(y0,&2 * r)}` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(q:A) IN U` THENL
   [EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER U)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\w:real^N. lift(smooth_bump r (&2 * r) w)) o
                (\z. chart_trans (V:A->bool,psi:A->real^N) (U,phi) z - (y0:real^N))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM; chart_trans] THEN
      X_GEN_TAC `p:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[FST; SND];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
          `phi:A->real^N`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
        EXISTS_TAC `top:A topology` THEN EXISTS_TAC
         `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((q:A) IN {x | x IN U /\ (phi:A->real^N) x IN cball(y0,&2 * r)})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (psi:A->real^N) (V DIFF {x | x IN U /\ (phi:A->real^N) x IN cball(y0,&2 * r)})` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; SUBSET_DIFF];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `(\z:real^N. vec 0:real^1)` THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST; FORALL_IN_IMAGE; IN_DIFF; o_THM] THEN
  X_GEN_TAC `p:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
  MATCH_MP_TAC SMOOTH_BUMP_0 THEN
  UNDISCH_TAC `~((p:A) IN {x | x IN U /\ (phi:A->real^N) x IN cball(y0,&2 * r)})` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_CBALL; dist] THEN
  MP_TAC(ISPECL [`(phi:A->real^N) p`; `y0:real^N`] NORM_SUB) THEN
  UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The cutoff theorem.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Around each point of an open set W there is a chart ball of radius 2r     *)
(* inside the chart image of W.                                              *)

let MFDC_LOCAL_BALL = prove
 (`!top atlas W (x:A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\ x IN W
        ==> ?U phi r. (U,phi) IN atlas /\ x IN U /\ &0 < r /\
                      cball(phi x,&2 * r) SUBSET IMAGE phi (U INTER W)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^N) (U INTER W))` MP_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) x`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`; `e / &2`] THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `&2 * e / &2 = e` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

(* The chart ball around a point is open. *)

let MFDC_CHART_BALL_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) y r.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> open_in top {p | p IN U /\ phi p IN ball(y,r)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
  EXISTS_TAC `euclidean:(real^N)topology` THEN
  ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]);;

(* Values of the chart bump. *)

let MFDC_BUMP_VALUES = prove
 (`!(U:A->bool) (phi:A->real^N) y0 r p.
        &0 < r
        ==> let b = (if p IN U then smooth_bump r (&2 * r) (phi p - y0) else &0) in
            &0 <= b /\ b <= &1 /\
            (p IN U /\ phi p IN ball(y0,r) ==> b = &1) /\
            (~(p IN U /\ phi p IN cball(y0,&2 * r)) ==> b = &0)`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS; SMOOTH_BUMP_BOUNDS] THEN
  REWRITE_TAC[IN_BALL; IN_CBALL; dist] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_BUMP_1; MATCH_MP_TAC SMOOTH_BUMP_0] THEN
  MP_TAC(ISPECL [`(phi:A->real^N) p`; `y0:real^N`] NORM_SUB) THEN
  ASM_REAL_ARITH_TAC);;

(* Smoothness of the combination 1 - prod (1 - b_i). *)

let MFDC_SMOOTH_ONE_MINUS = prove
 (`!s (g:real^M->real).
        open s /\ smooth_map_on s (\y. lift(g y))
        ==> smooth_map_on s (\y. lift(&1 - g y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\y:real^M. lift(&1)`; `\y:real^M. lift(g y)`]
    SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST]);;

let MFDC_SMOOTH_PRODUCT = prove
 (`!s (h:B->real^M->real) k.
        open s /\ FINITE k /\ (!i. i IN k ==> smooth_map_on s (\y. lift(h i y)))
        ==> smooth_map_on s (\y. lift(product k (\i. h i y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\i:B y:real^M. lift(h i y)`; `k:B->bool`]
    SMOOTH_MAP_ON_LIFT_PRODUCT) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let MFDC_SMOOTH_CUTOFF_FORM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (b:B->A->real) FF.
        smooth_manifold_atlas top atlas /\ FINITE FF /\
        (!x. x IN FF ==> mfd_smooth atlas (\p. lift(b x p)))
        ==> mfd_smooth atlas (\p. lift(&1 - product FF (\x. &1 - b x p)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC
  THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  MATCH_MP_TAC MFDC_SMOOTH_ONE_MINUS THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDC_SMOOTH_PRODUCT THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  MATCH_MP_TAC MFDC_SMOOTH_ONE_MINUS THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[mfd_smooth; o_DEF] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[]);;

let MFD_SMOOTH_CUTOFF = prove
 (`!top atlas K W.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_in top K /\ open_in top W /\ K SUBSET W
        ==> ?chi:A->real V L.
              mfd_smooth atlas (\x. lift(chi x)) /\
              (!x. &0 <= chi x /\ chi x <= &1) /\
              open_in top V /\ K SUBSET V /\ (!x. x IN V ==> chi x = &1) /\
              compact_in top L /\ L SUBSET W /\
              (!x. x IN topspace top DIFF L ==> chi x = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`] MFDC_LOCAL_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?UU PH RR. !x:A. x IN K
        ==> (UU x,PH x) IN atlas /\ x IN UU x /\ &0 < RR x /\
            cball((PH x:A->real^N) x,&2 * RR x) SUBSET IMAGE (PH x) (UU x INTER W)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; REWRITE_TAC[]];
    ALL_TAC] THEN
  (* finite subcover *)
  SUBGOAL_THEN
   `?FF. FINITE FF /\ FF SUBSET K /\
        K SUBSET UNIONS (IMAGE (\x:A. {p | p IN UU x /\
                                           (PH x:A->real^N) p IN ball(PH x x,RR x)}) FF)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in]) THEN
    DISCH_THEN(MP_TAC o SPEC
     `IMAGE (\x:A. {p | p IN UU x /\ (PH x:A->real^N) p IN ball(PH x x,RR x)}) K`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
        ASM_SIMP_TAC[ETA_AX];
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
        X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN
        ASM_SIMP_TAC[CENTRE_IN_BALL]];
      ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> (a /\ b) /\ c`] THEN
      REWRITE_TAC[FINITE_SUBSET_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `b = \(x:A) (p:A). if p IN UU x
                      then smooth_bump (RR x) (&2 * RR x) ((PH x:A->real^N) p - PH x x)
                      else &0` THEN
  SUBGOAL_THEN
   `!x p. x IN K
          ==> &0 <= (b:A->A->real) x p /\ b x p <= &1 /\
              (p IN UU x /\ (PH x:A->real^N) p IN ball(PH x x,RR x) ==> b x p = &1) /\
              (~(p IN UU x /\ (PH x:A->real^N) p IN cball(PH x x,&2 * RR x))
               ==> b x p = &0)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "b" THEN
    MP_TAC(ISPECL [`(UU:A->A->bool) x`; `(PH:A->A->real^N) x`;
                   `(PH:A->A->real^N) x x`; `(RR:A->real) x`; `p:A`]
                  MFDC_BUMP_VALUES) THEN
    ASM_SIMP_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN K ==> mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\p. lift((b:A->A->real) x p))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN BETA_TAC THEN
    MATCH_MP_TAC MFDC_BUMP_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[ETA_AX] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((PH:A->A->real^N) x) (UU x INTER W)` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\p:A. &1 - product FF (\x. &1 - (b:A->A->real) x p)` THEN
  EXISTS_TAC `UNIONS (IMAGE (\x:A. {p | p IN UU x /\
                     (PH x:A->real^N) p IN ball(PH x x,RR x)}) FF)` THEN
  EXISTS_TAC `UNIONS (IMAGE (\x:A. {p | p IN UU x /\
                     (PH x:A->real^N) p IN cball(PH x x,&2 * RR x)}) FF)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* smoothness *)
    MATCH_MP_TAC MFDC_SMOOTH_CUTOFF_FORM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    (* values *)
    X_GEN_TAC `p:A` THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= &1 ==> &0 <= &1 - a /\ &1 - a <= &1`) THEN
    CONJ_TAC THENL [MATCH_MP_TAC PRODUCT_POS_LE; MATCH_MP_TAC PRODUCT_LE_1] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `p:A`] o
      check (fun th -> can (term_match [] `!x p. x IN K ==> &0 <= (b:A->A->real) x p /\ q`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    (* V open *)
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFDC_CHART_BALL_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_MESON_TAC[SUBSET];
    ASM_REWRITE_TAC[];
    (* chi = 1 on V *)
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A` THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[REAL_ARITH `&1 - a = &1 <=> a = &0`] THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[REAL_SUB_0] THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    (* L compact *)
    MATCH_MP_TAC COMPACT_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFDC_CHART_COMPACT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((PH:A->A->real^N) x) (UU x INTER W)` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    (* L SUBSET W *)
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(PH:A->A->real^N) x p IN IMAGE (PH x) (UU x INTER W)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `p:A = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(UU:A->A->bool) x`; `(PH:A->A->real^N) x`] THEN
    ASM_SIMP_TAC[];
    (* chi = 0 off L *)
    REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A` THEN REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `&1 - a = &0 <=> a = &1`] THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 - a = &1 <=> a = &0`] THEN
    ASM_MESON_TAC[]]);;

