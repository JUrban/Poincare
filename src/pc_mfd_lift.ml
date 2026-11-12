(* ========================================================================= *)
(* pc_mfd_lift: smooth structures, metrics and flows lifted along a local    *)
(* homeomorphism f : topc -> top.  The lifted atlas                          *)
(* mfd_lift_atlas topc top f atlas has the charts (S INTER f^-1(U),phi o f)  *)
(* for S open in topc and mapped homeomorphically by f onto an open set of   *)
(* top, and (U,phi) in the atlas of top; the lifted metric is the pullback   *)
(* mfd_pullback_metric (pc_mfd_restrict).  In a lifted chart the chart       *)
(* representative of the lifted metric is that of the base chart             *)
(* (MFDL_METRIC_LOCAL), so curvature, lengths, distances, volumes and        *)
(* orientations transfer.  Used for the orientation double cover of X1       *)
(* (pc_p2b_x1, MT Prop 9.83 / Cor 9.53, first case).                         *)
(* ========================================================================= *)

needs "src/pc_mfd_restrict.ml";;
needs "src/pc_grg_dist2.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The lifted atlas.  Its charts are (S INTER f^-1(U),phi o f) with S a      *)
(* sheet (open, mapped homeomorphically onto the open set IMAGE f S) and     *)
(* (U,phi) a chart of top; they form a smooth atlas of topc whose transition *)
(* maps are restrictions of those of top.                                    *)
(* ========================================================================= *)

let mfd_lift_atlas = new_definition
 `mfd_lift_atlas (topc:A topology) (top:B topology) (f:A->B)
                 (atlas:((B->bool)#(B->real^N))->bool) =
    {(S INTER {w | f w IN FST c},SND c o f) | S,c |
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     c IN atlas}`;;

let IN_MFD_LIFT_ATLAS = prove
 (`!topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool) cc.
     cc IN mfd_lift_atlas topc top f atlas <=>
     ?S c. open_in topc S /\ open_in top (IMAGE f S) /\
           homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
           c IN atlas /\ cc = (S INTER {w | f w IN FST c},SND c o f)`,
  REWRITE_TAC[mfd_lift_atlas; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Basic facts on a sheet. *)

let MFDL_SHEET = prove
 (`!topc top (f:A->B) S.
     open_in topc S /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f
     ==> S SUBSET topspace topc /\ IMAGE f S SUBSET topspace top /\
         (!w1 w2. w1 IN S /\ w2 IN S /\ f w1 = f w2 ==> w1 = w2) /\
         continuous_map (subtopology topc S,top) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace topc` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology topc S,subtopology top (IMAGE (f:A->B) S)) f`
  ASSUME_TAC THENL [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:A->B) S SUBSET topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology topc S,subtopology top (IMAGE (f:A->B) S)) f` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `(S:A->bool) SUBSET topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_HOMEOMORPHIC_MAP_INJ THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`; `top:B topology`; `f:A->B`;
                          `S:A->bool`; `IMAGE (f:A->B) S`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]]);;

(* A local homeomorphism has a sheet at every point. *)

let MFDL_LH_SHEET = prove
 (`!topc top (f:A->B) w.
     local_homeomorphism_map (topc,top) f /\ w IN topspace topc
     ==> ?S. open_in topc S /\ w IN S /\ open_in top (IMAGE f S) /\
             homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[local_homeomorphism_map] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `w:A`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `V:B->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (f:A->B) U = V` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(U:A->bool) SUBSET topspace topc /\ (V:B->bool) SUBSET topspace top`
    MP_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]);;

(* A local homeomorphism is continuous. *)

let MFDL_LH_CONTINUOUS = prove
 (`!topc top (f:A->B).
     local_homeomorphism_map (topc,top) f ==> continuous_map (topc,top) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `w:A`] MFDL_LH_SHEET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* A lifted chart. *)

let MFDL_LIFT_CHART = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) S c.
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f
     ==> open_in topc (S INTER {w | f w IN FST c}) /\
         IMAGE f (S INTER {w | f w IN FST c}) = IMAGE f S INTER FST c /\
         open_in top (IMAGE f S INTER FST c) /\
         open (IMAGE (SND c) (IMAGE f S INTER FST c)) /\
         IMAGE (SND c o f) (S INTER {w | f w IN FST c}) =
         IMAGE (SND c) (IMAGE f S INTER FST c) /\
         homeomorphic_map (subtopology topc (S INTER {w | f w IN FST c}),
                           subtopology euclidean
                             (IMAGE (SND c o f) (S INTER {w | f w IN FST c})))
                          (SND c o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:A->B) (S INTER {w | f w IN FST (c:(B->bool)#(B->real^N))}) =
                IMAGE f S INTER FST c` ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (f:A->B) S INTER FST (c:(B->bool)#(B->real^N)))`
  ASSUME_TAC THENL [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (SND (c:(B->bool)#(B->real^N)) o (f:A->B)) (S INTER {w | f w IN FST c}) =
                IMAGE (SND c) (IMAGE f S INTER FST c)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))} =
                  {w | w IN topspace (subtopology topc S) /\ f w IN FST c}` SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN UNDISCH_TAC `(S:A->bool) SUBSET topspace topc` THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (IMAGE (f:A->B) S INTER FST (c:(B->bool)#(B->real^N)))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `subtopology topc (S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}) =
        subtopology (subtopology topc S) (S INTER {w | f w IN FST c}) /\
        subtopology top (IMAGE f S INTER FST c) =
        subtopology (subtopology top (IMAGE f S)) (IMAGE f S INTER FST c)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THEN AP_TERM_TAC THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      UNDISCH_TAC `IMAGE (f:A->B) S SUBSET topspace top` THEN
      UNDISCH_TAC `(S:A->bool) SUBSET topspace topc` THEN SET_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `subtopology top (IMAGE (f:A->B) S INTER FST (c:(B->bool)#(B->real^N))) =
        subtopology (subtopology top (FST c)) (IMAGE f S INTER FST c) /\
        subtopology euclidean (IMAGE (SND c) (IMAGE f S INTER FST c)) =
        subtopology (subtopology euclidean (IMAGE (SND c) (FST c)))
                    (IMAGE (SND c) (IMAGE f S INTER FST c))`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THEN AP_TERM_TAC THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
      SUBGOAL_THEN `FST (c:(B->bool)#(B->real^N)) SUBSET topspace top` MP_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET]; SET_TAC[]]]]);;

(* The lifted atlas is a smooth atlas. *)

let MFDL_ATLAS = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f
     ==> smooth_manifold_atlas topc (mfd_lift_atlas topc top f atlas)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (topc,top) (f:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDL_LH_CONTINUOUS]; ALL_TAC] THEN
  REWRITE_TAC[smooth_manifold_atlas] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    REWRITE_TAC[IN_MFD_LIFT_ATLAS; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))))) THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `w:A`] MFDL_LH_SHEET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:A->B) w IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`]
                    CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:A) IN topspace topc` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `(f:A->B) w`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`S INTER {z | (f:A->B) z IN FST (chart_at (atlas:((B->bool)#(B->real^N))->bool) (f w))}`;
      `SND (chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w)) o f`] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY EXISTS_TAC [`S:A->bool`;
                          `chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w)`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`] THEN
    REWRITE_TAC[IN_MFD_LIFT_ATLAS; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `S2:A->bool` (X_CHOOSE_THEN `c2:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^N))->bool)` THEN
    REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                               `FST (c2:(B->bool)#(B->real^N))`; `SND (c2:(B->bool)#(B->real^N))`] o
               last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g0:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1 INTER FST (c2:(B->bool)#(B->real^N)))` THEN
      ASM_REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]]);;

(* ========================================================================= *)
(* Chart inverses, transition Jacobians and preferred charts of the lifted   *)
(* atlas; the pullback metric in a lifted chart is the representative of the *)
(* base metric in the base chart (MFDL_METRIC_LOCAL).                        *)
(* ========================================================================= *)

let MFDL_CHART_INV = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) S c.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f
     ==> (!w. w IN S /\ f w IN FST c
              ==> chart_inv (S INTER {w | f w IN FST c},SND c o f) (SND c (f w)) = w) /\
         (!z. z IN IMAGE (SND c) (IMAGE f S INTER FST c)
              ==> chart_inv (S INTER {w | f w IN FST c},SND c o f) z IN S /\
                  f (chart_inv (S INTER {w | f w IN FST c},SND c o f) z) IN FST c /\
                  f (chart_inv (S INTER {w | f w IN FST c},SND c o f) z) = chart_inv c z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f) IN
                mfd_lift_atlas topc top f atlas` ASSUME_TAC THENL
   [REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY EXISTS_TAC [`S:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`] MFDL_ATLAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `(S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f)`]
                MFDM_CHART) THEN
  ASM_REWRITE_TAC[FST; SND; o_THM; IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN IMAGE (SND (c:(B->bool)#(B->real^N)) o (f:A->B))
                                  (S INTER {w | f w IN FST c})` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f) z IN
                S INTER {w | f w IN FST c} /\
                (SND c o f) (chart_inv (S INTER {w | f w IN FST c},SND c o f) z) = z`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                   `(S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f)`]
                  MFDM_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `chart_inv (S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f) z IN
               S INTER {w | f w IN FST c}` THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(SND (c:(B->bool)#(B->real^N)) o (f:A->B))
                 (chart_inv (S INTER {w | f w IN FST c},SND c o f) z) = z` THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Transition Jacobians from a lifted chart are those of the base charts. *)

let MFDL_CHART_JAC = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) S c V (c':(B->bool)#(B->real^N)) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     w IN S /\ f w IN FST c
     ==> chart_jac (S INTER {w | f w IN FST c},SND c o f) (V,SND c' o f) w =
         chart_jac c c' (f w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[chart_jac; SND; o_THM] THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) (IMAGE (f:A->B) S INTER FST c)` THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[chart_trans; SND; o_THM] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2) THEN
  ASM_SIMP_TAC[]);;

(* The preferred chart of the lifted atlas at w is a lifted chart. *)

let MFDL_CHART_AT = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     w IN topspace topc
     ==> ?S c. open_in topc S /\ open_in top (IMAGE f S) /\
               homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
               c IN atlas /\ w IN S /\ f w IN FST c /\
               chart_at (mfd_lift_atlas topc top f atlas) w =
               (S INTER {w | f w IN FST c},SND c o f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`] MFDL_ATLAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `w:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_REWRITE_TAC[FST; IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`S:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[]);;

(* The pullback metric at w, read in the base chart of the preferred chart. *)

let MFDL_PULLBACK_AT = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) S c w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     w IN S /\ f w IN FST c /\
     chart_at (mfd_lift_atlas topc top f atlas) w = (S INTER {w | f w IN FST c},SND c o f)
     ==> mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g w =
         metric_local atlas c g (SND c (f w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B) w IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) w`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w)` THEN
  STRIP_TAC THEN
  REWRITE_TAC[mfd_pullback_metric] THEN ASM_REWRITE_TAC[SND; o_THM] THEN
  SUBGOAL_THEN
   `SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
    chart_inv (S INTER {w | f w IN FST (c:(B->bool)#(B->real^N))},SND c o f) =
    chart_trans (S INTER {w | f w IN FST c},SND c o f) ((:A),SND c' o f)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; chart_trans; o_THM; SND]; ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (chart_trans (S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f)
                   ((:A),SND (c':(B->bool)#(B->real^N)) o f))
      (at (SND c (f w))) = chart_jac c c' (f w)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`;
                   `(:A)`; `c':(B->bool)#(B->real^N)`; `w:A`]
                  MFDL_CHART_JAC) THEN
    ASM_REWRITE_TAC[chart_jac; SND; o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_trans (S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f)
                ((:A),SND (c':(B->bool)#(B->real^N)) o f) (SND c (f w)) = SND c' (f w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[chart_trans; SND; o_THM] THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:A` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                 `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`;
                 `g:B->real^N^N`; `(f:A->B) w`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* The central identity: in a lifted chart the pullback metric has the       *)
(* representative of g in the base chart.                                    *)

let MFDL_METRIC_LOCAL = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) S c w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     w IN S /\ f w IN FST c
     ==> metric_local (mfd_lift_atlas topc top f atlas) (S INTER {w | f w IN FST c},SND c o f)
                      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
                      (SND c (f w)) =
         metric_local atlas c g (SND c (f w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A) IN topspace topc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:A` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `S1:A->bool`; `c1:(B->bool)#(B->real^N)`; `w:A`]
                MFDL_PULLBACK_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`;
                 `S1 INTER {w | (f:A->B) w IN FST (c1:(B->bool)#(B->real^N))}`;
                 `c1:(B->bool)#(B->real^N)`; `w:A`] MFDL_CHART_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                 `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                 `g:B->real^N^N`; `(f:A->B) w`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let MFDL_METRIC_LOCAL_ON = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) S c z.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     z IN IMAGE (SND c o f) (S INTER {w | f w IN FST c})
     ==> metric_local (mfd_lift_atlas topc top f atlas) (S INTER {w | f w IN FST c},SND c o f)
                      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) z =
         metric_local atlas c g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDL_METRIC_LOCAL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The lifted metric is Riemannian, and scalar curvature, sectional          *)
(* curvatures (up to the Jacobian J between the base chart of the preferred  *)
(* lifted chart and the preferred base chart) and |Rm| at w are those of g   *)
(* at f w.                                                                   *)
(* ========================================================================= *)

let MFDL_RIEMANNIAN = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g
     ==> riemannian_metric (mfd_lift_atlas topc top f atlas)
                           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
  REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local atlas (c:(B->bool)#(B->real^N)) (g:B->real^N^N)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MFDL_METRIC_LOCAL_ON THEN ASM_REWRITE_TAC[]]);;

(* The point of the base chart of the preferred lifted chart. *)

let MFDL_PREF = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     w IN topspace topc
     ==> ?S c. open_in topc S /\ open_in top (IMAGE f S) /\
               homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
               c IN atlas /\ w IN S /\ f w IN FST c /\
               chart_at (mfd_lift_atlas topc top f atlas) w =
               (S INTER {w | f w IN FST c},SND c o f) /\
               f w IN topspace top /\
               open (IMAGE (SND c o f) (S INTER {w | f w IN FST c})) /\
               SND c (f w) IN IMAGE (SND c o f) (S INTER {w | f w IN FST c})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:(B->bool)#(B->real^N)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MFDL_SCALAR = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ w IN topspace topc
     ==> mfd_scalar (mfd_lift_atlas topc top f atlas)
                    (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) w =
         mfd_scalar atlas g (f w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_PREF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    STRIP_ASSUME_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [mfd_scalar] THEN ASM_REWRITE_TAC[SND; o_THM] THEN
  TRANS_TAC EQ_TRANS
   `lscalar (metric_local atlas (c:(B->bool)#(B->real^N)) (g:B->real^N^N)) (SND c ((f:A->B) w))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N)) o (f:A->B)) (S INTER {w | f w IN FST c})` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MFDL_METRIC_LOCAL_ON THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                   `g:B->real^N^N`; `(f:A->B) w`] MFD_SCALAR_CHART) THEN
    ASM_REWRITE_TAC[PAIR]]);;

(* Sectional curvatures: the lifted ones at w are those of g at f w after a *)
(* linear isomorphism J (with inverse K).                                    *)

let MFDL_SECTIONAL = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ w IN topspace topc
     ==> ?J K. linear J /\ linear K /\ (!v. K(J v) = v) /\ (!v. J(K v) = v) /\
               !u v. mfd_sectional (mfd_lift_atlas topc top f atlas)
                       (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) w u v =
                     mfd_sectional atlas g (f w) (J u) (J v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_PREF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) w`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w)` THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`chart_jac (c:(B->bool)#(B->real^N)) c' ((f:A->B) w)`;
                        `chart_jac (c':(B->bool)#(B->real^N)) c ((f:A->B) w)`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                   `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`;
                   `(f:A->B) w`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`;
                   `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                   `(f:A->B) w`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                   `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`;
                   `(f:A->B) w`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`;
                   `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                   `(f:A->B) w`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM];
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[SND; o_THM] THEN
    TRANS_TAC EQ_TRANS
     `lsectional (metric_local atlas (c:(B->bool)#(B->real^N)) (g:B->real^N^N))
                 (SND c ((f:A->B) w)) u v` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
      EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N)) o (f:A->B)) (S INTER {w | f w IN FST c})` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC MFDL_METRIC_LOCAL_ON THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                     `FST (c':(B->bool)#(B->real^N))`; `SND (c':(B->bool)#(B->real^N))`;
                     `g:B->real^N^N`; `(f:A->B) w`; `u:real^N`; `v:real^N`]
                    LSECTIONAL_CHART_TRANS) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER]]]);;

let MFDL_SECTIONAL_SET = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ w IN topspace topc
     ==> {mfd_sectional (mfd_lift_atlas topc top f atlas)
            (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) w u v |
          u,v | ~collinear {vec 0,u,v}} =
         {mfd_sectional atlas g (f w) u v | u,v | ~collinear {vec 0,u,v}}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `w:A`] MFDL_SECTIONAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^N->real^N` (X_CHOOSE_THEN `K:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!u v. collinear {vec 0,(J:real^N->real^N) u,J v} <=> collinear {vec 0,u,v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0,(J:real^N->real^N) u,J v} = IMAGE J {vec 0,u,v}`
     SUBST1_TAC THENL
     [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (J:real^N->real^N)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC COLLINEAR_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. collinear {vec 0,(K:real^N->real^N) u,K v} <=> collinear {vec 0,u,v}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `{vec 0,(K:real^N->real^N) u,K v} = IMAGE K {vec 0,u,v}`
     SUBST1_TAC THENL
     [MP_TAC(MATCH_MP LINEAR_0 (ASSUME `linear (K:real^N->real^N)`)) THEN
      SIMP_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC COLLINEAR_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(J:real^N->real^N) u`; `(J:real^N->real^N) v`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(K:real^N->real^N) u`; `(K:real^N->real^N) v`] THEN
    ASM_REWRITE_TAC[]]);;

let MFDL_RM_NORM = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ w IN topspace topc
     ==> mfd_rm_norm (mfd_lift_atlas topc top f atlas)
                     (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) w =
         mfd_rm_norm atlas g (f w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `w:A`] MFDL_SECTIONAL_SET) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

let MFDL_SECTIONAL_NONNEG = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ w IN topspace topc /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 <= mfd_sectional atlas g (f w) u v)
     ==> !u v. ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional (mfd_lift_atlas topc top f atlas)
                          (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
                          w u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `w:A`] MFDL_SECTIONAL_SET) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC
   `mfd_sectional (mfd_lift_atlas topc top f atlas)
      (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))
                           atlas f (g:B->real^N^N)) w (u:real^N) (v:real^N)`) THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Curves.  f is smooth for the lifted atlas; C^1 curves project to C^1      *)
(* curves of the same length, continuous lifts of C^1 curves are C^1,        *)
(* distances do not increase under f, and for a covering map f maps the      *)
(* lifted ball B(w,r) onto B(f w,r) (path lifting).                          *)
(* ========================================================================= *)

let MFDL_SMOOTH_MAP = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f
     ==> mfd_smooth_map (mfd_lift_atlas topc top f atlas) atlas (topspace topc) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`cc:(A->bool)#(A->real^N)`; `c:(B->bool)#(B->real^N)`] THEN
  REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) ASSUME_TAC) THEN
  REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `chart_trans (c1:(B->bool)#(B->real^N)) c` THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `S:A->bool`; `c1:(B->bool)#(B->real^N)`] MFDL_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:A` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                   `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                   `(f:A->B) w`] CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[PAIR];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1 INTER FST (c:(B->bool)#(B->real^N)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                     `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`]
                    CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]]]);;

let MFDL_C1_PROJECT = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) gamma a b.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     mfd_c1_curve (topc,mfd_lift_atlas topc top f atlas) gamma a b /\ a < b
     ==> mfd_c1_curve (top,atlas) (f o gamma) a b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGD_C1_CURVE_PUSH THEN
  MAP_EVERY EXISTS_TAC [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                        `topspace topc:A->bool`] THEN
  ASM_SIMP_TAC[MFDL_ATLAS; MFDL_SMOOTH_MAP; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE;
               MFDL_LH_CONTINUOUS] THEN
  ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]);;

(* A continuous lift of a C^1 curve is C^1. *)

let MFDL_C1_LIFT = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) gamma h a b.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     mfd_c1_curve (top,atlas) gamma a b /\
     continuous_map (subtopology euclideanreal (real_interval[a,b]),topc) h /\
     (!t. t IN real_interval[a,b] ==> f(h t) = gamma t)
     ==> mfd_c1_curve (topc,mfd_lift_atlas topc top f atlas) h a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_c1_curve] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
  REWRITE_TAC[FST; SND; o_THM] THEN
  MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
  EXISTS_TAC `\s. SND (c:(B->bool)#(B->real^N)) ((gamma:real->B) (drop s))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{s | s IN interval[lift a,lift b] /\
                     (gamma:real->B) (drop s) IN FST (c:(B->bool)#(B->real^N))}` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:A->B) (h (drop (x:real^1))) = gamma (drop x)` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
      ASM_REWRITE_TAC[]]]);;

(* Speeds and lengths. *)

let MFDL_SPEED = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) gamma a b t.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     mfd_c1_curve (topc,mfd_lift_atlas topc top f atlas) gamma a b /\ a < b /\
     t IN real_interval[a,b]
     ==> mfd_speed (mfd_lift_atlas topc top f atlas)
                   (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
                   gamma a b t =
         mfd_speed atlas g (f o gamma) a b t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace topc` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `(gamma:real->A) t`] MFDL_PREF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  SUBGOAL_THEN `(S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f) IN
                mfd_lift_atlas topc top f atlas` ASSUME_TAC THENL
   [REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY EXISTS_TAC [`S:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      (g:B->real^N^N)`;
                 `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}`;
                 `SND (c:(B->bool)#(B->real^N)) o (f:A->B)`] MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `(f:A->B) o (gamma:real->A)`; `a:real`; `b:real`; `t:real`;
                 `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`]
                MFD_SPEED_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PAIR; o_THM] THEN MATCH_MP_TAC MFDL_C1_PROJECT THEN
    EXISTS_TAC `topc:A topology` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_THM; PAIR] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `S:A->bool`; `c:(B->bool)#(B->real^N)`;
                 `(gamma:real->A) t`] MFDL_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let MFDL_LENGTH = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) gamma a b.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     mfd_c1_curve (topc,mfd_lift_atlas topc top f atlas) gamma a b /\ a < b
     ==> mfd_length (mfd_lift_atlas topc top f atlas)
                    (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
                    gamma a b =
         mfd_length atlas g (f o gamma) a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC MFDL_SPEED THEN
  ASM_REWRITE_TAC[]);;

(* Joinability and distances. *)

let MFDL_DIST = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w1 w2.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\
     mfd_joinable (topc,mfd_lift_atlas topc top f atlas) w1 w2
     ==> mfd_joinable (top,atlas) (f w1) (f w2) /\
         mfd_dist (top,atlas) g (f w1) (f w2) <=
         mfd_dist (topc,mfd_lift_atlas topc top f atlas)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) w1 w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_joinable (topc,mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) w1 w2` THEN
    REWRITE_TAC[mfd_joinable] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:A->B) o (gamma:real->A)` THEN ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC MFDL_C1_PROJECT THEN EXISTS_TAC `topc:A topology` THEN
    ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `mfd_joinable (topc,mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) w1 w2` THEN
    REWRITE_TAC[mfd_joinable; GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `gamma:real->A`; `&0`; `&1`] MFDL_LENGTH) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(f:A->B) w1 = (f o gamma) (&0) /\ f w2 = (f o (gamma:real->A)) (&1)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDL_C1_PROJECT THEN EXISTS_TAC `topc:A topology` THEN
  ASM_REWRITE_TAC[REAL_LT_01]);;

(* For a covering map, f maps lifted balls onto balls. *)

let MFDL_BALL_IMAGE = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) w r.
     smooth_manifold_atlas top atlas /\ covering_map (topc,top) f /\
     riemannian_metric atlas g /\ w IN topspace topc
     ==> IMAGE f (mfd_ball (topc,mfd_lift_atlas topc top f atlas)
                           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
                           w r) =
         mfd_ball (top,atlas) g (f w) r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (f:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) /\
                riemannian_metric (mfd_lift_atlas topc top f atlas)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                       (g:B->real^N^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS; MFDL_RIEMANNIAN]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; mfd_ball; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `g:B->real^N^N`; `w:A`; `z:A`] MFDL_DIST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
            gamma(&0) = (f:A->B) w /\ gamma(&1) = y /\
            mfd_length atlas (g:B->real^N^N) gamma (&0) (&1) < r`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[] `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^N^N) ((f:A->B) w) y < r` THEN
    REWRITE_TAC[REAL_NOT_LT; mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_joinable (top,atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w) y` THEN
      REWRITE_TAC[mfd_joinable; GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN MESON_TAC[];
      REWRITE_TAC[GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[REAL_NOT_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `gamma:real->B`; `w:A`]
                COVERING_MAP_LIFT_PATH_STRONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[path_in] THEN ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  REWRITE_TAC[path_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_c1_curve (topc,mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) h (&0) (&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDL_C1_LIFT THEN EXISTS_TAC `gamma:real->B` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(h:real->A) (&1)` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN TRANS_TAC EQ_TRANS `(gamma:real->B) (&1)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
      check (fun th -> can (find_term ((=) `(h:real->A) (&0)`)) (concl th))) THEN
    MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
   `mfd_length (mfd_lift_atlas topc top f atlas)
      (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) atlas f (g:B->real^N^N))
      (h:real->A) (&0) (&1)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `w = (h:real->A) (&0)` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `h:real->A`; `&0`; `&1`] MFDL_LENGTH) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `mfd_length atlas (g:B->real^N^N) ((f:A->B) o (h:real->A)) (&0) (&1) =
                mfd_length atlas g (gamma:real->B) (&0) (&1)` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN ASM_SIMP_TAC[o_THM]; ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Completeness.  If f is proper (preimages of compact sets are compact) and *)
(* g is complete, the lifted metric is complete: a closed ball of the lift   *)
(* is closed and lies in the preimage of the closed ball of the same radius  *)
(* around the image point (distances do not increase).                       *)
(* ========================================================================= *)

let MFDL_COMPLETE = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!K. compact_in top K ==> compact_in topc {w | w IN topspace topc /\ f w IN K})
     ==> mfd_complete (topc,mfd_lift_atlas topc top f atlas)
                      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "prop" (last(CONJUNCTS th))) THEN
  REWRITE_TAC[mfd_complete] THEN MAP_EVERY X_GEN_TAC [`w:A`; `r:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) /\
                riemannian_metric (mfd_lift_atlas topc top f atlas)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                       (g:B->real^N^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS; MFDL_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (topc,top) (f:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDL_LH_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) w IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`]
                  CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:A) IN topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `{z | z IN topspace topc /\
                   (f:A->B) z IN mfd_cball (top,atlas) (g:B->real^N^N) (f w) r}` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "prop" MATCH_MP_TAC THEN
    UNDISCH_TAC `mfd_complete (top,atlas:((B->bool)#(B->real^N))->bool) (g:B->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `g:B->real^N^N`; `w:A`; `z:A`] MFDL_DIST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Volumes.  A measurable set inside one lifted chart has the volume of its  *)
(* image (MFDL_VOLUME_CHART); a set covered by finitely many lifted chart    *)
(* domains has an image of no larger volume (subadditivity), so for E inside *)
(* a compact set vol(IMAGE f E) <= vol(E) (MFDL_VOLUME_GE).                  *)
(* ========================================================================= *)

let MFDL_HAS_VOLUME_EMPTY = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N).
     mfd_has_volume (top,atlas) g {} (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_has_volume; mfd_has_integral; mfd_chart_partition] THEN
  MAP_EVERY EXISTS_TAC [`\n:num. (@c:(A->bool)#(A->real^N). T)`; `\n:num. {}:A->bool`] THEN
  REWRITE_TAC[EMPTY_SUBSET; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY; DISJOINT_EMPTY;
              INTEGRAL_EMPTY; DROP_VEC; ABSOLUTELY_INTEGRABLE_ON_EMPTY; REAL_SUMMABLE_0;
              REAL_SERIES_0] THEN
  REWRITE_TAC[UNIONS_GSPEC; NOT_IN_EMPTY; EMPTY_GSPEC]);;

(* Finite subadditivity for two sets. *)

let MFDL_HAS_VOLUME_UNION_LE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) X Y u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_volume (top,atlas) g X u /\ mfd_has_volume (top,atlas) g Y v
     ==> ?w. mfd_has_volume (top,atlas) g (X UNION Y) w /\ w <= u + v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) X /\
                mfd_lebesgue_measurable (top,atlas) Y`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_has_volume; MFD_HAS_INTEGRAL_IMP_MEASURABLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `(Y:A->bool) DIFF X`; `Y:A->bool`; `v:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_DIFF; SUBSET_DIFF] THEN STRIP_TAC THEN
  EXISTS_TAC `u + mfd_volume (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                             ((Y:A->bool) DIFF X)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(X:A->bool) UNION Y = X UNION (Y DIFF X)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* A set inside one lifted chart has the volume of its image. *)

let MFDL_VOLUME_CHART = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) S c E v.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ c IN atlas /\
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     E SUBSET S INTER {w | f w IN FST c}
     ==> (mfd_has_volume (topc,mfd_lift_atlas topc top f atlas)
            (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) E v <=>
          mfd_has_volume (top,atlas) g (IMAGE f E) v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) /\
                riemannian_metric (mfd_lift_atlas topc top f atlas)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                       (g:B->real^N^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS; MFDL_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `(S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f) IN
                mfd_lift_atlas topc top f atlas` ASSUME_TAC THENL
   [REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY EXISTS_TAC [`S:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      (g:B->real^N^N)`;
                 `(S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f)`;
                 `E:A->bool`; `v:real`] MFD_HAS_VOLUME_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `c:(B->bool)#(B->real^N)`; `IMAGE (f:A->B) E`; `v:real`]
                MFD_HAS_VOLUME_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND (c:(B->bool)#(B->real^N))) (IMAGE (f:A->B) E)
        ==> lift(mfd_density (mfd_lift_atlas topc top f atlas)
                   (S INTER {w | f w IN FST c},SND c o f)
                   (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                        (g:B->real^N^N)) y) =
            lift(mfd_density atlas c g y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_density] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MFDL_METRIC_LOCAL_ON THEN ASM_REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `(y:real^N) IN IMAGE (SND (c:(B->bool)#(B->real^N))) (IMAGE (f:A->B) E)` THEN
    UNDISCH_TAC `(E:A->bool) SUBSET S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(b <=> b') /\ (c <=> c') ==> (a /\ b /\ c <=> a /\ b' /\ c')`) THEN
  CONJ_TAC THENL
   [EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABSOLUTELY_INTEGRABLE_EQ) THEN
    ASM_SIMP_TAC[];
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    ASM_SIMP_TAC[]]);;

(* Finitely many open sets on which volumes are those of the images. *)

let MFDL_VOLUME_IMAGE_LE = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g
     ==> !V. FINITE V
             ==> (!u. u IN V
                      ==> open_in topc u /\
                          !E x. E SUBSET u
                                ==> (mfd_has_volume (topc,mfd_lift_atlas topc top f atlas)
                                       (mfd_pullback_metric (mfd_lift_atlas topc top f atlas)
                                                            atlas f g) E x <=>
                                     mfd_has_volume (top,atlas) g (IMAGE f E) x))
             ==> !E v. E SUBSET UNIONS V /\
                       mfd_has_volume (topc,mfd_lift_atlas topc top f atlas)
                         (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) E v
                       ==> ?v'. mfd_has_volume (top,atlas) g (IMAGE f E) v' /\ v' <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) /\
                riemannian_metric (mfd_lift_atlas topc top f atlas)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                       (g:B->real^N^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS; MFDL_RIEMANNIAN]; ALL_TAC] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; SUBSET_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`E:A->bool`; `v:real`] THEN STRIP_TAC THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; MFDL_HAS_VOLUME_EMPTY] THEN
    MATCH_MP_TAC MFD_HAS_VOLUME_POS_LE THEN
    MAP_EVERY EXISTS_TAC
     [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
      `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B) (g:B->real^N^N)`;
      `E:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `V:(A->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hu")) (LABEL_TAC "hV")) THEN
  MAP_EVERY X_GEN_TAC [`E:A->bool`; `v:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_lebesgue_measurable (topc,mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) (E:A->bool) /\
    mfd_lebesgue_measurable (topc,mfd_lift_atlas topc top f atlas) (u:A->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
      MAP_EVERY EXISTS_TAC
       [`mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B) (g:B->real^N^N)`;
        `\x:A. &1`; `v:real`] THEN
      ASM_REWRITE_TAC[GSYM mfd_has_volume];
      MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `mu = mfd_volume (topc,mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))
                     (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                          (g:B->real^N^N))` THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      (g:B->real^N^N)`;
                 `(E:A->bool) DIFF (E DIFF u)`; `E:A->bool`; `v:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_DIFF; SUBSET_DIFF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      (g:B->real^N^N)`;
                 `(E:A->bool) DIFF u`; `E:A->bool`; `v:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_DIFF; SUBSET_DIFF] THEN STRIP_TAC THEN
  (* additivity in the cover *)
  SUBGOAL_THEN `v = mu ((E:A->bool) DIFF (E DIFF u)) + mu (E DIFF u)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
      `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B) (g:B->real^N^N)`;
      `E:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(E:A->bool) = (E DIFF (E DIFF u)) UNION (E DIFF u)`
     (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the part in u *)
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:B->real^N^N) (IMAGE (f:A->B) (E DIFF (E DIFF u)))
                   (mu ((E:A->bool) DIFF (E DIFF u)))`
  ASSUME_TAC THENL
   [USE_THEN "hu" (fun th -> REWRITE_TAC[GSYM(MP (SPECL [`(E:A->bool) DIFF (E DIFF u)`;
                                                     `mu ((E:A->bool) DIFF (E DIFF u)):real`] th)
                                               (SET_RULE `(E:A->bool) DIFF (E DIFF u) SUBSET u`))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the rest: induction *)
  USE_THEN "hV" (fun hv -> USE_THEN "ih" (fun ih ->
    MP_TAC(SPECL [`(E:A->bool) DIFF u`; `mu ((E:A->bool) DIFF u):real`] (MP ih hv)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(E:A->bool) SUBSET UNIONS ((u:A->bool) INSERT V)` THEN
    REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `IMAGE (f:A->B) (E DIFF (E DIFF u))`; `IMAGE (f:A->B) (E DIFF u)`;
                 `mu ((E:A->bool) DIFF (E DIFF u)):real`; `v2:real`]
                MFDL_HAS_VOLUME_UNION_LE) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_UNION] THEN
  SUBGOAL_THEN `((E:A->bool) DIFF (E DIFF u)) UNION (E DIFF u) = E` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The volume inequality for sets inside a compact set. *)

let MFDL_VOLUME_GE = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) K E v v'.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\ compact_in topc K /\ E SUBSET K /\
     mfd_has_volume (topc,mfd_lift_atlas topc top f atlas)
       (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) E v /\
     mfd_has_volume (top,atlas) g (IMAGE f E) v'
     ==> v' <= v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  UNDISCH_TAC `compact_in topc (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `IMAGE FST (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`; `z:A`]
                  CHART_AT) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`] MFDL_VOLUME_IMAGE_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `V:(A->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?cc. cc IN mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool) /\
                       (u:A->bool) = FST cc` MP_TAC THENL
     [UNDISCH_TAC `(V:(A->bool)->bool) SUBSET IMAGE FST (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))` THEN
      UNDISCH_TAC `(u:A->bool) IN V` THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:(A->bool)#(A->real^N)` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`topc:A topology`;
                     `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                     `cc:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(cc:(A->bool)#(A->real^N)) IN mfd_lift_atlas topc (top:B topology) (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)` THEN
    REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
    REWRITE_TAC[FST] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MFDL_VOLUME_CHART THEN
    MAP_EVERY EXISTS_TAC [`S:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`E:A->bool`; `v:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v'':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v':real = v''` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                       `g:B->real^N^N`; `IMAGE (f:A->B) E`] MFD_HAS_VOLUME_UNIQUE) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Orientations.  Families of lifted charts that cover are smooth atlases;   *)
(* sheets restrict to open sets; an oriented atlas of the image f(W) of an   *)
(* open set W lifts to an oriented atlas of W (the lifted transition         *)
(* Jacobians are those of the base), so orientability lifts.                 *)
(* ========================================================================= *)

let MFDL_ATLAS_SUBSET = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) A.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     A SUBSET mfd_lift_atlas topc top f atlas /\
     (!w. w IN topspace topc ==> ?U phi. (U,phi) IN A /\ w IN U)
     ==> smooth_manifold_atlas topc A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`] MFDL_ATLAS) THEN
  ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "homeomorphic_map")) (concl th))) THEN
    ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th))) THEN
    ASM SET_TAC[]]);;

(* A sheet meets an open set W in a sheet of the restriction of f to W. *)

let MFDL_SHEET_RESTRICT = prove
 (`!topc top (f:A->B) S W.
     local_homeomorphism_map (topc,top) f /\ open_in topc W /\
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f
     ==> open_in (subtopology topc W) (S INTER W) /\
         open_in (subtopology top (IMAGE f W)) (IMAGE f (S INTER W)) /\
         homeomorphic_map (subtopology (subtopology topc W) (S INTER W),
                           subtopology (subtopology top (IMAGE f W)) (IMAGE f (S INTER W))) f /\
         open_in top (IMAGE f W) /\ open_in top (IMAGE f (S INTER W))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_map (topc,top) (f:A->B)` MP_TAC THENL
   [ASM_MESON_TAC[TOPC_LOCAL_HOMEOMORPHISM_OPEN_MAP]; REWRITE_TAC[open_map] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `open_in topc ((S:A->bool) INTER W)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (f:A->B) W) /\ open_in top (IMAGE f (S INTER W))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(W:A->bool) INTER (S INTER W) = S INTER W /\
                  IMAGE (f:A->B) W INTER IMAGE f (S INTER W) = IMAGE f (S INTER W)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `subtopology topc ((S:A->bool) INTER W) = subtopology (subtopology topc S) (S INTER W) /\
      subtopology top (IMAGE (f:A->B) (S INTER W)) =
      subtopology (subtopology top (IMAGE f S)) (IMAGE f (S INTER W))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THEN AP_TERM_TAC THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `IMAGE (f:A->B) S SUBSET topspace top` THEN
    UNDISCH_TAC `(S:A->bool) SUBSET topspace topc` THEN SET_TAC[]]);;

let MFDL_LH_RESTRICT = prove
 (`!topc top (f:A->B) W.
     local_homeomorphism_map (topc,top) f /\ open_in topc W
     ==> local_homeomorphism_map (subtopology topc W,subtopology top (IMAGE f W)) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[local_homeomorphism_map] THEN
  X_GEN_TAC `w:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `w:A`] MFDL_LH_SHEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`; `W:A->bool`]
                MFDL_SHEET_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(S:A->bool) INTER W`; `IMAGE (f:A->B) (S INTER W)`] THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* Orientability lifts. *)

let MFDL_ORIENTABLE = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) W.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     open_in topc W /\
     mfd_orientable (subtopology top (IMAGE f W)) (restrict_atlas atlas (IMAGE f W))
     ==> mfd_orientable (subtopology topc W) (restrict_atlas (mfd_lift_atlas topc top f atlas) W)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_orientable] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `A1:((B->bool)#(B->real^N))->bool` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `local_homeomorphism_map (subtopology topc W,subtopology top (IMAGE (f:A->B) W)) f`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_LH_RESTRICT]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top (IMAGE (f:A->B) W))
                                      (restrict_atlas (atlas:((B->bool)#(B->real^N))->bool)
                                                      (IMAGE f W))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[TOPC_LOCAL_HOMEOMORPHISM_OPEN_MAP; open_map];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_lift_atlas (subtopology topc W) (subtopology top (IMAGE (f:A->B) W)) f
                             (A1:((B->bool)#(B->real^N))->bool)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDL_ATLAS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFDL_ATLAS_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`subtopology top (IMAGE (f:A->B) W)`;
                          `restrict_atlas (atlas:((B->bool)#(B->real^N))->bool) (IMAGE (f:A->B) W)
                           UNION A1`; `f:A->B`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_RESTRICT_ATLAS; IN_MFD_LIFT_ATLAS] THEN
        MAP_EVERY X_GEN_TAC [`U':A->bool`; `phi:A->real^N`] THEN
        DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
        DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
          STRIP_ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`; `W:A->bool`]
                      MFDL_SHEET_RESTRICT) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [`(S:A->bool) INTER W`;
                              `(FST (c:(B->bool)#(B->real^N)) INTER IMAGE (f:A->B) W,SND c)`] THEN
        ASM_REWRITE_TAC[IN_UNION; FST; SND] THEN CONJ_TAC THENL
         [DISJ1_TAC THEN REWRITE_TAC[IN_RESTRICT_ATLAS] THEN
          EXISTS_TAC `FST (c:(B->bool)#(B->real^N))` THEN ASM_REWRITE_TAC[PAIR];
          UNDISCH_TAC `(U:A->bool,phi:A->real^N) =
                       S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f` THEN
          REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
          REWRITE_TAC[PAIR_EQ] THEN SET_TAC[]];
        REWRITE_TAC[SUBSET; IN_MFD_LIFT_ATLAS; IN_UNION] THEN MESON_TAC[]];
      MP_TAC(ISPECL [`subtopology topc (W:A->bool)`; `subtopology top (IMAGE (f:A->B) W)`;
                     `A1:((B->bool)#(B->real^N))->bool`; `f:A->B`] MFDL_ATLAS) THEN
      ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      REWRITE_TAC[IN_UNION] THEN MESON_TAC[]];
    REWRITE_TAC[mfd_oriented_atlas; IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY X_GEN_TAC [`cc1:(A->bool)#(A->real^N)`; `cc2:(A->bool)#(A->real^N)`; `w:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `S2:A->bool` (X_CHOOSE_THEN `c2:(B->bool)#(B->real^N)` STRIP_ASSUME_TAC))
      MP_TAC)) THEN
    ASM_REWRITE_TAC[FST; IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology topc (W:A->bool)`; `subtopology top (IMAGE (f:A->B) W)`;
                   `A1:((B->bool)#(B->real^N))->bool`; `f:A->B`; `S1:A->bool`;
                   `c1:(B->bool)#(B->real^N)`;
                   `S2 INTER {w | (f:A->B) w IN FST (c2:(B->bool)#(B->real^N))}`;
                   `c2:(B->bool)#(B->real^N)`; `w:A`] MFDL_CHART_JAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `mfd_oriented_atlas (A1:((B->bool)#(B->real^N))->bool)` THEN
    REWRITE_TAC[mfd_oriented_atlas] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER]]);;

(* ========================================================================= *)
(* Vectors.  A family V of vectors given at the points f w in the preferred  *)
(* charts of the base is lifted to the preferred charts of the lifted atlas  *)
(* (mfd_lift_vec, through the base chart mfd_lift_base of the preferred      *)
(* lifted chart).  In a lifted chart its representative is that of V in the  *)
(* base chart (MFDL_VREP), and inner products for the pullback metric are    *)
(* those of the base (MFDL_LIFT_VEC_DOT).                                    *)
(* ========================================================================= *)

let mfd_lift_base = new_definition
 `mfd_lift_base (topc:A topology) (top:B topology) (f:A->B)
                (atlas:((B->bool)#(B->real^N))->bool) (w:A) =
    @c. c IN atlas /\ f w IN FST c /\
        ?S. open_in topc S /\ open_in top (IMAGE f S) /\
            homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
            w IN S /\
            chart_at (mfd_lift_atlas topc top f atlas) w = (S INTER {z | f z IN FST c},SND c o f)`;;

let mfd_lift_vec = new_definition
 `mfd_lift_vec (topc:A topology) (top:B topology) (f:A->B)
               (atlas:((B->bool)#(B->real^N))->bool) (V:A->real^N) =
    \w. chart_jac (chart_at atlas (f w)) (mfd_lift_base topc top f atlas w) (f w) (V w)`;;

let MFDL_LIFT_BASE = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     w IN topspace topc
     ==> mfd_lift_base topc top f atlas w IN atlas /\
         f w IN FST (mfd_lift_base topc top f atlas w) /\
         ?S. open_in topc S /\ open_in top (IMAGE f S) /\
             homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
             w IN S /\
             chart_at (mfd_lift_atlas topc top f atlas) w =
             (S INTER {z | f z IN FST (mfd_lift_base topc top f atlas w)},
              SND (mfd_lift_base topc top f atlas w) o f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_lift_base] THEN CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `c:(B->bool)#(B->real^N)` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[]);;

(* The representative of a lifted vector family in a lifted chart. *)

let MFDL_VREP = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (V:A->real^N) S c w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     w IN S /\ f w IN FST c
     ==> mfd_vrep (mfd_lift_atlas topc top f atlas) (mfd_lift_vec topc top f atlas V)
                  (S INTER {w | f w IN FST c},SND c o f) (SND c (f w)) =
         chart_jac (chart_at atlas (f w)) c (f w) (V w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S:A->bool`] MFDL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A) IN topspace topc /\ (f:A->B) w IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_vrep] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:A` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_LIFT_BASE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c1 = mfd_lift_base topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool) w` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `S1:A->bool` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[mfd_lift_vec] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S1:A->bool`; `c1:(B->bool)#(B->real^N)`;
                 `S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}`;
                 `c:(B->bool)#(B->real^N)`; `w:A`] MFDL_CHART_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `(f:A->B) w`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST (chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w))`;
                 `SND (chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w))`;
                 `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                 `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                 `(f:A->B) w`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

let MFDL_VREP_EQ = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (V:A->real^N) (Y:B->real^N)
    S c Ow z.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     c IN atlas /\ open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     Ow SUBSET S INTER {w | f w IN FST c} /\ (!w. w IN Ow ==> V w = Y(f w)) /\
     z IN IMAGE (SND c o f) Ow
     ==> mfd_vrep (mfd_lift_atlas topc top f atlas) (mfd_lift_vec topc top f atlas V)
                  (S INTER {w | f w IN FST c},SND c o f) z =
         mfd_vrep atlas Y c z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `(x:A) IN S /\ (f:A->B) x IN FST (c:(B->bool)#(B->real^N))` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `V:A->real^N`; `S:A->bool`; `c:(B->bool)#(B->real^N)`; `x:A`]
                MFDL_VREP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mfd_vrep] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* Inner products of lifted vectors for the pullback metric. *)

let MFDL_LIFT_VEC_DOT = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N)
    (V1:A->real^N) V2 w.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     w IN topspace topc
     ==> mfd_lift_vec topc top f atlas V1 w dot
         (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g w **
          mfd_lift_vec topc top f atlas V2 w) =
         V1 w dot (g(f w) ** V2 w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `w:A`] MFDL_LIFT_BASE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c1 = mfd_lift_base topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool) w` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `S1:A->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `g:B->real^N^N`; `S1:A->bool`; `c1:(B->bool)#(B->real^N)`; `w:A`]
                MFDL_PULLBACK_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:A->B) w IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `S1:A->bool`] MFDL_SHEET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `(f:A->B) w`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) w)` THEN
  STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[mfd_lift_vec] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                 `FST (c0:(B->bool)#(B->real^N))`; `SND (c0:(B->bool)#(B->real^N))`;
                 `g:B->real^N^N`; `(f:A->B) w`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `(f:A->B) w`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `linear(chart_jac (c1:(B->bool)#(B->real^N)) c0 ((f:A->B) w)) /\
    linear(chart_jac c0 c1 (f w)) /\
    (!v. chart_jac c1 c0 (f w) (chart_jac c0 c1 (f w) v) = v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                     `FST (c0:(B->bool)#(B->real^N))`; `SND (c0:(B->bool)#(B->real^N))`;
                     `(f:A->B) w`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c0:(B->bool)#(B->real^N))`; `SND (c0:(B->bool)#(B->real^N))`;
                     `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                     `(f:A->B) w`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c0:(B->bool)#(B->real^N))`; `SND (c0:(B->bool)#(B->real^N))`;
                     `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                     `(f:A->B) w`] CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL; MATRIX_WORKS]);;

