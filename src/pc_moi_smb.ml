(* ========================================================================= *)
(* pc_moi_smb: smooth manifolds with boundary (basics).                      *)
(* A boundary atlas charts open sets of a space onto relatively open subsets *)
(* of the closed half-space 0 <= y$n (n = dimindex(:N)); transition maps are *)
(* restrictions of smooth maps on open neighbourhoods.  The boundary is the  *)
(* set of points charted to y$n = 0.  Results: invariance of the boundary,   *)
(* the interior atlas, the half-space and closed-ball examples, transport    *)
(* along homeomorphisms and restriction to open subsets (Lee, Introduction   *)
(* to Smooth Manifolds, Ch 1 and 9).                                         *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The two definitions.                                                      *)
(* ------------------------------------------------------------------------- *)

let smooth_boundary_atlas = new_definition
 `smooth_boundary_atlas (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) <=>
    (!U phi. (U,phi) IN atlas
             ==> open_in top U /\
                 open_in (subtopology euclidean {y:real^N | &0 <= y$(dimindex(:N))})
                         (IMAGE phi U) /\
                 homeomorphic_map (subtopology top U,
                                   subtopology euclidean (IMAGE phi U)) phi) /\
    (!x. x IN topspace top ==> ?U phi. (U,phi) IN atlas /\ x IN U) /\
    (!U phi V psi.
         (U,phi) IN atlas /\ (V,psi) IN atlas
         ==> ?g w. open w /\ IMAGE phi (U INTER V) SUBSET w /\ smooth_map_on w g /\
                   !x. x IN U INTER V ==> g(phi x) = psi x)`;;

let atlas_boundary = new_definition
 `atlas_boundary (atlas:((A->bool)#(A->real^N))->bool) =
    {x | ?U phi. (U,phi) IN atlas /\ x IN U /\ (phi x)$(dimindex(:N)) = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Unpacking a chart of a boundary atlas.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi.
     smooth_boundary_atlas top atlas /\ (U,phi) IN atlas
     ==> open_in top U /\ U SUBSET topspace top /\
         open_in (subtopology euclidean {y:real^N | &0 <= y$(dimindex(:N))})
                 (IMAGE phi U) /\
         IMAGE phi U SUBSET {y:real^N | &0 <= y$(dimindex(:N))} /\
         homeomorphic_map (subtopology top U,
                           subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_boundary_atlas] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]);;

let MOI_SMB_TRANSITION = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi V psi.
     smooth_boundary_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas
     ==> ?g w. open w /\ IMAGE phi (U INTER V) SUBSET w /\ smooth_map_on w g /\
               !x. x IN U INTER V ==> g(phi x) = psi x`,
  REWRITE_TAC[smooth_boundary_atlas] THEN MESON_TAC[]);;

let MOI_SMB_COVER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) x.
     smooth_boundary_atlas top atlas /\ x IN topspace top
     ==> ?U phi. (U,phi) IN atlas /\ x IN U`,
  REWRITE_TAC[smooth_boundary_atlas] THEN MESON_TAC[]);;

(* An open subset of the closed half-space lies in the open half-space.      *)

let MOI_SMB_OPEN_IN_HALF_SPACE = prove
 (`!s:real^N->bool.
     open s /\ s SUBSET {y:real^N | &0 <= y$(dimindex(:N))}
     ==> !y. y IN s ==> &0 < y$(dimindex(:N))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET interior {y:real^N | &0 <= y$(dimindex(:N))}`
  MP_TAC THENL [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&0`; `dimindex(:N)`] INTERIOR_HALFSPACE_COMPONENT_GE) THEN
  REWRITE_TAC[real_ge; real_gt] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM]);;

(* Restriction of a chart homeomorphism to a smaller domain.                 *)

let MOI_SMB_HOMEO_RESTRICT = prove
 (`!(top:A topology) U U' (phi:A->real^N).
     homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U)) phi /\
     U' SUBSET U /\ U SUBSET topspace top
     ==> homeomorphic_map (subtopology top U',subtopology euclidean (IMAGE phi U'))
                          phi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                 `subtopology euclidean (IMAGE (phi:A->real^N) U)`;
                 `phi:A->real^N`; `U':A->bool`; `IMAGE (phi:A->real^N) U'`]
                HOMEOMORPHIC_MAP_SUBTOPOLOGIES) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) INTER U' = U' /\
                IMAGE (phi:A->real^N) U INTER IMAGE phi U' = IMAGE phi U'`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Result: the closed half-space with the identity chart.                    *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_BOUNDARY_ATLAS_HALF_SPACE = prove
 (`smooth_boundary_atlas
    (subtopology euclidean {y:real^N | &0 <= y$(dimindex(:N))})
    {({y:real^N | &0 <= y$(dimindex(:N))},(\y. y))} /\
  atlas_boundary {({y:real^N | &0 <= y$(dimindex(:N))},(\y:real^N. y))} =
  {y:real^N | y$(dimindex(:N)) = &0}`,
  REWRITE_TAC[smooth_boundary_atlas; atlas_boundary; IN_SING; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IMAGE_ID; OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                SUBSET_UNIV; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT;
                HOMEOMORPHIC_MAP_ID];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`{y:real^N | &0 <= y$(dimindex(:N))}`;
                          `\y:real^N. y`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^N`;
                         `V:real^N->bool`; `psi:real^N->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST1_TAC)
                               (CONJUNCTS_THEN SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `(:real^N)`] THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_MAP_ON_ID];
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`{y:real^N | &0 <= y$(dimindex(:N))}`;
                            `\y:real^N. y`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of the boundary.  If psi x lies on y$n = 0 but phi x lies in   *)
(* the open half-space, the transition map g from phi to psi is continuous   *)
(* and injective on a small ball around phi x inside phi(U INTER V), so by   *)
(* invariance of domain its image is an open set inside the closed           *)
(* half-space containing psi x, which is impossible.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_OPEN_HALF_SPACE_POS = prove
 (`!(s:real^N->bool) y.
     open s /\ s SUBSET {y:real^N | &0 <= y$(dimindex(:N))} /\ y IN s
     ==> &0 < y$(dimindex(:N))`,
  MESON_TAC[MOI_SMB_OPEN_IN_HALF_SPACE]);;

let MOI_SMB_BOUNDARY_INVARIANT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi V psi x.
     smooth_boundary_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
     x IN U /\ x IN V /\ (psi x)$(dimindex(:N)) = &0
     ==> (phi x)$(dimindex(:N)) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] MOI_SMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                MOI_SMB_TRANSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N`
   (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(&0 < a) ==> a = &0`) THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (phi:A->real^N) U SUBSET {y:real^N | &0 <= y$(dimindex(:N))}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean {y:real^N | &0 <= y$(dimindex(:N))})
            (IMAGE (phi:A->real^N) (U INTER V))`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`;
                   `subtopology euclidean (IMAGE (phi:A->real^N) U)`;
                   `(U:A->bool) INTER V`] HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (t1 INTER {y:real^N | y$(dimindex(:N)) > &0})` MP_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) x` o REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_gt] THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball((phi:A->real^N) x,r) SUBSET IMAGE phi (U INTER V)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ball((phi:A->real^N) x,r) SUBSET
                 t1 INTER {y:real^N | y$(dimindex(:N)) > &0}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; real_gt] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^N) continuous_on ball((phi:A->real^N) x,r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN ball((phi:A->real^N) x,r) /\ y2 IN ball(phi x,r) /\
            (g:real^N->real^N) y1 = g y2 ==> y1 = y2`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y1:real^N) IN IMAGE (phi:A->real^N) (U INTER V) /\
                  y2 IN IMAGE phi (U INTER V)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z1:A` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `z2:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(psi:A->real^N) z1 = psi z2` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z1:A) = z2` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`subtopology top (V:A->bool)`;
                   `subtopology euclidean (IMAGE (psi:A->real^N) V)`;
                   `psi:A->real^N`] HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPECL [`z1:A`; `z2:A`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (g:real^N->real^N) (ball((phi:A->real^N) x,r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^N->real^N) (ball((phi:A->real^N) x,r)) SUBSET
    {y:real^N | &0 <= y$(dimindex(:N))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (phi:A->real^N) (U INTER V)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:real^N->real^N) y = (psi:A->real^N) z` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (psi:A->real^N) V SUBSET {y:real^N | &0 <= y$(dimindex(:N))}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(psi:A->real^N) x IN IMAGE (g:real^N->real^N) (ball((phi:A->real^N) x,r))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(phi:A->real^N) x` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (psi:A->real^N) x$(dimindex(:N))` MP_TAC THENL
   [MATCH_MP_TAC MOI_SMB_OPEN_HALF_SPACE_POS THEN
    EXISTS_TAC `IMAGE (g:real^N->real^N) (ball((phi:A->real^N) x,r))` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Result: membership in the boundary can be read off any chart.             *)
(* ------------------------------------------------------------------------- *)

let ATLAS_BOUNDARY_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi x.
     smooth_boundary_atlas top atlas /\ (U,phi) IN atlas /\ x IN U
     ==> (x IN atlas_boundary atlas <=> (phi x)$(dimindex(:N)) = &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[atlas_boundary; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `V:A->bool`
      (X_CHOOSE_THEN `psi:A->real^N` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                   `x:A`] MOI_SMB_BOUNDARY_INVARIANT) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

(* The part of a chart domain off the boundary.                              *)

let MOI_SMB_CHART_DIFF_BOUNDARY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi.
     smooth_boundary_atlas top atlas /\ (U,phi) IN atlas
     ==> U DIFF atlas_boundary atlas =
         {x | x IN U /\ &0 < (phi x)$(dimindex(:N))}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  ASM_CASES_TAC `(x:A) IN U` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `x:A`] ATLAS_BOUNDARY_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 <= (phi:A->real^N) x$(dimindex(:N))` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (phi:A->real^N) U SUBSET {y:real^N | &0 <= y$(dimindex(:N))}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Result: the boundary is closed.                                           *)
(* ------------------------------------------------------------------------- *)

let ATLAS_BOUNDARY_CLOSED_IN = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool).
     smooth_boundary_atlas top atlas ==> closed_in top (atlas_boundary atlas)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[atlas_boundary; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool`
      (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] MOI_SMB_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool`
    (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC
   `(U:A->bool) DIFF atlas_boundary (atlas:((A->bool)#(A->real^N))->bool)` THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[IN_DIFF]; ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART_DIFF_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{x:A | x IN U /\ &0 < (phi:A->real^N) x$(dimindex(:N))} =
    {x | x IN topspace (subtopology top U) /\
         phi x IN {y:real^N | y$(dimindex(:N)) > &0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; real_gt] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `euclidean:(real^N)topology` THEN
  REWRITE_TAC[GSYM OPEN_IN; OPEN_HALFSPACE_COMPONENT_GT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]);;

(* ------------------------------------------------------------------------- *)
(* Result: the interior, with the restricted charts, is a smooth manifold.   *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_IMAGE_DIFF_BOUNDARY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi.
     smooth_boundary_atlas top atlas /\ (U,phi) IN atlas
     ==> open (IMAGE phi (U DIFF atlas_boundary atlas))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART_DIFF_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `open_in (subtopology euclidean {y:real^N | &0 <= y$(dimindex(:N))})
            (IMAGE (phi:A->real^N) U)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `IMAGE (phi:A->real^N) {x | x IN U /\ &0 < phi x$(dimindex(:N))} =
    t1 INTER {y:real^N | y$(dimindex(:N)) > &0}`
  SUBST1_TAC THENL
   [UNDISCH_TAC
     `IMAGE (phi:A->real^N) U = {y:real^N | &0 <= y$(dimindex(:N))} INTER t1` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; real_gt] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT]]);;

let SMOOTH_BOUNDARY_ATLAS_INTERIOR = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool).
     smooth_boundary_atlas top atlas
     ==> smooth_manifold_atlas
           (subtopology top (topspace top DIFF atlas_boundary atlas))
           {(U DIFF atlas_boundary atlas,phi) | U,phi | (U,phi) IN atlas}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ATLAS_BOUNDARY_CLOSED_IN) THEN
  REWRITE_TAC[smooth_manifold_atlas; IN_ELIM_THM; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U':A->bool`; `phi':A->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U:A->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_SMB_IMAGE_DIFF_BOUNDARY THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN
       `(topspace top DIFF atlas_boundary atlas) INTER
        (U DIFF atlas_boundary atlas) =
        (U:A->bool) DIFF atlas_boundary (atlas:((A->bool)#(A->real^N))->bool)`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SMB_HOMEO_RESTRICT THEN EXISTS_TAC `U:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DIFF] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] MOI_SMB_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool`
      (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`(U:A->bool) DIFF atlas_boundary (atlas:((A->bool)#(A->real^N))->bool)`;
      `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U':A->bool`; `phi':A->real^N`;
                         `V':A->bool`; `psi':A->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))
      (X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                  MOI_SMB_TRANSITION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N`
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `g:real^N->real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_INTER; IN_DIFF] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]]);;

(* ------------------------------------------------------------------------- *)
(* Transport of a boundary atlas along a homeomorphism (adapted from         *)
(* MOI_SMOOTH_ATLAS_TRANSPORT of pc_moi_assembly.ml to boundary atlases; the *)
(* membership lemma is a renamed copy of its MOI_SMOOTH_ATLAS_IMAGE_IN,      *)
(* since that file is not loaded here).                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_IMAGE_IN = prove
 (`!(t:A->B) (s:B->A) (atlas:((A->bool)#(A->real^N))->bool) V psi.
        (V,psi) IN IMAGE (\c. IMAGE t (FST c),SND c o s) atlas <=>
        ?U phi. (U,phi) IN atlas /\ V = IMAGE t U /\ psi = phi o s`,
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MOI_SMB_BOUNDARY_IMAGE = prove
 (`!(top:A topology) (t:A->B) (s:B->A) (atlas:((A->bool)#(A->real^N))->bool).
        (!U phi. (U,phi) IN atlas ==> U SUBSET topspace top) /\
        (!x. x IN topspace top ==> s(t x) = x)
        ==> atlas_boundary (IMAGE (\c. IMAGE t (FST c),SND c o s) atlas) =
            IMAGE t (atlas_boundary atlas)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[atlas_boundary; MOI_SMB_IMAGE_IN] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (X_CHOOSE_THEN `psi:B->real^N`
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
          STRIP_ASSUME_TAC))
        STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(psi:B->real^N) y$(dimindex(:N)) = &0` THEN
    UNDISCH_TAC `(y:B) IN V` THEN ASM_REWRITE_TAC[IN_IMAGE; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:B->A) y = x` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    EXISTS_TAC `x:A` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
          STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (t:A->B) U`; `(phi:A->real^N) o (s:B->A)`] THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:B->A) y = x` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; IN_IMAGE] THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[]]);;

let SMOOTH_BOUNDARY_ATLAS_TRANSPORT = prove
 (`!(top:A topology) (top':B topology) (t:A->B) (atlas:((A->bool)#(A->real^N))->bool).
     homeomorphic_map (top,top') t /\ smooth_boundary_atlas top atlas
     ==> ?atlas':((B->bool)#(B->real^N))->bool.
           smooth_boundary_atlas top' atlas' /\
           atlas_boundary atlas' = IMAGE t (atlas_boundary atlas)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:B->A`) ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  SUBGOAL_THEN
   `!U phi. (U,phi) IN (atlas:((A->bool)#(A->real^N))->bool)
            ==> U SUBSET topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_SMB_CHART]; ALL_TAC] THEN
  EXISTS_TAC
   `IMAGE (\c:(A->bool)#(A->real^N). IMAGE (t:A->B) (FST c),SND c o (s:B->A))
          atlas` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_SMB_BOUNDARY_IMAGE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[smooth_boundary_atlas; MOI_SMB_IMAGE_IN] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `IMAGE ((phi:A->real^N) o (s:B->A)) (IMAGE (t:A->B) U) =
                  IMAGE phi U` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:A->B`; `top:A topology`; `top':B topology`;
                     `U:A->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP; HOMEOMORPHIC_MAPS_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (t:A->B) U SUBSET topspace top'` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; IMAGE_SUBSET;
                    SUBSET_TRANS];
      ALL_TAC] THEN
    ASM SET_TAC[];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(s:B->A) y`] MOI_SMB_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool`
      (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (t:A->B) U`; `(phi:A->real^N) o (s:B->A)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(s:B->A) y` THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`V1:B->bool`; `psi1:B->real^N`;
                         `V2:B->bool`; `psi2:B->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))
     (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U1:A->bool`; `phi1:A->real^N`; `U2:A->bool`; `phi2:A->real^N`]
                  MOI_SMB_TRANSITION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N`
      (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `w:real^N->bool`] THEN
    SUBGOAL_THEN `(U1:A->bool) SUBSET topspace top /\ U2 SUBSET topspace top`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE ((phi1:A->real^N) o (s:B->A))
            (IMAGE (t:A->B) U1 INTER IMAGE t U2) =
      IMAGE phi1 (U1 INTER U2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; IN_INTER; IN_IMAGE] THEN
    X_GEN_TAC `y:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (X_CHOOSE_TAC `b:A`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Result: restriction of a boundary atlas to an open subset.                *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_OPEN_SUBSET_ATLAS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) w.
     smooth_boundary_atlas top atlas /\ open_in top w
     ==> smooth_boundary_atlas (subtopology top w)
           {(U INTER w,phi) | U,phi | (U,phi) IN atlas}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_boundary_atlas; IN_ELIM_THM; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U':A->bool`; `phi':A->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] MOI_SMB_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `U:A->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`;
                     `subtopology euclidean (IMAGE (phi:A->real^N) U)`;
                     `(U:A->bool) INTER w`] HOMEOMORPHIC_MAP_OPENNESS) THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `w:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `(w:A->bool) INTER (U INTER w) = U INTER w` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SMB_HOMEO_RESTRICT THEN EXISTS_TAC `U:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] MOI_SMB_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool`
      (X_CHOOSE_THEN `phi:A->real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(U:A->bool) INTER w`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U':A->bool`; `phi':A->real^N`;
                         `V':A->bool`; `psi':A->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))
      (X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `psi:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                  MOI_SMB_TRANSITION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N`
      (X_CHOOSE_THEN `w1:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `w1:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]]);;

let SMOOTH_BOUNDARY_ATLAS_OPEN_SUBSET = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) w.
     smooth_boundary_atlas top atlas /\ open_in top w
     ==> smooth_boundary_atlas (subtopology top w)
           {(U INTER w,phi) | U,phi | (U,phi) IN atlas} /\
         atlas_boundary {(U INTER w,phi) | U,phi | (U,phi) IN atlas} =
         w INTER atlas_boundary atlas`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SMB_OPEN_SUBSET_ATLAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[atlas_boundary] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER; PAIR_EQ] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `U':A->bool` (X_CHOOSE_THEN `phi':A->real^N`
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
           STRIP_ASSUME_TAC))
        MP_TAC))) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
         STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`(U:A->bool) INTER w`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A criterion for boundary atlases on subsets of real^N: every chart map is *)
(* smooth on all of real^N and has a left inverse on its domain that is      *)
(* smooth on an open set containing the chart image.  Transition maps are    *)
(* then compositions psi o ginv.                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_EUCLIDEAN_CHART_HOMEO = prove
 (`!(U:real^N->bool) (phi:real^N->real^N) ginv w.
     phi continuous_on U /\ ginv continuous_on w /\ IMAGE phi U SUBSET w /\
     (!x. x IN U ==> ginv(phi x) = x)
     ==> homeomorphic_map (subtopology euclidean U,
                           subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
  EXISTS_TAC `ginv:real^N->real^N` THEN REWRITE_TAC[homeomorphism] THEN
  ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ASM SET_TAC[];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

let MOI_SMB_EUCLIDEAN_ATLAS = prove
 (`!(s:real^N->bool) (atlas:((real^N->bool)#(real^N->real^N))->bool).
     (!U phi. (U,phi) IN atlas
              ==> open_in (subtopology euclidean s) U /\
                  open_in (subtopology euclidean
                             {y:real^N | &0 <= y$(dimindex(:N))})
                          (IMAGE phi U) /\
                  smooth_map_on (:real^N) phi /\
                  ?ginv w. open w /\ IMAGE phi U SUBSET w /\
                           smooth_map_on w ginv /\
                           !x. x IN U ==> ginv(phi x) = x) /\
     (!x. x IN s ==> ?U phi. (U,phi) IN atlas /\ x IN U)
     ==> smooth_boundary_atlas (subtopology euclidean s) atlas`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[smooth_boundary_atlas] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^N`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ginv:real^N->real^N`
        (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC))))) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(s:real^N->bool) INTER U = U` SUBST1_TAC THENL
     [UNDISCH_TAC `open_in (subtopology euclidean s) (U:real^N->bool)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_SMB_EUCLIDEAN_CHART_HOMEO THEN
    MAP_EVERY EXISTS_TAC [`ginv:real^N->real^N`; `w:real^N->bool`] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^N`;
                         `V:real^N->bool`; `psi:real^N->real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `smooth_map_on (:real^N) (psi:real^N->real^N)` ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `ginv:real^N->real^N`
        (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC
     [`(psi:real^N->real^N) o (ginv:real^N->real^N)`; `w:real^N->bool`] THEN
    ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
      REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Smoothness of linear maps and of lifted real-valued expressions.          *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_SMOOTH_LINEAR = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
     open s /\ linear f ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `f:real^M->real^N`]
                SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let MOI_SMB_SL_CONST = prove
 (`!(s:real^M->bool) c. smooth_map_on s (\x. lift c)`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let MOI_SMB_SL_ADD = prove
 (`!(s:real^M->bool) (a:real^M->real) b.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
     ==> smooth_map_on s (\x. lift(a x + b x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]);;

let MOI_SMB_SL_SUB = prove
 (`!(s:real^M->bool) (a:real^M->real) b.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
     ==> smooth_map_on s (\x. lift(a x - b x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[]);;

let MOI_SMB_SL_MUL = prove
 (`!(s:real^M->bool) (a:real^M->real) b.
     open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
     ==> smooth_map_on s (\x. lift(a x * b x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((a:real^M->real) x)`;
                 `\x:real^M. lift((b:real^M->real) x)`] SMOOTH_MAP_ON_LIFT_MUL) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]);;

let MOI_SMB_SL_POW = prove
 (`!(s:real^M->bool) (a:real^M->real) n.
     open s /\ smooth_map_on s (\x. lift(a x))
     ==> smooth_map_on s (\x. lift(a x pow n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((a:real^M->real) x)`;
                 `n:num`] SMOOTH_MAP_ON_LIFT_POW) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]);;

let MOI_SMB_SL_SQRT = prove
 (`!(s:real^M->bool) (a:real^M->real).
     open s /\ smooth_map_on s (\x. lift(a x)) /\ (!x. x IN s ==> &0 < a x)
     ==> smooth_map_on s (\x. lift(sqrt(a x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift((a:real^M->real) x)`]
                SMOOTH_MAP_ON_LIFT_SQRT) THEN
  BETA_TAC THEN ASM_SIMP_TAC[LIFT_DROP]);;

let MOI_SMB_SL_NORM_POW2 = prove
 (`!(s:real^M->bool). open s ==> smooth_map_on s (\x. lift(norm x pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

(* Proves smooth_map_on s (\x. lift(e x)) for polynomial expressions e in    *)
(* the coordinates and norm x pow 2, given open s as an assumption or s the  *)
(* whole space.                                                              *)

let MOI_SMB_SL_TAC =
  REPEAT (FIRST
   [MATCH_ACCEPT_TAC OPEN_UNIV;
    FIRST_ASSUM ACCEPT_TAC;
    CONJ_TAC;
    MATCH_MP_TAC MOI_SMB_SL_ADD;
    MATCH_MP_TAC MOI_SMB_SL_SUB;
    MATCH_MP_TAC MOI_SMB_SL_MUL;
    MATCH_MP_TAC MOI_SMB_SL_NORM_POW2;
    MATCH_MP_TAC MOI_SMB_SL_POW;
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COORDINATE;
    MATCH_ACCEPT_TAC MOI_SMB_SL_CONST]);;

(* ------------------------------------------------------------------------- *)
(* The closed unit ball of real^3 as a smooth manifold with boundary.  One   *)
(* interior chart (translation of the open ball into the open upper half-    *)
(* space) and, for each orthogonal transformation p, a boundary chart on     *)
(* the part of the ball where (p x)$3 > 0, namely moi_smb_cap o p with       *)
(* moi_smb_cap x = (x$1, x$2, 1 - |x|^2); its inverse on the cap image is    *)
(* (a,b,t) -> (a, b, sqrt(1 - t - a^2 - b^2)).  Every unit vector is moved   *)
(* to basis 3 by some orthogonal p (ORTHOGONAL_TRANSFORMATION_EXISTS), so    *)
(* the boundary charts cover the sphere; the boundary is the unit sphere.   *)
(* ------------------------------------------------------------------------- *)

let moi_smb_cap = new_definition
 `moi_smb_cap (x:real^3) = vector[x$1; x$2; &1 - norm x pow 2]:real^3`;;

let moi_smb_capinv = new_definition
 `moi_smb_capinv (y:real^3) =
    vector[y$1; y$2; sqrt(&1 - y$3 - y$1 pow 2 - y$2 pow 2)]:real^3`;;

let moi_smb_cball_atlas = new_definition
 `moi_smb_cball_atlas =
    (ball(vec 0:real^3,&1),(\x:real^3. &2 % basis 3 + x)) INSERT
    {({x:real^3 | x IN cball(vec 0,&1) /\ &0 < ((p:real^3->real^3) x)$3},
      moi_smb_cap o p) | p | orthogonal_transformation p}`;;

(* ------------------------------------------------------------------------- *)
(* Coordinates in real^3.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_VEC3_EQ = prove
 (`!x y:real^3. x = y <=> x$1 = y$1 /\ x$2 = y$2 /\ x$3 = y$3`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3]);;

let MOI_SMB_NORM_SQ3 = prove
 (`!x:real^3. norm x pow 2 = x$1 pow 2 + x$2 pow 2 + x$3 pow 2`,
  REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC);;

let MOI_SMB_CBALL_SQ = prove
 (`!x:real^3. x IN cball(vec 0,&1) <=> x$1 pow 2 + x$2 pow 2 + x$3 pow 2 <= &1`,
  REWRITE_TAC[IN_CBALL_0; NORM_LE_SQUARE; DOT_3; REAL_POW_2] THEN REAL_ARITH_TAC);;

let MOI_SMB_CAP_3 = prove
 (`!x:real^3. moi_smb_cap x$3 = &1 - norm x pow 2`,
  REWRITE_TAC[moi_smb_cap; VECTOR_3]);;

let MOI_SMB_CAP_COMPONENTS = prove
 (`!x:real^3. moi_smb_cap x$1 = x$1 /\ moi_smb_cap x$2 = x$2 /\
              moi_smb_cap x$3 = &1 - (x$1 pow 2 + x$2 pow 2 + x$3 pow 2)`,
  REWRITE_TAC[moi_smb_cap; VECTOR_3; MOI_SMB_NORM_SQ3]);;

let MOI_SMB_CAPINV_COMPONENTS = prove
 (`!y:real^3. moi_smb_capinv y$1 = y$1 /\ moi_smb_capinv y$2 = y$2 /\
              moi_smb_capinv y$3 = sqrt(&1 - y$3 - y$1 pow 2 - y$2 pow 2)`,
  REWRITE_TAC[moi_smb_capinv; VECTOR_3]);;

(* ------------------------------------------------------------------------- *)
(* The cap chart: left inverse, image, smoothness.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_CAP_LEFT_INVERSE = prove
 (`!x:real^3. x IN cball(vec 0,&1) /\ &0 < x$3
              ==> moi_smb_capinv(moi_smb_cap x) = x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MOI_SMB_VEC3_EQ; MOI_SMB_CAPINV_COMPONENTS; MOI_SMB_CAP_COMPONENTS] THEN
  SUBGOAL_THEN
   `&1 - (&1 - ((x:real^3)$1 pow 2 + x$2 pow 2 + x$3 pow 2)) -
    x$1 pow 2 - x$2 pow 2 = x$3 pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[POW_2_SQRT_ABS] THEN ASM_REAL_ARITH_TAC);;

let MOI_SMB_CAP_IMAGE = prove
 (`IMAGE moi_smb_cap {x:real^3 | x IN cball(vec 0,&1) /\ &0 < x$3} =
   {y:real^3 | &0 <= y$3} INTER {y:real^3 | y$1 pow 2 + y$2 pow 2 + y$3 < &1}`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; MOI_SMB_CBALL_SQ] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[MOI_SMB_CAP_COMPONENTS] THEN
    SUBGOAL_THEN `&0 < (x:real^3)$3 pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `moi_smb_capinv y` THEN
    SUBGOAL_THEN `&0 < &1 - (y:real^3)$3 - y$1 pow 2 - y$2 pow 2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `sqrt(&1 - (y:real^3)$3 - y$1 pow 2 - y$2 pow 2) pow 2 =
      &1 - y$3 - y$1 pow 2 - y$2 pow 2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MOI_SMB_VEC3_EQ; MOI_SMB_CAP_COMPONENTS;
                MOI_SMB_CAPINV_COMPONENTS] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC]);;

let MOI_SMB_W_OPEN = prove
 (`open {y:real^3 | y$1 pow 2 + y$2 pow 2 + y$3 < &1}`,
  MP_TAC(ISPECL [`\y:real^3. lift(y$1 pow 2 + y$2 pow 2 + y$3)`;
                 `{z:real^1 | z$1 < &1}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; LIFT_COMPONENT] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^3) (\y:real^3. lift(y$1 pow 2 + y$2 pow 2 + y$3))`
  MP_TAC THENL [MOI_SMB_SL_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]);;

let MOI_SMB_CAP_SMOOTH = prove
 (`smooth_map_on (:real^3) moi_smb_cap`,
  SUBGOAL_THEN
   `moi_smb_cap = (\x:real^3. vector[x$1; x$2; &1 - norm x pow 2]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_smb_cap]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE OPEN_UNIV] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3] THEN BETA_TAC THEN REWRITE_TAC[VECTOR_3] THEN
  MOI_SMB_SL_TAC);;

let MOI_SMB_CAPINV_SMOOTH = prove
 (`smooth_map_on {y:real^3 | y$1 pow 2 + y$2 pow 2 + y$3 < &1} moi_smb_capinv`,
  SUBGOAL_THEN
   `moi_smb_capinv =
    (\y:real^3. vector[y$1; y$2; sqrt(&1 - y$3 - y$1 pow 2 - y$2 pow 2)]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_smb_capinv]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE MOI_SMB_W_OPEN] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3] THEN BETA_TAC THEN REWRITE_TAC[VECTOR_3] THEN
  ASSUME_TAC MOI_SMB_W_OPEN THEN
  REPEAT CONJ_TAC THENL [MOI_SMB_SL_TAC; MOI_SMB_SL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_SMB_SL_SQRT THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MOI_SMB_SL_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonal transformations move the cap domains onto the upper cap.       *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_ORTH_IMAGE = prove
 (`!p:real^3->real^3.
     orthogonal_transformation p
     ==> IMAGE p {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3} =
         {y | y IN cball(vec 0,&1) /\ &0 < y$3}`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_CBALL_0] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION];
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o
      MATCH_MP ORTHOGONAL_TRANSFORMATION_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]]);;

(* ------------------------------------------------------------------------- *)
(* The two kinds of charts satisfy the criterion MOI_SMB_EUCLIDEAN_ATLAS.    *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_CBALL_INTERIOR_CHART = prove
 (`open_in (subtopology euclidean (cball(vec 0:real^3,&1))) (ball(vec 0,&1)) /\
   open_in (subtopology euclidean {y:real^3 | &0 <= y$(dimindex(:3))})
           (IMAGE (\x:real^3. &2 % basis 3 + x) (ball(vec 0,&1))) /\
   smooth_map_on (:real^3) (\x:real^3. &2 % basis 3 + x) /\
   ?ginv w. open w /\
            IMAGE (\x:real^3. &2 % basis 3 + x) (ball(vec 0,&1)) SUBSET w /\
            smooth_map_on w ginv /\
            !x:real^3. x IN ball(vec 0,&1) ==> ginv(&2 % basis 3 + x) = x`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL; OPEN_BALL];
    MATCH_MP_TAC OPEN_SUBSET THEN SIMP_TAC[OPEN_TRANSLATION; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0; IN_ELIM_THM; DIMINDEX_3] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    MAP_EVERY EXISTS_TAC [`\y:real^3. y - &2 % basis 3`; `(:real^3)`] THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
      REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC]]);;

let MOI_SMB_CBALL_BOUNDARY_CHART = prove
 (`!p:real^3->real^3.
     orthogonal_transformation p
     ==> open_in (subtopology euclidean (cball(vec 0:real^3,&1)))
                 {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3} /\
         open_in (subtopology euclidean {y:real^3 | &0 <= y$(dimindex(:3))})
                 (IMAGE (moi_smb_cap o p)
                        {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3}) /\
         smooth_map_on (:real^3) (moi_smb_cap o p) /\
         ?ginv w. open w /\
                  IMAGE (moi_smb_cap o p)
                        {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3} SUBSET w /\
                  smooth_map_on w ginv /\
                  !x. x IN {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3}
                      ==> ginv((moi_smb_cap o p) x) = x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC o
    MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  SUBGOAL_THEN
   `IMAGE (moi_smb_cap o (p:real^3->real^3))
          {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3} =
    {y:real^3 | &0 <= y$3} INTER {y:real^3 | y$1 pow 2 + y$2 pow 2 + y$3 < &1}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_o; MOI_SMB_ORTH_IMAGE; MOI_SMB_CAP_IMAGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `{x:real^3 | (p:real^3->real^3) x IN {y:real^3 | y$3 > &0}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; OPEN_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]];
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `{y:real^3 | y$1 pow 2 + y$2 pow 2 + y$3 < &1}` THEN
    REWRITE_TAC[MOI_SMB_W_OPEN];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; MOI_SMB_CAP_SMOOTH;
                 MOI_SMB_SMOOTH_LINEAR];
    MAP_EVERY EXISTS_TAC
     [`(q:real^3->real^3) o moi_smb_capinv`;
      `{y:real^3 | y$1 pow 2 + y$2 pow 2 + y$3 < &1}`] THEN
    REWRITE_TAC[MOI_SMB_W_OPEN; INTER_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
      ASM_SIMP_TAC[MOI_SMB_W_OPEN; MOI_SMB_CAPINV_SMOOTH;
                   ORTHOGONAL_TRANSFORMATION_LINEAR];
      REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `moi_smb_capinv (moi_smb_cap ((p:real^3->real^3) x)) = p x`
      SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_SMB_CAP_LEFT_INVERSE THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; IN_CBALL_0];
        ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The atlas and its boundary.                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SMB_CBALL_ATLAS_IN = prove
 (`!U phi.
     (U,phi) IN moi_smb_cball_atlas <=>
     (U = ball(vec 0,&1) /\ phi = (\x:real^3. &2 % basis 3 + x)) \/
     (?p:real^3->real^3.
          orthogonal_transformation p /\
          U = {x | x IN cball(vec 0,&1) /\ &0 < (p x)$3} /\
          phi = moi_smb_cap o p)`,
  REWRITE_TAC[moi_smb_cball_atlas; IN_INSERT; IN_ELIM_THM; PAIR_EQ]);;

let MOI_SMB_CBALL_SMOOTH_ATLAS = prove
 (`smooth_boundary_atlas (subtopology euclidean (cball(vec 0:real^3,&1)))
                         moi_smb_cball_atlas`,
  MATCH_MP_TAC MOI_SMB_EUCLIDEAN_ATLAS THEN REWRITE_TAC[MOI_SMB_CBALL_ATLAS_IN] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^3->bool`; `phi:real^3->real^3`] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (CONJUNCTS_THEN SUBST1_TAC)
      (X_CHOOSE_THEN `p:real^3->real^3`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THENL
     [BETA_TAC THEN REWRITE_TAC[MOI_SMB_CBALL_INTERIOR_CHART];
      MATCH_MP_TAC MOI_SMB_CBALL_BOUNDARY_CHART THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(x:real^3) < &1` THENL
     [MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&1)`; `\x:real^3. &2 % basis 3 + x`] THEN
      ASM_REWRITE_TAC[IN_BALL_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(x:real^3) = norm(basis 3:real^3)` MP_TAC THENL
     [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^3` STRIP_ASSUME_TAC o
      MATCH_MP ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
    MAP_EVERY EXISTS_TAC
     [`{y:real^3 | y IN cball(vec 0,&1) /\ &0 < ((p:real^3->real^3) y)$3}`;
      `moi_smb_cap o (p:real^3->real^3)`] THEN
    CONJ_TAC THENL
     [DISJ2_TAC THEN EXISTS_TAC `p:real^3->real^3` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]);;

let MOI_SMB_CBALL_BOUNDARY = prove
 (`atlas_boundary moi_smb_cball_atlas = sphere(vec 0:real^3,&1)`,
  REWRITE_TAC[atlas_boundary; MOI_SMB_CBALL_ATLAS_IN; DIMINDEX_3] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SPHERE_0] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U:real^3->bool`; `phi:real^3->real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
         (X_CHOOSE_THEN `p:real^3->real^3` STRIP_ASSUME_TAC))
      MP_TAC) THEN
    ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[IN_BALL_0; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; o_THM; MOI_SMB_CAP_3; IN_CBALL_0] THEN
      SUBGOAL_THEN `norm((p:real^3->real^3) x) = norm(x:real^3)` SUBST1_TAC THENL
       [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
      REWRITE_TAC[NORM_EQ_SQUARE; GSYM NORM_POW_2] THEN REAL_ARITH_TAC];
    DISCH_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) = norm(basis 3:real^3)` MP_TAC THENL
     [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^3` STRIP_ASSUME_TAC o
      MATCH_MP ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
    MAP_EVERY EXISTS_TAC
     [`{y:real^3 | y IN cball(vec 0,&1) /\ &0 < ((p:real^3->real^3) y)$3}`;
      `moi_smb_cap o (p:real^3->real^3)`] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN EXISTS_TAC `p:real^3->real^3` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0; REAL_LE_REFL] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[o_THM; MOI_SMB_CAP_3] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Result: the closed unit ball of real^3 with boundary the unit sphere.     *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_BOUNDARY_ATLAS_CBALL = prove
 (`?atlas:((real^3->bool)#(real^3->real^3))->bool.
     smooth_boundary_atlas (subtopology euclidean (cball(vec 0:real^3,&1))) atlas /\
     atlas_boundary atlas = sphere(vec 0,&1)`,
  EXISTS_TAC `moi_smb_cball_atlas` THEN
  REWRITE_TAC[MOI_SMB_CBALL_SMOOTH_ATLAS; MOI_SMB_CBALL_BOUNDARY]);;

