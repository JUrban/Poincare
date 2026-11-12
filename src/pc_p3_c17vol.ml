(* ========================================================================= *)
(* Unit pc_p3_c17vol: volumes at an event, for MT Lemma                     *)
(* 17.12.  Reference manifold: the preview slice M = X|Omega (old stage     *)
(* restricted to Omega) with the limit metric gl (rfs_preview at the event  *)
(* time).  The new stage is the retained part W (isometric to (W,gl)) plus *)
(* the minus caps; the discarded part contains the positive halves of the  *)
(* necks; near the event time volumes for gl are at most (1+e) times those *)
(* for the slab metric.                                                     *)
(*                                                                         *)
(* The restricted limit metric; chart transfer of quadratic                *)
(* form bounds to restricted charts.                                       *)
(* ========================================================================= *)

needs "src/pc_p2b_cap.ml";;
needs "src/pc_p3_s13rot.ml";;
needs "src/pc_p3_s14ftr.ml";;
needs "src/pc_p3_c17top.ml";;
needs "src/pc_p3_c17vgen.ml";;

prioritize_real();;
type_invention_error := true;;

(* The limit metric is a Riemannian metric of the restriction to any open  *)
(* subset W of Omega, in particular to Omega itself.                        *)

let P3H_LIMIT_RESTRICT_RIEMANNIAN_SUB = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) Om ts g gl W.
        smooth_manifold_atlas top atlas /\ open_in top W /\ W SUBSET Om /\
        rfs_limit_metric (top,atlas) Om ts g gl
        ==> riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W gl)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local atlas (U,phi) (gl:A->real^3^3)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER Om)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `rfs_limit_metric (top,atlas) (Om:A->bool) ts (g:real->A->real^3^3) gl` THEN
      REWRITE_TAC[rfs_limit_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[FST; SND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

let P3H_LIMIT_RESTRICT_RIEMANNIAN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) Om ts g gl.
        smooth_manifold_atlas top atlas /\ open_in top Om /\
        rfs_limit_metric (top,atlas) Om ts g gl
        ==> riemannian_metric (restrict_atlas atlas Om) (restrict_metric atlas Om gl)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN_SUB THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `Om:A->bool`; `ts:real`; `g:real->A->real^3^3`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* The matrix of a restricted metric at x is J^T (g x) J with J the chart  *)
(* change Jacobian, the same J for every metric: quadratic-form bounds      *)
(* between two metrics pass to their restrictions.                         *)

let P3H_RESTRICT_QF_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W (G1:A->real^3^3) G2 x lam.
        smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
        (!v. v dot (G1 x ** v) <= lam * (v dot (G2 x ** v)))
        ==> !w. w dot (restrict_metric atlas W G1 x ** w) <=
                lam * (w dot (restrict_metric atlas W G2 x ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
                 `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!G:A->real^3^3. restrict_metric atlas W G x =
                    metric_local atlas (U,phi) G (phi x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[restrict_metric] THEN ASM_REWRITE_TAC[SND] THEN
    MATCH_MP_TAC MFDR_METRIC_LOCAL_RESTRICT_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] P2BC_METRIC_LOCAL_AT_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `w:real^3` THEN
  ABBREV_TAC `J = matrix(frechet_derivative (chart_trans (U,phi:A->real^3)
                                             (chart_at atlas x)) (at (phi x)))` THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(J:real^3^3) ** w` o
    check (fun th -> can (find_term ((=) `lam:real`)) (concl th) && is_forall(concl th))) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* The retained part.  On an open set W of both stages where                *)
(* the identity is a diffeomorphism and the metrics agree (rfs_same_metric_ *)
(* on), the restricted manifolds are isometric by the identity, so volumes *)
(* of subsets of W agree.                                                   *)
(* ========================================================================= *)

let P3H_RETAINED_ISOMETRY = prove
 (`!topX atlasX (gl:A->real^3^3) topY atlasY gY W.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_diffeo topX atlasX W topY atlasY W (\x. x) (\x. x) /\
        rfs_same_metric_on atlasX gl atlasY gY W
        ==> mfd_isometry (subtopology topX W,restrict_atlas atlasX W)
                         (restrict_metric atlasX W gl)
                         (subtopology topY W,restrict_atlas atlasY W)
                         (restrict_metric atlasY W gY) (\x. x) (\x. x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in topX (W:A->bool) /\ open_in topY W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  REWRITE_TAC[mfd_isometry] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `W:A->bool`; `\x:A. x`; `\x:A. x`] P2BC_RESTRICT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`U1:A->bool`; `phi:A->real^3`; `V1:A->bool`; `psi:A->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))
    (X_CHOOSE_THEN `V:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`; `W:A->bool`; `gl:A->real^3^3`; `x:A`]
                METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback; o_THM] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`; `W:A->bool`; `x:A`]
                MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `V:A->bool`; `psi:A->real^3`; `W:A->bool`; `gY:A->real^3^3`; `x:A`]
                METRIC_LOCAL_RESTRICT) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `rfs_same_metric_on atlasX (gl:A->real^3^3) atlasY gY W` THEN
  REWRITE_TAC[rfs_same_metric_on] THEN
  DISCH_THEN(MP_TAC o SPECL [`(U:A->bool,phi:A->real^3)`; `(V:A->bool,psi:A->real^3)`;
                             `(phi:A->real^3) x`]) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. (psi:A->real^3) (chart_inv (U INTER W,phi:A->real^3) z))
                       (at ((phi:A->real^3) x)) =
    frechet_derivative (\z. psi (chart_inv (U,phi) z)) (at (phi x))`
  (fun th -> REWRITE_TAC[th]) THEN
   (MATCH_MP_TAC P2BC_FRECHET_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                     `U:A->bool`; `phi:A->real^3`; `W:A->bool`; `z:A`]
                    MFDR_CHART_INV_RESTRICT) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]]));;

(* Volumes of subsets of W agree. *)

let P3H_RETAINED_VOLUME = prove
 (`!topX atlasX (gl:A->real^3^3) topY atlasY gY W S v.
        smooth_manifold_atlas topX atlasX /\ smooth_manifold_atlas topY atlasY /\
        mfd_diffeo topX atlasX W topY atlasY W (\x. x) (\x. x) /\
        rfs_same_metric_on atlasX gl atlasY gY W /\
        riemannian_metric (restrict_atlas atlasX W) (restrict_metric atlasX W gl) /\
        riemannian_metric atlasY gY /\ S SUBSET W
        ==> (mfd_has_volume (topY,atlasY) gY S v <=>
             mfd_has_volume (topX,atlasX) gl S v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in topX (W:A->bool) /\ open_in topY W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `gY:A->real^3^3`; `W:A->bool`; `S:A->bool`; `v:real`]
                P2BC_VOLUME_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gl:A->real^3^3`; `W:A->bool`; `S:A->bool`; `v:real`]
                P2BC_VOLUME_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`subtopology topX (W:A->bool)`;
                 `restrict_atlas (atlasX:((A->bool)#(A->real^3))->bool) W`;
                 `restrict_metric (atlasX:((A->bool)#(A->real^3))->bool) W (gl:A->real^3^3)`;
                 `subtopology topY (W:A->bool)`;
                 `restrict_atlas (atlasY:((A->bool)#(A->real^3))->bool) W`;
                 `restrict_metric (atlasY:((A->bool)#(A->real^3))->bool) W (gY:A->real^3^3)`;
                 `\x:A. x`; `\x:A. x`; `S:A->bool`; `v:real`] MFD_HAS_VOLUME_ISOMETRY) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `topY:A topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P3H_RETAINED_ISOMETRY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in topX (W:A->bool)`)) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IMAGE_ID]]);;

(* ========================================================================= *)
(* Boxes in the positive half of a neck.  The box                          *)
(* B j = 2^j [4/3,5/3] x [-1/6,1/6]^2 lies in the shell 2^j < |y| < 2^(j+1)  *)
(* and has measure 8^j / 27; there the cylinder metric is >= 2/(3 4^j) I,   *)
(* so in a dl-neck centred at a point with scalar curvature Q the box      *)
(* image has volume >= (1 / (3 Q))^(3/2) / 27 (dl <= 1/2), independently   *)
(* of j.                                                                     *)
(* ========================================================================= *)

let p3h_box = new_definition
 `p3h_box (j:num) =
    interval[(&2 pow j) % vector[&4 / &3; --(&1 / &6); --(&1 / &6)]:real^3,
             (&2 pow j) % vector[&5 / &3; &1 / &6; &1 / &6]]`;;

let P3H_BOX_COMPONENTS = prove
 (`!j (y:real^3).
     y IN p3h_box j <=>
     &4 / &3 * &2 pow j <= y$1 /\ y$1 <= &5 / &3 * &2 pow j /\
     abs(y$2) <= &1 / &6 * &2 pow j /\ abs(y$3) <= &1 / &6 * &2 pow j`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3h_box; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT;
              VECTOR_3] THEN
  REAL_ARITH_TAC);;

let P3H_BOX_NORM = prove
 (`!j (y:real^3). y IN p3h_box j
         ==> &4 / &3 * &2 pow j <= norm y /\ norm y pow 2 <= &3 * &4 pow j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P3H_BOX_COMPONENTS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&4 pow j = &2 pow j * &2 pow j` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC `p = &2 pow j` THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(y:real^3)$1` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`y:real^3`; `1`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3] THEN
  SUBGOAL_THEN `&0 <= (&5 / &3 * p - (y:real^3)$1) * (y$1 + &5 / &3 * p) /\
                &0 <= (&1 / &6 * p - y$2) * (y$2 + &1 / &6 * p) /\
                &0 <= (&1 / &6 * p - y$3) * (y$3 + &1 / &6 * p)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `p:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC]);;

let P3H_BOX_SHELL = prove
 (`!j (y:real^3). y IN p3h_box j ==> &2 pow j < norm y /\ norm y < &2 pow (j + 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P3H_BOX_NORM) THEN
  SUBGOAL_THEN `&0 < &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 pow j = &2 pow j * &2 pow j /\ &2 pow (j + 1) = &2 * &2 pow j`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL; REAL_POW_ADD] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p = &2 pow j` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&2 * p) * (&2 * p) <= norm(y:real^3) * norm y` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `norm(y:real^3) pow 2 <= &3 * p * p` THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&0 < p * p` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let P3H_BOX_DISJOINT = prove
 (`!i j. ~(i = j) ==> DISJOINT (p3h_box i) (p3h_box j)`,
  SUBGOAL_THEN `!i j. i < j ==> DISJOINT (p3h_box i) (p3h_box j)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `y:real^3`] P3H_BOX_SHELL) THEN
    MP_TAC(SPECL [`j:num`; `y:real^3`] P3H_BOX_SHELL) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`i + 1`; `j:num`; `&2`] REAL_POW_MONO) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `i < j \/ j < (i:num) \/ i = j`) THENL
   [ASM_SIMP_TAC[];
    FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
     [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_SIMP_TAC[]; ASM_MESON_TAC[]]]);;

let P3H_BOX_MEASURE = prove
 (`!j. p3h_box j has_measure (&8 pow j / &27)`,
  GEN_TAC THEN REWRITE_TAC[p3h_box] THEN
  MATCH_MP_TAC(MESON[] `!s:real^3->bool x y. s has_measure x /\ x = y ==> s has_measure y`) THEN
  EXISTS_TAC `content(interval[(&2 pow j) % vector[&4 / &3; --(&1 / &6); --(&1 / &6)]:real^3,
                               (&2 pow j) % vector[&5 / &3; &1 / &6; &1 / &6]])` THEN
  REWRITE_TAC[HAS_MEASURE_INTERVAL] THEN
  SUBGOAL_THEN `&0 < &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CONTENT_CLOSED_INTERVAL o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PRODUCT_3; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  SUBGOAL_THEN `&8 pow j = &2 pow j * &2 pow j * &2 pow j` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC `p = &2 pow j` THEN REAL_ARITH_TAC);;

let P3H_BOX_IN_DOM = prove
 (`!dl j. &0 < dl /\ &2 pow (j + 1) <= exp(inv(sqrt(&2) * dl))
          ==> p3h_box j SUBSET {y | y IN rfs_neck_dom dl /\ &1 < norm y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; rfs_neck_dom; annulus] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_THEN(MP_TAC o MATCH_MP P3H_BOX_SHELL) THEN
  SUBGOAL_THEN `&1 <= &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(inv(sqrt(&2) * dl))) < &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_NEG_LT0; REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3H_BOX_VOL_ARITH = prove
 (`!a j. &0 < a ==> sqrt((a / &4 pow j) pow 3) * (&8 pow j / &27) = sqrt(a pow 3) / &27`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_DIV; SQRT_DIV] THEN
  SUBGOAL_THEN `(&4 pow j) pow 3 = (&8 pow j) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &8 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `&0 < &8 pow j` THEN CONV_TAC REAL_FIELD);;

(* The pullback by a map from the flat real^N in its identity chart is the  *)
(* chart-free pullback rfs_pullback.                                         *)

let P3H_PULLBACK_OPEN_UNIV = prove
 (`!atlas (e:real^N->A) (g:A->real^N^N) y.
     mfd_pullback_metric (open_set_atlas (:real^N)) atlas e g y = rfs_pullback atlas e g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_pullback_metric; rfs_pullback; GEOL_EUCLID_FACTS] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV]);;

let P3H_CYL0_QF = prove
 (`!(z:real^3) w. w dot (cylinder_flow (&0) z ** w) = &2 / norm z pow 2 * (w dot w)`,
  REWRITE_TAC[cylinder_flow; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO;
              MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_LID;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL]);;

let P3H_NECK_QF_ARITH = prove
 (`!dl Q N2 P W X.
     &0 <= dl /\ dl <= &1 / &2 /\ &0 < Q /\ &0 < N2 /\ N2 <= &3 * P /\ &0 <= W /\
     (&1 - dl) * (&2 / N2 * W) <= Q * X
     ==> inv(&3 * Q) / P * W <= X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&3 * P) <= inv N2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `W * inv(&3 * P) <= W * inv N2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - &2 * dl) * (W * inv N2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `W * inv(&3 * P) <= Q * X` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 - dl) * (&2 / N2 * W) <= Q * X` THEN REWRITE_TAC[real_div] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&3 * Q) / P * W = inv Q * (W * inv(&3 * P))` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Q` THEN UNDISCH_TAC `&0 < P` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv Q * (Q * X)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REAL_ARITH_TAC]);;

(* Pointwise lower bound for the neck pullback on a box. *)

let P3H_NECK_BOX_QF = prove
 (`!top atlas (g:A->real^3^3) dl y e j z w.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g dl y e /\ dl <= &1 / &2 /\
     &2 pow (j + 1) <= exp(inv(sqrt(&2) * dl)) /\ z IN p3h_box j
     ==> inv(&3 * mfd_scalar atlas g y) / &4 pow j * (w dot w) <=
         w dot (rfs_pullback atlas e g z ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `j:num`] P3H_BOX_IN_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `dl:real`; `y:A`; `e:real^3->A`] APX_NECK_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                 (\y'. mfd_scalar atlas g (y:A) %% rfs_pullback atlas (e:real^3->A) g y')` THEN
  REWRITE_TAC[rfs_close_on] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`rfs_kreg dl`; `rfs_neck_dom dl`; `cylinder_flow (&0)`;
                 `\y'. mfd_scalar atlas g (y:A) %% rfs_pullback atlas (e:real^3->A) g y'`;
                 `z:real^3`; `w:real^3`] LCK_DIST_C0) THEN
  ASM_SIMP_TAC[APX_NECK_CYL_FIELD_GEN; REAL_ARITH `&0 < &1`] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                  (\y'. mfd_scalar atlas g (y:A) %% rfs_pullback atlas (e:real^3->A) g y') z)
                <= dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; P3H_CYL0_QF] THEN
  ABBREV_TAC `Q = mfd_scalar atlas (g:A->real^3^3) y` THEN
  ABBREV_TAC `X = (w:real^3) dot (rfs_pullback atlas (e:real^3->A) g z ** w)` THEN
  ABBREV_TAC `s = sqrt(lck_dist2 (rfs_kreg dl) (cylinder_flow (&0))
                  (\y'. Q %% rfs_pullback atlas (e:real^3->A) g y') z)` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`j:num`; `z:real^3`] P3H_BOX_NORM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&4 / &3 * &2 pow j` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 / norm(z:real^3) pow 2 * ((w:real^3) dot w)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[DOT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P3H_NECK_QF_ARITH THEN
  MAP_EVERY EXISTS_TAC [`dl:real`; `norm(z:real^3) pow 2`] THEN
  ASM_REWRITE_TAC[DOT_POS_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * (&2 / norm(z:real^3) pow 2 * ((w:real^3) dot w)) <=
                dl * (&2 / norm z pow 2 * (w dot w))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `abs(Q * X - &2 / norm(z:real^3) pow 2 * ((w:real^3) dot w)) <=
               s * &2 / norm z pow 2 * (w dot w)` THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REAL_ARITH_TAC);;

let P3H_NECK_BOX_VOLUME = prove
 (`!top atlas (g:A->real^3^3) dl y e j.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g dl y e /\ dl <= &1 / &2 /\
     &2 pow (j + 1) <= exp(inv(sqrt(&2) * dl))
     ==> ?v. mfd_has_volume (top,atlas) g (IMAGE e (p3h_box j)) v /\
             sqrt(inv(&3 * mfd_scalar atlas g y) pow 3) / &27 <= v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `p3h_box j SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
   [MP_TAC(SPECL [`dl:real`; `j:num`] P3H_BOX_IN_DOM) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (e:real^3->A) (p3h_box j))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom dl)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    REWRITE_TAC[p3h_box; COMPACT_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `IMAGE (e:real^3->A) (p3h_box j)`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Q = mfd_scalar atlas (g:A->real^3^3) y` THEN
  ABBREV_TAC `a = inv(&3 * Q)` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a / &4 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (euclidean,open_set_atlas (:real^3))
      (\x:real^3. (a / &4 pow j) %% mat 1) (p3h_box j)
      (sqrt((a / &4 pow j) pow 3) * (&8 pow j / &27))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(\x:real^3. mat 1):real^3->real^3^3`; `p3h_box j`;
                   `&8 pow j / &27`; `a / &4 pow j`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `p3h_box j`; `&8 pow j / &27`] MFD_HAS_VOLUME_EUCLIDEAN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas;
                P3H_BOX_MEASURE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(\x:real^3. (a / &4 pow j) %% mat 1):real^3->real^3^3`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `rfs_neck_dom dl`; `IMAGE (e:real^3->A) (rfs_neck_dom dl)`;
                 `e:real^3->A`; `e':A->real^3`; `p3h_box j`;
                 `sqrt((a / &4 pow j) pow 3) * (&8 pow j / &27)`; `v:real`; `&1`]
                P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; REAL_POS] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[GEOL_EUCLID_FACTS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[P3H_BOX_VOL_ARITH; SQRT_1; REAL_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `w:real^3`] THEN DISCH_TAC THEN
  REWRITE_TAC[P3H_PULLBACK_OPEN_UNIV; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  EXPAND_TAC "a" THEN EXPAND_TAC "Q" THEN
  MATCH_MP_TAC P3H_NECK_BOX_QF THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `dl:real`] THEN ASM_REWRITE_TAC[]);;

(* The first n boxes of the positive half of a neck: compact, inside the    *)
(* positive half, total volume >= n (1 / (3 Q))^(3/2) / 27.                  *)

let P3H_NECK_PLUS_BOXES = prove
 (`!top atlas (g:A->real^3^3) dl x e n.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g dl x e /\ dl <= &1 / &2 /\
     &2 pow n <= exp(inv(sqrt(&2) * dl))
     ==> compact_in top (UNIONS {IMAGE e (p3h_box j) | j | j < n}) /\
         UNIONS {IMAGE e (p3h_box j) | j | j < n} SUBSET
         IMAGE e {z | z IN rfs_neck_dom dl /\ &1 < norm z} /\
         ?v. mfd_has_volume (top,atlas) g (UNIONS {IMAGE e (p3h_box j) | j | j < n}) v /\
             &n * sqrt(inv(&3 * mfd_scalar atlas g x) pow 3) / &27 <= v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e ==> f <=> a /\ b /\ c /\ d ==> e ==> f`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  ABBREV_TAC `c = sqrt(inv(&3 * mfd_scalar atlas (g:A->real^3^3) x) pow 3) / &27` THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `{IMAGE (e:real^3->A) (p3h_box j) | j | j < 0} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[LT; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[UNIONS_0; EMPTY_SUBSET; COMPACT_IN_EMPTY] THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[MFD_HAS_VOLUME_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&2 pow n <= exp(inv(sqrt(&2) * dl))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow SUC n` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `UNIONS {IMAGE (e:real^3->A) (p3h_box j) | j | j < SUC n} =
                UNIONS {IMAGE e (p3h_box j) | j | j < n} UNION IMAGE e (p3h_box n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNION; IN_ELIM_THM; LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `dl:real`; `x:A`; `e:real^3->A`; `n:num`] P3H_NECK_BOX_VOLUME) THEN
  ASM_REWRITE_TAC[GSYM ADD1] THEN DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p3h_box n SUBSET {z | z IN rfs_neck_dom dl /\ &1 < norm z}` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_BOX_IN_DOM THEN ASM_REWRITE_TAC[GSYM ADD1]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom dl)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    REWRITE_TAC[p3h_box; COMPACT_INTERVAL] THEN REWRITE_TAC[GSYM p3h_box] THEN
    ASM SET_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `v + w:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM;
                IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:A->bool` MP_TAC)
      (X_CHOOSE_THEN `z2:real^3` STRIP_ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `p3h_box i SUBSET {z | z IN rfs_neck_dom dl /\ &1 < norm z}` ASSUME_TAC THENL
     [MATCH_MP_TAC P3H_BOX_IN_DOM THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z1:real^3) = z2` ASSUME_TAC THENL
     [SUBGOAL_THEN `(z1:real^3) IN rfs_neck_dom dl /\ z2 IN rfs_neck_dom dl` STRIP_ASSUME_TAC
      THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`i:num`; `n:num`] P3H_BOX_DISJOINT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z1:real^3`) THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
    UNDISCH_TAC `&n * c <= v` THEN UNDISCH_TAC `c <= w` THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The volume of a surgery cap.  A cap is the image under Phi               *)
(* of the compact region d_g0 <= A0 + 4 of the standard initial metric, and  *)
(* h^-2 Phi^* g is dd-close to g0 there; for dd <= 1/4 the cap volume is    *)
(* at most 2 h^3 times the g0-volume of that region (p3h_capvol g0 A0).     *)
(* ========================================================================= *)

let p3h_capvol = new_definition
 `p3h_capvol (g0:real^3->real^3^3) (A0:real) =
    mfd_volume (euclidean,open_set_atlas (:real^3)) g0
               {x | &0 <= A0 + &4 - p3_std_dist g0 x}`;;

let P3H_STD_REGION_COMPACT = prove
 (`!g0 A0 r. p3_std_initial g0 A0 ==> compact {x | p3_std_dist g0 x <= r}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | p3_std_dist g0 x <= r} =
                mfd_cball (euclidean,open_set_atlas (:real^3)) g0 (vec 0) r` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM; P2C_RAD_JOINABLE; p3_std_dist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN
  UNDISCH_TAC `p3_std_initial g0 A0` THEN REWRITE_TAC[p3_std_initial; mfd_complete] THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^3`; `r:real`] o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV]);;

let P3H_CAP_LAM_ARITH = prove
 (`!dd h. &0 <= dd /\ dd <= &1 / &4 /\ &0 < h
          ==> &0 <= (&1 + dd) * h pow 2 /\
              ((&1 + dd) * h pow 2) * sqrt((&1 + dd) * h pow 2) <= &2 * h pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= h pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + dd) /\ sqrt(&1 + dd) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&3 / &2 = sqrt((&3 / &2) pow 2)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + dd) * sqrt(&1 + dd) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&5 / &4) * (&3 / &2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + dd) * h pow 2) * sqrt(&1 + dd) * h =
                ((&1 + dd) * sqrt(&1 + dd)) * h pow 3` SUBST1_TAC THENL
   [REWRITE_TAC[num_CONV `3`; num_CONV `2`; real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]);;

let P3H_CAP_QF_ARITH = prove
 (`!h X G dd s. &0 < h /\ &0 <= G /\ s <= dd /\ abs(inv(h pow 2) * X - G) <= s * G
                ==> X <= ((&1 + dd) * h pow 2) * G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s * G <= dd * G` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(h pow 2) * X <= (&1 + dd) * G` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `X = h pow 2 * (inv(h pow 2) * X)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + dd) * h pow 2) * G = h pow 2 * ((&1 + dd) * G)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

(* Generic form: a parametrization Phi whose rescaled pullback is dd-close  *)
(* to g0 on D' (inside its domain D) maps a compact S inside D' to a set of *)
(* volume at most 2 h^3 Vol_g0(S).                                           *)

let P3H_PB_VOLUME_UPPER = prove
 (`!top atlas (g:A->real^3^3) g0 A0 D D' S Phi h dd k.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p3_std_initial g0 A0 /\ mfd_param top atlas D Phi /\
     compact S /\ S SUBSET D' /\ D' SUBSET D /\ &0 < h /\ &0 < dd /\ dd <= &1 / &4 /\
     rfs_close_on k dd D' g0 (\x. inv(h pow 2) %% rfs_pullback atlas Phi g x)
     ==> ?v. mfd_has_volume (top,atlas) g (IMAGE Phi S) v /\
             v <= &2 * h pow 3 * mfd_volume (euclidean,open_set_atlas (:real^3)) g0 S`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Phi':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `S SUBSET (D:real^3->bool)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (Phi:real^3->A) S)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology euclidean (D:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `IMAGE (Phi:real^3->A) S`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (g0:real^3->real^3^3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`; `S:real^3->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; COMPACT_IN_EUCLIDEAN] THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real`) THEN
  SUBGOAL_THEN `mfd_volume (euclidean,open_set_atlas (:real^3)) g0 S = v0` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_VOLUME THEN ASM_REWRITE_TAC[GEOL_EUCLID_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= v0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g0:real^3->real^3^3`; `S:real^3->bool`; `v0:real`]
                  MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[GEOL_EUCLID_FACTS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dd:real`; `h:real`] P3H_CAP_LAM_ARITH) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `lam = (&1 + dd) * h pow 2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g0:real^3->real^3^3`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `D:real^3->bool`; `IMAGE (Phi:real^3->A) D`; `Phi:real^3->A`;
                 `Phi':A->real^3`; `S:real^3->bool`; `v0:real`; `v:real`; `lam:real`]
                P2BC_VOLUME_PB_COMPARE) THEN
  ASM_REWRITE_TAC[GEOL_EUCLID_FACTS] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    REWRITE_TAC[P3H_PULLBACK_OPEN_UNIV] THEN
    SUBGOAL_THEN `(y:real^3) IN D' /\ y IN D` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `rfs_close_on k dd D' g0
                   (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) g x)` THEN
    REWRITE_TAC[rfs_close_on] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:num`; `D:real^3->bool`; `g0:real^3->real^3^3`;
                   `\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) g x`;
                   `y:real^3`; `w:real^3`] LCK_DIST_C0) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P3S_STD_METRIC_FIELD THEN
        EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
        ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT] THEN
        MATCH_MP_TAC APX_RFS_PULLBACK_FIELD THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN DISCH_TAC THEN
    EXPAND_TAC "lam" THEN MATCH_MP_TAC P3H_CAP_QF_ARITH THEN
    EXISTS_TAC `sqrt(lck_dist2 k g0
                  (\x. inv(h pow 2) %% rfs_pullback atlas (Phi:real^3->A) g x) y)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3S_STD_POS_LE THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * sqrt lam * v0` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]]);;

(* The minus cap of neck i at event k has volume <= 2 h^3 p3h_capvol g0 A0  *)
(* once dl(ts) <= md(1 / (A0 + 5)) (closeness clause with dd = 1/(A0+5)).   *)

let P3H_CAP_VOLUME = prove
 (`!md g0 A0 dl h (hs:(A)rfs_history) k i Phi xi.
     p3_std_initial g0 A0 /\ p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi /\
     &0 < dl(hs_time hs k) /\ dl(hs_time hs k) <= md(inv(A0 + &5)) /\
     &0 < h(hs_time hs k) /\
     hausdorff_space (hs_top hs k) /\ smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k) /\
     riemannian_metric (hs_atlas hs k) (hs_metric hs k (hs_time hs k))
     ==> ?v. mfd_has_volume (hs_top hs k,hs_atlas hs k) (hs_metric hs k (hs_time hs k))
               (IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))) v /\
             v <= &2 * h(hs_time hs k) pow 3 * p3h_capvol g0 A0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_cap_param]) THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  ABBREV_TAC `ts = hs_time (hs:(A)rfs_history) k` THEN
  ABBREV_TAC `dd = inv(A0 + &5)` THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= &1 / &4 /\ inv dd = A0 + &5` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[REAL_INV_INV] THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &4 = inv(&4)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dd:real` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_close_on")) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "ev_capm")) (concl th) &&
    is_eq (concl th))) THEN
  REWRITE_TAC[p3h_capvol] THEN
  MATCH_MP_TAC P3H_PB_VOLUME_UPPER THEN
  MAP_EVERY EXISTS_TAC
   [`A0:real`; `{x | --(inv(dl(ts:real))) < A0 + &4 - p3_std_dist g0 x}`;
    `{x | p3_std_dist g0 x < inv dd /\ --(inv(dl(ts:real))) < A0 + &4 - p3_std_dist g0 x}`;
    `dd:real`; `rfs_kreg dd`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(dl(ts:real))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{x | &0 <= A0 + &4 - p3_std_dist g0 x} = {x | p3_std_dist g0 x <= A0 + &4}`
    SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P3H_STD_REGION_COMPACT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Tools for the event volume inequality: volumes of finite                 *)
(* disjoint unions; the closure of the retained part of an event lies in    *)
(* the retained part plus the cut spheres (so in Omega); the C^0 volume     *)
(* comparison between the limit metric on Omega (as a metric of the open    *)
(* submanifold Omega) and the slab metrics just before the event time.     *)
(* ========================================================================= *)

let P3H_HAS_VOLUME_UNIONS = prove
 (`!top atlas (g:A->real^N^N) (f:num->A->bool) (v:num->real) J.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ FINITE J /\
     (!i. i IN J ==> mfd_has_volume (top,atlas) g (f i) (v i)) /\
     (!i j. i IN J /\ j IN J /\ ~(i = j) ==> DISJOINT (f i) (f j))
     ==> mfd_has_volume (top,atlas) g (UNIONS (IMAGE f J)) (sum J v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e ==> f <=> a /\ b ==> c ==> d /\ e ==> f`] THEN
  STRIP_TAC THEN SPEC_TAC(`J:num->bool`,`J:num->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUM_CLAUSES; MFD_HAS_VOLUME_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `s:num->bool`] THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; UNIONS_INSERT; SUM_CLAUSES] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:A->bool` MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `~(n:num = m)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m:num`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[]]);;

(* The closure in X of the retained part W = Y INTER X lies in W plus the  *)
(* cut spheres: off the spheres, X and Z agree near each point, and W is    *)
(* the complement of the clopen discarded set D there.                     *)

let P3H_EVENT_RETAINED_CLOSURE = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev
     ==> topX closure_of (topspace topY INTER topspace topX) SUBSET
         (topspace topY INTER topspace topX) UNION
         mfd_cut_spheres (ev_index ev) (ev_neck ev)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_event_ok] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_CUT_SAME_SUBSPACE) THEN STRIP_TAC THEN
  ABBREV_TAC `X' = topspace topX DIFF mfd_cut_spheres (ev_index ev)
                                        (ev_neck (ev:(A)rfs_event))` THEN
  ABBREV_TAC `D = ev_disc (ev:(A)rfs_event)` THEN
  ABBREV_TAC `Z = ev_ztop (ev:(A)rfs_event)` THEN
  SUBGOAL_THEN `topspace topY = topspace Z DIFF (D:A->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX ((D:A->bool) INTER X')` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `X':A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && is_comb (lhs (concl th)) &&
      can (find_term (fun t -> t = `Z:A topology`)) (lhs (concl th)))) THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `D:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_CLOSURE_OF] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:A) IN mfd_cut_spheres (ev_index ev) (ev_neck ev)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:A) IN X'` ASSUME_TAC THENL [EXPAND_TAC "X'" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN topspace Z` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(p:A) IN D` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(D:A->bool) INTER X'`) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]);;

(* Pointwise C^0 comparison of the limit metric with the slab metric near   *)
(* the event time on a compact subset of Omega (preferred charts of X).    *)

let P3H_LIMIT_QF_NEAR = prove
 (`!top atlas a Om ts (g:real->A->real^3^3) gl K q.
        smooth_manifold_atlas top atlas /\ a < ts /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlas (g t)) /\
        rfs_limit_metric (top,atlas) Om ts g gl /\
        compact_in top K /\ K SUBSET Om /\ &0 < q /\ q < &1
        ==> ?d. &0 < d /\ d <= ts - a /\
                !t y w. ts - d < t /\ t < ts /\ y IN K
                        ==> w dot (gl y ** w) <= inv(&1 - q) * (w dot (g t y ** w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(q pow 2) = q` ASSUME_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`K:A->bool`; `0`; `q pow 2`] o CONJUNCT2 o
              GEN_REWRITE_RULE I [rfs_limit_metric]) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d0 (ts - a)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`; `w:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN Om /\ y IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c INTER Om))
                  (metric_local (atlas:((A->bool)#(A->real^3))->bool) c (gl:A->real^3^3))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_limit_metric]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER Om)`;
                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c (gl:A->real^3^3)`;
                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                               ((g:real->A->real^3^3) t)`;
                 `SND (c:(A->bool)#(A->real^3)) y`; `q pow 2`] P3H_LCK_QF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; SET_TAC[]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN EXPAND_TAC "c" THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `w:real^3`) THEN
  EXPAND_TAC "c" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `gl:A->real^3^3`; `y:A`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `y:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv(&1 - q) * (&1 - q) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = (w:real^3) dot ((gl:A->real^3^3) y ** w)` THEN
  ABBREV_TAC `Y = (w:real^3) dot ((g:real->A->real^3^3) t y ** w)` THEN
  SUBGOAL_THEN `inv(&1 - q) * ((&1 - q) * X) = X` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`inv(&1 - q)`; `(&1 - q) * X`; `Y:real`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Volume form on the open submanifold Omega. *)

let P3H_LIMIT_VOLUME_COMPARE_OM = prove
 (`!top atlas a Om ts (g:real->A->real^3^3) gl K e.
        smooth_manifold_atlas top atlas /\ open_in top Om /\ a < ts /\
        (!t. a <= t /\ t < ts ==> riemannian_metric atlas (g t)) /\
        rfs_limit_metric (top,atlas) Om ts g gl /\
        compact_in top K /\ K SUBSET Om /\ &0 < e
        ==> ?d. &0 < d /\ d <= ts - a /\
                !t S v v'. ts - d < t /\ t < ts /\ S SUBSET K /\
                           mfd_has_volume (subtopology top Om,restrict_atlas atlas Om)
                                          (restrict_metric atlas Om gl) S v /\
                           mfd_has_volume (top,atlas) (g t) S v'
                           ==> v <= (&1 + e) * v'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = min (&1 / &4) (e / &8)` THEN
  SUBGOAL_THEN `&0 < q /\ q <= &1 / &4 /\ &5 * q <= e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `lam = inv(&1 - q)` THEN
  SUBGOAL_THEN `&1 <= lam /\ lam * sqrt lam <= &1 + e` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `q:real` P3H_LAM_BOUND) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `Om:A->bool`; `ts:real`; `g:real->A->real^3^3`; `gl:A->real^3^3`;
                 `K:A->bool`; `q:real`] P3H_LIMIT_QF_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `S:A->bool`; `v:real`; `v':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top Om)
                  (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om)` ASSUME_TAC
  THENL [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om)
                  (restrict_metric atlas Om (gl:A->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ts:real`; `g:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om)
                  (restrict_metric atlas Om ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_has_volume (subtopology top Om,restrict_atlas atlas Om)
                  (restrict_metric atlas Om ((g:real->A->real^3^3) t)) S v'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `Om:A->bool`; `S:A->bool`; `v':real`]
                  P2BC_VOLUME_RESTRICT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * sqrt lam * v'` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_COMPARE_QF THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology top (Om:A->bool)`; `restrict_atlas (atlas:((A->bool)#(A->real^3))->bool) Om`;
      `restrict_metric atlas Om (gl:A->real^3^3)`;
      `restrict_metric atlas Om ((g:real->A->real^3^3) t)`; `S:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC P3H_RESTRICT_QF_TRANSFER THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `u:real^3` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `S:A->bool`; `v':real`]
                  MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The volume inequality at one event.  On the open                         *)
(* submanifold Omega of the old stage X with the limit metric: the retained *)
(* part W and compact pieces Kp i of the discarded positive halves are      *)
(* disjoint, inside a compact subset of Omega, so their total volume is at  *)
(* most (1 + e) Vol(X, gX t) for t close to the event time; the new stage  *)
(* is W plus the minus caps.                                                *)
(* ========================================================================= *)

let P3H_EVENT_XO_VOLUME = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts Om gl a W (Kp:num->A->bool) kv J B vW e.
     hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\ compact_space topX /\
     open_in topX Om /\ a < ts /\ (!t. a <= t /\ t < ts ==> riemannian_metric atlasX (gX t)) /\
     rfs_limit_metric (topX,atlasX) Om ts gX gl /\
     open_in topX W /\ topX closure_of W SUBSET Om /\ FINITE J /\
     (!i. i IN J
          ==> compact_in topX (Kp i) /\ Kp i SUBSET Om /\ DISJOINT (Kp i) W /\
              mfd_has_volume (subtopology topX Om,restrict_atlas atlasX Om)
                             (restrict_metric atlasX Om gl) (Kp i) (kv i) /\ B <= kv i) /\
     (!i j. i IN J /\ j IN J /\ ~(i = j) ==> DISJOINT (Kp i) (Kp j)) /\
     mfd_has_volume (subtopology topX Om,restrict_atlas atlasX Om)
                    (restrict_metric atlasX Om gl) W vW /\ &0 < e
     ==> ?d. &0 < d /\ d <= ts - a /\
             !t. ts - d < t /\ t < ts
                 ==> vW + &(CARD J) * B <=
                     (&1 + e) * mfd_volume (topX,atlasX) (gX t) (topspace topX)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology topX Om)
                  (restrict_atlas (atlasX:((A->bool)#(A->real^3))->bool) Om)` ASSUME_TAC
  THENL [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas (atlasX:((A->bool)#(A->real^3))->bool) Om)
                  (restrict_metric atlasX Om (gl:A->real^3^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `ts:real`; `gX:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (subtopology topX Om,restrict_atlas atlasX Om)
      (restrict_metric atlasX Om (gl:A->real^3^3)) (UNIONS (IMAGE (Kp:num->A->bool) J))
      (sum (J:num->bool) (kv:num->real))` ASSUME_TAC THENL
   [MATCH_MP_TAC P3H_HAS_VOLUME_UNIONS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (W:A->bool) (UNIONS (IMAGE (Kp:num->A->bool) J))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (subtopology topX Om,restrict_atlas atlasX Om)
      (restrict_metric atlasX Om (gl:A->real^3^3))
      (W UNION UNIONS (IMAGE (Kp:num->A->bool) J)) (vW + sum J kv)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD (J:num->bool)) * B <= sum J (kv:num->real)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_CONST] THEN MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in topX (UNIONS (IMAGE (Kp:num->A->bool) J))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `K = topX closure_of (W:A->bool) UNION UNIONS (IMAGE (Kp:num->A->bool) J)` THEN
  SUBGOAL_THEN `compact_in topX (K:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET Om` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:A->bool) SUBSET topX closure_of W` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `Om:A->bool`; `ts:real`; `gX:real->A->real^3^3`; `gl:A->real^3^3`;
                 `K:A->bool`; `e:real`] P3H_LIMIT_VOLUME_COMPARE_OM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cmp")))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlasX ((gX:real->A->real^3^3) t)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(gX:real->A->real^3^3) t`; `topspace topX:A->bool`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `VX:real`) THEN
  SUBGOAL_THEN `mfd_volume (topX,atlasX) ((gX:real->A->real^3^3) t) (topspace topX) = VX`
  SUBST1_TAC THENL [MATCH_MP_TAC MFD_HAS_VOLUME_VOLUME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(gX:real->A->real^3^3) t`; `W:A->bool`; `topspace topX:A->bool`;
                 `VX:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN; OPEN_IN_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `(gX:real->A->real^3^3) t`; `UNIONS (IMAGE (Kp:num->A->bool) J)`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `vK:real`) THEN
  ABBREV_TAC `vWt = mfd_volume (topX,atlasX) ((gX:real->A->real^3^3) t) W` THEN
  SUBGOAL_THEN
   `mfd_has_volume (topX,atlasX) ((gX:real->A->real^3^3) t)
      (W UNION UNIONS (IMAGE (Kp:num->A->bool) J)) (vWt + vK)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `vW + sum (J:num->bool) (kv:num->real) <= (&1 + e) * (vWt + vK)` ASSUME_TAC THENL
   [USE_THEN "cmp" (MATCH_MP_TAC o SPECL
      [`t:real`; `W UNION UNIONS (IMAGE (Kp:num->A->bool) J)`]) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vWt + vK <= VX` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `(gX:real->A->real^3^3) t`;
                   `W UNION UNIONS (IMAGE (Kp:num->A->bool) J)`;
                   `topspace topX:A->bool`; `vWt + vK:real`; `VX:real`]
                  MFD_HAS_VOLUME_MONO) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET; COMPACT_IN_SUBSET_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) * (vWt + vK) <= (&1 + e) * VX` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Minus caps are compact subsets of the new stage. *)

let P3H_EVENT_CAP_COMPACT = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev i.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\ i IN ev_index ev
     ==> compact_in topY (IMAGE (ev_capm ev i) (cball(vec 0,&1)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_EVENT_STAGE_DECOMP) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_event_ok]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [mfd_cut_cap]) THEN
  ASM_REWRITE_TAC[mfd_ball_chart] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cm':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS o
    check (fun th -> can (find_term (fun t -> t = `ev_capm (ev:(A)rfs_event)`)) (concl th))) THEN
  SUBGOAL_THEN `compact_in (ev_ztop ev) (IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL;
                    SUBSET_BALLS; DIST_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1)) SUBSET topspace topY` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

(* The new stage: retained part W (open) plus the minus caps, volumes add. *)

let P3H_EVENT_Y_VOLUME = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\ compact_space topY /\
     riemannian_metric atlasY (gY ts)
     ==> open_in topY (topspace topY INTER topspace topX) /\
         ?vW c. mfd_has_volume (topY,atlasY) (gY ts) (topspace topY INTER topspace topX) vW /\
                (!i. i IN ev_index ev
                     ==> mfd_has_volume (topY,atlasY) (gY ts)
                           (IMAGE (ev_capm ev i) (cball(vec 0,&1))) (c i)) /\
                mfd_has_volume (topY,atlasY) (gY ts) (topspace topY)
                  (vW + sum (ev_index ev) c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (ev_index (ev:(A)rfs_event))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_cut_cap] o
      el 5 o CONJUNCTS o GEN_REWRITE_RULE I [rfs_event_ok]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P3H_EVENT_STAGE_DECOMP) THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN
  ABBREV_TAC `cap = \i. IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1))` THEN
  SUBGOAL_THEN `!i. IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1)) = cap i`
  (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "cap" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  ABBREV_TAC `W = topspace topY INTER topspace (topX:A topology)` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `topspace (topY:A topology)`)) THEN
  SUBGOAL_THEN `!i. i IN ev_index (ev:(A)rfs_event) ==> compact_in topY ((cap:num->A->bool) i)` ASSUME_TAC
  THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "cap" THEN BETA_TAC THEN
    MATCH_MP_TAC P3H_EVENT_CAP_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                          `gX:real->A->real^3^3`; `ts:real`;
                          `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in topY (UNIONS (IMAGE (cap:num->A->bool) (ev_index (ev:(A)rfs_event))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_UNIONS THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topY (W:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `W = topspace topY DIFF UNIONS (IMAGE (cap:num->A->bool) (ev_index (ev:(A)rfs_event)))`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `(gY:real->A->real^3^3) ts`; `topspace topY:A->bool`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM compact_space]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `VY:real`) THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `(gY:real->A->real^3^3) ts`; `W:A->bool`; `topspace topY:A->bool`;
                 `VY:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN; OPEN_IN_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  EXISTS_TAC `mfd_volume (topY,atlasY) ((gY:real->A->real^3^3) ts) W` THEN
  EXISTS_TAC `\i. mfd_volume (topY,atlasY) ((gY:real->A->real^3^3) ts) ((cap:num->A->bool) i)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. i IN ev_index (ev:(A)rfs_event)
                    ==> mfd_has_volume (topY,atlasY) ((gY:real->A->real^3^3) ts)
                          ((cap:num->A->bool) i)
                          (mfd_volume (topY,atlasY) (gY ts) (cap i))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `(gY:real->A->real^3^3) ts`; `(cap:num->A->bool) i`]
                  MFD_HAS_VOLUME_COMPACT) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `(gY:real->A->real^3^3) ts`; `(cap:num->A->bool) i`; `u:real`]
                  MFD_HAS_VOLUME_VOLUME) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `topspace topY = (W:A->bool) UNION UNIONS (IMAGE (cap:num->A->bool) (ev_index (ev:(A)rfs_event)))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                 `(gY:real->A->real^3^3) ts`; `cap:num->A->bool`;
                 `\i. mfd_volume (topY,atlasY) ((gY:real->A->real^3^3) ts) ((cap:num->A->bool) i)`;
                 `ev_index (ev:(A)rfs_event)`] P3H_HAS_VOLUME_UNIONS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th) &&
    is_forall (concl th))) THEN ASM_REWRITE_TAC[]);;

(* The event inequality: with compact pieces Kp i of the discarded region   *)
(* inside Omega (pairwise disjoint, limit-metric volume >= B each) and minus *)
(* caps of volume <= Kc, for t close to ts                                    *)
(*   Vol(Y) + m (B - Kc) <= (1 + e) Vol(X, gX t),   m = number of necks.     *)

let P3H_EVENT_VOLUME_INEQ = prove
 (`!topX atlasX (gX:real->A->real^3^3) ts topY atlasY gY ev a (Kp:num->A->bool) kv B Kc e.
     rfs_event_ok (topX,atlasX) gX ts (topY,atlasY) gY ev /\
     hausdorff_space topX /\ smooth_manifold_atlas topX atlasX /\ compact_space topX /\
     a < ts /\ (!t. a <= t /\ t < ts ==> riemannian_metric atlasX (gX t)) /\
     hausdorff_space topY /\ smooth_manifold_atlas topY atlasY /\ compact_space topY /\
     riemannian_metric atlasY (gY ts) /\
     (!i. i IN ev_index ev
          ==> compact_in topX (Kp i) /\ Kp i SUBSET ev_omega ev /\
              DISJOINT (Kp i) (topspace topY) /\
              mfd_has_volume (subtopology topX (ev_omega ev),restrict_atlas atlasX (ev_omega ev))
                             (restrict_metric atlasX (ev_omega ev) (ev_limit ev)) (Kp i) (kv i) /\
              B <= kv i) /\
     (!i j. i IN ev_index ev /\ j IN ev_index ev /\ ~(i = j) ==> DISJOINT (Kp i) (Kp j)) /\
     (!i. i IN ev_index ev
          ==> ?v. mfd_has_volume (topY,atlasY) (gY ts)
                    (IMAGE (ev_capm ev i) (cball(vec 0,&1))) v /\ v <= Kc) /\
     &0 < e
     ==> ?d. &0 < d /\ d <= ts - a /\
             !t. ts - d < t /\ t < ts
                 ==> mfd_volume (topY,atlasY) (gY ts) (topspace topY) +
                     &(CARD(ev_index ev)) * (B - Kc) <=
                     (&1 + e) * mfd_volume (topX,atlasX) (gX t) (topspace topX)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `J = ev_index (ev:(A)rfs_event)` THEN
  ABBREV_TAC `Om = ev_omega (ev:(A)rfs_event)` THEN
  ABBREV_TAC `gl = ev_limit (ev:(A)rfs_event)` THEN
  SUBGOAL_THEN `FINITE (J:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_cut_cap] o
      el 5 o CONJUNCTS o GEN_REWRITE_RULE I [rfs_event_ok]) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in topX (Om:A->bool) /\
                rfs_limit_metric (topX,atlasX) Om ts (gX:real->A->real^3^3) gl /\
                rfs_same_metric_on atlasX gl atlasY ((gY:real->A->real^3^3) ts)
                  (topspace topY INTER topspace topX) /\
                (!i. i IN J
                     ==> IMAGE (ev_neck ev i) (annulus (&1 / &2) (&2)) SUBSET Om)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_event_ok (topX,atlasX) (gX:real->A->real^3^3) ts (topY,atlasY) gY ev` THEN
    REWRITE_TAC[rfs_event_ok] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`] P3H_EVENT_Y_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `W = topspace topY INTER topspace (topX:A topology)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!i. i IN J ==> (c:num->real) i <= Kc` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `Kc:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:num->real) i = u` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`topY:A topology`; `atlasY:((A->bool)#(A->real^3))->bool`;
                   `(gY:real->A->real^3^3) ts`;
                   `IMAGE (ev_capm (ev:(A)rfs_event) i) (cball(vec 0,&1))`;
                   `(c:num->real) i`; `u:real`] MFD_HAS_VOLUME_UNIQUE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum J (c:num->real) <= &(CARD (J:num->bool)) * Kc` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `topY:A topology`;
                 `atlasY:((A->bool)#(A->real^3))->bool`; `gY:real->A->real^3^3`;
                 `ev:(A)rfs_event`; `W:A->bool`] P3S_EVENT_RETAINED) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [EXPAND_TAC "W" THEN SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_has_volume (subtopology topX Om,restrict_atlas atlasX Om)
                  (restrict_metric atlasX Om (gl:A->real^3^3)) W vW` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gl:A->real^3^3`; `Om:A->bool`; `W:A->bool`; `vW:real`]
                  P2BC_VOLUME_RESTRICT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                   `gl:A->real^3^3`; `topY:A topology`;
                   `atlasY:((A->bool)#(A->real^3))->bool`; `(gY:real->A->real^3^3) ts`;
                   `W:A->bool`; `W:A->bool`; `vW:real`] P3H_RETAINED_VOLUME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P3H_LIMIT_RESTRICT_RIEMANNIAN_SUB THEN
      MAP_EVERY EXISTS_TAC [`topX:A topology`; `Om:A->bool`; `ts:real`;
                            `gX:real->A->real^3^3`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `topX closure_of (W:A->bool) SUBSET Om` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(W:A->bool) UNION mfd_cut_spheres J (ev_neck (ev:(A)rfs_event))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "W" THEN EXPAND_TAC "J" THEN MATCH_MP_TAC P3H_EVENT_RETAINED_CLOSURE THEN
      MAP_EVERY EXISTS_TAC [`atlasX:((A->bool)#(A->real^3))->bool`; `gX:real->A->real^3^3`;
                            `ts:real`; `atlasY:((A->bool)#(A->real^3))->bool`;
                            `gY:real->A->real^3^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_MFD_CUT_SPHERES] THEN X_GEN_TAC `p:A` THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "annulus")) (concl th))) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topX:A topology`; `atlasX:((A->bool)#(A->real^3))->bool`;
                 `gX:real->A->real^3^3`; `ts:real`; `Om:A->bool`; `gl:A->real^3^3`;
                 `a:real`; `W:A->bool`; `Kp:num->A->bool`; `kv:num->real`; `J:num->bool`;
                 `B:real`; `vW:real`; `e:real`] P3H_EVENT_XO_VOLUME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `B:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_volume (topY,atlasY) ((gY:real->A->real^3^3) ts) (topspace topY) =
                vW + sum J (c:num->real)` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_VOLUME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `vW:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `sum J (c:num->real) <= &(CARD (J:num->bool)) * Kc` THEN
  REAL_ARITH_TAC);;

