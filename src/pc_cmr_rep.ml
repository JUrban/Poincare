(* ========================================================================= *)
(* Unit pc_cmr_rep (a unit of the replacement chain of pc_cm_replacement):   *)
(* harmonic replacement of an S^2 map on one cap IMAGE (cm_capmap Q)         *)
(* (ball(c,r)), with the minimizer selected by CM_REPLACEMENT clause 1       *)
(* (unique on the closed disc by clause 2), and on finite families of caps.  *)
(*                                                                           *)
(* The selected minimizer and the chart maps of S^2 maps.                    *)
(* ========================================================================= *)

needs "src/pc_cmr_scale.ml";;
needs "src/pc_cmr_crit.ml";;
needs "src/pc_cmw_pos.ml";;
needs "src/pc_hm_dexist.ml";;

prioritize_real();;
type_invention_error := true;;

let cmr_minw = new_definition
 `cmr_minw (S:real^K->bool) (G:real^K->real^K^K) (c:real^2) r (f:real^2->real^K) =
    @w:real^2->real^K.
       cm_minimizer S G (ball(c,r)) w /\ wan_w120 (ball(c,r)) (\x. w x - f x) /\
       cm_cmap S (ball(c,r)) w /\ cm_harmonic S G (ball(c,r)) w /\
       (!x. x IN sphere(c,r) ==> w x = f x)`;;

let cmr_rep1 = new_definition
 `cmr_rep1 (S:real^K->bool) (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r
           (u:real^3->real^K) =
    \y:real^3. if y IN IMAGE (cm_capmap Q) (ball(c,r))
               then cmr_minw S G c r (\x. u(cm_capmap Q x)) (cmr_chart Q y)
               else u y`;;

let CMR_MINW_WORKS = prove
 (`!S (G:real^K->real^K^K) e (c:real^2) r (f:real^2->real^K).
     cmw_repex S G e /\ &0 < r /\ cm_cmap S (ball(c,r)) f /\ wan_gdir (ball(c,r)) G f <= e
     ==> cm_minimizer S G (ball(c,r)) (cmr_minw S G c r f) /\
         wan_w120 (ball(c,r)) (\x. cmr_minw S G c r f x - f x) /\
         cm_cmap S (ball(c,r)) (cmr_minw S G c r f) /\
         cm_harmonic S G (ball(c,r)) (cmr_minw S G c r f) /\
         (!x. x IN sphere(c,r) ==> cmr_minw S G c r f x = f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_repex] THEN STRIP_TAC THEN
  REWRITE_TAC[cmr_minw] THEN CONV_TAC SELECT_CONV THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^2`; `r:real`; `f:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let CMR_MIN_UNIQUE = prove
 (`!S (G:real^K->real^K^K) e (c:real^2) r (f:real^2->real^K) w1 w2.
     cmw_repcont S G e /\ &0 < r /\
     cm_cmap S (ball(c,r)) f /\ wan_gdir (ball(c,r)) G f <= e /\
     cm_minimizer S G (ball(c,r)) w1 /\ cm_cmap S (ball(c,r)) w1 /\
     (!x. x IN sphere(c,r) ==> w1 x = f x) /\
     cm_minimizer S G (ball(c,r)) w2 /\ cm_cmap S (ball(c,r)) w2 /\
     (!x. x IN sphere(c,r) ==> w2 x = f x)
     ==> !x. x IN cball(c,r) ==> w1 x = w2 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_repcont] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c:real^2`; `r:real`; `\n:num. (f:real^2->real^K)`; `f:real^2->real^K`;
    `\n:num. (w1:real^2->real^K)`; `w2:real^2->real^K`]) THEN
  ASM_SIMP_TAC[LIM_CONST; VECTOR_SUB_REFL; NORM_0; WAN_DIR_ZERO; OPEN_BALL;
               REALLIM_CONST] THEN
  ANTS_TAC THENL [SIMP_TAC[EVENTUALLY_TRUE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(&0 < a) ==> a = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `norm((w1:real^2->real^K) x - w2 x)`) THEN
  ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;

let CMR_MINW_UNIQUE = prove
 (`!S (G:real^K->real^K^K) e (c:real^2) r (f:real^2->real^K) w.
     cmw_repex S G e /\ cmw_repcont S G e /\ &0 < r /\
     cm_cmap S (ball(c,r)) f /\ wan_gdir (ball(c,r)) G f <= e /\
     cm_minimizer S G (ball(c,r)) w /\ cm_cmap S (ball(c,r)) w /\
     (!x. x IN sphere(c,r) ==> w x = f x)
     ==> !x. x IN cball(c,r) ==> w x = cmr_minw S G c r f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_MIN_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `f:real^2->real^K`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `f:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_SIMP_TAC[ETA_AX]);;


(* ========================================================================= *)
(* Chart maps of S^2 maps are W^{1,2}_loc on the plane and                   *)
(* C^0 /\ W^{1,2} on chart discs; the chart map of a one-cap replacement.  *)
(* ========================================================================= *)

let CMR_CHART_W12LOC = prove
 (`!(u:real^3->real^K) (Q:real^3^3).
     wan_s2_w12 u /\ orthogonal_matrix Q
     ==> wan_lloc (:real^2) (\x. u(cm_capmap Q x)) /\
         !i. 1 <= i /\ i <= 2
             ==> ?v. v IN lspace (:real^2) (&2) /\
                     wan_wpd (:real^2) i (\x. u(cm_capmap Q x)) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `u:real^3->real^K`] CMR_ROT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPEC `(:K)` WAN_S2_STEREO) THEN REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:real^3. (u:real^3->real^K)((Q:real^3^3) ** y)` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[cm_capmap] THEN SIMP_TAC[]);;

let CMR_SPHERE_CONT_BOUND = prove
 (`!u:real^3->real^K.
     u continuous_on sphere(vec 0,&1)
     ==> ?M. &0 < M /\ !y. y IN sphere(vec 0,&1) ==> norm(u y) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (u:real^3->real^K) (sphere(vec 0,&1))` COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]]);;

let CMR_CHART_CONT = prove
 (`!(u:real^3->real^K) (Q:real^3^3).
     u continuous_on sphere(vec 0,&1) /\ orthogonal_matrix Q
     ==> (\x. u(cm_capmap Q x)) continuous_on (:real^2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (u:real^3->real^K)(cm_capmap Q x)) = u o cm_capmap Q` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[CMR_CAPMAP_SMOOTH];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    ASM_MESON_TAC[CMR_CAPMAP_FACTS]]);;

let CMR_CHART_CMAP = prove
 (`!S (u:real^3->real^K) (Q:real^3^3) (c:real^2) r.
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r
     ==> cm_cmap S (ball(c,r)) (\x. u(cm_capmap Q x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_smap] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL] THEN
  SUBGOAL_THEN `(\x. (u:real^3->real^K)(cm_capmap Q x)) continuous_on (:real^2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[CMR_CHART_CONT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]] THEN
  REWRITE_TAC[wan_w12; DIMINDEX_2] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `u:real^3->real^K` CMR_SPHERE_CONT_BOUND) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HMC_BOUNDED_LSPACE THEN EXISTS_TAC `M:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^2->real^K` THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_BALL];
    MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let CMR_REP1_CHART = prove
 (`!S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) x.
     orthogonal_matrix Q
     ==> cmr_rep1 S G Q c r u (cm_capmap Q x) =
         if x IN ball(c,r) then cmr_minw S G c r (\x. u(cm_capmap Q x)) x
         else u(cm_capmap Q x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  REWRITE_TAC[cmr_rep1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cm_capmap (Q:real^3^3) x IN IMAGE (cm_capmap Q) (ball(c,r)) <=> x IN ball(c,r)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x:real^2 = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `cmr_chart (Q:real^3^3)`) THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The one-cap replacement is a C^0 /\ W^{1,2} map of S^2                    *)
(* into S, and its energy formula.                                          *)
(* ========================================================================= *)

let CMR_CHART_CONT_SPHERE = prove
 (`!Q:real^3^3.
     orthogonal_matrix Q
     ==> cmr_chart Q continuous_on (sphere(vec 0,&1) DELETE (Q ** basis 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cmr_chart (Q:real^3^3) = stereo2_n o (\y. transp Q ** y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; cmr_chart]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | x$3 < &1}` THEN
  SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; STEX_STEREO2_N_SMOOTH] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_SPHERE_0; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC CMR_UNIT_NE_E3 THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM; ORTHOGONAL_MATRIX_TRANSP] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(y:real^3 = (Q:real^3^3) ** basis 3)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. (Q:real^3^3) ** v`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_LID]);;

let CMR_CAP_OPEN_IN = prove
 (`!(Q:real^3^3) D.
     orthogonal_matrix Q /\ open D
     ==> open_in (subtopology euclidean (sphere(vec 0,&1))) (IMAGE (cm_capmap Q) D)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  SUBGOAL_THEN
   `IMAGE (cm_capmap (Q:real^3^3)) D =
    {y | y IN sphere(vec 0,&1) DELETE (Q ** basis 3) /\ cmr_chart Q y IN D}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_DELETE] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN EXISTS_TAC `cmr_chart (Q:real^3^3) y` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `sphere(vec 0:real^3,&1) DELETE ((Q:real^3^3) ** basis 3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[CMR_CHART_CONT_SPHERE];
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) DELETE ((Q:real^3^3) ** basis 3) =
                  sphere(vec 0,&1) INTER ((:real^3) DELETE (Q ** basis 3))`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV]]);;

let CMR_PASTE_CONT = prove
 (`!(Q:real^3^3) (c:real^2) r (u:real^3->real^K) (w:real^2->real^K).
     orthogonal_matrix Q /\ &0 < r /\ u continuous_on sphere(vec 0,&1) /\
     w continuous_on cball(c,r) /\ (!x. x IN sphere(c,r) ==> w x = u(cm_capmap Q x))
     ==> (\y. if y IN IMAGE (cm_capmap Q) (ball(c,r)) then w(cmr_chart Q y) else u y)
         continuous_on sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  SUBGOAL_THEN `IMAGE (cm_capmap (Q:real^3^3)) (cball(c,r)) SUBSET sphere(vec 0,&1)`
  ASSUME_TAC THENL [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sphere(vec 0:real^3,&1) =
    IMAGE (cm_capmap Q) (cball(c,r)) UNION
    (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (ball(c,r)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET s /\ (u:real^3->bool) SUBSET t
                           ==> s = t UNION (s DIFF u)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_SUBSET THEN REWRITE_TAC[SUBSET_UNION] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV; CMR_CAPMAP_SMOOTH];
    MATCH_MP_TAC CLOSED_IN_SUBSET_TRANS THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
      ASM_SIMP_TAC[CMR_CAP_OPEN_IN; OPEN_BALL];
      SET_TAC[];
      ASM SET_TAC[]];
    SUBGOAL_THEN `(\y. (w:real^2->real^K)(cmr_chart (Q:real^3^3) y)) = w o cmr_chart Q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1) DELETE ((Q:real^3^3) ** basis 3)` THEN
      ASM_SIMP_TAC[CMR_CHART_CONT_SPHERE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:real^2,r)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (cm_capmap Q) (cball(c,r))` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN sphere(c,r)` (fun th -> ASM_SIMP_TAC[th]) THEN
    UNDISCH_TAC `~((y:real^3) IN IMAGE (cm_capmap Q) (ball(c,r)))` THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    UNDISCH_TAC `(x:real^2) IN cball(c,r)` THEN
    REWRITE_TAC[IN_CBALL; IN_BALL; IN_SPHERE] THEN MESON_TAC[REAL_LE_LT]]);;

let CMR_REP1_FACTS = prove
 (`!S (G:real^K->real^K^K) e (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cm_smap S (cmr_rep1 S G Q c r u) /\
         (!x. x IN ball(c,r)
              ==> cmr_rep1 S G Q c r u (cm_capmap Q x) =
                  cmr_minw S G c r (\x. u(cm_capmap Q x)) x) /\
         (!x. ~(x IN ball(c,r))
              ==> cmr_rep1 S G Q c r u (cm_capmap Q x) = u(cm_capmap Q x)) /\
         (!y. ~(y IN IMAGE (cm_capmap Q) (ball(c,r))) ==> cmr_rep1 S G Q c r u y = u y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `U = \x. (u:real^3->real^K)(cm_capmap (Q:real^3^3) x)` THEN
  ABBREV_TAC `w = cmr_minw S (G:real^K->real^K^K) (c:real^2) r U` THEN
  SUBGOAL_THEN `cm_cmap S (ball(c,r)) (U:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `U:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMR_CAPMAP_FACTS) THEN
  SUBGOAL_THEN
   `!x. cmr_rep1 S G Q c r u (cm_capmap Q x) =
        if x IN ball(c,r) then (w:real^2->real^K) x else U x`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[CMR_REP1_CHART] THEN MAP_EVERY EXPAND_TAC ["w"; "U"] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ~(y IN IMAGE (cm_capmap (Q:real^3^3)) (ball(c,r)))
        ==> cmr_rep1 S G Q c r u y = (u:real^3->real^K) y`
  ASSUME_TAC THENL [SIMP_TAC[cmr_rep1]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[]] THEN
  UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN REWRITE_TAC[cm_smap] THEN STRIP_TAC THEN
  UNDISCH_TAC `cm_cmap S (ball(c,r)) (w:real^2->real^K)` THEN
  ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmr_rep1 S G Q c r (u:real^3->real^K) continuous_on sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `cmr_rep1 S G Q c r (u:real^3->real^K) =
      (\y. if y IN IMAGE (cm_capmap Q) (ball(c,r)) then (w:real^2->real^K)(cmr_chart Q y)
           else u y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; cmr_rep1] THEN MAP_EVERY EXPAND_TAC ["w"; "U"] THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CMR_PASTE_CONT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [    ALL_TAC;
    (* values in S *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[cmr_rep1] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (cm_capmap Q) (ball(c,r))` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cmr_minw S G c r (\x. (u:real^3->real^K)(cm_capmap Q x)) x = w x`
    SUBST1_TAC THENL [MAP_EVERY EXPAND_TAC ["w"; "U"] THEN REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]] THEN
  ABBREV_TAC `R = cmr_rep1 S G Q c r (u:real^3->real^K)` THEN
  ABBREV_TAC `v = \y:real^3. (R:real^3->real^K)((Q:real^3^3) ** y)` THEN
  SUBGOAL_THEN `(R:real^3->real^K) = (\y. v(transp(Q:real^3^3) ** y))` SUBST1_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[FUN_EQ_THM; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_s2_w12 (v:real^3->real^K)` ASSUME_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`transp(Q:real^3^3)`; `v:real^3->real^K`] CMR_ROT_FACTS) THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP]] THEN
  SUBGOAL_THEN `(v:real^3->real^K) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    SUBGOAL_THEN `(\y. (R:real^3->real^K)((Q:real^3^3) ** y)) = R o (\y. Q ** y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MATRIX_VECTOR_MUL_LINEAR] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:K)` WAN_S2_STEREO) THEN REWRITE_TAC[WAN_S2_STEREO_STATEMENT] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `(\y. (v:real^3->real^K)(stereo2_n_inv y)) =
                (\x. (U:real^2->real^K) x +
                     (\x. if x IN ball(c,r) then (w:real^2->real^K) x - U x else vec 0) x)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v"; "R"] THEN REWRITE_TAC[FUN_EQ_THM; GSYM cm_capmap] THEN
    X_GEN_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN REWRITE_TAC[wan_rext] THEN
    SUBGOAL_THEN `(\z:real^3. (v:real^3->real^K)(inv(norm z) % z)) =
                  v o (\z. inv(norm z) % z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[SMT_NORMALIZE_SPHERE]];
    MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN
    SUBGOAL_THEN
     `(\x. (U:real^2->real^K) x +
           (\x. if x IN ball(c,r) then (w:real^2->real^K) x - U x else vec 0) x) =
      (\x. (v:real^3->real^K)(stereo2_n_inv x))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["v"; "R"] THEN REWRITE_TAC[FUN_EQ_THM; GSYM cm_capmap] THEN
      X_GEN_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[VECTOR_ADD_RID] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. (v:real^3->real^K)(stereo2_n_inv x)) = v o stereo2_n_inv`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; STEX_STEREO2_N_INV_SMOOTH] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    MP_TAC(SPEC `mat 1:real^3^3` CMR_CAPMAP_FACTS) THEN
    REWRITE_TAC[ORTHOGONAL_MATRIX_ID; cm_capmap; MATRIX_VECTOR_MUL_LID] THEN SIMP_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `Q:real^3^3`] CMR_CHART_W12LOC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^2->real^K` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`ball(c:real^2,r)`; `\x. (w:real^2->real^K) x - U x`] WAN_W120_ZERO_EXT) THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXISTS_TAC `\x. (a:real^2->real^K) x +
                    (\x. if x IN ball(c,r)
                         then wan_wd (ball(c,r)) i (\x. (w:real^2->real^K) x - U x) x
                         else vec 0) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC WAN_SOB_LSPACE_ZERO_EXT THEN EXISTS_TAC `ball(c:real^2,r)` THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      MP_TAC(ISPECL [`ball(c:real^2,r)`;
                     `\x. if x IN ball(c,r)
                          then wan_wd (ball(c,r)) i (\x. (w:real^2->real^K) x - U x) x
                          else vec 0`;
                     `wan_wd (ball(c,r)) i (\x. (w:real^2->real^K) x - U x)`; `&2`]
                    CMT_LSPACE_EQ) THEN
      SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      MP_TAC(ISPECL [`ball(c:real^2,r)`; `i:num`; `\x. (w:real^2->real^K) x - U x`]
                    WAN_WD_WORKS) THEN
      ASM_REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
       [ASM_MESON_TAC[wan_w120]; SIMP_TAC[]];
      MATCH_MP_TAC WAN_WPD_ADD THEN ASM_REWRITE_TAC[ETA_AX]]]);;


(* ========================================================================= *)
(* The energy of a one-cap replacement.                                      *)
(* ========================================================================= *)

let CMR_REP1_SEN = prove
 (`!S (G:real^K->real^K^K) e (Q:real^3^3) (c:real^2) r (u:real^3->real^K) Lam.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cm_sen G (cmr_rep1 S G Q c r u) =
         cm_sen G u -
         (cm_gen G (ball(c,r)) (\x. u(cm_capmap Q x)) -
          cm_gen G (ball(c,r)) (cmr_minw S G c r (\x. u(cm_capmap Q x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`] CMR_REP1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K) /\
                wan_s2_w12 (cmr_rep1 S G Q c r (u:real^3->real^K))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `cmr_rep1 S G Q c r (u:real^3->real^K)`;
                 `Q:real^3^3`; `Lam:real`; `c:real^2`; `r:real`] CMR_SEN_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`;
                 `Q:real^3^3`; `Lam:real`; `c:real^2`; `r:real`] CMR_SEN_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `wan_gdir (ball(c,r)) G (\y. cmr_rep1 S G Q c r (u:real^3->real^K) (cm_capmap Q y)) =
    wan_gdir (ball(c,r)) G (cmr_minw S G c r (\x. u(cm_capmap Q x))) /\
    wan_gdir ((:real^2) DIFF cball(c,r)) G
      (\y. cmr_rep1 S G Q c r (u:real^3->real^K) (cm_capmap Q y)) =
    wan_gdir ((:real^2) DIFF cball(c,r)) G (\y. u(cm_capmap Q y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th)))) THEN
    REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cm_gen] THEN
  ABBREV_TAC `U = \x. (u:real^3->real^K)(cm_capmap (Q:real^3^3) x)` THEN REAL_ARITH_TAC);;

let CMR_REP1_SEN_LE = prove
 (`!S (G:real^K->real^K^K) e (Q:real^3^3) (c:real^2) r (u:real^3->real^K) Lam.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cm_gen G (ball(c,r)) (cmr_minw S G c r (\x. u(cm_capmap Q x))) <=
         cm_gen G (ball(c,r)) (\x. u(cm_capmap Q x)) /\
         cm_sen G (cmr_rep1 S G Q c r u) <= cm_sen G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ (a <= b ==> c = d - (b - a)) ==> a <= b /\ c <= d`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC CMR_REP1_SEN THEN EXISTS_TAC `e:real` THEN
    EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `U = \x. (u:real^3->real^K)(cm_capmap (Q:real^3^3) x)` THEN
  SUBGOAL_THEN `cm_cmap S (ball(c,r)) (U:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `U:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cm_minimizer S G (ball(c,r)) (cmr_minw S G c r (U:real^2->real^K))` THEN
  REWRITE_TAC[cm_minimizer] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [UNDISCH_TAC `cm_cmap S (ball(c,r)) (U:real^2->real^K)` THEN
    ASM_SIMP_TAC[cm_cmap; cm_wmap; CLOSURE_BALL] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^2) IN ball(c,r)` THEN REWRITE_TAC[IN_BALL; IN_CBALL] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`ball(c:real^2,r)`;
                   `\x. cmr_minw S G c r (U:real^2->real^K) x - U x`] WAN_W120_NEG) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    VECTOR_ARITH_TAC]);;


(* ========================================================================= *)
(* Successive replacement on caps 1..n; for pairwise disjoint                *)
(* closed caps it is the replacement on the whole family (each disc sees   *)
(* the data of u), with the additive energy formula.  Caps of radius <= 0  *)
(* are empty and do nothing.                                                 *)
(* ========================================================================= *)

let cmr_repn = define
 `(cmr_repn (S:real^K->bool) (G:real^K->real^K^K) 0 (Q:num->real^3^3) (c:num->real^2)
            (r:num->real) (u:real^3->real^K) = u) /\
  (cmr_repn S G (SUC n) Q c r u =
   cmr_rep1 S G (Q(SUC n)) (c(SUC n)) (r(SUC n)) (cmr_repn S G n Q c r u))`;;

let CMR_REP1_NONPOS = prove
 (`!S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     r <= &0 ==> cmr_rep1 S G Q c r u = u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; cmr_rep1] THEN
  ASM_SIMP_TAC[BALL_EMPTY; IMAGE_CLAUSES; NOT_IN_EMPTY]);;

let CMR_MINW_CONG = prove
 (`!S (G:real^K->real^K^K) (c:real^2) r (f:real^2->real^K) f'.
     (!x. x IN cball(c,r) ==> f x = f' x)
     ==> cmr_minw S G c r f = cmr_minw S G c r f'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_minw] THEN AP_TERM_TAC THEN ABS_TAC THEN
  SUBGOAL_THEN
   `wan_w120 (ball(c,r)) (\x. (w:real^2->real^K) x - f x) <=>
    wan_w120 (ball(c,r)) (\x. w x - (f':real^2->real^K) x)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `negligible {x | x IN ball(c,r) /\
                      ~((\x. (w:real^2->real^K) x - f x) x = (\x. w x - (f':real^2->real^K) x) x)} /\
      negligible {x | x IN ball(c,r) /\
                      ~((\x. (w:real^2->real^K) x - f' x) x = (\x. w x - (f:real^2->real^K) x) x)}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{}:real^2->bool` THEN
      REWRITE_TAC[NEGLIGIBLE_EMPTY; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^2` THEN BETA_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^2->real^K) x = f' x` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
      ALL_TAC] THEN
    EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HMD_W120_AE THENL
     [EXISTS_TAC `\x. (w:real^2->real^K) x - f x`;
      EXISTS_TAC `\x. (w:real^2->real^K) x - f' x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(c,r) ==> (f:real^2->real^K) x = f' x` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; SPHERE_SUBSET_CBALL]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let CMR_REPN_FACTS = prove
 (`!S (G:real^K->real^K^K) e Lam n (Q:num->real^3^3) (c:num->real^2) (r:num->real)
    (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\
     (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k)) /\
     (!k l. 1 <= k /\ k < l /\ l <= n /\ &0 < r k /\ &0 < r l
            ==> DISJOINT (IMAGE (cm_capmap (Q k)) (cball(c k,r k)))
                         (IMAGE (cm_capmap (Q l)) (cball(c l,r l)))) /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e)
     ==> !m. m <= n
             ==> cm_smap S (cmr_repn S G m Q c r u) /\
                 (!k y. m < k /\ k <= n /\ &0 < r k /\
                        y IN IMAGE (cm_capmap (Q k)) (cball(c k,r k))
                        ==> cmr_repn S G m Q c r u y = u y) /\
                 (!y. (!k. 1 <= k /\ k <= m
                           ==> ~(y IN IMAGE (cm_capmap (Q k)) (ball(c k,r k))))
                      ==> cmr_repn S G m Q c r u y = u y) /\
                 (!k x. 1 <= k /\ k <= m /\ &0 < r k /\ x IN ball(c k,r k)
                        ==> cmr_repn S G m Q c r u (cm_capmap (Q k) x) =
                            cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x)) x) /\
                 cm_sen G (cmr_repn S G m Q c r u) =
                 cm_sen G u -
                 sum(1..m) (\k. if &0 < r k
                                then cm_gen G (ball(c k,r k)) (\x. u(cm_capmap (Q k) x)) -
                                     cm_gen G (ball(c k,r k))
                                       (cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x)))
                                else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[cmr_repn; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `v = cmr_repn S G m (Q:num->real^3^3) (c:num->real^2) (r:num->real)
                           (u:real^3->real^K)` THEN
  STRIP_TAC THEN
  REWRITE_TAC[cmr_repn] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
  ASM_CASES_TAC `&0 < (r:num->real)(SUC m)` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < x) ==> x <= &0`; REAL_ADD_RID] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th))) THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `~(k = SUC m)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cmr_minw")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]] THEN
  (* the case 0 < r (SUC m) *)
  SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) (SUC m))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN cball((c:num->real^2) (SUC m),(r:num->real) (SUC m))
        ==> (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) (SUC m)) x) = u(cm_capmap (Q (SUC m)) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
    EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ARITH_TAC; REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_minw S G ((c:num->real^2) (SUC m)) ((r:num->real) (SUC m))
      (\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) (SUC m)) x)) =
    cmr_minw S G (c (SUC m)) (r (SUC m)) (\x. (u:real^3->real^K)(cm_capmap (Q (SUC m)) x))`
  ASSUME_TAC THENL [MATCH_MP_TAC CMR_MINW_CONG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_gdir (ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))) G
      (\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) (SUC m)) x)) =
    wan_gdir (ball(c (SUC m),r (SUC m))) G (\x. (u:real^3->real^K)(cm_capmap (Q (SUC m)) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_gdir (ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))) G
      (\x. (v:real^3->real^K)(cm_capmap ((Q:num->real^3^3) (SUC m)) x)) <= e`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC m`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(Q:num->real^3^3) (SUC m)`;
                 `(c:num->real^2) (SUC m)`; `(r:num->real) (SUC m)`; `v:real^3->real^K`]
                CMR_REP1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(Q:num->real^3^3) (SUC m)`;
                 `(c:num->real^2) (SUC m)`; `(r:num->real) (SUC m)`; `v:real^3->real^K`; `Lam:real`]
                CMR_REP1_SEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (cm_capmap ((Q:num->real^3^3) (SUC m))) (ball((c:num->real^2) (SUC m),(r:num->real) (SUC m)))
        ==> !k. 1 <= k /\ k <= m /\ &0 < r k
                ==> ~(y IN IMAGE (cm_capmap (Q k)) (cball(c k,r k)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `SUC m`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (cm_capmap ((Q:num->real^3^3) (SUC m))) (ball(c (SUC m),r (SUC m)))` THEN
    MP_TAC(ISPECL [`cm_capmap ((Q:num->real^3^3) (SUC m))`; `ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))`;
                   `cball((c:num->real^2) (SUC m),(r:num->real) (SUC m))`] IMAGE_SUBSET) THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* later closed caps are untouched *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN IMAGE (cm_capmap ((Q:num->real^3^3) (SUC m)))
                                  (ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))))`
    ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`SUC m`; `k:num`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN IMAGE (cm_capmap ((Q:num->real^3^3) (SUC m))) (ball(c (SUC m),r (SUC m)))` THEN
      MP_TAC(ISPECL [`cm_capmap ((Q:num->real^3^3) (SUC m))`; `ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))`;
                     `cball((c:num->real^2) (SUC m),(r:num->real) (SUC m))`] IMAGE_SUBSET) THEN
      REWRITE_TAC[BALL_SUBSET_CBALL] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    (* points outside all open caps 1..(SUC m) are untouched *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN IMAGE (cm_capmap ((Q:num->real^3^3) (SUC m)))
                                  (ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= SUC m`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    (* the discs: (SUC m) itself and the earlier ones *)
    MAP_EVERY X_GEN_TAC [`k:num`; `x:real^2`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `k:num = (SUC m)` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num <= m` ASSUME_TAC THENL
     [UNDISCH_TAC `k <= SUC m` THEN UNDISCH_TAC `~(k:num = SUC m)` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(cm_capmap ((Q:num->real^3^3) k) x IN
                    IMAGE (cm_capmap (Q (SUC m))) (ball((c:num->real^2) (SUC m),(r:num->real) (SUC m))))`
    ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `cm_capmap ((Q:num->real^3^3) k) x` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `SUC m`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN
      ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    (* the energy *)
    REWRITE_TAC[cm_gen] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

