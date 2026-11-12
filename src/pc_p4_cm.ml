(* ========================================================================= *)
(* Unit pc_p4_cm: the Colding-Minicozzi level of Part 4: the sweepout width  *)
(* is a width system with c = 4 pi given the CM0 statements                  *)
(* (P4_CM_WIDTH_SYSTEM), the combinations P4_FINITE_EXTINCTION_CM and        *)
(* P4_RFS_EXTINCTION_CM, the Dini comparison and the slab inequality from CM *)
(* Thm 1.7 in forward-difference form (P4_CM_SLAB_FROM_DINI), CM Thm 1.7     *)
(* from the level CM1 statements (P4_CM_DINI_FROM_C1), and                   *)
(* P4_FINITE_EXTINCTION_CM1, P4_RFS_EXTINCTION_CM1.                          *)
(* ========================================================================= *)

needs "src/pc_p4_top.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The CM width: nonnegativity, comparison with one sweepout, transport      *)
(* by pinch maps, and the width-system theorem.                              *)
(* ------------------------------------------------------------------------- *)

let P4_SWEEP_AREA_NONNEG = prove
 (`!top atlas (g:A->real^3^3) sigma.
        P4_CM_NONNEG_STATEMENT (:A) /\
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g /\ p4_sweepout (top,atlas) sigma
        ==> &0 <= p4_sweep_area atlas g sigma`,
  REWRITE_TAC[P4_CM_NONNEG_STATEMENT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                `g:A->real^3^3`; `sigma:real^3->real->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `B:real`)) THEN
  REWRITE_TAC[p4_sweep_area] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_s2_area atlas (g:A->real^3^3) (\y. (sigma:real^3->real->A) y (&0))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]]);;

let P4_CM_WIDTH_NONNEG = prove
 (`!top atlas (g:A->real^3^3) U.
        P4_CM_NONNEG_STATEMENT (:A) /\
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g /\ p4_cm_adm (top,atlas) U
        ==> &0 <= p4_cm_width (top,atlas) g U`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_cm_width] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[p4_cm_adm]) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC; p4_sweepout_in] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P4_SWEEP_AREA_NONNEG THEN ASM_MESON_TAC[]]);;

let P4_CM_WIDTH_LE = prove
 (`!top atlas (g:A->real^3^3) U sigma.
        P4_CM_NONNEG_STATEMENT (:A) /\
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g /\
        p4_sweepout_in (top,atlas) U sigma
        ==> p4_cm_width (top,atlas) g U <= p4_sweep_area atlas g sigma`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_cm_width] THEN
  MATCH_MP_TAC REAL_INF_LE THEN
  EXISTS_TAC `&0` THEN
  EXISTS_TAC `p4_sweep_area atlas (g:A->real^3^3) sigma` THEN
  REWRITE_TAC[REAL_LE_REFL; FORALL_IN_GSPEC; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[p4_sweepout_in] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P4_SWEEP_AREA_NONNEG THEN ASM_MESON_TAC[]]);;

let P4_CM_TRANSPORT_SWEEPOUT = prove
 (`!topX atlasX (gX:B->real^3^3) X topY atlasY (gY:B->real^3^3) Y L p sigma.
        P4_DEGREE_ONE_STATEMENT (:B) (:B) /\ P4_PINCH_AREA_STATEMENT (:B) (:B) /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((B->bool)#(B->real^3))->bool) /\
        compact_space topX /\ mfd_orientable topX atlasX /\ riemannian_metric atlasX gX /\
        hausdorff_space topY /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        compact_space topY /\ mfd_orientable topY atlasY /\ riemannian_metric atlasY gY /\
        X IN connected_components_of topX /\ Y IN connected_components_of topY /\
        &1 <= L /\ p4_pinch_map (topX,atlasX) gX X (topY,atlasY) gY Y L p /\
        p4_sweepout_in (topX,atlasX) X sigma
        ==> p4_sweepout_in (topY,atlasY) Y (\y t. p(sigma y t)) /\
            p4_sweep_area atlasY gY (\y t. p(sigma y t))
            <= L pow 2 * p4_sweep_area atlasX gX sigma`,
  REWRITE_TAC[P4_DEGREE_ONE_STATEMENT; P4_PINCH_AREA_STATEMENT; p4_sweepout_in] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "deg") (CONJUNCTS_THEN2 (LABEL_TAC "pin")
    STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "pin" (MP_TAC o SPECL
   [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`; `gX:B->real^3^3`;
    `X:B->bool`; `topY:B topology`; `atlasY:((B->bool)#(B->real^3))->bool`;
    `gY:B->real^3^3`; `Y:B->bool`; `L:real`; `p:B->B`; `sigma:real^3->real->B`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[P4_SUSP_COMPOSE] THEN
  REMOVE_THEN "deg" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`topX:B topology`; `atlasX:((B->bool)#(B->real^3))->bool`;
                        `X:B->bool`; `atlasY:((B->bool)#(B->real^3))->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p4_pinch_map]) THEN
  SIMP_TAC[]);;

let P4_CM_TRANSPORT = prove
 (`!topX atlasX (gX:B->real^3^3) X topY atlasY (gY:B->real^3^3) Y L p.
        P4_DEGREE_ONE_STATEMENT (:B) (:B) /\ P4_PINCH_AREA_STATEMENT (:B) (:B) /\
        P4_CM_NONNEG_STATEMENT (:B) /\
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((B->bool)#(B->real^3))->bool) /\
        compact_space topX /\ mfd_orientable topX atlasX /\ riemannian_metric atlasX gX /\
        hausdorff_space topY /\
        smooth_manifold_atlas topY (atlasY:((B->bool)#(B->real^3))->bool) /\
        compact_space topY /\ mfd_orientable topY atlasY /\ riemannian_metric atlasY gY /\
        X IN connected_components_of topX /\ Y IN connected_components_of topY /\
        &1 <= L /\ p4_pinch_map (topX,atlasX) gX X (topY,atlasY) gY Y L p /\
        p4_cm_adm (topX,atlasX) X
        ==> p4_cm_adm (topY,atlasY) Y /\
            p4_cm_width (topY,atlasY) gY Y <= L pow 2 * p4_cm_width (topX,atlasX) gX X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!sigma. p4_sweepout_in (topX,atlasX) X sigma
            ==> p4_sweepout_in (topY,atlasY) Y (\y t. (p:B->B)(sigma y t)) /\
                p4_sweep_area atlasY (gY:B->real^3^3) (\y t. p(sigma y t))
                <= L pow 2 * p4_sweep_area atlasX (gX:B->real^3^3) sigma`
  (LABEL_TAC "tr") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P4_CM_TRANSPORT_SWEEPOUT THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `sigma0:real^3->real->B` o REWRITE_RULE[p4_cm_adm]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p4_cm_adm] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `p4_cm_width (topY,atlasY) (gY:B->real^3^3) Y / L pow 2 <=
    p4_cm_width (topX,atlasX) (gX:B->real^3^3) X`
  MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [p4_cm_width] THEN
    MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `sigma:real^3->real->B` THEN
      DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p4_sweep_area atlasY (gY:B->real^3^3) (\y t. (p:B->B)(sigma y t))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P4_CM_WIDTH_LE THEN ASM_MESON_TAC[];
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_MESON_TAC[]]];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let P4_CM_WIDTH_SYSTEM = prove
 (`CM_SLAB_STATEMENT (:B) /\ P4_DEGREE_ONE_STATEMENT (:B) (:B) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_AREA_STATEMENT (:B) (:B) /\ P4_CM_NONNEG_STATEMENT (:B) /\
   P4_CM_ISOMETRY_STATEMENT (:A) (:B)
   ==> p4_width_system
         ((p4_cm_width:(A topology#(((A->bool)#(A->real^3))->bool))->
                       (A->real^3^3)->(A->bool)->real),p4_cm_adm)
         ((p4_cm_width:(B topology#(((B->bool)#(B->real^3))->bool))->
                       (B->real^3^3)->(B->bool)->real),p4_cm_adm)
         (&4 * pi)`,
  STRIP_TAC THEN REWRITE_TAC[p4_width_system] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_CM_WIDTH_NONNEG THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `CM_SLAB_STATEMENT (:B)` THEN REWRITE_TAC[CM_SLAB_STATEMENT];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P4_CM_TRANSPORT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `P4_SC_DEGREE_ONE_STATEMENT (:A)` THEN
    REWRITE_TAC[P4_SC_DEGREE_ONE_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `f:real^4->A`) THEN
    UNDISCH_TAC `P4_SMOOTHING_STATEMENT (:A)` THEN
    REWRITE_TAC[P4_SMOOTHING_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `f:real^4->A` THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN
    SUBGOAL_THEN `connected_space (top:A topology)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE;
                    PATH_CONNECTED_IMP_CONNECTED_SPACE];
      ASM_SIMP_TAC[CONNECTED_COMPONENTS_OF_CONNECTED_SPACE; IN_SING]];
    UNDISCH_TAC `P4_CM_ISOMETRY_STATEMENT (:A) (:B)` THEN
    REWRITE_TAC[P4_CM_ISOMETRY_STATEMENT]]);;


let P4_FINITE_EXTINCTION_CM = prove
 (`CM_SLAB_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_AREA_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_CM_NONNEG_STATEMENT (:A+num#num#real^3) /\
   P4_CM_ISOMETRY_STATEMENT (:A) (:A+num#num#real^3)
   ==> FINITE_EXTINCTION_STATEMENT (:A)`,
  DISCH_THEN(MP_TAC o MATCH_MP (INST_TYPE [`:A+num#num#real^3`,`:B`] P4_CM_WIDTH_SYSTEM)) THEN
  MATCH_ACCEPT_TAC P4_FINITE_EXTINCTION_FROM_WIDTH);;

let P4_RFS_EXTINCTION_CM = prove
 (`RFS_CONTINUATION_STATEMENT (:A) /\
   CM_SLAB_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_AREA_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_CM_NONNEG_STATEMENT (:A+num#num#real^3) /\
   P4_CM_ISOMETRY_STATEMENT (:A) (:A+num#num#real^3)
   ==> RFS_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_RFS_EXTINCTION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_FINITE_EXTINCTION_CM THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Dini comparison and the CM slab inequality from CM Thm 1.7 in             *)
(* forward-difference form: P4_DINI_MONO (a continuous function with         *)
(* nonpositive upper right Dini derivative is non-increasing; HOL Light has  *)
(* no Dini derivatives), convexity of (4t+1)^(-3/4) and concavity of         *)
(* (4t+1)^(1/4) in the forms needed, the one-step bound P4_Q_DINI_STEP, and  *)
(* P4_CM_SLAB_FROM_DINI.                                                     *)
(* ------------------------------------------------------------------------- *)

let P4_DINI_MONO = prove
 (`!f a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!t. a <= t /\ t < b
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             !h. &0 < h /\ h < d /\ t + h <= b
                                 ==> f(t + h) <= f t + e * h)
        ==> f b <= f a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cont")
    (LABEL_TAC "dini"))) THEN
  SUBGOAL_THEN `!e. &0 < e ==> (f:real->real) b <= f a + e * (b - a) + e`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P4_REAL_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (b - a + &1)`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y = e ==> x <= f + y ==> x <= f + e`) THEN
    REWRITE_TAC[REAL_ARITH `x * y + x = x * (y + &1)`] THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `S = {t | t IN real_interval[a,b] /\
                       (f:real->real) a + e * (t - a) + e < f t}` THEN
  SUBGOAL_THEN `(b:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN S <=> a <= t /\ t <= b /\
                               (f:real->real) a + e * (t - a) + e < f t`
  (LABEL_TAC "Sdef") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `s = inf S` THEN
  SUBGOAL_THEN `!t. t IN S ==> s <= t` (LABEL_TAC "infle") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `t:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (!t. t IN S ==> y <= t) ==> y <= s` (LABEL_TAC "infge") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN MATCH_MP_TAC REAL_LE_INF THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a <= s /\ s <= b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "infge" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "infle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s IN real_interval[a,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) a + e * (s - a) + e <= f s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `q = (f:real->real) a + e * (s - a) + e - f s` THEN
    SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < q / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "cont" (MP_TAC o C MP (ASSUME `&0 < q / &2`) o SPEC `q / &2` o
      C MP (ASSUME `s IN real_interval[a,b]`) o SPEC `s:real` o
      REWRITE_RULE[real_continuous_on]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `m = min d (q / (&2 * e))` THEN
    SUBGOAL_THEN `&0 < m /\ m <= d /\ e * m <= q / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * q / (&2 * e)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?t. t IN S /\ t < s + m` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE
        [NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT]) THEN
      SUBGOAL_THEN `s + m <= s` MP_TAC THENL
       [USE_THEN "infge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `s <= t /\ a <= t /\ t <= b /\ (f:real->real) a + e * (t - a) + e < f t`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term (fun u -> u = `abs(x' - s) < d`)) (concl th))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= e * (t - s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < s` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) s <= f a + e * (s - a) + e` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC `q = (f:real->real) s - (f a + e * (s - a) + e)` THEN
    SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < q / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "cont" (MP_TAC o C MP (ASSUME `&0 < q / &2`) o SPEC `q / &2` o
      C MP (ASSUME `s IN real_interval[a,b]`) o SPEC `s:real` o
      REWRITE_RULE[real_continuous_on]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `m = min d (q / (&2 * e))` THEN
    SUBGOAL_THEN `&0 < m /\ m <= d /\ e * m <= q / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * q / (&2 * e)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    ABBREV_TAC `t = max a (s - m / &2)` THEN
    SUBGOAL_THEN `a <= t /\ t < s /\ t <= b /\ abs(t - s) < d /\ s - t <= m`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(t:real) IN S` ASSUME_TAC THENL
     [USE_THEN "Sdef" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        can (find_term (fun u -> u = `abs(x' - s) < d`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      SUBGOAL_THEN `&0 <= e * (s - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "infle" (MP_TAC o C MP (ASSUME `(t:real) IN S`) o SPEC `t:real`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s < b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "dini" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
    C MP (CONJ (ASSUME `a <= s`) (ASSUME `s < b`)) o SPEC `s:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s + d <= s` MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  USE_THEN "infge" MATCH_MP_TAC THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s <= t /\ a <= t /\ t <= b /\ (f:real->real) a + e * (t - a) + e < f t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `t:real = s` THENL
   [UNDISCH_TAC `(f:real->real) a + e * (t - a) + e < f t` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - s`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `s + (t - s) = t`] THEN ASM_REAL_ARITH_TAC);;

(* The Dini condition is only needed at interior times, the left end point *)
(* being handled by continuity.                                              *)

let P4_DINI_MONO_OPEN = prove
 (`!f a b.
        a <= b /\ f real_continuous_on real_interval[a,b] /\
        (!t. a < t /\ t < b
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             !h. &0 < h /\ h < d /\ t + h <= b
                                 ==> f(t + h) <= f t + e * h)
        ==> f b <= f a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cont")
    (LABEL_TAC "dini"))) THEN
  ASM_CASES_TAC `a:real = b` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!c. a < c /\ c <= b ==> (f:real->real) b <= f c` (LABEL_TAC "right")
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_DINI_MONO THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "dini" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  USE_THEN "cont" (MP_TAC o SPEC `a:real` o REWRITE_RULE[real_continuous_on]) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) b - f a`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `c = a + min d (b - a) / &2` THEN
  SUBGOAL_THEN `a < c /\ c <= b /\ abs(c - a) < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) b <= f c` ASSUME_TAC THENL
   [USE_THEN "right" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `d:real`)) (concl th))) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

let P4_A_CONVEX = prove
 (`!t h. &0 <= t /\ &0 <= h
         ==> inv((&4 * (t + h) + &1) rpow (&3 / &4))
             <= inv((&4 * t + &1) rpow (&3 / &4)) *
                (&1 - &3 * h / (&4 * t + &1) + &21 * h pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `X = &4 * t + &1` THEN
  SUBGOAL_THEN `&4 * (t + h) + &1 = X + &4 * h` SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Y = X + &4 * h` THEN
  SUBGOAL_THEN `&1 <= X /\ X <= Y /\ &0 < X /\ &0 < Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Y"; "X"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real. x rpow (--(&3 / &4))`;
                 `--(&3 / &4) * Y rpow (--(&3 / &4) - &1)`;
                 `{x:real | &0 < x}`; `Y:real`; `X:real`]
                REAL_CONVEX_ON_DERIVATIVE_SECANT_IMP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONVEX_ON_RPOW_NEG THEN REWRITE_TAC[SUBSET_REFL] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_REAL_SEGMENT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_RPOW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[RPOW_NEG] THEN
  SUBGOAL_THEN `Y rpow (--(&3 / &4) - &1) = inv(Y rpow (&3 / &4)) * inv Y`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `--(&3 / &4) - &1 = --(&3 / &4) + --(&1)`] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_NEG; RPOW_POW; REAL_POW_1]; ALL_TAC] THEN
  ABBREV_TAC `fX = inv(X rpow (&3 / &4))` THEN
  ABBREV_TAC `fY = inv(Y rpow (&3 / &4))` THEN
  SUBGOAL_THEN `&0 < fX /\ &0 < fY` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fX"; "fY"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC RPOW_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X - Y = --(&4 * h)` SUBST1_TAC THENL
   [EXPAND_TAC "Y" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `fY * (Y + &3 * h) <= fX * Y` ASSUME_TAC THENL
   [SUBGOAL_THEN `fY * (Y + &3 * h) = (fY + &3 * h * (fY * inv Y)) * Y` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `Y <= (&1 - &3 * h / X + &21 * h pow 2) * (Y + &3 * h)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 - &3 * h / X + &21 * h pow 2) * (Y + &3 * h) - Y =
                  (&21 * h pow 2 * (X - &1) * (X + &1) + &147 * h pow 3 * X) / X`
    MP_TAC THENL
     [EXPAND_TAC "Y" THEN UNDISCH_TAC `&0 < X` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&21 * h pow 2 * (X - &1) * (X + &1) + &147 * h pow 3 * X) / X`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `fY * (Y + &3 * h) <= (fX * (&1 - &3 * h / X + &21 * h pow 2)) * (Y + &3 * h)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `fX * Y` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_ARITH `&0 < Y /\ &0 <= h ==> &0 < Y + &3 * h`]);;

let P4_B_CONCAVE = prove
 (`!t h. &0 <= t /\ &0 <= h
         ==> (&4 * (t + h) + &1) rpow (&1 / &4)
             <= (&4 * t + &1) rpow (&1 / &4) + h * inv((&4 * t + &1) rpow (&3 / &4))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = (&4 * t + &1) rpow (&1 / &4)` THEN
  ABBREV_TAC `v = (&4 * (t + h) + &1) rpow (&1 / &4)` THEN
  SUBGOAL_THEN `(&4 * t + &1) rpow (&3 / &4) = u pow 3` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[GSYM RPOW_POW] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RPOW_RPOW o rand o snd) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= u /\ u <= v` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P4_B_GE_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `u pow 4 = &4 * t + &1 /\ v pow 4 = &4 * (t + h) + &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN CONJ_TAC THEN
    MATCH_MP_TAC P4_RPOW_QUARTER_POW THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v - u) * (&4 * u pow 3) <= &4 * h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(v - u) * ((u + v) * (u pow 2 + v pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&4 * u pow 3 = (&2 * u) * (&2 * u pow 2)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `u pow 2 <= v pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      SUBGOAL_THEN `(v - u) * ((u + v) * (u pow 2 + v pow 2)) = v pow 4 - u pow 4`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `v - u <= h * inv(u pow 3)` MP_TAC THENL
   [REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P4_MUL_LE_MAX = prove
 (`!a x. &0 <= a /\ a <= &1 ==> a * x <= max x (&0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= x` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * x <= &0 <=> &0 <= a * --x`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let P4_Q_DINI_STEP = prove
 (`!c w wn t h e.
        &0 < c /\ &0 <= w /\ &0 <= t /\ &0 < h /\ h <= &1 /\ &0 <= e /\ e <= &1 /\
        &0 <= wn /\ wn <= w + h * (--c + &3 / (&4 * t + &1) * w + e)
        ==> p4_q c wn (t + h)
            <= p4_q c w t + h * e + h pow 2 * (&84 * w + &3 * c + &21)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. p4_q c x y = x * inv((&4 * y + &1) rpow (&3 / &4)) +
                                   c * (&4 * y + &1) rpow (&1 / &4)`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[p4_q; real_div]; ALL_TAC] THEN
  MP_TAC(SPECL [`t:real`; `h:real`] P4_A_CONVEX) THEN
  MP_TAC(SPECL [`t:real`; `h:real`] P4_B_CONCAVE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ABBREV_TAC `a = inv((&4 * t + &1) rpow (&3 / &4))` THEN
  ABBREV_TAC `a1 = inv((&4 * (t + h) + &1) rpow (&3 / &4))` THEN
  ABBREV_TAC `B = (&4 * t + &1) rpow (&1 / &4)` THEN
  ABBREV_TAC `B1 = (&4 * (t + h) + &1) rpow (&1 / &4)` THEN
  ABBREV_TAC `u = inv(&4 * t + &1)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < u /\ u <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a /\ a <= &1 /\ &0 <= a1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "a1"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC RPOW_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * h / (&4 * t + &1) = &3 * h * u /\
                &3 / (&4 * t + &1) * w = &3 * u * w`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `P = &1 - &3 * h * u + &21 * h pow 2` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    SUBGOAL_THEN `h * u <= h` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `h * u <= h * &1 ==> h * u <= h`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `h - &1 / &14` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wn * a1 <= (w + h * (--c + &3 * u * w + e)) * (a * P)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `wn * (a * P)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_MUL_SYM];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w + h * (--c + &3 * u * w + e)) * (a * P) + c * (B + h * a) =
    w * a + c * B + a * (h * e) +
    a * (h pow 2 * (&21 * w + &3 * c * u - &9 * w * u pow 2 - &3 * e * u)) +
    a * (h pow 2 * (h * (--(&21) * c + &63 * w * u + &21 * e)))`
  ASSUME_TAC THENL [EXPAND_TAC "P" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a * (h * e) <= h * e` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a * x <= &1 * x ==> a * x <= x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `a * (h pow 2 * (&21 * w + &3 * c * u - &9 * w * u pow 2 - &3 * e * u))
    <= h pow 2 * (&21 * w + &3 * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max (h pow 2 * (&21 * w + &3 * c * u - &9 * w * u pow 2 - &3 * e * u)) (&0)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC P4_MUL_LE_MAX THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MAX_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      SUBGOAL_THEN `c * u <= c /\ &0 <= w * u pow 2 /\ &0 <= e * u` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `c * u <= c * &1 ==> c * u <= c`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a * (h pow 2 * (h * (--(&21) * c + &63 * w * u + &21 * e)))
    <= h pow 2 * (&63 * w + &21)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `max (h pow 2 * (h * (--(&21) * c + &63 * w * u + &21 * e))) (&0)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC P4_MUL_LE_MAX THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MAX_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `max (--(&21) * c + &63 * w * u + &21 * e) (&0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P4_MUL_LE_MAX THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MAX_LE] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `w * u <= w` MP_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `w * u <= w * &1 ==> w * u <= w`) THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * B1 <= c * (B + h * a)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P4_AFFINE_RPOW_CONTINUOUS = prove
 (`!r s. &0 <= r ==> (\t. (&4 * t + &1) rpow r) real_continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. (&4 * t + &1) rpow r) = (\x. x rpow r) o (\t. &4 * t + &1)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REWRITE_TAC[]]);;

let P4_CM_SLAB_FROM_DINI = prove
 (`CM_DINI_STATEMENT (:A) /\ P4_WIDTH_CONTINUITY_STATEMENT (:A) /\
   P4_CM_NONNEG_STATEMENT (:A)
   ==> CM_SLAB_STATEMENT (:A)`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dini")
    (CONJUNCTS_THEN2 (LABEL_TAC "cont") (LABEL_TAC "nonneg"))) THEN
  REWRITE_TAC[CM_SLAB_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:real->A->real^3^3`; `a:real`; `b:real`; `t0:real`; `t1:real`;
                       `U:A->bool`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `W = \t. p4_cm_width (top,atlas) ((g:real->A->real^3^3) t) U` THEN
  SUBGOAL_THEN `!t. p4_cm_width (top,atlas) ((g:real->A->real^3^3) t) U = W t`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b ==> &0 <= (W:real->real) t` (LABEL_TAC "Wpos") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "W" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P4_CM_WIDTH_NONNEG THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P4_RF_METRIC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. p4_q (&4 * pi) ((W:real->real) t) t`; `t0:real`; `t1:real`]
                P4_DINI_MONO_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p4_q] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_DIV THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `real_interval[a,t1]` THEN CONJ_TAC THENL
         [USE_THEN "cont" (MP_TAC o REWRITE_RULE[P4_WIDTH_CONTINUITY_STATEMENT]) THEN
          DISCH_THEN(MP_TAC o SPECL
           [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
            `g:real->A->real^3^3`; `a:real`; `b:real`; `t1:real`; `U:A->bool`]) THEN
          ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          EXPAND_TAC "W" THEN REWRITE_TAC[ETA_AX];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC P4_AFFINE_RPOW_CONTINUOUS THEN REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC RPOW_POS_LT THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC P4_AFFINE_RPOW_CONTINUOUS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "dini" (MP_TAC o REWRITE_RULE[CM_DINI_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:real->A->real^3^3`; `a:real`; `b:real`; `t:real`; `U:A->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p4_cm_width] THEN
  SUBGOAL_THEN `!s. inf {p4_sweep_area atlas ((g:real->A->real^3^3) s) sigma | sigma |
                        p4_sweepout_in (top,atlas) U sigma} = (W:real->real) s`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[p4_cm_width]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `min (e / &2) (&1)`) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K = &84 * (W:real->real) t + &3 * (&4 * pi) + &21` THEN
  SUBGOAL_THEN `&0 <= (W:real->real) t /\ &0 < K` STRIP_ASSUME_TAC THENL
   [USE_THEN "Wpos" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "K" THEN MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min d1 (min (&1) (e / (&2 * K)))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&4 * pi`; `(W:real->real) t`; `(W:real->real)(t + h)`; `t:real`;
                `h:real`; `min (e / &2) (&1)`] P4_Q_DINI_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [MP_TAC PI_POS THEN REAL_ARITH_TAC;
           ASM_REAL_ARITH_TAC;
           REWRITE_TAC[REAL_LE_MIN] THEN ASM_REAL_ARITH_TAC;
           REWRITE_TAC[REAL_MIN_LE] THEN REAL_ARITH_TAC;
           USE_THEN "Wpos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
           FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h pow 2 * K <= h * (e / &2)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / (&2 * K) * K` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < K` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * min (e / &2) (&1) <= h * (e / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* CM Thm 1.7 in forward-difference form from the level CM1 statements       *)
(* (CM's proof, pp. 7-8: the good sweepouts at time tau are competitors at  *)
(* time tau + h; slices of area > W - d are close to nonempty collections   *)
(* of harmonic spheres, which give the -4 pi through Lemma 1.22; the other  *)
(* slices stay below W - d/2; e' -> 0 before h), and the combinations down  *)
(* to level CM1.                                                             *)
(* ------------------------------------------------------------------------- *)

let P4_SUM_HARMONIC = prove
 (`!n (ar:num->real) (tr:num->real) c0.
        1 <= n /\ &0 <= c0 /\
        (!i. 1 <= i /\ i <= n ==> &4 * pi - c0 * ar i <= tr i)
        ==> &4 * pi - c0 * sum(1..n) ar <= sum(1..n) tr`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..n) (\i. &4 * pi - c0 * (ar:num->real) i)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_SUB_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - z <= y - z`) THEN
    REWRITE_TAC[REAL_ARITH `&4 * pi <= &((n + 1) - 1) * &4 * pi <=>
                            &1 * (&4 * pi) <= &((n + 1) - 1) * (&4 * pi)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MP_TAC PI_POS THEN REAL_ARITH_TAC];
    MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]]);;

let P4_SLICE_A = prove
 (`!h c0 C A An Tr W0 e' eps.
        &0 <= h /\ &0 <= c0 /\ &0 <= C /\ &0 <= A /\ &0 <= eps /\
        A <= W0 + e' /\
        An <= A - h * Tr + C * h pow 2 * A /\
        &4 * pi - c0 * (A + eps) - eps <= Tr
        ==> An <= (W0 + e') + h * (--(&4 * pi) + c0 * (W0 + e' + eps) + eps) +
                  C * h pow 2 * (W0 + e')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h * (&4 * pi - c0 * (A + eps) - eps) <= h * Tr` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `A * (&1 + h * c0 + C * h pow 2) <= (W0 + e') * (&1 + h * c0 + C * h pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= &1 + x + y`) THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P4_SLICE_B = prove
 (`!h c0 C A An Tr W0 delta e.
        &0 <= h /\ h <= &1 /\ &0 <= c0 /\ &0 <= C /\ &0 <= A /\ &0 <= W0 /\ &0 <= e /\
        A <= W0 - delta /\ abs Tr <= C * A /\
        An <= A - h * Tr + C * h pow 2 * A /\
        h * (&2 * C * W0 + &4 * pi + &1) <= delta
        ==> An <= W0 + h * (--(&4 * pi) + c0 * W0 + e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(h * Tr) <= h * (C * A)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `--(h * t) = h * --t`] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * h pow 2 * A <= h * (C * A)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_ARITH `C * (h * h) * A = h * (h * (C * A))`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `h * x <= &1 * x ==> h * x <= x`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= h * (&2 * C * W0 + &4 * pi + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= p ==> &0 <= &2 * x + &4 * p + &1`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MP_TAC PI_POS THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `h * (C * A) <= h * (C * W0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= h * (c0 * W0 + e)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P4_CM_DINI_FROM_C1 = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A) /\ CM_HARMONIC_SPHERE_STATEMENT (:A) /\
   P4_AREA_TAYLOR_STATEMENT (:A) /\ P4_CM_NONNEG_STATEMENT (:A)
   ==> CM_DINI_STATEMENT (:A)`,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "good") (CONJUNCTS_THEN2 (LABEL_TAC "harm")
    (CONJUNCTS_THEN2 (LABEL_TAC "tay") (LABEL_TAC "nonneg")))) THEN
  REWRITE_TAC[CM_DINI_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:real->A->real^3^3`; `a:real`; `b:real`; `tau:real`;
                       `U:A->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_RF_METRIC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W0 = p4_cm_width (top,atlas) ((g:real->A->real^3^3) tau) U` THEN
  ABBREV_TAC `c0 = &3 / (&4 * tau + &1)` THEN
  SUBGOAL_THEN `&0 <= c0 /\ --(&6) / (&4 * tau + &1) / &2 = --c0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < &4 * tau + &1` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]; ALL_TAC] THEN
  USE_THEN "tay" (MP_TAC o REWRITE_RULE[P4_AREA_TAYLOR_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
    `a:real`; `b:real`; `tau:real`; `(tau + b) / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tb"))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) tau)` ASSUME_TAC THENL
   [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o REWRITE_RULE[CM_GOOD_SWEEPOUT_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `(g:real->A->real^3^3) tau`; `U:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e / (&2 * (c0 + &1))`)) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sw"))) THEN
  ABBREV_TAC `eps = e / (&2 * (c0 + &1))` THEN
  SUBGOAL_THEN `&0 < eps /\ (c0 + &1) * eps = e / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 <= c0` THEN CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * C * W0 + &4 * pi + &1 /\ &0 < &2 * (C * W0 + &1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= C * W0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min ((b - tau) / &2) (min (&1) (min (delta / (&2 * C * W0 + &4 * pi + &1))
                                                 (e / (&2 * (C * W0 + &1)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LT_DIV) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `h:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `h * (&2 * C * W0 + &4 * pi + &1) <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `C * h pow 2 * W0 <= h * (e / &2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `h * (&2 * (C * W0 + &1)) <= e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `C * (h * h) * W0 = h * (h * (C * W0))`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= h * &2` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) (tau + h))` ASSUME_TAC THENL
   [USE_THEN "rm" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K1 = &1 + h * c0 + C * h pow 2` THEN
  SUBGOAL_THEN `&0 < K1` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN
    SUBGOAL_THEN `&0 <= h * c0 /\ &0 <= C * h pow 2` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC P4_REAL_LE_EPS THEN X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
  USE_THEN "sw" (MP_TAC o SPEC `ee / K1`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^3->real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p4_sweepout (top,atlas:((A->bool)#(A->real^3))->bool) (sigma:real^3->real->A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p4_sweepout_in]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p4_sweep_area atlas ((g:real->A->real^3^3) (tau + h)) sigma` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P4_CM_WIDTH_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "nonneg" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `(g:real->A->real^3^3) tau`; `sigma:real^3->real->A`] o
   REWRITE_RULE[P4_CM_NONNEG_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "apos") (X_CHOOSE_TAC `Bd:real`)) THEN
  REWRITE_TAC[p4_sweep_area] THEN MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `p4_s2_area atlas ((g:real->A->real^3^3) (tau + h))
                  (\y. (sigma:real^3->real->A) y (&0))` THEN
    EXISTS_TAC `&0` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  ABBREV_TAC `A0 = p4_s2_area atlas ((g:real->A->real^3^3) tau)
                     (\y. (sigma:real^3->real->A) y (s:real))` THEN
  ABBREV_TAC `Tr = p4_s2_trint atlas ((g:real->A->real^3^3) tau)
                     (mfd_ricci_matrix atlas (g tau)) (\y. (sigma:real^3->real->A) y (s:real))` THEN
  ABBREV_TAC `An = p4_s2_area atlas ((g:real->A->real^3^3) (tau + h))
                     (\y. (sigma:real^3->real->A) y (s:real))` THEN
  SUBGOAL_THEN `&0 <= A0 /\ A0 < W0 + ee / K1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "A0" THEN USE_THEN "apos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `p4_sweep_area atlas ((g:real->A->real^3^3) tau) sigma` THEN
      ASM_REWRITE_TAC[p4_sweep_area] THEN EXPAND_TAC "A0" THEN
      MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [EXISTS_TAC `Bd:real` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  USE_THEN "tb" (MP_TAC o SPECL [`sigma:real^3->real->A`; `s:real`; `tau:real`; `h:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `W0 - delta < A0` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `W0 + h * (--(&4 * pi) + c0 * W0 + e)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P4_SLICE_B THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `A0:real`; `Tr:real`; `delta:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC] THEN
  USE_THEN "sw" (K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
     can (find_term (fun u -> is_const u &&
                              fst(dest_const u) = "p4_harmonic_sphere")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `v:num->real^3->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= n
        ==> &4 * pi - c0 * p4_s2_area atlas ((g:real->A->real^3^3) tau) (v i)
            <= p4_s2_trint atlas (g tau) (mfd_ricci_matrix atlas (g tau)) (v i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "harm" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `(g:real->A->real^3^3) tau`; `U:A->bool`; `(v:num->real^3->A) i`;
      `--(&6) / (&4 * tau + &1)`] o REWRITE_RULE[CM_HARMONIC_SPHERE_STATEMENT]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`;
                 `\i. p4_s2_area atlas ((g:real->A->real^3^3) tau) ((v:num->real^3->A) i)`;
                 `\i. p4_s2_trint atlas ((g:real->A->real^3^3) tau)
                        (mfd_ricci_matrix atlas (g tau)) ((v:num->real^3->A) i)`;
                 `c0:real`] P4_SUM_HARMONIC) THEN
  ASM_SIMP_TAC[ETA_AX] THEN DISCH_TAC THEN
  ABBREV_TAC `SA = sum(1..n) (\i. p4_s2_area atlas ((g:real->A->real^3^3) tau)
                                   ((v:num->real^3->A) i))` THEN
  ABBREV_TAC `ST = sum(1..n) (\i. p4_s2_trint atlas ((g:real->A->real^3^3) tau)
                                   (mfd_ricci_matrix atlas (g tau)) ((v:num->real^3->A) i))` THEN
  SUBGOAL_THEN `c0 * SA <= c0 * (A0 + eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real`; `c0:real`; `C:real`; `A0:real`; `An:real`; `Tr:real`;
                `W0:real`; `ee / K1`; `eps:real`] P4_SLICE_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
  SUBGOAL_THEN `(ee / K1) * K1 = ee` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * (c0 * (ee / K1)) + C * h pow 2 * (ee / K1) + ee / K1 = ee`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h * ((c0 + &1) * eps) = h * (e / &2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P4_FINITE_EXTINCTION_CM1 = prove
 (`CM_GOOD_SWEEPOUT_STATEMENT (:A+num#num#real^3) /\
   CM_HARMONIC_SPHERE_STATEMENT (:A+num#num#real^3) /\
   P4_AREA_TAYLOR_STATEMENT (:A+num#num#real^3) /\
   P4_WIDTH_CONTINUITY_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_AREA_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_CM_NONNEG_STATEMENT (:A+num#num#real^3) /\
   P4_CM_ISOMETRY_STATEMENT (:A) (:A+num#num#real^3)
   ==> FINITE_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_FINITE_EXTINCTION_CM THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_CM_SLAB_FROM_DINI THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_CM_DINI_FROM_C1 THEN ASM_REWRITE_TAC[]);;

let P4_RFS_EXTINCTION_CM1 = prove
 (`RFS_CONTINUATION_STATEMENT (:A) /\
   CM_GOOD_SWEEPOUT_STATEMENT (:A+num#num#real^3) /\
   CM_HARMONIC_SPHERE_STATEMENT (:A+num#num#real^3) /\
   P4_AREA_TAYLOR_STATEMENT (:A+num#num#real^3) /\
   P4_WIDTH_CONTINUITY_STATEMENT (:A+num#num#real^3) /\
   P4_DEGREE_ONE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_SC_DEGREE_ONE_STATEMENT (:A) /\ P4_SMOOTHING_STATEMENT (:A) /\
   P4_PINCH_AREA_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
   P4_CM_NONNEG_STATEMENT (:A+num#num#real^3) /\
   P4_CM_ISOMETRY_STATEMENT (:A) (:A+num#num#real^3)
   ==> RFS_EXTINCTION_STATEMENT (:A)`,
  STRIP_TAC THEN MATCH_MP_TAC P4_RFS_EXTINCTION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P4_FINITE_EXTINCTION_CM1 THEN ASM_REWRITE_TAC[]);;


