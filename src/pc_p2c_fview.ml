(* ========================================================================= *)
(* Unit pc_p2c_fview (Part 2C): views of Ricci flows on a fixed manifold are *)
(* regular.  P2C_FLOW_VIEW_REGULAR |- !u. P2C_FLOW_VIEW_REGULAR_STATEMENT u  *)
(* (flows smooth from their initial time, views on [a,b)) and the companion  *)
(* P2C_FLOW_VIEW_REGULAR_UPTO for rfs_flow_upto flows (views on (a,b]: the   *)
(* limit flows of p3_flow_limit and kappa-solutions), both hypotheses of     *)
(* P2C_FULL_CHAIN (pc_p2c_iface).  Ingredients: the restriction of           *)
(* ricci_flow_on, rfs_flow_upto and ricci_flow_from to an open subset        *)
(* (restrict_atlas, restrict_metric), congruence of the flow predicates, and *)
(* the identity pullback.                                                    *)
(* ========================================================================= *)

needs "src/pc_p2c_views.ml";;
needs "src/pc_rf_extend.ml";;
needs "src/pc_lrg_flowsmooth.ml";;
needs "src/pc_p2c_iface.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Smooth maps and metric fields on the empty set; restriction              *)
(* of ricci_flow_on to an open subset W (atlas restrict_atlas atlas W,       *)
(* metrics restrict_metric atlas W (g t)).                                   *)
(* ------------------------------------------------------------------------- *)

let P2CF_SMOOTH_MAP_ON_EMPTY = prove
 (`!f:real^M->real^N. smooth_map_on {} f`,
  GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\x. vec 0):real^M->real^N` THEN
  REWRITE_TAC[NOT_IN_EMPTY; SMOOTH_MAP_ON_CONST]);;

let P2CF_METRIC_FIELD_EMPTY = prove
 (`!G:real^N->real^N^N. metric_field {} G`,
  REWRITE_TAC[metric_field; OPEN_EMPTY; NOT_IN_EMPTY; P2CF_SMOOTH_MAP_ON_EMPTY]);;

(* The local representative of the restricted metric in a restricted chart  *)
(* is the original representative, on the whole image of the chart.         *)

let P2CF_METRIC_LOCAL_RESTRICT_ON = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) W (g:A->real^N^N) y.
     smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open_in top W /\
     y IN IMAGE phi (U INTER W)
     ==> metric_local (restrict_atlas atlas W) (U INTER W,phi)
                      (restrict_metric atlas W g) y =
         metric_local atlas (U,phi) g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))))) THEN
  MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* The restricted metric at a point of W, through a chart of the atlas.    *)

let P2CF_RESTRICT_METRIC_AT = prove
 (`!top atlas (W:A->bool) x.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     open_in top W /\ x IN W
     ==> ?U phi. (U,phi) IN atlas /\ x IN U /\
                 chart_at (restrict_atlas atlas W) x = (U INTER W,phi) /\
                 !g:A->real^N^N. restrict_metric atlas W g x =
                                 metric_local atlas (U,phi) g (phi x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  ASM_REWRITE_TAC[restrict_metric] THEN
  MATCH_MP_TAC MFDR_METRIC_LOCAL_RESTRICT_CHART THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER]);;

let P2CF_RFO_RESTRICT = prove
 (`!top atlas a b (g:real->A->real^N^N) W.
     ricci_flow_on (top,atlas) a b g /\ open_in top W
     ==> ricci_flow_on (subtopology top W,restrict_atlas atlas W) a b
                       (\t. restrict_metric atlas W (g t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[ricci_flow_on] THEN
  ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
          (metric_local atlas (U:A->bool,phi:A->real^N)
             ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(U:A->bool,phi:A->real^N)) (FST(U,phi))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rm")))))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`;
                   `(U:A->bool,phi:A->real^N)`] LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[lricci_flow] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `(phi:A->real^N) x`; `i:num`; `j:num`] o
               last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[mfd_ricci_matrix; LAMBDA_BETA; mfd_ricci] THEN
    MATCH_MP_TAC LRICCI_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER W)` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Congruence of ricci_flow_on and rfs_flow_upto (values on the              *)
(* topspace at the relevant times), and the pullback of a metric by the     *)
(* identity of the same atlas.                                               *)
(* ------------------------------------------------------------------------- *)

let P2CF_RFO_CONG = prove
 (`!top atlas a b (g:real->A->real^N^N) g'.
     ricci_flow_on (top,atlas) a b g /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> g' t x = g t x)
     ==> ricci_flow_on (top,atlas) a b g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_RIEMANNIAN_METRIC_CONG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^N^N) t`] THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
          (metric_local atlas (c:(A->bool)#(A->real^N))
             ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC PDE_RFF_REP_EQ THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_ricci_matrix atlas ((g':real->A->real^N^N) t) x =
      mfd_ricci_matrix atlas (g t) x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PDE_MFD_RICCI_MATRIX_CONG THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s. (g:real->A->real^N^N) s x$i$j`; `min (t - a) (b - t)`] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g':real->A->real^N^N) s x = g s x`
      (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2CF_RFU_CONG = prove
 (`!top atlas a b (g:real->A->real^3^3) g'.
     rfs_flow_upto (top,atlas) a b g /\
     (!t x. a < t /\ t <= b /\ x IN topspace top ==> g' t x = g t x)
     ==> rfs_flow_upto (top,atlas) a b g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "on") (CONJUNCTS_THEN2 (LABEL_TAC "gb") (LABEL_TAC "ext")))
    (LABEL_TAC "eq")) THEN
  USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFO_CONG THEN EXISTS_TAC `g:real->A->real^3^3` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC PDE_RIEMANNIAN_METRIC_CONG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^3^3) b`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    USE_THEN "ext" (fun th -> MP_TAC(MP (SPEC `c:(A->bool)#(A->real^3)` th)
                                        (ASSUME `(c:(A->bool)#(A->real^3)) IN atlas`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`; `(g:real->A->real^3^3) t`;
                   `(g':real->A->real^3^3) t`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      REMOVE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* The pullback by the identity of the same atlas is the metric itself, on  *)
(* the topspace.                                                             *)

let P2CF_MPULLBACK_LOCAL_ID = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) s y.
     open s /\ y IN s /\ (!z. z IN s ==> h z = z)
     ==> mpullback h G y = G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (h:real^N->real^N) (at y) = (\x. x)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mpullback; MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let P2CF_PULLBACK_ID = prove
 (`!top atlas (G:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> mfd_pullback_metric atlas atlas (\y. y) G x = G x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_pullback_metric] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`SND(c:(A->bool)#(A->real^N)) o (\y:A. y) o chart_inv c`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (G:A->real^N^N)`;
                 `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `SND(c:(A->bool)#(A->real^N)) x`] P2CF_MPULLBACK_LOCAL_ID) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "c" THEN
  MATCH_MP_TAC METRIC_LOCAL_AT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of rfs_flow_upto and ricci_flow_from to an open              *)
(* subset; the degenerate case W = {}; congruence of restrict_metric.       *)
(* ------------------------------------------------------------------------- *)

let P2CF_RFU_RESTRICT = prove
 (`!top atlas a b (g:real->A->real^3^3) W.
     rfs_flow_upto (top,atlas) a b g /\ open_in top W
     ==> rfs_flow_upto (subtopology top W,restrict_atlas atlas W) a b
                       (\t. restrict_metric atlas W (g t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "on") (CONJUNCTS_THEN2 (LABEL_TAC "gb") (LABEL_TAC "ext")))
    ASSUME_TAC) THEN
  USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFO_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^3`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "ext" (fun th -> MP_TAC(MP (SPEC `(U:A->bool,phi:A->real^3)` th)
                         (ASSUME `(U:A->bool,phi:A->real^3) IN atlas`))) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS IMAGE (phi:A->real^3) U` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN IMAGE phi (U:A->bool)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN IMAGE phi (U INTER (W:A->bool))` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]]);;

let P2CF_RFF_RESTRICT = prove
 (`!top atlas a b (g:real->A->real^N^N) W.
     ricci_flow_from (top,atlas) a b g /\ open_in top W
     ==> ricci_flow_from (subtopology top W,restrict_atlas atlas W) a b
                         (\t. restrict_metric atlas W (g t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "on") (CONJUNCTS_THEN2 (LABEL_TAC "ga") (LABEL_TAC "ext")))
    ASSUME_TAC) THEN
  USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CF_RFO_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `phi:A->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "ext" (fun th -> MP_TAC(MP (SPEC `(U:A->bool,phi:A->real^N)` th)
                         (ASSUME `(U:A->bool,phi:A->real^N) IN atlas`))) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS IMAGE (phi:A->real^N) U` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN IMAGE phi (U:A->bool)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^N) IN IMAGE phi (U INTER (W:A->bool))` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2CF_METRIC_LOCAL_RESTRICT_ON THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]]);;

(* The degenerate case W = {}. *)

let P2CF_RIEMANNIAN_EMPTY = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) G.
     riemannian_metric (restrict_atlas atlas {}) G`,
  REWRITE_TAC[riemannian_metric; FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; P2CF_METRIC_FIELD_EMPTY]);;

let P2CF_RFO_EMPTY = prove
 (`!top atlas a b (G:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ a < b
     ==> ricci_flow_on (subtopology top {},restrict_atlas atlas {}) a b G`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ricci_flow_on; SMOOTH_MANIFOLD_ATLAS_RESTRICT; OPEN_IN_EMPTY;
               P2CF_RIEMANNIAN_EMPTY; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY;
               NOT_IN_EMPTY] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; PCROSS_EMPTY; P2CF_SMOOTH_MAP_ON_EMPTY]);;

let P2CF_RFU_EMPTY = prove
 (`!top atlas a b (G:real->A->real^3^3).
     smooth_manifold_atlas top atlas /\ a < b
     ==> rfs_flow_upto (subtopology top {},restrict_atlas atlas {}) a b G`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[rfs_flow_upto; P2CF_RFO_EMPTY; P2CF_RIEMANNIAN_EMPTY] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; PCROSS_EMPTY; P2CF_SMOOTH_MAP_ON_EMPTY;
                  NOT_IN_EMPTY] THEN
  MESON_TAC[REAL_LT_01]);;

let P2CF_RFF_EMPTY = prove
 (`!top atlas a b (G:real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ a < b
     ==> ricci_flow_from (subtopology top {},restrict_atlas atlas {}) a b G`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ricci_flow_from; P2CF_RFO_EMPTY; P2CF_RIEMANNIAN_EMPTY] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; PCROSS_EMPTY; P2CF_SMOOTH_MAP_ON_EMPTY;
                  NOT_IN_EMPTY] THEN
  MESON_TAC[REAL_LT_01]);;

let P2CF_DIFFEO_EMPTY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (top':B topology)
    (atlas':((B->bool)#(B->real^M))->bool) f g.
     mfd_diffeo top atlas {} top' atlas' {} f g`,
  REWRITE_TAC[mfd_diffeo; mfd_smooth_map; OPEN_IN_EMPTY; INTER_EMPTY; NOT_IN_EMPTY;
              EMPTY_GSPEC; IMAGE_CLAUSES; P2CF_SMOOTH_MAP_ON_EMPTY] THEN
  REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY; NOT_IN_EMPTY] THEN
  SIMP_TAC[CONTINUOUS_MAP_ON_EMPTY; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY]);;

(* restrict_metric atlas W g at points of W depends only on g on the        *)
(* topspace.                                                                 *)

let P2CF_RESTRICT_METRIC_CONG = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) g' x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
     (!y. y IN topspace top ==> g' y = g y)
     ==> restrict_metric atlas W g' x = restrict_metric atlas W g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`; `x:A`] P2CF_RESTRICT_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(U:A->bool,phi:A->real^N)`; `g':A->real^N^N`; `g:A->real^N^N`]
                PDE_METRIC_LOCAL_CONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Views of a flow on a fixed manifold over a time set J are                 *)
(* regular as soon as the slices are riemannian, every interval (a,b] in J   *)
(* carries an rfs_flow_upto flow and every such interval with a in J a       *)
(* ricci_flow_from flow (P2CF_FLOW_VIEW_REGULAR_GEN).                        *)
(* ------------------------------------------------------------------------- *)

let P2CF_FLOW_VIEW_PARTS = prove
 (`!top atlas J (g:real->A->real^3^3) t.
     rfs_vtop (rfs_flow_view (top,atlas) J g) t =
       (if t IN J then top else discrete_topology {}) /\
     rfs_vatlas (rfs_flow_view (top,atlas) J g) t = atlas /\
     rfs_vmetric (rfs_flow_view (top,atlas) J g) t = g t`,
  REWRITE_TAC[rfs_flow_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2CF_FLOW_PERSISTS = prove
 (`!top atlas J (g:real->A->real^3^3) W a b.
     rfs_persists (rfs_flow_view (top,atlas) J g) W a b <=>
     !s. a < s /\ s <= b
         ==> smooth_manifold_atlas (if s IN J then top else discrete_topology {}) atlas /\
             open_in (if s IN J then top else discrete_topology {}) W`,
  REWRITE_TAC[rfs_flow_view; rfs_persists]);;

(* A nonempty persisting set lives in slices of times in J. *)

let P2CF_FLOW_PERSIST_IN = prove
 (`!top atlas J (g:real->A->real^3^3) W a b.
     rfs_persists (rfs_flow_view (top,atlas) J g) W a b /\ ~(W = {})
     ==> !s. a < s /\ s <= b
             ==> s IN J /\ smooth_manifold_atlas top atlas /\ open_in top W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2CF_FLOW_PERSISTS] THEN
  STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[]);;

let P2CF_FLOW_OPEN_IN = prove
 (`!top (J:real->bool) (W:A->bool) (a:real).
     open_in (if a IN J then top else discrete_topology {}) W /\ ~(W = {})
     ==> a IN J /\ open_in top W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (if (a:real) IN J then top else discrete_topology {})
                         (W:A->bool)` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[];
    UNDISCH_TAC `open_in (if (a:real) IN J then top else discrete_topology {})
                         (W:A->bool)` THEN
    ASM_REWRITE_TAC[]]);;

let P2CF_VFAM_FLOW = prove
 (`!top atlas J (g:real->A->real^3^3) W b t x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W
     ==> p2c_vfam (rfs_flow_view (top,atlas) J g) W b t x =
         restrict_metric atlas W (g t) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2c_vfam; P2CF_FLOW_VIEW_PARTS] THEN
  MATCH_MP_TAC P2CF_RESTRICT_METRIC_CONG THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CF_PULLBACK_ID THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

let P2CF_FLOW_VIEW_REGULAR_GEN = prove
 (`!top atlas J (g:real->A->real^3^3).
     hausdorff_space top /\
     (!t. t IN J ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g t)) /\
     (!a b. a < b /\ (!s. a < s /\ s <= b ==> s IN J)
            ==> rfs_flow_upto (top,atlas) a b g) /\
     (!a b. a < b /\ a IN J /\ (!s. a < s /\ s <= b ==> s IN J)
            ==> ricci_flow_from (top,atlas) a b g)
     ==> p2c_regular_view (rfs_flow_view (top,atlas) J g)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "from")))) THEN
  SUBGOAL_THEN
   `!W a b. a < b /\ rfs_persists (rfs_flow_view (top,atlas) J g) W a b
            ==> p2c_vflow (rfs_flow_view (top,atlas) J (g:real->A->real^3^3)) W a b`
  (LABEL_TAC "vflow") THENL
   [MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[p2c_vflow] THEN REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CF_RFU_EMPTY THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_persists (rfs_flow_view (top,atlas) J (g:real->A->real^3^3)) {} a b` THEN
      REWRITE_TAC[P2CF_FLOW_PERSISTS] THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `J:real->bool`; `g:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2CF_FLOW_PERSIST_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "in") THEN
    USE_THEN "in" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CF_RFU_CONG THEN
    EXISTS_TAC `\t. restrict_metric atlas W ((g:real->A->real^3^3) t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFU_RESTRICT THEN ASM_REWRITE_TAC[] THEN
      REMOVE_THEN "upto" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2CF_VFAM_FLOW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2c_regular_view] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    COND_CASES_TAC THEN REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN
    DISCH_TAC THEN ASM_MESON_TAC[];
    REMOVE_THEN "vflow" (fun th -> REWRITE_TAC[th]);
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[p2c_vflow_from] THEN REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    ASM_CASES_TAC `W:A->bool = {}` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CF_RFF_EMPTY THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_persists (rfs_flow_view (top,atlas) J (g:real->A->real^3^3)) {} a b` THEN
      REWRITE_TAC[P2CF_FLOW_PERSISTS] THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `J:real->bool`; `g:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2CF_FLOW_PERSIST_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "in") THEN
    USE_THEN "in" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `open_in (rfs_vtop (rfs_flow_view (top,atlas) J (g:real->A->real^3^3)) a) W` THEN
    REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `J:real->bool`; `W:A->bool`; `a:real`]
                  P2CF_FLOW_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_RFF_CONG THEN
    EXISTS_TAC `\t. restrict_metric atlas W ((g:real->A->real^3^3) t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_RFF_RESTRICT THEN ASM_REWRITE_TAC[] THEN
      REMOVE_THEN "from" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2CF_VFAM_FLOW THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`; `s:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    ASM_CASES_TAC `W:A->bool = {}` THEN ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `J:real->bool`; `g:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2CF_FLOW_PERSIST_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `s:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[];
    (* conjunct 5: the slice at the left end a *)
    MAP_EVERY X_GEN_TAC [`W:A->bool`; `a:real`; `b:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN
    ASM_CASES_TAC `W:A->bool = {}` THEN ASM_REWRITE_TAC[P2CF_DIFFEO_EMPTY] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `J:real->bool`; `g:real->A->real^3^3`; `W:A->bool`; `a:real`; `b:real`]
                  P2CF_FLOW_PERSIST_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
    UNDISCH_TAC `open_in (rfs_vtop (rfs_flow_view (top,atlas) J (g:real->A->real^3^3)) a) W` THEN
    REWRITE_TAC[P2CF_FLOW_VIEW_PARTS] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `J:real->bool`; `W:A->bool`; `a:real`]
                  P2CF_FLOW_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_DIFFEO_ID THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Flows on subintervals, and the two instances: views of                    *)
(* ricci_flow_from flows on [a,b) (P2C_FLOW_VIEW_REGULAR) and of            *)
(* rfs_flow_upto flows on (a,b] (P2CF_FLOW_VIEW_REGULAR_UPTO).               *)
(* ------------------------------------------------------------------------- *)

(* A flow on (a,b) gives an rfs_flow_upto flow on any (a',b'] with b' < b   *)
(* and a ricci_flow_from flow on any [a',b') with a < a'.                    *)

let P2CF_RFO_UPTO = prove
 (`!top atlas a b a' b' (g:real->A->real^3^3).
     ricci_flow_on (top,atlas) a b g /\ a <= a' /\ a' < b' /\ b' < b
     ==> rfs_flow_upto (top,atlas) a' b' g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[rfs_flow_upto] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`b - b':real`;
      `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
           (metric_local atlas (c:(A->bool)#(A->real^3))
              ((g:real->A->real^3^3) (drop(fstcart z))) (sndcart z))`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]]);;

let P2CF_RFO_FROM = prove
 (`!top atlas a b a' b' (g:real->A->real^N^N).
     ricci_flow_on (top,atlas) a b g /\ a < a' /\ a' < b' /\ b' <= b
     ==> ricci_flow_from (top,atlas) a' b' g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[ricci_flow_from] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`a' - a:real`;
      `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           (metric_local atlas (c:(A->bool)#(A->real^N))
              ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]]);;

let P2CF_RFU_LEFT = prove
 (`!top atlas a b a' (g:real->A->real^3^3).
     rfs_flow_upto (top,atlas) a b g /\ a <= a' /\ a' < b
     ==> rfs_flow_upto (top,atlas) a' b g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_flow_upto] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_SIMP_TAC[REAL_LE_REFL];
    X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* An interval (a',b'] inside the times s with a <= s and P s starts at or  *)
(* after a.                                                                  *)

let P2CF_INTERVAL_LOWER = prove
 (`!a a' b' P. a' < b' /\ (!s. a' < s /\ s <= b' ==> a <= s /\ P s) ==> a <= a'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min b' ((a' + a) / &2)`) THEN
  REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISJ1_TAC THEN ASM_REAL_ARITH_TAC]);;

let P2C_FLOW_VIEW_REGULAR = prove
 (`!u:A->bool. P2C_FLOW_VIEW_REGULAR_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_FLOW_VIEW_REGULAR_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^3^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MATCH_MP_TAC P2CF_FLOW_VIEW_REGULAR_GEN THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CF_INTERVAL_LOWER THEN
      MAP_EVERY EXISTS_TAC [`b':real`; `\s:real. s < b`] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REAL_ARITH_TAC]);;

let P2CF_FLOW_VIEW_REGULAR_UPTO = prove
 (`!top atlas a b (g:real->A->real^3^3).
     hausdorff_space top /\ rfs_flow_upto (top,atlas) a b g
     ==> p2c_regular_view (rfs_flow_view (top,atlas) {s | a < s /\ s <= b} g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_flow_upto]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  MATCH_MP_TAC P2CF_FLOW_VIEW_REGULAR_GEN THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t:real = b` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= a' /\ b' <= b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC P2CF_INTERVAL_LOWER THEN
        MAP_EVERY EXISTS_TAC [`b':real`; `\s:real. s <= b`] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `b':real = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC P2CF_RFU_LEFT THEN
      EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[rfs_flow_upto];
      MATCH_MP_TAC P2CF_RFO_UPTO THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CF_RFO_FROM THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* P2C_FLOW_VIEW_REGULAR_UPTO, the views of rfs_flow_upto flows.             *)
(* ------------------------------------------------------------------------- *)

let P2C_FLOW_VIEW_REGULAR_UPTO = prove
 (`!u:A->bool. P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT u`,
  REWRITE_TAC[P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT; P2CF_FLOW_VIEW_REGULAR_UPTO]);;

