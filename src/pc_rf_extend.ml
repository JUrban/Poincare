(* ========================================================================= *)
(* Unit pc_rf_extend (PDE layer): facts about Ricci flows smooth up to the   *)
(* initial time (congruence, restriction, concatenation on an open overlap,  *)
(* union of a chain), finite chart covers and chart bounds, and the          *)
(* assemblies of the statements of pc_pde_iface: uniform existence from the  *)
(* Ricci-DeTurck existence and the gauge, existence from uniform existence,  *)
(* the extension criterion (restart before the final time and uniqueness),   *)
(* maximal flows, existence time from curvature.                             *)
(*                                                                           *)
(* First congruence (chart quantities only read the values of the metric on  *)
(* the space).                                                               *)
(* ========================================================================= *)

needs "src/pc_pde_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let PDE_METRIC_LOCAL_CONG = prove
 (`!top atlas c (g:A->real^N^N) g'.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        (!y. y IN topspace top ==> g y = g' y)
        ==> !z. z IN IMAGE (SND c) (FST c)
                ==> metric_local atlas c g z = metric_local atlas c g' z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) z IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ASM_SIMP_TAC[metric_local]]);;

(* The preferred chart at x: its image is open and contains the chart point. *)

let PDE_CHART_AT_FACTS = prove
 (`!top atlas (x:A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        x IN topspace top
        ==> chart_at atlas x IN atlas /\ x IN FST(chart_at atlas x) /\
            open(IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))) /\
            SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ASM SET_TAC[]]);;

let PDE_MFD_RM_NORM_CONG = prove
 (`!top atlas (g:A->real^N^N) g' x.
        smooth_manifold_atlas top atlas /\
        (!y. y IN topspace top ==> g y = g' y) /\ x IN topspace top
        ==> mfd_rm_norm atlas g x = mfd_rm_norm atlas g' x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `g:A->real^N^N`; `g':A->real^N^N`]
                PDE_METRIC_LOCAL_CONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_rm_norm; mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `r:real` THEN
  SUBGOAL_THEN
   `!u v:real^N. lsectional (metric_local atlas c (g:A->real^N^N)) (SND c x) u v =
                 lsectional (metric_local atlas (c:(A->bool)#(A->real^N)) g') (SND c x) u v`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g':A->real^N^N)`;
                 `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `SND(c:(A->bool)#(A->real^N)) x`; `u:real^N`; `v:real^N`; `v:real^N`]
                LRIEMANN_LOCAL) THEN
  ASM_SIMP_TAC[]);;

let PDE_MFD_RICCI_MATRIX_CONG = prove
 (`!top atlas (g:A->real^N^N) g' x.
        smooth_manifold_atlas top atlas /\
        (!y. y IN topspace top ==> g y = g' y) /\ x IN topspace top
        ==> mfd_ricci_matrix atlas g x = mfd_ricci_matrix atlas g' x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                PDE_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `g:A->real^N^N`; `g':A->real^N^N`]
                PDE_METRIC_LOCAL_CONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!u v:real^N. lricci (metric_local atlas c (g:A->real^N^N)) (SND c x) u v =
                 lricci (metric_local atlas (c:(A->bool)#(A->real^N)) g') (SND c x) u v`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC LRICCI_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[]);;

let PDE_RIEMANNIAN_METRIC_CONG = prove
 (`!top atlas (g:A->real^N^N) g'.
        smooth_manifold_atlas top atlas /\
        (!y. y IN topspace top ==> g y = g' y) /\ riemannian_metric atlas g
        ==> riemannian_metric atlas g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[riemannian_metric] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `g:A->real^N^N`; `g':A->real^N^N`]
                PDE_METRIC_LOCAL_CONG) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Ricci flows smooth up to the initial time: congruence,                    *)
(* restriction to subintervals, gluing of extensions, concatenation of two   *)
(* flows agreeing on an open overlap, union of an increasing family.         *)
(* ========================================================================= *)

(* A map smooth below an initial time a (on (a-e,b) x U) and a map smooth    *)
(* after it (on (a,c) x U) that agree on [a,b) x U glue to a smooth map on   *)
(* (a-e,c) x U.                                                              *)

let PDE_EXTENSION_GLUE = prove
 (`!a b c e (U:real^N->bool) (F1:real^(1,N)finite_sum->real^K) H.
        open U /\ &0 < e /\ a < b /\ b <= c /\
        smooth_map_on (interval(lift(a - e),lift b) PCROSS U) F1 /\
        smooth_map_on (interval(lift a,lift c) PCROSS U) H /\
        (!t y. a <= t /\ t < b /\ y IN U
               ==> F1(pastecart (lift t) y) = H(pastecart (lift t) y))
        ==> smooth_map_on (interval(lift(a - e),lift c) PCROSS U)
                          (\z. if drop(fstcart z) < a then F1 z else H z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t0 < b` THENL
   [EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `F1:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `interval(lift a,lift c) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `H:real^(1,N)finite_sum->real^K` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The chart representative of a family of metrics as a space-time map.     *)

let PDE_RFF_REP_EQ = prove
 (`!top atlas c a b (g:real->A->real^N^N) g'.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        (!t x. a < t /\ t < b /\ x IN topspace top ==> g' t x = g t x)
        ==> !z. z IN interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)
                ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c (g (drop(fstcart z))) (sndcart z)) =
                    (vectorize:real^N^N->real^(N,N)finite_prod)
                      (metric_local atlas c (g' (drop(fstcart z))) (sndcart z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(g:real->A->real^N^N) t`;
                 `(g':real->A->real^N^N) t`] PDE_METRIC_LOCAL_CONG) THEN
  ASM_SIMP_TAC[]);;

let PDE_RFF_CONG = prove
 (`!top atlas a b (g:real->A->real^N^N) g'.
        ricci_flow_from (top,atlas) a b g /\
        (!t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x)
        ==> ricci_flow_from (top,atlas) a b g'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC PDE_RIEMANNIAN_METRIC_CONG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^N^N) t`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
          (metric_local atlas (c:(A->bool)#(A->real^N))
             ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC PDE_RFF_REP_EQ THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_ricci_matrix atlas ((g':real->A->real^N^N) t) x =
      mfd_ricci_matrix atlas (g t) x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PDE_MFD_RICCI_MATRIX_CONG THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s. (g:real->A->real^N^N) s x$i$j`; `min (t - a) (b - t)`] THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g':real->A->real^N^N) s x = g s x`
      (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PDE_RIEMANNIAN_METRIC_CONG THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^N^N) a`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`
        STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `(g:real->A->real^N^N) t`;
                   `(g':real->A->real^N^N) t`] PDE_METRIC_LOCAL_CONG) THEN
    ASM_SIMP_TAC[]]);;

let PDE_RFF_RESTRICT = prove
 (`!top atlas a b a' b' (g:real->A->real^N^N).
        ricci_flow_from (top,atlas) a b g /\ a <= a' /\ a' < b' /\ b' <= b
        ==> ricci_flow_from (top,atlas) a' b' g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "on") (CONJUNCTS_THEN2 (LABEL_TAC "ga") (LABEL_TAC "ext")))
    STRIP_ASSUME_TAC) THEN
  USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `a':real = a` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    ASM_CASES_TAC `a':real = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "ext" (fun th -> MP_TAC(MP (SPEC `c:(A->bool)#(A->real^N)` th)
                                          (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real`
        (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`
          STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`e:real`; `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
                    IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
        REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
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
        ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC PCROSS_MONO THEN
        REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]]]]);;

(* Union of an increasing family of flows: the open-interval part.           *)

let PDE_RFO_UNION = prove
 (`!top atlas a tm (g:real->A->real^N^N).
        a < tm /\ (!b. a < b /\ b < tm ==> ricci_flow_on (top,atlas) a b g)
        ==> ricci_flow_on (top,atlas) a tm g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all")) THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < tm
        ==> ricci_flow_on (top,atlas) a ((t + tm) / &2) (g:real->A->real^N^N)`
  (LABEL_TAC "loc") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "all" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL
   [USE_THEN "loc" (MP_TAC o SPEC `(a + tm) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[ricci_flow_on]];
    ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `interval(lift a,lift((t + tm) / &2)) PCROSS
                IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN];
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "loc" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Extension past a of a flow on [a,b), given the extension of its           *)
(* restriction to an initial subinterval [a,b0).                             *)

let PDE_RFF_FROM_ON = prove
 (`!top atlas a b0 b (g:real->A->real^N^N).
        ricci_flow_from (top,atlas) a b0 g /\ ricci_flow_on (top,atlas) a b g /\
        b0 <= b
        ==> ricci_flow_from (top,atlas) a b g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "on") ASSUME_TAC)) THEN
  REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ a < b0`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`a:real`; `b0:real`; `b:real`; `e:real`;
    `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
    `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         (metric_local atlas (c:(A->bool)#(A->real^N))
            ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))`]
   PDE_EXTENSION_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "on" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC
   `\z. if drop(fstcart z) < a then (FF:real^(1,N)finite_sum->real^(N,N)finite_prod) z
        else (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N))
                ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  SIMP_TAC[GSYM REAL_NOT_LE]);;

let PDE_RFF_UNION = prove
 (`!top atlas a tm (g:real->A->real^N^N).
        a < tm /\ (!b. a < b /\ b < tm ==> ricci_flow_from (top,atlas) a b g)
        ==> ricci_flow_from (top,atlas) a tm g`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all")) THEN
  MATCH_MP_TAC PDE_RFF_FROM_ON THEN EXISTS_TAC `(a + tm) / &2` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "all" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PDE_RFO_UNION THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `b:real` THEN STRIP_TAC THEN
    REMOVE_THEN "all" (MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[ricci_flow_from];
    ASM_REAL_ARITH_TAC]);;

(* Two flows on overlapping open intervals give a flow on the union.         *)

let PDE_RFO_UNION2 = prove
 (`!top atlas a b s c (g:real->A->real^N^N).
        ricci_flow_on (top,atlas) a b g /\ ricci_flow_on (top,atlas) s c g /\
        a <= s /\ s < b /\ b <= c
        ==> ricci_flow_on (top,atlas) a c g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "one") (CONJUNCTS_THEN2 (LABEL_TAC "two")
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "one" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t < b` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "two" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    SUBGOAL_THEN `open(IMAGE (SND(cc:(A->bool)#(A->real^N))) (FST cc))` ASSUME_TAC THENL
     [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t < b` THENL
     [EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND(cc:(A->bool)#(A->real^N))) (FST cc)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP];
      USE_THEN "two" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      EXISTS_TAC `interval(lift s,lift c) PCROSS
                  IMAGE (SND(cc:(A->bool)#(A->real^N))) (FST cc)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `t < b` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "two" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let PDE_RFF_CONCAT = prove
 (`!top atlas a b s c (g:real->A->real^N^N) g'.
        ricci_flow_from (top,atlas) a b g /\ ricci_flow_from (top,atlas) s c g' /\
        a <= s /\ s < b /\ b <= c /\
        (!t x. s <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x)
        ==> ricci_flow_from (top,atlas) a c (\t. if t < s then g t else g' t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ricci_flow_from (top,atlas) a b (\t. if t < s then (g:real->A->real^N^N) t else g' t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `g:real->A->real^N^N` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_from (top,atlas) s c (\t. if t < s then (g:real->A->real^N^N) t else g' t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `g':real->A->real^N^N` THEN
    ASM_SIMP_TAC[GSYM REAL_NOT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_RFF_FROM_ON THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_RFO_UNION2 THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `s:real`] THEN
  ASM_MESON_TAC[ricci_flow_from]);;

(* ========================================================================= *)
(* Finite chart covers of compact manifolds, and chart bounds                *)
(* of smooth metrics on them.                                                *)
(* ========================================================================= *)

let PDE_CHART_BALL_IMAGE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) B.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        B SUBSET IMAGE (SND c) (FST c)
        ==> IMAGE (chart_inv c) B = {z | z IN FST c /\ SND c z IN B}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                CHART_INV) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    STRIP_TAC THEN EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) z` THEN
    ASM_SIMP_TAC[]]);;

let PDE_COVER_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas /\ compact_space top
        ==> ?n0 cs ks. pde_cover (top,atlas) n0 cs ks`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?r. !x. x IN topspace top
            ==> &0 < r x /\
                cball(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) (x:A),r x)
                SUBSET IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                  PDE_CHART_AT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    DISCH_THEN(MP_TAC o SPEC
      `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `V = \x:A. {z:A | z IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) /\
                     SND(chart_at atlas x) z IN
                     ball(SND(chart_at atlas x) x,(r:A->real) x)}` THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> open_in top (V x) /\ x IN V x /\
              V x = IMAGE (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                          (ball(SND(chart_at atlas x) x,(r:A->real) x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                  PDE_CHART_AT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                     `ball(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x,
                           (r:A->real) x)`]
                    GRGD_CHART_PREIMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; OPEN_BALL];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDE_CHART_BALL_IMAGE THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x,
                        (r:A->real) x)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact_space]) THEN
  REWRITE_TAC[compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `{(V:A->A->bool) x | x IN topspace top}` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:(A->bool)->bool`; `CARD(W:(A->bool)->bool)`] HAS_SIZE_INDEX) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?p. !m. m < CARD(W:(A->bool)->bool)
            ==> (p:num->A) m IN topspace top /\ f m = (V:A->A->bool) (p m)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:num->A->bool) m IN {(V:A->A->bool) x | x IN topspace top}` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`CARD(W:(A->bool)->bool)`;
    `\m. chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:num->A) m)`;
    `\m. cball(SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:num->A) m)) (p m),
               (r:A->real) (p m))`] THEN
  REWRITE_TAC[pde_cover; INTERIOR_CBALL; COMPACT_CBALL] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[CHART_AT];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:A` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?u:A->bool. u IN W /\ z IN u` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [EXISTS_UNIQUE_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   ((p:num->A) m)))
                      (ball(SND(chart_at atlas (p m)) (p m),(r:A->real) (p m)))` THEN
    CONJ_TAC THENL [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:num->A) m`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:num->A) i`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2 th))]) THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(p:num->A) i`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:num->A) i))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((p:num->A) i))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[]]);;

(* A smooth map is bounded with all its iterated partials on a compact       *)
(* subset of its open domain.                                                *)

let PDE_SMOOTH_PARTIAL_BOUNDED = prove
 (`!s (f:real^M->real^K) k l.
        open s /\ smooth_map_on s f /\ compact k /\ k SUBSET s
        ==> ?b. !y. y IN k ==> norm(iterated_partial l f y) <= b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `s:real^M->bool`; `f:real^M->real^K`]
                SMOOTH_MAP_ON_ITERATED_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`iterated_partial l (f:real^M->real^K)`; `k:real^M->bool`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let PDE_CBOUND_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks (g:A->real^N^N) m.
        smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
        riemannian_metric atlas g
        ==> ?B. pde_cbound atlas n0 cs ks m B g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_cover] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. ?b. i < n0
            ==> &0 < b /\
                (!l y. l IN pde_index_lists m (:N) /\ y IN ks i
                       ==> norm(iterated_partial l
                                  ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                   metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                     (g:A->real^N^N)) y) <= b) /\
                (!y v. y IN ks i
                       ==> norm v pow 2 <=
                           b * (v dot (metric_local atlas (cs i) g y ** v)))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                   (metric_local atlas (cs i) (g:A->real^N^N))`
    MP_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!l. ?b. l IN pde_index_lists m (:N)
              ==> !y. y IN ks i
                      ==> norm(iterated_partial l
                                 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                  metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                    (g:A->real^N^N)) y) <= b`
    MP_TAC THENL
     [X_GEN_TAC `l:num list` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC PDE_SMOOTH_PARTIAL_BOUNDED THEN
      EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `bl:(num)list->real`) THEN
    MP_TAC(ISPECL [`bl:(num)list->real`; `pde_index_lists m (:N)`]
                  UPPER_BOUND_FINITE_SET_REAL) THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    DISCH_THEN(X_CHOOSE_TAC `b1:real`) THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `FST((cs:num->(A->bool)#(A->real^N)) i)`;
                   `SND((cs:num->(A->bool)#(A->real^N)) i)`;
                   `(ks:num->real^N->bool) i`] GRGD_METRIC_BOUNDS) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `max b1 (inv c0)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv c0` THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(bl:(num)list->real) l` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `b1:real` THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `v:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ABBREV_TAC `q = v dot (metric_local atlas
                    ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N) y ** v)` THEN
      SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c0 * norm(v:real^N) pow 2` THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POW_LE; NORM_POS_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv c0 * q` THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `bi:num->real`) THEN
  MP_TAC(ISPECL [`bi:num->real`; `{i:num | i < n0}`] UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `B:real` THEN REWRITE_TAC[pde_cbound] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(bi:num->real) i` THEN
    ASM_SIMP_TAC[];
    ABBREV_TAC `q = v dot (metric_local atlas
                  ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N) y ** v)` THEN
    SUBGOAL_THEN `norm(v:real^N) pow 2 <= (bi:num->real) i * q` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(bi:num->real) i`; `q:real`] (CONJUNCT1 REAL_LE_MUL_EQ)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(v:real^N) pow 2` THEN
      ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(bi:num->real) i * q` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL]]);;

(* ========================================================================= *)
(* The assemblies: PDE_STE_UNIFORM_FROM_RDT, PDE_STE_FROM_UNIFORM,           *)
(* PDE_CURVATURE_TIME_FROM, PDE_EXTENSION_FROM, PDE_MAXIMAL_FROM.            *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)

let PDE_STE_UNIFORM_FROM_RDT = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_RDT_UNIFORM_STATEMENT u n /\ PDE_GAUGE_STATEMENT u n
        ==> PDE_STE_UNIFORM_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PDE_RDT_UNIFORM_STATEMENT; PDE_GAUGE_STATEMENT;
              PDE_STE_UNIFORM_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gauge")) THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `B:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `tau:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rdt")) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g0:A->real^N^N`; `a:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "rdt" (MP_TAC o SPECL [`g0:A->real^N^N`; `a:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gb:real->A->real^N^N` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "gauge" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
    `a:real`; `a + tau:real`; `gb:real->A->real^N^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real->A->A`
    (X_CHOOSE_THEN `g:real->A->real^N^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real->A->real^N^N` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)

let PDE_STE_FROM_UNIFORM = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_STE_UNIFORM_STATEMENT u n ==> PDE_STE_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PDE_STE_UNIFORM_STATEMENT; PDE_STE_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "unif") THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
    `a:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                PDE_COVER_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `cs:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `ks:num->real^N->bool` ASSUME_TAC))) THEN
  REMOVE_THEN "unif" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` (LABEL_TAC "m")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
                 `g0:A->real^N^N`; `m:num`] PDE_CBOUND_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  REMOVE_THEN "m" (MP_TAC o SPEC `B:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:A->real^N^N`; `a:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->A->real^N^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`a + tau:real`; `g:real->A->real^N^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)

let PDE_CURVATURE_TIME_FROM = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_MAXIMAL_FLOW_STATEMENT u n /\ PDE_REQ_RM_DOUBLING_STATEMENT u n
        ==> PDE_CURVATURE_TIME_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PDE_MAXIMAL_FLOW_STATEMENT; PDE_REQ_RM_DOUBLING_STATEMENT;
              PDE_CURVATURE_TIME_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "max")
    (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dbl")))))) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `C:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
    `a:real`; `K:real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "max" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
    `a:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->A->real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `&0 < c / K` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> mfd_rm_norm atlas ((g:real->A->real^N^N) a) x <= K`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) a`; `g0:A->real^N^N`; `x:A`]
                  PDE_MFD_RM_NORM_CONG) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a + c / K + &1`; `g:real->A->real^N^N`] THEN
    SUBGOAL_THEN `ricci_flow_from (top,atlas) a (a + c / K + &1)
                                  (g:real->A->real^N^N)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "dbl" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
      `a + c / K + &1`; `g:real->A->real^N^N`; `K:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a + c / K < b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `C * K:real`) THEN
    REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
    REWRITE_TAC[TAUT `~(p /\ q /\ r /\ s) <=> p /\ q /\ r ==> ~s`; REAL_NOT_LT] THEN
    STRIP_TAC THEN
    REMOVE_THEN "dbl" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
      `b:real`; `g:real->A->real^N^N`; `K:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `g:real->A->real^N^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REMOVE_THEN "dbl" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
    `b:real`; `g:real->A->real^N^N`; `K:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)

let PDE_EXTENSION_FROM = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_STE_UNIFORM_STATEMENT u n /\ PDE_UNIQUENESS_STATEMENT u n /\
        PDE_REQ_DERIV_BOUNDS_STATEMENT u n
        ==> PDE_EXTENSION_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PDE_STE_UNIFORM_STATEMENT; PDE_UNIQUENESS_STATEMENT;
              PDE_REQ_DERIV_BOUNDS_STATEMENT; PDE_EXTENSION_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "unif")
    (CONJUNCTS_THEN2 (LABEL_TAC "uniq") (LABEL_TAC "bds"))) THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
    `g:real->A->real^N^N`; `B:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ a < b`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                PDE_COVER_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `cs:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `ks:num->real^N->bool` ASSUME_TAC))) THEN
  REMOVE_THEN "unif" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` (LABEL_TAC "m")) THEN
  REMOVE_THEN "bds" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `n0:num`; `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`;
    `a:real`; `b:real`; `g:real->A->real^N^N`; `B:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `B':real` (LABEL_TAC "cb")) THEN
  REMOVE_THEN "m" (MP_TAC o SPEC `B':real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ex"))) THEN
  ABBREV_TAC `s = max a (b - tau / &2)` THEN
  SUBGOAL_THEN `a <= s /\ s < b /\ b < s + tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) s)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = a:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pde_cbound atlas n0 cs ks m B' ((g:real->A->real^N^N) s)` ASSUME_TAC THENL
   [REMOVE_THEN "cb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ex" (MP_TAC o SPECL [`(g:real->A->real^N^N) s`; `s:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->A->real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) s b (g:real->A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. s <= t /\ t < b /\ x IN topspace top
          ==> (h:real->A->real^N^N) t x = g t x`
  ASSUME_TAC THENL
   [REMOVE_THEN "uniq" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `s:real`; `b:real`;
      `s + tau:real`; `g:real->A->real^N^N`; `h:real->A->real^N^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`s + tau:real`; `\t. if t < s then (g:real->A->real^N^N) t else h t`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONCAT THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)

let PDE_MAXIMAL_FROM = prove
 (`!(u:A->bool) (n:N->bool).
        PDE_STE_STATEMENT u n /\ PDE_UNIQUENESS_STATEMENT u n /\
        PDE_EXTENSION_STATEMENT u n
        ==> PDE_MAXIMAL_FLOW_STATEMENT u n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PDE_STE_STATEMENT; PDE_UNIQUENESS_STATEMENT;
              PDE_EXTENSION_STATEMENT; PDE_MAXIMAL_FLOW_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ste")
    (CONJUNCTS_THEN2 (LABEL_TAC "uniq") (LABEL_TAC "ext"))) THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
    `a:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC
   `G = \t:real. (@g:real->A->real^N^N.
                    ?b. t < b /\ ricci_flow_from (top,atlas) a b g /\
                        (!x. x IN topspace top ==> g a x = g0 x)) t` THEN
  SUBGOAL_THEN
   `!b (gb:real->A->real^N^N).
        ricci_flow_from (top,atlas) a b gb /\
        (!x. x IN topspace top ==> gb a x = g0 x)
        ==> !t x. a <= t /\ t < b /\ x IN topspace top
                  ==> (G:real->A->real^N^N) t x = gb t x`
  (LABEL_TAC "cons") THENL
   [MAP_EVERY X_GEN_TAC [`b:real`; `gb:real->A->real^N^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `?b. t < b /\
          ricci_flow_from (top,atlas) a b
            (@g:real->A->real^N^N.
               ?b. t < b /\ ricci_flow_from (top,atlas) a b g /\
                   (!x. x IN topspace top ==> g a x = g0 x)) /\
          (!x. x IN topspace top
               ==> (@g:real->A->real^N^N.
                      ?b. t < b /\ ricci_flow_from (top,atlas) a b g /\
                          (!x. x IN topspace top ==> g a x = g0 x)) a x = g0 x)`
    MP_TAC THENL
     [CONV_TAC SELECT_CONV THEN
      MAP_EVERY EXISTS_TAC [`gb:real->A->real^N^N`; `b:real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC
     `gc = (@g:real->A->real^N^N.
              ?b. t < b /\ ricci_flow_from (top,atlas) a b g /\
                  (!x. x IN topspace top ==> g a x = g0 x))` THEN
    DISCH_THEN(X_CHOOSE_THEN `bc:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "uniq" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
      `bc:real`; `gb:real->A->real^N^N`; `gc:real->A->real^N^N`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b (gb:real->A->real^N^N).
        ricci_flow_from (top,atlas) a b gb /\
        (!x. x IN topspace top ==> gb a x = g0 x)
        ==> ricci_flow_from (top,atlas) a b (G:real->A->real^N^N) /\
            (!x. x IN topspace top ==> G a x = g0 x)`
  (LABEL_TAC "flowG") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < b` ASSUME_TAC THENL
     [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `gb:real->A->real^N^N` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "cons" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      TRANS_TAC EQ_TRANS `(gb:real->A->real^N^N) a x` THEN ASM_SIMP_TAC[] THEN
      USE_THEN "cons" (MP_TAC o SPECL [`b:real`; `gb:real->A->real^N^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real`; `x:A`]) THEN
      ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `S = {b | a < b /\
             ?gb:real->A->real^N^N. ricci_flow_from (top,atlas) a b gb /\
                                    (!x. x IN topspace top ==> gb a x = g0 x)}` THEN
  SUBGOAL_THEN `~(S:real->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    REMOVE_THEN "ste" (MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g0:A->real^N^N`;
      `a:real`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. b IN S ==> ricci_flow_from (top,atlas) a b (G:real->A->real^N^N) /\
                   (!x. x IN topspace top ==> G a x = g0 x)`
  (LABEL_TAC "inS") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (G:real->A->real^N^N) a x = g0 x`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `G:real->A->real^N^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `?B. !b. b IN S ==> b <= B` THENL
   [DISJ2_TAC;
    DISJ1_TAC THEN X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `b':real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b':real`] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `B0:real`) THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `T0 = sup(S:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b. b IN S ==> a < b` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `a < T0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `b1:real`) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `b1:real` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b'. a < b' /\ b' < T0 ==> ?b. b IN S /\ b' < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[] `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `T0 <= b'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas) a T0 (G:real->A->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_UNION THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `b':real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `b':real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `B:real` THEN MATCH_MP_TAC(MESON[] `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < T0 /\ x IN topspace top
          ==> mfd_rm_norm atlas ((G:real->A->real^N^N) t) x <= B`
  ASSUME_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ALL_TAC] THEN
  REMOVE_THEN "ext" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `T0:real`;
    `G:real->A->real^N^N`; `B:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b':real` (X_CHOOSE_THEN `g':real->A->real^N^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(b':real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `g':real->A->real^N^N` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `x:A`]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `b' <= T0` MP_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]);;

