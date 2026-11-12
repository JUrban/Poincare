(* ========================================================================= *)
(* pc_geo_flow: the exponential map.  Its domain is open and star-shaped,    *)
(* it is smooth (also jointly in the chart coordinates of the tangent        *)
(* bundle), its differential at 0 is the identity, it is a local             *)
(* diffeomorphism at 0, maximal geodesics with bounded time leave compact    *)
(* sets, and compact manifolds are geodesically complete.  Its theorems      *)
(* belong to the geodesics API pc_geo_iface.                                 *)
(*                                                                           *)
(* Chart states of geodesics and the spray flow.                             *)
(* ========================================================================= *)

needs "src/pc_geo_max.ml";;
(* MFD_PARAM_CHART_INV, MFD_PARAM_PRECOMPOSE, MFD_PARAM_RESTRICT, MFD_PARAM_EQ *)
needs "src/pc_smt_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* Initial data read off a point z = (y,w) of a chart of the tangent bundle, *)
(* and the chart state (position, chart velocity) of a curve at time t.      *)

let geo_cpt = new_definition
 `geo_cpt (c:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum) =
    chart_inv c (fstcart z)`;;

let geo_cvec = new_definition
 `geo_cvec (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
           (z:real^(N,N)finite_sum) =
    chart_jac c (chart_at atlas (chart_inv c (fstcart z)))
              (chart_inv c (fstcart z)) (sndcart z)`;;

let geo_cstate = new_definition
 `geo_cstate (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
             (gamma:real->A) (t:real) =
    pastecart (SND c (gamma t))
              (chart_jac (chart_at atlas (gamma t)) c (gamma t)
                         (mfd_vel atlas gamma t))`;;

(* The two readings are inverse to each other. *)

let GEOF_CSTATE_DATA = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (gamma:real->A) t.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        gamma t IN topspace top /\ gamma t IN FST c
        ==> geo_cpt c (geo_cstate atlas c gamma t) = gamma t /\
            geo_cvec atlas c (geo_cstate atlas c gamma t) = mfd_vel atlas gamma t /\
            geo_cstate atlas c gamma t IN IMAGE (SND c) (FST c) PCROSS (:real^N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[geo_cpt; geo_cvec; geo_cstate; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_IN_PCROSS; IN_UNIV] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `(gamma:real->A) t`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

let GEOF_CDATA_PASTE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (x:A) w.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> geo_cpt c (pastecart (SND c x) w) = x /\
            geo_cvec atlas c (pastecart (SND c x) w) = chart_jac c (chart_at atlas x) x w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[geo_cpt; geo_cvec; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[]);;

(* Real time sets from intervals of real^1. *)

let GEOF_REAL_TIMES = prove
 (`!M:real^1->bool.
        open M /\ is_interval M
        ==> real_open {r | lift r IN M} /\ is_realinterval {r | lift r IN M}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE lift {r | lift r IN M} = M` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[LIFT_DROP];
    ASM_REWRITE_TAC[REAL_OPEN; IS_REALINTERVAL_IS_INTERVAL]]);;

(* The spray flow in a chart from z gives, through the chart, the maximal   *)
(* geodesic with the initial data read off z, and its chart states.          *)

let GEOF_FLOW_MAXGEO = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) z t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas /\
        z IN IMAGE (SND c) (FST c) PCROSS (:real^N) /\
        lift t IN ode_vf_maxint (geo_spray (metric_local atlas c g))
                   (IMAGE (SND c) (FST c) PCROSS (:real^N)) z
        ==> t IN mfd_geo_maxint (top,atlas) g (geo_cpt c z) (geo_cvec atlas c z) /\
            mfd_geo (top,atlas) g (geo_cpt c z) (geo_cvec atlas c z) t IN FST c /\
            geo_cstate atlas c
              (mfd_geo (top,atlas) g (geo_cpt c z) (geo_cvec atlas c z)) t =
            ode_vf_flow (geo_spray (metric_local atlas c g))
              (IMAGE (SND c) (FST c) PCROSS (:real^N)) (lift t) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `X = geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
  ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (D:real^(N,N)finite_sum->bool) /\
    continuously_differentiable 1 D (X:real^(N,N)finite_sum->real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "X"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`]
        GEOL_SPRAY_SMOOTH) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[riemannian_metric]; SIMP_TAC[smooth_map_on]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(N,N)finite_sum->bool`; `z:real^(N,N)finite_sum`]
    ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = ode_vf_maxint (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D z` THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `M:real^1->bool` GEOF_REAL_TIMES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  (* the geodesic of the chart solution *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `{r | lift r IN M}`;
                 `\s. ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                  D s z`] GEOL_SPRAY_GEODESIC) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift r` o check (fun th -> can (term_match []
      `!t. t IN (M:real^1->bool)
           ==> ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D t z IN D /\
               P t`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN SIMP_TAC[GEOL_IN_PCROSS];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \r. chart_inv (c:(A->bool)#(A->real^N))
              (fstcart(ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                   D (lift r) z))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 IN {r | lift r IN (M:real^1->bool)}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN {r | lift r IN (M:real^1->bool)}
                    ==> (G:real->A) r IN FST c /\ G r IN topspace top /\
                        SND (c:(A->bool)#(A->real^N)) (G r) =
                        fstcart(ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                            D (lift r) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `fstcart(ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D (lift r) z)
      IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `lift r` o check (fun th -> can (term_match []
        `!t. t IN (M:real^1->bool)
             ==> ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D t z IN D /\
                 P t`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN SIMP_TAC[GEOL_IN_PCROSS];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `FST (c:(A->bool)#(A->real^N)) SUBSET topspace top` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  (* initial data of G *)
  SUBGOAL_THEN
   `(G:real->A)(&0) = geo_cpt (c:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_REWRITE_TAC[LIFT_NUM; geo_cpt]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r IN {r | lift r IN (M:real^1->bool)}
        ==> chart_jac (chart_at atlas ((G:real->A) r)) c (G r) (mfd_vel atlas G r) =
            sndcart(ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                D (lift r) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_CHART_VEL_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`;
                          `{r | lift r IN (M:real^1->bool)}`] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> can (term_match []
      `!t. lift t IN (M:real^1->bool)
           ==> ((\s. SND (c:(A->bool)#(A->real^N))
                       (chart_inv c (fstcart(ode_vf_flow
                          (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D
                          (lift(drop s)) z))))
                has_vector_derivative sndcart(ode_vf_flow X D (lift t) z))
               (at (lift t))`) (concl th))) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (G:real->A) (&0) =
    geo_cvec atlas (c:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `geo_cpt (c:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum) IN FST c /\
      geo_cpt c z IN topspace top`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> can (term_match []
        `!r. r IN {r | lift r IN (M:real^1->bool)}
             ==> (G:real->A) r IN FST (c:(A->bool)#(A->real^N)) /\ P r`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> can (term_match []
      `!r. r IN {r | lift r IN (M:real^1->bool)}
           ==> chart_jac (chart_at atlas ((G:real->A) r)) (c:(A->bool)#(A->real^N))
                         (G r) (mfd_vel atlas G r) = Q r`) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_NUM] THEN
    ABBREV_TAC `x = geo_cpt (c:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum)` THEN
    DISCH_THEN(MP_TAC o AP_TERM
      `chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (x:A)) x`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXPAND_TAC ["c0"; "x"] THEN REWRITE_TAC[geo_cvec; geo_cpt];
    ALL_TAC] THEN
  (* maximality *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `G:real->A`; `{r | lift r IN (M:real^1->bool)}`;
                 `geo_cpt (c:(A->bool)#(A->real^N)) z`;
                 `geo_cvec atlas (c:(A->bool)#(A->real^N)) z`] MFD_GEO_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `t IN {r | lift r IN (M:real^1->bool)}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP (ASSUME
      `t IN {r | lift r IN (M:real^1->bool)}`)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[geo_cstate] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME
    `t IN {r | lift r IN (M:real^1->bool)}`))]) THEN
  SUBGOAL_THEN
   `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N)
                     (geo_cpt (c:(A->bool)#(A->real^N)) z) (geo_cvec atlas c z)) t =
    mfd_vel atlas (G:real->A) t`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOM_VEL_LOCAL THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open] o
      check (fun th -> can (term_match [] `real_open {r | lift r IN (M:real^1->bool)}`)
                         (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t. t IN {r | lift r IN (M:real^1->bool)}
           ==> (G:real->A) t = mfd_geo (top,atlas) (g:A->real^N^N) x w t`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PASTECART_FST_SND]);;

(* Conversely, the chart states of a maximal geodesic evolve by the spray    *)
(* flow of the chart.                                                        *)

let GEOF_MAXGEO_FLOW = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) x v s h.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas /\ x IN topspace top /\
        s IN mfd_geo_maxint (top,atlas) g x v /\
        mfd_geo (top,atlas) g x v s IN FST c /\
        lift h IN ode_vf_maxint (geo_spray (metric_local atlas c g))
                   (IMAGE (SND c) (FST c) PCROSS (:real^N))
                   (geo_cstate atlas c (mfd_geo (top,atlas) g x v) s)
        ==> s + h IN mfd_geo_maxint (top,atlas) g x v /\
            mfd_geo (top,atlas) g x v (s + h) IN FST c /\
            geo_cstate atlas c (mfd_geo (top,atlas) g x v) (s + h) =
            ode_vf_flow (geo_spray (metric_local atlas c g))
              (IMAGE (SND c) (FST c) PCROSS (:real^N)) (lift h)
              (geo_cstate atlas c (mfd_geo (top,atlas) g x v) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(gam:real->A) s IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `M:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `gam:real->A`; `s:real`]
    GEOF_CSTATE_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `geo_cstate atlas (c:(A->bool)#(A->real^N)) (gam:real->A) s`; `h:real`]
    GEOF_FLOW_MAXGEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `s:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s + h IN (M:real->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `h IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) ((gam:real->A) s)
             (mfd_vel atlas gam s)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. s + t IN M
        ==> mfd_geo (top,atlas) (g:A->real^N^N) ((gam:real->A) s)
                    (mfd_vel atlas gam s) t = gam(s + t)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST_ALL_TAC o C MATCH_MP (ASSUME `s + h IN (M:real->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
    `geo_cstate atlas (c:(A->bool)#(A->real^N)) (G:real->A) h = Q`) (concl th))) THEN
  REWRITE_TAC[geo_cstate] THEN
  SUBGOAL_THEN
   `mfd_vel atlas (gam:real->A) (s + h) =
    mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) (gam s) (mfd_vel atlas gam s)) h`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `M:real->bool`; `&1`; `s:real`]
      MFD_GEODESIC_AFFINE) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; VECTOR_MUL_LID] THEN
    DISCH_THEN(MP_TAC o SPEC `h:real` o CONJUNCT2) THEN
    SUBGOAL_THEN `h + s:real = s + h` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC GEOM_VEL_LOCAL THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s + h` o GEN_REWRITE_RULE I [real_open] o
      check (fun th -> aconv (concl th) `real_open (M:real->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s + r IN (M:real->bool)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Changing the chart of the tangent bundle.                                 *)
(* ========================================================================= *)

(* (y,w) |-> Dh(y) w is smooth when h is. *)

let GEOF_TB_SMOOTH = prove
 (`!U (h:real^N->real^M).
        open U /\ smooth_map_on U h
        ==> smooth_map_on (U PCROSS (:real^N))
              (\z. frechet_derivative h (at (fstcart z)) (sndcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open ((U:real^N->bool) PCROSS (:real^N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\z:real^(N,N)finite_sum.
      vsum (1..dimindex(:N))
        (\i. drop(lift((sndcart z)$i)) %
             frechet_derivative (h:real^N->real^M) (at (fstcart z)) (basis i))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `w:real^N`] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(U:real^N->bool) PCROSS (:real^N)`;
                 `\x:real^1 w:real^M. drop x % w`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[BILINEAR_DROP_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\z:real^(N,N)finite_sum. lift((sndcart z)$i)) =
      (\x:real^N. lift(x$i)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE THEN
    REWRITE_TAC[LINEAR_SNDCART; LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(N,N)finite_sum.
       frechet_derivative (h:real^N->real^M) (at (fstcart z)) (basis i)) =
    (\y. frechet_derivative h (at y) (basis i)) o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    SIMP_TAC[];
    MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]]);;

(* The chart change of the tangent bundle and of chart states. *)

let GEOF_TB_TRANS = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c'.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas
        ==> open (IMAGE (SND c) (FST c INTER FST c') PCROSS (:real^N)) /\
            smooth_map_on (IMAGE (SND c) (FST c INTER FST c') PCROSS (:real^N))
              (\z. pastecart (chart_trans c c' (fstcart z))
                             (frechet_derivative (chart_trans c c') (at (fstcart z))
                                                 (sndcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c:(A->bool)#(A->real^N)))
                (FST c INTER FST (c':(A->bool)#(A->real^N))) PCROSS (:real^N))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GEOF_TB_SMOOTH] THEN
  SUBGOAL_THEN
   `(\z:real^(N,N)finite_sum. chart_trans (c:(A->bool)#(A->real^N)) c' (fstcart z)) =
    chart_trans c c' o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                    (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    SIMP_TAC[];
    MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]]);;

let GEOF_CSTATE_CHANGE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' (gamma:real->A) t.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        gamma t IN topspace top /\ gamma t IN FST c INTER FST c'
        ==> geo_cstate atlas c gamma t IN
              IMAGE (SND c) (FST c INTER FST c') PCROSS (:real^N) /\
            geo_cstate atlas c' gamma t =
            (\z. pastecart (chart_trans c c' (fstcart z))
                           (frechet_derivative (chart_trans c c') (at (fstcart z))
                                               (sndcart z)))
            (geo_cstate atlas c gamma t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[geo_cstate; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_IN_PCROSS; IN_UNIV] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PASTECART_INJ] THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM chart_jac] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `(gamma:real->A) t`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Propagation of smooth dependence on initial data along                    *)
(* maximal geodesics (in chart coordinates of the tangent bundle).          *)
(* ========================================================================= *)

(* At time s, for initial chart states z near z0 in chart c0, the maximal   *)
(* geodesics are defined at s, lie in one chart c, and their chart states   *)
(* at s depend smoothly on z.                                               *)

let geo_flowprop = new_definition
 `geo_flowprop (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (g:A->real^N^N) (c0:(A->bool)#(A->real^N))
               (z0:real^(N,N)finite_sum) (s:real) <=>
    ?N c Z. open N /\ z0 IN N /\ N SUBSET IMAGE (SND c0) (FST c0) PCROSS (:real^N) /\
            c IN atlas /\
            smooth_map_on N (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) /\
            !z. z IN N
                ==> s IN mfd_geo_maxint (top,atlas) g (geo_cpt c0 z)
                                         (geo_cvec atlas c0 z) /\
                    mfd_geo (top,atlas) g (geo_cpt c0 z) (geo_cvec atlas c0 z) s
                    IN FST c /\
                    geo_cstate atlas c
                      (mfd_geo (top,atlas) g (geo_cpt c0 z) (geo_cvec atlas c0 z)) s =
                    Z z`;;

(* Facts about the spray flow of a chart. *)

let GEOF_CHART_FLOW = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas
        ==> open (IMAGE (SND c) (FST c) PCROSS (:real^N)) /\
            continuously_differentiable 1 (IMAGE (SND c) (FST c) PCROSS (:real^N))
              (geo_spray (metric_local atlas c g)) /\
            open (ode_vf_domain (geo_spray (metric_local atlas c g))
                                (IMAGE (SND c) (FST c) PCROSS (:real^N))) /\
            smooth_map_on (ode_vf_domain (geo_spray (metric_local atlas c g))
                                         (IMAGE (SND c) (FST c) PCROSS (:real^N)))
              (\w. ode_vf_flow (geo_spray (metric_local atlas c g))
                     (IMAGE (SND c) (FST c) PCROSS (:real^N)) (fstcart w) (sndcart w)) /\
            (!h z. pastecart h z IN
                   ode_vf_domain (geo_spray (metric_local atlas c g))
                                 (IMAGE (SND c) (FST c) PCROSS (:real^N)) <=>
                   z IN IMAGE (SND c) (FST c) PCROSS (:real^N) /\
                   h IN ode_vf_maxint (geo_spray (metric_local atlas c g))
                          (IMAGE (SND c) (FST c) PCROSS (:real^N)) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)) /\
    smooth_map_on (IMAGE (SND c) (FST c) PCROSS (:real^N))
                  (geo_spray (metric_local atlas c (g:A->real^N^N)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC GEOL_SPRAY_SMOOTH THEN ASM_MESON_TAC[riemannian_metric]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`geo_spray (metric_local atlas (c:(A->bool)#(A->real^N))
                                          (g:A->real^N^N))`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)`]
    ODE_VF_FLOW_SMOOTH) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ode_vf_domain; IN_ELIM_THM; PASTECART_INJ] THEN MESON_TAC[]);;

(* The property at time 0. *)

let GEOF_PROP_ZERO = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        z0 IN IMAGE (SND c0) (FST c0) PCROSS (:real^N)
        ==> geo_flowprop (top,atlas) g c0 z0 (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[geo_flowprop] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0) PCROSS (:real^N)`;
    `c0:(A->bool)#(A->real^N)`; `\z:real^(N,N)finite_sum. z`] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`] GEOF_CHART_FLOW) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; SMOOTH_MAP_ON_ID] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^(N,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `geo_cpt (c0:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum) IN FST c0 /\
    SND c0 (geo_cpt c0 z) = fstcart z`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[geo_cpt] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[GEOL_IN_PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN `geo_cpt (c0:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum) IN topspace top`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `geo_cpt (c0:(A->bool)#(A->real^N)) z`;
                 `geo_cvec atlas (c0:(A->bool)#(A->real^N)) z`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[geo_cstate] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM PASTECART_FST_SND] THEN
  ASM_REWRITE_TAC[PASTECART_INJ] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `geo_cpt (c0:(A->bool)#(A->real^N)) z`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c1 = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                            (geo_cpt (c0:(A->bool)#(A->real^N)) z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c1:(A->bool)#(A->real^N))`; `SND(c1:(A->bool)#(A->real^N))`;
                 `geo_cpt (c0:(A->bool)#(A->real^N)) z`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN
  REWRITE_TAC[geo_cvec; GSYM geo_cpt] THEN ASM_SIMP_TAC[]);;

(* Flowing on in the same chart. *)

let GEOF_PROP_JUMP = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0 s h N c Z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        open N /\ z0 IN N /\ N SUBSET IMAGE (SND c0) (FST c0) PCROSS (:real^N) /\
        c IN atlas /\
        smooth_map_on N (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) /\
        (!z. z IN N
             ==> s IN mfd_geo_maxint (top,atlas) g (geo_cpt c0 z)
                                      (geo_cvec atlas c0 z) /\
                 mfd_geo (top,atlas) g (geo_cpt c0 z) (geo_cvec atlas c0 z) s
                 IN FST c /\
                 geo_cstate atlas c
                   (mfd_geo (top,atlas) g (geo_cpt c0 z) (geo_cvec atlas c0 z)) s =
                 Z z) /\
        pastecart (lift h) (Z z0) IN
        ode_vf_domain (geo_spray (metric_local atlas c g))
                      (IMAGE (SND c) (FST c) PCROSS (:real^N))
        ==> geo_flowprop (top,atlas) g c0 z0 (s + h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_CHART_FLOW) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `X = geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
  ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)` THEN
  ABBREV_TAC `Dom = ode_vf_domain (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D` THEN
  STRIP_TAC THEN
  REWRITE_TAC[geo_flowprop] THEN
  EXISTS_TAC `{z | z IN N /\ pastecart (lift h) ((Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z) IN Dom}` THEN
  EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN
  EXISTS_TAC `(\w. ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D
                               (fstcart w) (sndcart w)) o
              (\z. pastecart (lift h) ((Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z))` THEN
  SUBGOAL_THEN
   `smooth_map_on N
      (\z. pastecart (lift h) ((Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN N /\
              pastecart (lift h) ((Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z) IN Dom}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `N:real^(N,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `Dom:real^(1,(N,N)finite_sum)finite_sum->bool` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `N:real^(N,N)finite_sum->bool` THEN
      CONJ_TAC THENL [SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^(N,N)finite_sum` THEN STRIP_TAC THEN
  UNDISCH_TAC
   `pastecart (lift h) ((Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z) IN Dom` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,N)finite_sum` o check (fun th -> can (term_match []
    `!z. z IN N ==> s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                          (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `geo_cpt (c0:(A->bool)#(A->real^N)) (z:real^(N,N)finite_sum) IN topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[geo_cpt] THEN STRIP_TAC THEN
    SUBGOAL_THEN `fstcart (z:real^(N,N)finite_sum) IN IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`
    ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET; GEOL_IN_PCROSS]; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `geo_cpt (c0:(A->bool)#(A->real^N)) z`;
                 `geo_cvec atlas (c0:(A->bool)#(A->real^N)) z`; `s:real`; `h:real`]
    GEOF_MAXGEO_FLOW) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART]);;

(* Changing the chart in which the states are read. *)

let GEOF_PROP_CHANGE = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0 s c'.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\ c' IN atlas /\
        geo_flowprop (top,atlas) g c0 z0 s /\
        mfd_geo (top,atlas) g (geo_cpt c0 z0) (geo_cvec atlas c0 z0) s IN FST c'
        ==> ?N Z. open N /\ z0 IN N /\
                  N SUBSET IMAGE (SND c0) (FST c0) PCROSS (:real^N) /\
                  smooth_map_on N (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) /\
                  !z. z IN N
                      ==> s IN mfd_geo_maxint (top,atlas) g (geo_cpt c0 z)
                                               (geo_cvec atlas c0 z) /\
                          mfd_geo (top,atlas) g (geo_cpt c0 z) (geo_cvec atlas c0 z) s
                          IN FST c' /\
                          geo_cstate atlas c'
                            (mfd_geo (top,atlas) g (geo_cpt c0 z)
                                     (geo_cvec atlas c0 z)) s =
                          Z z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geo_flowprop] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^(N,N)finite_sum->bool` (X_CHOOSE_THEN
    `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN
    `Z:real^(N,N)finite_sum->real^(N,N)finite_sum` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOF_TB_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `O1 = IMAGE (SND (c:(A->bool)#(A->real^N)))
                         (FST c INTER FST (c':(A->bool)#(A->real^N))) PCROSS (:real^N)` THEN
  ABBREV_TAC
   `Tr = \w:real^(N,N)finite_sum.
          pastecart (chart_trans (c:(A->bool)#(A->real^N)) c' (fstcart w))
                    (frechet_derivative (chart_trans c c') (at (fstcart w)) (sndcart w))` THEN
  STRIP_TAC THEN
  (* the states read in c' *)
  SUBGOAL_THEN
   `!z. z IN N /\ (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z IN O1
        ==> mfd_geo (top,atlas) (g:A->real^N^N) (geo_cpt c0 z) (geo_cvec atlas c0 z) s
            IN FST (c':(A->bool)#(A->real^N)) /\
            geo_cstate atlas c'
              (mfd_geo (top,atlas) g (geo_cpt c0 z) (geo_cvec atlas c0 z)) s =
            (Tr:real^(N,N)finite_sum->real^(N,N)finite_sum) (Z z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(N,N)finite_sum` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,N)finite_sum` o check (fun th ->
      can (term_match []
       `!z. z IN N ==> s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                             (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N)
                      (geo_cpt (c0:(A->bool)#(A->real^N)) z) (geo_cvec atlas c0 z) s` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN FST (c':(A->bool)#(A->real^N))` ASSUME_TAC THENL
     [UNDISCH_TAC `(Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z IN O1` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
        `geo_cstate atlas (c:(A->bool)#(A->real^N)) G s = (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z`)
        (concl th))) THEN
      EXPAND_TAC "O1" THEN
      REWRITE_TAC[geo_cstate; PASTECART_IN_PCROSS; IN_UNIV; IN_IMAGE; IN_INTER] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y':A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y:A = y'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`] THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `geo_cstate atlas (c:(A->bool)#(A->real^N)) G s = (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z`)
      (concl th))) THEN
    EXPAND_TAC "Tr" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N)
                      (geo_cpt (c0:(A->bool)#(A->real^N)) z) (geo_cvec atlas c0 z)`;
                   `s:real`] GEOF_CSTATE_CHANGE) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{z | z IN N /\ (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z IN O1}` THEN
  EXISTS_TAC `(Tr:real^(N,N)finite_sum->real^(N,N)finite_sum) o
              (Z:real^(N,N)finite_sum->real^(N,N)finite_sum)` THEN
  SUBGOAL_THEN
   `open {z | z IN N /\ (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z IN O1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^(N,N)finite_sum` o check (fun th ->
      can (term_match []
       `!z. z IN N ==> s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                             (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `geo_cstate atlas (c:(A->bool)#(A->real^N)) G s = (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z0`)
      (concl th))) THEN
    EXPAND_TAC "O1" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `mfd_geo (top,atlas) (g:A->real^N^N)
                      (geo_cpt (c0:(A->bool)#(A->real^N)) z0) (geo_cvec atlas c0 z0)`;
                   `s:real`] GEOF_CSTATE_CHANGE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O1:real^(N,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `N:real^(N,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    X_GEN_TAC `z:real^(N,N)finite_sum` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

(* Small times for the spray flow of a chart. *)

let GEOF_FLOW_SMALL_TIMES = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) zeta.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
        zeta IN IMAGE (SND c) (FST c) PCROSS (:real^N)
        ==> ?e. &0 < e /\
                !h. abs h < e
                    ==> pastecart (lift h) zeta IN
                        ode_vf_domain (geo_spray (metric_local atlas c g))
                          (IMAGE (SND c) (FST c) PCROSS (:real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_CHART_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`geo_spray (metric_local atlas (c:(A->bool)#(A->real^N))
                                          (g:A->real^N^N))`;
                 `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)`;
                 `zeta:real^(N,N)finite_sum`] ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> can (term_match []
      `open (ode_vf_maxint (X:real^(N,N)finite_sum->real^(N,N)finite_sum) U x)`)
      (concl th))) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; DIST_0] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_LIFT]);;

(* The property propagates to nearby times. *)

let GEOF_PROP_OPEN = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0 s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        geo_flowprop (top,atlas) g c0 z0 s
        ==> ?e. &0 < e /\
                !r. abs(r - s) < e ==> geo_flowprop (top,atlas) g c0 z0 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [geo_flowprop] o check (fun th ->
    can (term_match [] `geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 s`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^(N,N)finite_sum->bool` (X_CHOOSE_THEN
    `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN
    `Z:real^(N,N)finite_sum->real^(N,N)finite_sum` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM((fun th -> MP_TAC(MATCH_MP th (ASSUME `(z0:real^(N,N)finite_sum) IN N`))) o
    check (fun th -> can (term_match []
     `!z. z IN N ==> s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                           (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
  ABBREV_TAC `gam0 = mfd_geo (top,atlas) (g:A->real^N^N)
                       (geo_cpt (c0:(A->bool)#(A->real^N)) z0) (geo_cvec atlas c0 z0)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(gam0:real->A) s IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `gam0:real->A`; `s:real`]
    GEOF_CSTATE_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `(Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z0`]
    GEOF_FLOW_SMALL_TIMES) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `r = s + (r - s)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC GEOF_PROP_JUMP THEN
  MAP_EVERY EXISTS_TAC [`N:real^(N,N)finite_sum->bool`; `c:(A->bool)#(A->real^N)`;
                        `Z:real^(N,N)finite_sum->real^(N,N)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
    `!h. abs h < e ==> pastecart (lift h) ((Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z0) IN D`)
    (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* Near a time z of the maximal interval of z0, the property at a nearby    *)
(* time gives the property at z.                                            *)

let GEOF_PROP_BACK = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0 z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        z0 IN IMAGE (SND c0) (FST c0) PCROSS (:real^N) /\
        z IN mfd_geo_maxint (top,atlas) g (geo_cpt c0 z0) (geo_cvec atlas c0 z0)
        ==> ?e. &0 < e /\
                !r. abs(r - z) < e /\ geo_flowprop (top,atlas) g c0 z0 r
                    ==> geo_flowprop (top,atlas) g c0 z0 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x0 = geo_cpt (c0:(A->bool)#(A->real^N)) (z0:real^(N,N)finite_sum)` THEN
  ABBREV_TAC `v0 = geo_cvec atlas (c0:(A->bool)#(A->real^N)) (z0:real^(N,N)finite_sum)` THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "x0" THEN
    REWRITE_TAC[geo_cpt] THEN
    SUBGOAL_THEN `fstcart (z0:real^(N,N)finite_sum) IN IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`
    ASSUME_TAC THENL [ASM_MESON_TAC[GEOL_IN_PCROSS]; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`; `v0:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x0 v0` THEN
  ABBREV_TAC `gam0 = mfd_geo (top,atlas) (g:A->real^N^N) x0 v0` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(gam0:real->A) z IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `M0:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gam0:real->A) z`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gam0:real->A) z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `gam0:real->A`; `z:real`]
    GEOF_CSTATE_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `zeta = geo_cstate atlas (c:(A->bool)#(A->real^N)) (gam0:real->A) z` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `zeta:real^(N,N)finite_sum`]
    GEOF_FLOW_SMALL_TIMES) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  (* r lies in the maximal interval *)
  SUBGOAL_THEN `r IN (M0:real->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [geo_flowprop] o check (fun th ->
      can (term_match [] `geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 r`) (concl th))) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`N:real^(N,N)finite_sum->bool`; `c1:(A->bool)#(A->real^N)`;
                         `Z:real^(N,N)finite_sum->real^(N,N)finite_sum`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^(N,N)finite_sum` o check (fun th ->
      can (term_match []
       `!z. z IN N ==> r IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                             (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
    ALL_TAC] THEN
  (* the flow from the state at z reaches time r - z *)
  SUBGOAL_THEN
   `lift(r - z) IN
    ode_vf_maxint (geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)))
                  (IMAGE (SND c) (FST c) PCROSS (:real^N)) zeta`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_CHART_FLOW) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`lift(r - z)`; `zeta:real^(N,N)finite_sum`] o
      last o CONJUNCTS) THEN
    MATCH_MP_TAC(TAUT `a ==> (a <=> b /\ d) ==> d`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!h. abs h < e ==> pastecart (lift h) (zeta:real^(N,N)finite_sum) IN D`)
      (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `x0:A`; `v0:real^N`;
                 `z:real`; `r - z:real`] GEOF_MAXGEO_FLOW) THEN
  ASM_REWRITE_TAC[REAL_SUB_ADD2] THEN STRIP_TAC THEN
  (* read the states at time r in the chart c *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `z0:real^(N,N)finite_sum`;
                 `r:real`; `c:(A->bool)#(A->real^N)`] GEOF_PROP_CHANGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N':real^(N,N)finite_sum->bool` (X_CHOOSE_THEN
    `Z':real^(N,N)finite_sum->real^(N,N)finite_sum` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM((fun th -> MP_TAC(MATCH_MP th (ASSUME `(z0:real^(N,N)finite_sum) IN N'`))) o
    check (fun th -> can (term_match []
     `!z. z IN N' ==> r IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                            (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* flowing back from time r to time z *)
  SUBGOAL_THEN
   `pastecart (lift (z - r)) ((Z':real^(N,N)finite_sum->real^(N,N)finite_sum) z0) IN
    ode_vf_domain (geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)))
                  (IMAGE (SND c) (FST c) PCROSS (:real^N))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `ode_vf_flow X D h (zeta:real^(N,N)finite_sum) =
       (Z':real^(N,N)finite_sum->real^(N,N)finite_sum) z0`) (concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_CHART_FLOW) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `X = geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
    ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`X:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(N,N)finite_sum->bool`; `zeta:real^(N,N)finite_sum`]
      ODE_VF_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`X:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                   `D:real^(N,N)finite_sum->bool`; `zeta:real^(N,N)finite_sum`;
                   `lift(r - z)`] ODE_VF_GROUP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
    ASM_REWRITE_TAC[LIFT_SUB] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z = r + (z - r)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC GEOF_PROP_JUMP THEN
  MAP_EVERY EXISTS_TAC [`N':real^(N,N)finite_sum->bool`; `c:(A->bool)#(A->real^N)`;
                        `Z':real^(N,N)finite_sum->real^(N,N)finite_sum`] THEN
  ASM_REWRITE_TAC[]);;

(* The property holds at all times of [0,b] inside the maximal interval of  *)
(* z0 (clopen argument on [0,b]).                                            *)

let GEOF_PROPAGATE = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0 b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        z0 IN IMAGE (SND c0) (FST c0) PCROSS (:real^N) /\ &0 <= b /\
        b IN mfd_geo_maxint (top,atlas) g (geo_cpt c0 z0) (geo_cvec atlas c0 z0)
        ==> !s. s IN real_interval[&0,b] ==> geo_flowprop (top,atlas) g c0 z0 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x0 = geo_cpt (c0:(A->bool)#(A->real^N)) (z0:real^(N,N)finite_sum)` THEN
  ABBREV_TAC `v0 = geo_cvec atlas (c0:(A->bool)#(A->real^N)) (z0:real^(N,N)finite_sum)` THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "x0" THEN
    REWRITE_TAC[geo_cpt] THEN
    SUBGOAL_THEN `fstcart (z0:real^(N,N)finite_sum) IN IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`
    ASSUME_TAC THENL [ASM_MESON_TAC[GEOL_IN_PCROSS]; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`; `v0:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x0 v0` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,b] SUBSET (M0:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval] o
      check (fun th -> aconv (concl th) `is_realinterval (M0:real->bool)`)) THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = {s | s IN real_interval[&0,b] /\
                       geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 s}` THEN
  SUBGOAL_THEN `S = topspace (subtopology euclideanreal (real_interval[&0,b]))`
  MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "S" THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[]] THEN
  MATCH_MP_TAC TOPC_CONNECTED_SPACE_CLOPEN THEN EXISTS_TAC `&0` THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
    EXPAND_TAC "S" THEN SET_TAC[];
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC GEOF_PROP_ZERO THEN
    ASM_REWRITE_TAC[];
    (* S is open in [0,b] *)
    X_GEN_TAC `s:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`;
                   `z0:real^(N,N)finite_sum`; `s:real`] GEOF_PROP_OPEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{r | r IN real_interval[&0,b] /\ abs(r - s) < e}` THEN
    ASM_REWRITE_TAC[GEOL_OPEN_IN_REAL_BALL; IN_ELIM_THM; REAL_SUB_REFL; REAL_ABS_0] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    (* its complement is open in [0,b] *)
    X_GEN_TAC `s:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 s` ASSUME_TAC THENL
     [UNDISCH_TAC `~(s IN real_interval[&0,b] /\
                     geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 s)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`;
                   `z0:real^(N,N)finite_sum`; `s:real`] GEOF_PROP_BACK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET] o check (fun th ->
        can (term_match [] `real_interval[&0,b] SUBSET (M0:real->bool)`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{r | r IN real_interval[&0,b] /\ abs(r - s) < e}` THEN
    ASM_REWRITE_TAC[GEOL_OPEN_IN_REAL_BALL; IN_ELIM_THM; REAL_SUB_REFL; REAL_ABS_0] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 s` THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!r. abs(r - s) < e /\ geo_flowprop (top,atlas) (g:A->real^N^N) c0 z0 r
           ==> geo_flowprop (top,atlas) g c0 z0 s`) (concl th))) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The exponential map: radial behaviour, domain, continuity                 *)
(* and smoothness (also in the chart coordinates of the tangent bundle).     *)
(* ========================================================================= *)

(* Initial data read in the preferred chart at x. *)

let GEOF_CDATA_AT = prove
 (`!top atlas (x:A) (w:real^N).
        smooth_manifold_atlas top atlas /\ x IN topspace top
        ==> geo_cpt (chart_at atlas x) (pastecart (SND (chart_at atlas x) x) w) = x /\
            geo_cvec atlas (chart_at atlas x)
                     (pastecart (SND (chart_at atlas x) x) w) = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `x:A`;
                 `w:real^N`] GEOF_CDATA_PASTE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`; `x:A`]
    CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[]);;

(* The chart form of the exponential map and of its domain. *)

let GEOF_EXP_CHART_DOM = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) z.
        z IN mfd_exp_chart_dom (top,atlas) g c <=>
        z IN IMAGE (SND c) (FST c) PCROSS (:real^N) /\
        &1 IN mfd_geo_maxint (top,atlas) g (geo_cpt c z) (geo_cvec atlas c z)`,
  REWRITE_TAC[mfd_exp_chart_dom; mfd_exp_dom; IN_ELIM_THM; geo_cpt; geo_cvec;
              GEOL_IN_PCROSS; IN_UNIV]);;

let GEOF_EXP_CHART_EQ = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) z.
        mfd_exp_chart (top,atlas) g c z =
        mfd_geo (top,atlas) g (geo_cpt c z) (geo_cvec atlas c z) (&1)`,
  REWRITE_TAC[mfd_exp_chart; mfd_exp; geo_cpt; geo_cvec]);;

(* A map from an open set of real^K that is smooth when read in one chart   *)
(* is smooth.                                                                *)

let GEOF_SMOOTH_MAP_CHART_REP = prove
 (`!top atlas (f:real^K->A) W (c:(A->bool)#(A->real^N)) Fr.
        smooth_manifold_atlas top atlas /\ open W /\ c IN atlas /\
        smooth_map_on W Fr /\
        (!w. w IN W ==> f w IN FST c /\ SND c (f w) = Fr w)
        ==> mfd_smooth_map (open_set_atlas (:real^K)) atlas W f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN
  X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{w | w IN W /\ (f:real^K->A) w IN FST (c':(A->bool)#(A->real^N))} =
    {w | w IN W /\ (Fr:real^K->real^N) w IN
                   IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST c')}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `w:real^K` THEN ASM_CASES_TAC `(w:real^K) IN W` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^K` o check (fun th -> can (term_match []
      `!w. w IN W ==> (f:real^K->A) w IN FST (c:(A->bool)#(A->real^N)) /\
                      SND c (f w) = (Fr:real^K->real^N) w`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(f:real^K->A) w` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `chart_trans (c:(A->bool)#(A->real^N)) c' o (Fr:real^K->real^N)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^K` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID; IN_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^K` o check (fun th -> can (term_match []
      `!w. w IN W ==> (f:real^K->A) w IN FST (c:(A->bool)#(A->real^N)) /\
                      SND c (f w) = (Fr:real^K->real^N) w`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                      (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^K->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* Continuity from a chart representation. *)

let GEOF_CONTINUOUS_CHART_REP = prove
 (`!top atlas (f:real^K->A) W (c:(A->bool)#(A->real^N)) Fr.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        Fr continuous_on W /\
        (!w. w IN W ==> f w IN FST c /\ SND c (f w) = Fr w)
        ==> continuous_map (subtopology euclidean W,top) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) o (Fr:real^K->real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
    X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^K` o check (fun th -> can (term_match []
      `!w. w IN W ==> (f:real^K->A) w IN FST (c:(A->bool)#(A->real^N)) /\
                      SND c (f w) = (Fr:real^K->real^N) w`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^K` o check (fun th -> can (term_match []
        `!w. w IN W ==> (f:real^K->A) w IN FST (c:(A->bool)#(A->real^N)) /\
                        SND c (f w) = (Fr:real^K->real^N) w`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFDD_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]]]);;

(* Local chart representations give openness of the domain, continuity and *)
(* smoothness.                                                              *)

let GEOF_LOCAL_REP_SMOOTH = prove
 (`!top atlas (f:real^K->A) D.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        (!z0. z0 IN D
              ==> ?W c (Fr:real^K->real^N).
                     open W /\ z0 IN W /\ W SUBSET D /\ c IN atlas /\
                     smooth_map_on W Fr /\
                     !z. z IN W ==> f z IN FST c /\ SND c (f z) = Fr z)
        ==> open D /\ continuous_map (subtopology euclidean D,top) f /\
            mfd_smooth_map (open_set_atlas (:real^K)) atlas D f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")) THEN
  SUBGOAL_THEN `open (D:real^K->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN X_GEN_TAC `z0:real^K` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z0:real^K) IN D`))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean D,top) (f:real^K->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    X_GEN_TAC `z0:real^K` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z0:real^K) IN D`))) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`W:real^K->bool`; `c:(A->bool)#(A->real^N)`;
                         `Fr:real^K->real^N`] THEN
    STRIP_TAC THEN EXISTS_TAC `W:real^K->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(D:real^K->bool) INTER W = W` SUBST1_TAC THENL
     [UNDISCH_TAC `(W:real^K->bool) SUBSET D` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GEOF_CONTINUOUS_CHART_REP THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`; `Fr:real^K->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^K))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^K)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^K)topology`; `open_set_atlas (:real^K)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `D:real^K->bool`; `f:real^K->A`] MFDD_SMOOTH_MAP_LOCAL) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `z0:real^K` THEN DISCH_TAC THEN
  USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z0:real^K) IN D`))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:real^K->bool`; `c:(A->bool)#(A->real^N)`;
                       `Fr:real^K->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `W:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GEOF_SMOOTH_MAP_CHART_REP THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `c:(A->bool)#(A->real^N)`;
                        `Fr:real^K->real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* Local chart representations of the exponential map in the chart         *)
(* coordinates of the tangent bundle.                                        *)

let GEOF_EXP_CHART_LOCAL_REP = prove
 (`!top atlas (g:A->real^N^N) (c0:(A->bool)#(A->real^N)) z0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        z0 IN mfd_exp_chart_dom (top,atlas) g c0
        ==> ?W c (Fr:real^(N,N)finite_sum->real^N).
               open W /\ z0 IN W /\ W SUBSET mfd_exp_chart_dom (top,atlas) g c0 /\
               c IN atlas /\ smooth_map_on W Fr /\
               !z. z IN W ==> mfd_exp_chart (top,atlas) g c0 z IN FST c /\
                              SND c (mfd_exp_chart (top,atlas) g c0 z) = Fr z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GEOF_EXP_CHART_DOM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`;
                 `z0:real^(N,N)finite_sum`; `&1`] GEOF_PROPAGATE) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL; geo_flowprop] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^(N,N)finite_sum->bool` (X_CHOOSE_THEN
    `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN
    `Z:real^(N,N)finite_sum->real^(N,N)finite_sum` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`N:real^(N,N)finite_sum->bool`; `c:(A->bool)#(A->real^N)`;
                        `fstcart o (Z:real^(N,N)finite_sum->real^(N,N)finite_sum)`] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FSTCART_OPEN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; GEOF_EXP_CHART_DOM] THEN
    X_GEN_TAC `z:real^(N,N)finite_sum` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,N)finite_sum` o check (fun th ->
        can (term_match []
         `!z. z IN N ==> &1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                                (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    X_GEN_TAC `z:real^(N,N)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,N)finite_sum` o check (fun th ->
      can (term_match []
       `!z. z IN N ==> &1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (geo_cpt c0 z)
                                              (geo_cvec atlas c0 z) /\ P z`) (concl th))) THEN
    ASM_REWRITE_TAC[GEOF_EXP_CHART_EQ; o_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `geo_cstate atlas (c:(A->bool)#(A->real^N)) G (&1) =
       (Z:real^(N,N)finite_sum->real^(N,N)finite_sum) z`) (concl th))) THEN
    REWRITE_TAC[geo_cstate; FSTCART_PASTECART]]);;

(* Local chart representations of the exponential map at x. *)

let GEOF_EXP_LOCAL_REP = prove
 (`!top atlas (g:A->real^N^N) (x:A) v0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v0 IN mfd_exp_dom (top,atlas) g x
        ==> ?W c (Fr:real^N->real^N).
               open W /\ v0 IN W /\ W SUBSET mfd_exp_dom (top,atlas) g x /\
               c IN atlas /\ smooth_map_on W Fr /\
               !w. w IN W ==> mfd_exp (top,atlas) g x w IN FST c /\
                              SND c (mfd_exp (top,atlas) g x w) = Fr w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    GEOF_CDATA_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `y = SND (c0:(A->bool)#(A->real^N)) x` THEN
  DISCH_THEN(LABEL_TAC "cd") THEN
  SUBGOAL_THEN `!w. mfd_exp (top,atlas) (g:A->real^N^N) x w =
                    mfd_exp_chart (top,atlas) g c0 (pastecart (y:real^N) w)`
  (LABEL_TAC "ee") THENL
   [GEN_TAC THEN REWRITE_TAC[GEOF_EXP_CHART_EQ; mfd_exp] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pastecart (y:real^N) (v0:real^N) IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c0`
  ASSUME_TAC THENL
   [REWRITE_TAC[GEOF_EXP_CHART_DOM; PASTECART_IN_PCROSS; IN_UNIV] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "y" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `v0 IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
      REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`;
                 `pastecart (y:real^N) (v0:real^N)`] GEOF_EXP_CHART_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^(N,N)finite_sum->bool` (X_CHOOSE_THEN
    `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN
    `Fr:real^(N,N)finite_sum->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!w:real^N. (\w:real^N. pastecart (y:real^N) w) continuous at w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {w:real^N | pastecart (y:real^N) w IN N}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^N. pastecart (y:real^N) w`;
                   `N:real^(N,N)finite_sum->bool`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{w:real^N | pastecart (y:real^N) w IN N}`; `c:(A->bool)#(A->real^N)`;
    `(Fr:real^(N,N)finite_sum->real^N) o (\w:real^N. pastecart (y:real^N) w)`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `pastecart (y:real^N) (w:real^N) IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c0`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[GEOF_EXP_CHART_DOM; mfd_exp_dom; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `N:real^(N,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[]]);;

(* The radial behaviour of the exponential map. *)

let MFD_EXP_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) v t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> (t % v IN mfd_exp_dom (top,atlas) g x <=>
             t IN mfd_geo_maxint (top,atlas) g x v) /\
            (t IN mfd_geo_maxint (top,atlas) g x v
             ==> mfd_exp (top,atlas) g x (t % v) = mfd_geo (top,atlas) g x v t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_exp_dom; mfd_exp; IN_ELIM_THM; REAL_MUL_RID] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID]);;

(* Openness, continuity and smoothness of the exponential map at x. *)

let GEOF_EXP_ALL = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> open(mfd_exp_dom (top,atlas) g x) /\
            continuous_map
              (subtopology euclidean (mfd_exp_dom (top,atlas) g x),top)
              (mfd_exp (top,atlas) g x) /\
            mfd_smooth_map (open_set_atlas (:real^N)) atlas
              (mfd_exp_dom (top,atlas) g x) (mfd_exp (top,atlas) g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOF_LOCAL_REP_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v0:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC GEOF_EXP_LOCAL_REP THEN ASM_REWRITE_TAC[]);;

let MFD_EXP_DOM = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> open(mfd_exp_dom (top,atlas) g x) /\
            vec 0 IN mfd_exp_dom (top,atlas) g x /\
            (!v t. v IN mfd_exp_dom (top,atlas) g x /\ &0 <= t /\ t <= &1
                   ==> t % v IN mfd_exp_dom (top,atlas) g x) /\
            mfd_exp (top,atlas) g x (vec 0) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(:real) SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) x (vec 0) /\
    !t. mfd_geo (top,atlas) g x (vec 0) t = x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_GEODESIC_CONST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\t:real. (x:A)`; `(:real)`; `x:A`;
                   `vec 0:real^N`] MFD_GEO_MAXIMAL_UNIQUE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0 IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET; IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_exp] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOF_EXP_ALL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N`; `t:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval] o
    check (fun th -> can (term_match [] `is_realinterval (s:real->bool)`) (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
  REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM]);;

let MFD_EXP_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> continuous_map
              (subtopology euclidean (mfd_exp_dom (top,atlas) g x),top)
              (mfd_exp (top,atlas) g x) /\
            mfd_smooth_map (open_set_atlas (:real^N)) atlas
              (mfd_exp_dom (top,atlas) g x) (mfd_exp (top,atlas) g x)`,
  MESON_TAC[GEOF_EXP_ALL]);;

let MFD_EXP_CHART_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas
        ==> open(mfd_exp_chart_dom (top,atlas) g c) /\
            continuous_map
              (subtopology euclidean (mfd_exp_chart_dom (top,atlas) g c),top)
              (mfd_exp_chart (top,atlas) g c) /\
            mfd_smooth_map (open_set_atlas (:real^(N,N)finite_sum)) atlas
              (mfd_exp_chart_dom (top,atlas) g c) (mfd_exp_chart (top,atlas) g c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOF_LOCAL_REP_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z0:real^(N,N)finite_sum` THEN DISCH_TAC THEN
  MATCH_MP_TAC GEOF_EXP_CHART_LOCAL_REP THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The differential of the exponential map at 0.                             *)
(* ========================================================================= *)

(* The chart representation of exp_x in the preferred chart at x is        *)
(* differentiable at 0.                                                     *)

let GEOF_EXP_DIFFERENTIABLE_ZERO = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> (\y. SND (chart_at atlas x) (mfd_exp (top,atlas) g x y))
            differentiable (at (vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_EXP_ALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^N),(\y:real^N. y)) IN open_set_atlas (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^N),(\y:real^N. y))`; `c0:(A->bool)#(A->real^N)`;
                 `mfd_exp_dom (top,atlas) (g:A->real^N^N) x`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`((:real^N),(\y:real^N. y))`; `c0:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((A->bool)#(A->real^N))->bool)
                      W (f:real^N->A)`) (concl th))) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. SND (c0:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x y)) =
    SND c0 o mfd_exp (top,atlas) g x o chart_inv ((:real^N),(\y:real^N. y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{y | y IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                   mfd_exp (top,atlas) g x y IN FST (c0:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let GEOF_LINEAR_DROP_VMUL = prove
 (`!w:real^N. linear (\s:real^1. drop s % w)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. x`; `w:real^N`] LINEAR_VMUL_DROP) THEN
  REWRITE_TAC[LINEAR_ID]);;

(* The differential of exp_x at 0 is the identity. *)

let MFD_EXP_DIFFERENTIAL_ZERO = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (vec 0) = (\h. h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_EXP_DIFFERENTIABLE_ZERO) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `phi = \y. SND (c0:(A->bool)#(A->real^N))
                            (mfd_exp (top,atlas) (g:A->real^N^N) x y)` THEN
  DISCH_TAC THEN
  ABBREV_TAC `D = frechet_derivative (phi:real^N->real^N) (at (vec 0))` THEN
  SUBGOAL_THEN `linear (D:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((phi:real^N->real^N) has_derivative D) (at (vec 0))` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^N` THEN
  (* the derivative along the ray, by the chain rule *)
  SUBGOAL_THEN
   `((\s. (phi:real^N->real^N)(drop s % w)) has_vector_derivative (D:real^N->real^N) w)
    (at (vec 0))`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN
    SUBGOAL_THEN `(\s. (phi:real^N->real^N)(drop s % w)) = phi o (\s. drop s % w)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\s:real^1. drop s % (D:real^N->real^N) w) = D o (\s. drop s % w)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[GEOF_LINEAR_DROP_VMUL];
      REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the derivative along the ray, from the geodesic *)
  SUBGOAL_THEN
   `((\s. (phi:real^N->real^N)(drop s % w)) has_vector_derivative w) (at (vec 0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `w:real^N`] MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x w` THEN
    ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x w` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `M:real->bool`;
                   `c0:(A->bool)#(A->real^N)`; `&0`] MFD_GEODESIC_VEL_CHART) THEN
    ASM_REWRITE_TAC[LIFT_NUM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `&0` o GEN_REWRITE_RULE I [real_open] o
      check (fun th -> can (term_match [] `real_open (M:real->bool)`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC
     [`\s. SND (c0:(A->bool)#(A->real^N)) ((gam:real->A)(drop s))`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_0; NORM_1] THEN DISCH_TAC THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `w:real^N`; `drop s`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x'. abs x' < d ==> x' IN (M:real->bool)`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`\s. (phi:real^N->real^N)(drop s % w)`; `vec 0:real^1`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* exp_x is a diffeomorphism near 0 (MFD_EXP_LOCAL_DIFFEO).                  *)
(* ========================================================================= *)

(* Tangent balls: the quadratic form, openness, comparison with balls. *)

let GEOF_TBALL_ALT = prove
 (`!(g:A->real^N^N) x r.
        &0 < r ==> mfd_tball g x r = {v:real^N | v dot (g x ** v) < r pow 2}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tball; mfd_tnorm; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `r = sqrt(r pow 2)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE]; REWRITE_TAC[SQRT_MONO_LT_EQ]]);;

let GEOF_TBALL_OPEN = prove
 (`!(g:A->real^N^N) x r. &0 < r ==> open(mfd_tball g x r)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOF_TBALL_ALT] THEN
  SUBGOAL_THEN
   `{v:real^N | v dot ((g:A->real^N^N) x ** v) < r pow 2} =
    {v | (\v. lift(v dot (g x ** v))) v IN {y:real^1 | y$1 < r pow 2}}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; LIFT_COMPONENT]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN X_GEN_TAC `w:real^N` THEN
  MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN
  REWRITE_TAC[CONTINUOUS_AT_ID] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let GEOF_TBALL_SUBSET_BALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) d.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ &0 < d
        ==> ?r. &0 < r /\ mfd_tball g x r SUBSET ball(vec 0:real^N,d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `{SND (c0:(A->bool)#(A->real^N)) x}`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_SING; SING_SUBSET; IN_SING] THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `sqrt m * d` THEN ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT] THEN
  REWRITE_TAC[SUBSET; mfd_tball; mfd_tnorm; IN_ELIM_THM; IN_BALL_0] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SND (c0:(A->bool)#(A->real^N)) x`; `v:real^N`] o
    check (fun th -> can (term_match []
     `!y (v:real^N). y = SND (c0:(A->bool)#(A->real^N)) x ==> P y v`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= v dot ((g:A->real^N^N) x ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m * norm(v:real^N) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POW_LE; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `v dot ((g:A->real^N^N) x ** v) < m * d pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `sqrt(v dot ((g:A->real^N^N) x ** v))`; `sqrt m * d`]
      REAL_POW_LT2) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; ARITH_EQ; REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `m * norm(v:real^N) pow 2 < m * d pow 2` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

(* exp_x read in the preferred chart at x near 0. *)

let GEOF_EXP_CHART0 = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> open {v | v IN mfd_exp_dom (top,atlas) g x /\
                      mfd_exp (top,atlas) g x v IN FST (chart_at atlas x)} /\
            vec 0 IN {v | v IN mfd_exp_dom (top,atlas) g x /\
                          mfd_exp (top,atlas) g x v IN FST (chart_at atlas x)} /\
            smooth_map_on {v | v IN mfd_exp_dom (top,atlas) g x /\
                               mfd_exp (top,atlas) g x v IN FST (chart_at atlas x)}
                          (\v. SND (chart_at atlas x) (mfd_exp (top,atlas) g x v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_EXP_ALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^N),(\y:real^N. y)) IN open_set_atlas (:real^N)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^N),(\y:real^N. y))`; `c0:(A->bool)#(A->real^N)`;
                 `mfd_exp_dom (top,atlas) (g:A->real^N^N) x`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`((:real^N),(\y:real^N. y))`; `c0:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((A->bool)#(A->real^N))->bool)
                      W (f:real^N->A)`) (concl th))) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\v. SND (c0:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x v)) =
    SND c0 o mfd_exp (top,atlas) g x o chart_inv ((:real^N),(\y:real^N. y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* exp_x is a diffeomorphism of a tangent ball onto an open set. *)

let MFD_EXP_LOCAL_DIFFEO = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> ?r. &0 < r /\ mfd_inj_ball (top,atlas) g x r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_EXP_CHART0) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `S0 = {v | v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                        mfd_exp (top,atlas) g x v IN FST (c0:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `phi = \v. SND (c0:(A->bool)#(A->real^N))
                            (mfd_exp (top,atlas) (g:A->real^N^N) x v)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the derivative at 0 is the identity *)
  SUBGOAL_THEN `frechet_derivative (phi:real^N->real^N) (at (vec 0)) = (\h. h)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "phi" THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the inverse function theorem *)
  MP_TAC(ISPECL [`phi:real^N->real^N`; `S0:real^N->bool`; `vec 0:real^N`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_ID; DET_I] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `u:real^N->bool`
    (X_CHOOSE_THEN `psi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    check (fun th -> can (term_match [] `diffeomorphism_on t u (phi:real^N->real^N) psi`)
                         (concl th))) THEN
  (* exp on t is the chart inverse of phi *)
  SUBGOAL_THEN
   `!v. v IN t
        ==> mfd_exp (top,atlas) (g:A->real^N^N) x v IN FST (c0:(A->bool)#(A->real^N)) /\
            chart_inv c0 ((phi:real^N->real^N) v) = mfd_exp (top,atlas) g x v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN S0` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S0" THEN EXPAND_TAC "phi" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
      `IMAGE (phi:real^N->real^N) t = u`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* exp is a parametrization on t *)
  SUBGOAL_THEN `mfd_param top atlas t (mfd_exp (top,atlas) (g:A->real^N^N) x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_EQ THEN
    EXISTS_TAC `chart_inv (c0:(A->bool)#(A->real^N)) o (phi:real^N->real^N)` THEN
    ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`;
                          `u:real^N->bool`; `psi:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
      MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  (* a tangent ball inside t *)
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> aconv (concl th) `open (t:real^N->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `d:real`] GEOF_TBALL_SUBSET_BALL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[mfd_inj_ball] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x r SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `S0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S0" THEN SET_TAC[];
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_SIMP_TAC[GEOF_TBALL_OPEN]]);;

(* ========================================================================= *)
(* Uniform existence times, escape from compact sets and                     *)
(* completeness of compact manifolds.                                       *)
(* ========================================================================= *)

(* The tangent quadratic form read in a chart. *)

let GEOF_QUAD_CHART = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) p v.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ p IN FST c /\
        p IN topspace top
        ==> chart_jac (chart_at atlas p) c p v dot
            (metric_local atlas c g (SND c p) ** chart_jac (chart_at atlas p) c p v) =
            v dot (g p ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `linear(chart_jac (c:(A->bool)#(A->real^N))
                     (chart_at (atlas:((A->bool)#(A->real^N))->bool) p) p)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `p:A`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM GRGD_QUAD_CONGR] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `p:A`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

(* Initial data in an arbitrary chart. *)

let GEOF_CDATA_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (y:A) v.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN FST c /\
        y IN topspace top
        ==> geo_cpt c (pastecart (SND c y) (chart_jac (chart_at atlas y) c y v)) = y /\
            geo_cvec atlas c (pastecart (SND c y) (chart_jac (chart_at atlas y) c y v)) =
            v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:A`;
                 `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))
                            (c:(A->bool)#(A->real^N)) y (v:real^N)`] GEOF_CDATA_PASTE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `y:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `y:A`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

(* Uniform existence time near a point for bounded speeds. *)

let GEOF_UNIFORM_TIME = prove
 (`!top atlas (g:A->real^N^N) (x:A) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> ?V e. open_in top V /\ x IN V /\ &0 < e /\
                  !y v t. y IN V /\ mfd_tnorm g y v <= R /\ abs t <= e
                          ==> t IN mfd_geo_maxint (top,atlas) g y v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) x` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
    check (fun th -> aconv (concl th)
      `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`)) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `cball(SND (c:(A->bool)#(A->real^N)) x,rho)`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_CHART_FLOW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`;
    `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)`;
    `cball(SND (c:(A->bool)#(A->real^N)) x,rho) PCROSS
     cball(vec 0:real^N,sqrt(R pow 2 / m))`] ODE_VF_DOMAIN_UNIFORM_TIME) THEN
  ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; PCROSS_MONO; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{p:A | p IN FST (c:(A->bool)#(A->real^N)) /\
                     SND c p IN ball(SND c x,rho)}` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `ball(SND (c:(A->bool)#(A->real^N)) x,rho)`]
      GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; OPEN_BALL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `v:real^N`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `y:A`; `v:real^N`]
    GEOF_QUAD_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:A`; `v:real^N`] GEOF_CDATA_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (y:A))
                            (c:(A->bool)#(A->real^N)) y (v:real^N)` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `pastecart (SND (c:(A->bool)#(A->real^N)) y) (w:real^N)`; `t:real`]
    GEOF_FLOW_MAXGEO) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
    `!x t. x IN (C:real^(N,N)finite_sum->bool) /\ abs(drop t) <= e
           ==> t IN ode_vf_maxint X U x`) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP; PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  (* the chart velocity is bounded *)
  FIRST_X_ASSUM(MP_TAC o SPECL [`SND (c:(A->bool)#(A->real^N)) y`; `w:real^N`] o
    check (fun th -> can (term_match []
     `!y (v:real^N). y IN cball(SND (c:(A->bool)#(A->real^N)) x,rho) ==> P y v`)
     (concl th))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_CBALL_0] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= v dot ((g:A->real^N^N) y ** v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m * norm(w:real^N) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POW_LE; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `v dot ((g:A->real^N^N) y ** v) <= R pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `sqrt(v dot ((g:A->real^N^N) y ** v))`; `R:real`] REAL_POW_LE2) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `mfd_tnorm (g:A->real^N^N) y v <= R` THEN REWRITE_TAC[mfd_tnorm];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Uniform existence time over a compact set. *)

let GEOF_UNIFORM_TIME_COMPACT = prove
 (`!top atlas (g:A->real^N^N) K R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_in top K
        ==> ?e. &0 < e /\
                !y v t. y IN K /\ mfd_tnorm g y v <= R /\ abs t <= e
                        ==> t IN mfd_geo_maxint (top,atlas) g y v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:A. ?V e. x IN topspace top
                ==> open_in top V /\ x IN V /\ &0 < e /\
                    !y v t. y IN V /\ mfd_tnorm (g:A->real^N^N) y v <= R /\ abs t <= e
                            ==> t IN mfd_geo_maxint (top,atlas) g y v`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC GEOF_UNIFORM_TIME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`V:A->A->bool`; `e:A->real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (V:A->A->bool) K` o CONJUNCT2 o
    GEN_REWRITE_RULE I [compact_in] o
    check (fun th -> can (term_match [] `compact_in top (K:A->bool)`) (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `Fs:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (IMAGE (V:A->A->bool) Fs)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `inf (IMAGE (e:A->real) Fs)` THEN
  ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `v:real^N`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z:A. z IN Fs /\ (y:A) IN (V:A->A->bool) z` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (IMAGE (V:A->A->bool) Fs)` THEN
    REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inf (IMAGE (e:A->real) Fs) <= e (z:A)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o check (fun th -> can (term_match []
    `!x:A. x IN topspace top ==> P x`) (concl th))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Maximal geodesics with bounded forward time leave every compact set for *)
(* good.                                                                     *)

let MFD_GEO_ESCAPE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v K b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ compact_in top K /\
        (!t. t IN mfd_geo_maxint (top,atlas) g x v ==> t < b)
        ==> ?t1. t1 IN mfd_geo_maxint (top,atlas) g x v /\
                 !t. t IN mfd_geo_maxint (top,atlas) g x v /\ t1 <= t
                     ==> ~(mfd_geo (top,atlas) g x v t IN K)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `K:A->bool`; `mfd_tnorm (g:A->real^N^N) x v`]
    GEOF_UNIFORM_TIME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `M:real->bool` SUP) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM SET_TAC[];
      EXISTS_TAC `b:real` THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `beta = sup (M:real->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t1. t1 IN M /\ beta - e < t1` STRIP_ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `beta <= beta - e` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!b. (!x. x IN (M:real->bool) ==> x <= b) ==> beta <= b`) (concl th))) THEN
      ASM_MESON_TAC[REAL_NOT_LT];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `M:real->bool`; `t:real`; `&0`]
    MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(gam:real->A) t`; `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) t`;
                                `e:real`] o
    check (fun th -> can (term_match []
      `!y v t. y IN K /\ mfd_tnorm (g:A->real^N^N) y v <= R /\ abs t <= e
               ==> t IN mfd_geo_maxint (top,atlas) g y v`) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t + e <= beta` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x. x IN (M:real->bool) ==> x <= beta`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* Compact manifolds are geodesically complete. *)

let GEOF_COMPACT_NOT_BOUNDED_ABOVE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ x IN topspace top
        ==> ~(!t. t IN mfd_geo_maxint (top,atlas) g x v ==> t < b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `topspace top:A->bool`; `b:real`]
    MFD_GEO_ESCAPE) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t1:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                        `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_SIMP_TAC[]);;

let GEOF_COMPACT_FORWARD = prove
 (`!top atlas (g:A->real^N^N) (x:A) v t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ x IN topspace top /\
        &0 <= t
        ==> t IN mfd_geo_maxint (top,atlas) g x v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`]
    GEOF_COMPACT_NOT_BOUNDED_ABOVE) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[is_realinterval] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`&0`; `s:real`] THEN ASM_REWRITE_TAC[]);;

let MFD_COMPACT_GEO_COMPLETE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_space top /\ x IN topspace top
        ==> mfd_geo_maxint (top,atlas) g x v = (:real) /\
            mfd_exp_dom (top,atlas) g x = (:real^N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v t. t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:real^N`; `t:real`] THEN
    ASM_CASES_TAC `&0 <= t` THENL
     [MATCH_MP_TAC GEOF_COMPACT_FORWARD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `w:real^N`; `--(&1)`] MFD_GEO_RESCALE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `--t`) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) * --t = t`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC GEOF_COMPACT_FORWARD THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EXTENSION; IN_UNIV; mfd_exp_dom; IN_ELIM_THM]);;

(* ========================================================================= *)
(* Uniformly normal neighbourhoods (MFD_UNIFORMLY_NORMAL):                   *)
(* Euclidean preliminaries and the map (y,w) -> (y, exp in the chart).      *)
(* ========================================================================= *)

(* Linear maps are smooth; invertible linear maps are diffeomorphisms. *)

let GEOF_SMOOTH_LINEAR = prove
 (`!s (f:real^M->real^N). open s /\ linear f ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `f:real^M->real^N`]
    SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let GEOF_LINEAR_DIFFEO = prove
 (`!(f:real^N->real^N) g S.
        linear f /\ linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y) /\ open S
        ==> diffeomorphism_on {v | f v IN S} S f g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  SUBGOAL_THEN `open {v | (f:real^N->real^N) v IN S}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GEOF_SMOOTH_LINEAR; IN_ELIM_THM] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* Slices of a diffeomorphism preserving first components. *)

let GEOF_SLICE_DIFFEO = prove
 (`!Tz U (Phi:real^(M,N)finite_sum->real^(M,N)finite_sum) Psi (y:real^M).
        diffeomorphism_on Tz U Phi Psi /\
        (!z. z IN Tz ==> fstcart(Phi z) = fstcart z)
        ==> diffeomorphism_on {w:real^N | pastecart y w IN Tz}
                              {w | pastecart y w IN U}
                              (\w. sndcart(Phi(pastecart y w)))
                              (\w. sndcart(Psi(pastecart y w)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN U ==> (Psi:real^(M,N)finite_sum->real^(M,N)finite_sum) z IN Tz /\
                   fstcart(Psi z) = fstcart z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(M,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Psi:real^(M,N)finite_sum->real^(M,N)finite_sum) z IN Tz`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN Tz ==> (Phi:real^(M,N)finite_sum->real^(M,N)finite_sum) z IN U`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. pastecart (y:real^M) w IN Tz
               ==> (Phi:real^(M,N)finite_sum->real^(M,N)finite_sum) (pastecart y w) =
                   pastecart y (sndcart(Phi(pastecart y w)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. pastecart (y:real^M) w IN U
               ==> (Psi:real^(M,N)finite_sum->real^(M,N)finite_sum) (pastecart y w) =
                   pastecart y (sndcart(Psi(pastecart y w)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. (\w:real^N. pastecart (y:real^M) w) continuous at z`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {w:real^N | pastecart (y:real^M) w IN Tz} /\
                open {w:real^N | pastecart (y:real^M) w IN U}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\w:real^N. pastecart (y:real^M) w`;
                     `Tz:real^(M,N)finite_sum->bool`] CONTINUOUS_OPEN_PREIMAGE_UNIV);
      MP_TAC(ISPECL [`\w:real^N. pastecart (y:real^M) w`;
                     `U:real^(M,N)finite_sum->bool`] CONTINUOUS_OPEN_PREIMAGE_UNIV)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {w:real^N | pastecart (y:real^M) w IN Tz} (\w. pastecart y w) /\
    smooth_map_on {w:real^N | pastecart (y:real^M) w IN U} (\w. pastecart y w)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `sndcart((Psi:real^(M,N)finite_sum->real^(M,N)finite_sum)
                                          (pastecart (y:real^M) (u:real^N)))` THEN
      ASM_MESON_TAC[SNDCART_PASTECART]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN EXISTS_TAC `sndcart((Phi:real^(M,N)finite_sum->real^(M,N)finite_sum)
                                          (pastecart (y:real^M) (u:real^N)))` THEN
      ASM_MESON_TAC[SNDCART_PASTECART]];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    ASM_MESON_TAC[SNDCART_PASTECART];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    ASM_MESON_TAC[SNDCART_PASTECART];
    SUBGOAL_THEN
     `(\w:real^N. sndcart((Phi:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart (y:real^M) w))) =
      sndcart o (Phi o (\w. pastecart y w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `Tz:real^(M,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
    SUBGOAL_THEN
     `(\w:real^N. sndcart((Psi:real^(M,N)finite_sum->real^(M,N)finite_sum)
                            (pastecart (y:real^M) w))) =
      sndcart o (Psi o (\w. pastecart y w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U:real^(M,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]]);;

(* A block lower triangular linear map with identity diagonal block in the *)
(* second component is invertible.                                          *)

let GEOF_TRIANGULAR_INVERTIBLE = prove
 (`!D:real^(M,N)finite_sum->real^N.
        linear D /\ (!k. D(pastecart (vec 0) k) = k)
        ==> ~(det(matrix(\h. pastecart (fstcart h) (D h))) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (\h. pastecart (fstcart h) ((D:real^(M,N)finite_sum->real^N) h))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_PASTECART THEN ASM_REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
  UNDISCH_TAC `det(matrix(\h. pastecart (fstcart h)
                               ((D:real^(M,N)finite_sum->real^N) h))) = &0` THEN
  ASM_SIMP_TAC[DET_MATRIX_EQ_0_LEFT] THEN
  MATCH_MP_TAC LINEAR_INJECTIVE_LEFT_INVERSE THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a. (D:real^(M,N)finite_sum->real^N) a = D(pastecart (fstcart a) (vec 0)) + sndcart a`
  ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
    SUBGOAL_THEN
     `pastecart (fstcart (a:real^(M,N)finite_sum)) (sndcart a) =
      pastecart (fstcart a) (vec 0) + pastecart (vec 0) (sndcart a)`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^(M,N)finite_sum`; `b:real^(M,N)finite_sum`] THEN
  REWRITE_TAC[PASTECART_INJ] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN ASM_REWRITE_TAC[PASTECART_INJ] THEN
  SUBGOAL_THEN
   `(D:real^(M,N)finite_sum->real^N)(pastecart (fstcart (b:real^(M,N)finite_sum)) (vec 0)) +
    sndcart (a:real^(M,N)finite_sum) =
    D(pastecart (fstcart b) (vec 0)) + sndcart b`
  MP_TAC THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[VECTOR_ARITH `x + a:real^N = x + b <=> a = b`]]);;

(* ========================================================================= *)
(* The map (y,w) -> (y, chart exp) near the zero section and                 *)
(* its inverse function theorem.                                            *)
(* ========================================================================= *)

(* The chart exponential read back in the same chart. *)

let GEOF_EXP_CHART_SELF = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas
        ==> open {z | z IN mfd_exp_chart_dom (top,atlas) g c /\
                      mfd_exp_chart (top,atlas) g c z IN FST c} /\
            smooth_map_on {z | z IN mfd_exp_chart_dom (top,atlas) g c /\
                               mfd_exp_chart (top,atlas) g c z IN FST c}
                          (\z. SND c (mfd_exp_chart (top,atlas) g c z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] MFD_EXP_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas euclidean (open_set_atlas (:real^(N,N)finite_sum))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^(N,N)finite_sum)` MFD_EUCLIDEAN_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; open_set_atlas] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((:real^(N,N)finite_sum),(\y:real^(N,N)finite_sum. y)) IN
    open_set_atlas (:real^(N,N)finite_sum)`
  ASSUME_TAC THENL [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^(N,N)finite_sum)topology`;
                 `open_set_atlas (:real^(N,N)finite_sum)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `((:real^(N,N)finite_sum),(\y:real^(N,N)finite_sum. y))`;
                 `c:(A->bool)#(A->real^N)`;
                 `mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c`;
                 `mfd_exp_chart (top,atlas) (g:A->real^N^N) c`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`((:real^(N,N)finite_sum),(\y:real^(N,N)finite_sum. y))`;
    `c:(A->bool)#(A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^(N,N)finite_sum))
                      (atlas:((A->bool)#(A->real^N))->bool)
                      W (f:real^(N,N)finite_sum->A)`) (concl th))) THEN
  ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. SND (c:(A->bool)#(A->real^N)) (mfd_exp_chart (top,atlas) (g:A->real^N^N) c z)) =
    SND c o mfd_exp_chart (top,atlas) g c o
    chart_inv ((:real^(N,N)finite_sum),(\y:real^(N,N)finite_sum. y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The zero section. *)

let GEOF_EXP_CHART_ZERO = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) p.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas /\ p IN FST c /\ p IN topspace top
        ==> pastecart (SND c p) (vec 0) IN mfd_exp_chart_dom (top,atlas) g c /\
            mfd_exp_chart (top,atlas) g c (pastecart (SND c p) (vec 0)) = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))
              (c:(A->bool)#(A->real^N)) p (vec 0) = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `p:A`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN MESON_TAC[LINEAR_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `p:A`; `vec 0:real^N`] GEOF_CDATA_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GEOF_EXP_CHART_DOM; GEOF_EXP_CHART_EQ; PASTECART_IN_PCROSS; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `vec 0 IN mfd_exp_dom (top,atlas) (g:A->real^N^N) p` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    UNDISCH_TAC `mfd_exp (top,atlas) (g:A->real^N^N) p (vec 0) = p` THEN
    REWRITE_TAC[mfd_exp]]);;

(* The fibre derivative of the chart exponential at the zero section over  *)
(* x, in the preferred chart at x, is the identity.                          *)

let GEOF_PHI_DERIV = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> (\z. SND (chart_at atlas x)
                   (mfd_exp_chart (top,atlas) g (chart_at atlas x) z))
            differentiable at (pastecart (SND (chart_at atlas x) x) (vec 0)) /\
            !k. frechet_derivative
                  (\z. SND (chart_at atlas x)
                         (mfd_exp_chart (top,atlas) g (chart_at atlas x) z))
                  (at (pastecart (SND (chart_at atlas x) x) (vec 0)))
                  (pastecart (vec 0) k) = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    GEOF_CDATA_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^N)) x` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_EXP_CHART_SELF) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S1 = {z | z IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c /\
                        mfd_exp_chart (top,atlas) g c z IN FST (c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `Fc = \z. SND (c:(A->bool)#(A->real^N))
                           (mfd_exp_chart (top,atlas) (g:A->real^N^N) c z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `x:A`] GEOF_EXP_CHART_ZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (y0:real^N) (vec 0:real^N) IN (S1:real^(N,N)finite_sum->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fc:real^(N,N)finite_sum->real^N) differentiable at (pastecart (y0:real^N) (vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S1:real^(N,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = frechet_derivative (Fc:real^(N,N)finite_sum->real^N)
                                     (at (pastecart (y0:real^N) (vec 0)))` THEN
  SUBGOAL_THEN
   `((Fc:real^(N,N)finite_sum->real^N) has_derivative D) (at (pastecart (y0:real^N) (vec 0)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. pastecart (y0:real^N) k) has_derivative (\k. pastecart (vec 0) k))
    (at (vec 0:real^N))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`at (vec 0:real^N)`; `\k:real^N. (y0:real^N)`; `\k:real^N. k`;
                   `\h:real^N. vec 0:real^N`; `\h:real^N. h`] HAS_DERIVATIVE_PASTECART) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((Fc:real^(N,N)finite_sum->real^N) o (\k. pastecart (y0:real^N) k)) has_derivative
     ((D:real^(N,N)finite_sum->real^N) o (\k. pastecart (vec 0) k))) (at (vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fc:real^(N,N)finite_sum->real^N) o (\k. pastecart (y0:real^N) k) =
    (\k. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x k))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Fc" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; GEOF_EXP_CHART_EQ; mfd_exp] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\k. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x k))
     has_derivative (\h. h)) (at (vec 0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOF_EXP_DIFFERENTIABLE_ZERO) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^(N,N)finite_sum->real^N) o (\k. pastecart (vec 0) k) = (\h. h)`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC
     [`\k. SND (c:(A->bool)#(A->real^N)) (mfd_exp (top,atlas) (g:A->real^N^N) x k)`;
      `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `(((Fc:real^(N,N)finite_sum->real^N) o (\k. pastecart (y0:real^N) k)) has_derivative
       ((D:real^(N,N)finite_sum->real^N) o (\k. pastecart (vec 0) k))) (at (vec 0))` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; o_THM]]);;

(* The inverse function theorem for (y,w) -> (y, SND c (exp_chart (y,w))). *)

let GEOF_PHI_IFT = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> ?Tz U Psi.
              open Tz /\ pastecart (SND (chart_at atlas x) x) (vec 0) IN Tz /\
              Tz SUBSET {z | z IN mfd_exp_chart_dom (top,atlas) g (chart_at atlas x) /\
                             mfd_exp_chart (top,atlas) g (chart_at atlas x) z
                             IN FST (chart_at atlas x)} /\
              open U /\
              diffeomorphism_on Tz U
                (\z. pastecart (fstcart z)
                       (SND (chart_at atlas x)
                            (mfd_exp_chart (top,atlas) g (chart_at atlas x) z)))
                Psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_PHI_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`] GEOF_EXP_CHART_SELF) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `x:A`] GEOF_EXP_CHART_ZERO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S1 = {z | z IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c /\
                        mfd_exp_chart (top,atlas) g c z IN FST (c:(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC `z0 = pastecart (SND (c:(A->bool)#(A->real^N)) x) (vec 0:real^N)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z0:real^(N,N)finite_sum) IN S1` ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC
   `D = frechet_derivative
          (\z. SND (c:(A->bool)#(A->real^N))
                 (mfd_exp_chart (top,atlas) (g:A->real^N^N) c z)) (at z0)` THEN
  SUBGOAL_THEN `linear (D:real^(N,N)finite_sum->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. pastecart (fstcart z)
             (SND (c:(A->bool)#(A->real^N))
                  (mfd_exp_chart (top,atlas) (g:A->real^N^N) c z))) (at z0) =
    (\h. pastecart (fstcart h) ((D:real^(N,N)finite_sum->real^N) h))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[ETA_AX; LINEAR_FSTCART];
      EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. pastecart (fstcart z)
           (SND (c:(A->bool)#(A->real^N))
                (mfd_exp_chart (top,atlas) (g:A->real^N^N) c z))`;
    `S1:real^(N,N)finite_sum->bool`; `z0:real^(N,N)finite_sum`]
   SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GEOF_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_FSTCART];
      MATCH_MP_TAC GEOF_TRIANGULAR_INVERTIBLE THEN ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

(* ========================================================================= *)
(* Uniformly normal neighbourhoods (MFD_UNIFORMLY_NORMAL).                   *)
(* ========================================================================= *)

(* Uniform radii for the inverse of (y,w) -> (y, SND c (exp_chart (y,w))).  *)

let GEOF_UNORMAL_SETUP = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> ?Tz U Psi r rho.
              &0 < r /\ &0 < rho /\ open Tz /\ open U /\
              Tz SUBSET {z | z IN mfd_exp_chart_dom (top,atlas) g (chart_at atlas x) /\
                             mfd_exp_chart (top,atlas) g (chart_at atlas x) z
                             IN FST (chart_at atlas x)} /\
              diffeomorphism_on Tz U
                (\z. pastecart (fstcart z)
                       (SND (chart_at atlas x)
                            (mfd_exp_chart (top,atlas) g (chart_at atlas x) z)))
                Psi /\
              ball(SND (chart_at atlas x) x,rho) SUBSET
                IMAGE (SND (chart_at atlas x)) (FST (chart_at atlas x)) /\
              (!y w. y IN ball(SND (chart_at atlas x) x,rho) /\
                     w dot (metric_local atlas (chart_at atlas x) g y ** w) < r pow 2
                     ==> pastecart y w IN Tz) /\
              (!y y'. y IN ball(SND (chart_at atlas x) x,rho) /\
                      y' IN ball(SND (chart_at atlas x) x,rho)
                      ==> ?w. w dot (metric_local atlas (chart_at atlas x) g y ** w) <
                              r pow 2 /\
                              pastecart y w IN Tz /\
                              SND (chart_at atlas x)
                                (mfd_exp_chart (top,atlas) g (chart_at atlas x)
                                               (pastecart y w)) = y')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_PHI_IFT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `x:A`] GEOF_EXP_CHART_ZERO) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `E = mfd_exp_chart (top,atlas) (g:A->real^N^N) c` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^N)) x` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ABBREV_TAC `Phi = \z:real^(N,N)finite_sum.
                       pastecart (fstcart z) (SND (c:(A->bool)#(A->real^N)) ((E:real^(N,N)finite_sum->A) z))` THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    check (fun th -> can (term_match []
      `diffeomorphism_on (Tz:real^(N,N)finite_sum->bool) (U:real^(N,N)finite_sum->bool)
         (f:real^(N,N)finite_sum->real^(N,N)finite_sum)
         (h:real^(N,N)finite_sum->real^(N,N)finite_sum)`) (concl th))) THEN
  SUBGOAL_THEN
   `!z. fstcart((Phi:real^(N,N)finite_sum->real^(N,N)finite_sum) z) = fstcart z /\
        sndcart(Phi z) = SND (c:(A->bool)#(A->real^N)) ((E:real^(N,N)finite_sum->A) z)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  (* a ball in Tz around the zero section point *)
  FIRST_ASSUM(MP_TAC o SPEC `pastecart (y0:real^N) (vec 0:real^N)` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> aconv (concl th) `open (Tz:real^(N,N)finite_sum->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ep:real` STRIP_ASSUME_TAC) THEN
  (* a compact coordinate ball and metric bounds *)
  FIRST_ASSUM(MP_TAC o SPEC `y0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL] o
    check (fun th -> aconv (concl th)
      `open (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`)) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `cball(y0:real^N,rho0)`] GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[PAIR; COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `r = sqrt m * ep / &2` THEN
  ABBREV_TAC `rho1 = min rho0 (ep / &2)` THEN
  ABBREV_TAC `dl = r / sqrt M` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; SQRT_POS_LT; REAL_HALF; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho1 /\ &0 < dl` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho1"; "dl"] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; SQRT_POS_LT; REAL_HALF];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 = m * (ep / &2) pow 2 /\ M * dl pow 2 = r pow 2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["dl"; "r"] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; REAL_POW_DIV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y0:real^N,rho1) SUBSET cball(y0,rho0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y0:real^N,rho0)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
    EXPAND_TAC "rho1" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* small tangent vectors at points of the small ball give points of Tz *)
  SUBGOAL_THEN
   `!y w. y IN ball(y0:real^N,rho1) /\
          w dot ((G:real^N->real^N^N) y ** w) < r pow 2
          ==> pastecart y w IN (Tz:real^(N,N)finite_sum->bool)`
  (LABEL_TAC "inT") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th -> can (term_match []
      `ball(pastecart (y0:real^N) (vec 0:real^N),ep) SUBSET Tz`) (concl th))) THEN
    REWRITE_TAC[IN_BALL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(y0:real^N,y) + dist(vec 0:real^N,w)` THEN
    REWRITE_TAC[DIST_PASTECART_LE] THEN
    SUBGOAL_THEN `dist(y0:real^N,y) < ep / &2 /\ dist(vec 0:real^N,w) < ep / &2`
    MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN ball(y0,rho1)` THEN REWRITE_TAC[IN_BALL] THEN
      EXPAND_TAC "rho1" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DIST_0] THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `w:real^N`] o check (fun th ->
      can (term_match [] `!y (v:real^N). y IN cball(y0:real^N,rho0) ==> P y v`)
          (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `m * norm(w:real^N) pow 2 < m * (ep / &2) pow 2` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
    ALL_TAC] THEN
  (* the image of the small product set is an open neighbourhood of (y0,y0) *)
  ABBREV_TAC
   `Q = {z | z IN U /\
             (Psi:real^(N,N)finite_sum->real^(N,N)finite_sum) z IN
             ball(y0:real^N,rho1) PCROSS ball(vec 0:real^N,dl)}` THEN
  SUBGOAL_THEN `open (Q:real^(N,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_PCROSS; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (y0:real^N) y0 IN (Q:real^(N,N)finite_sum->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(Phi:real^(N,N)finite_sum->real^(N,N)finite_sum) (pastecart y0 (vec 0)) =
      pastecart y0 y0`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART];
      ALL_TAC] THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `pastecart (y0:real^N) y0` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> aconv (concl th) `open (Q:real^(N,N)finite_sum->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ep1:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`Tz:real^(N,N)finite_sum->bool`; `U:real^(N,N)finite_sum->bool`;
    `Psi:real^(N,N)finite_sum->real^(N,N)finite_sum`; `r:real`; `min rho1 (ep1 / &2)`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN
  SUBGOAL_THEN `ball(y0:real^N,min rho1 (ep1 / &2)) SUBSET ball(y0,rho1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    REPEAT STRIP_TAC THEN USE_THEN "inT" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `y':real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (y:real^N) y' IN (Q:real^(N,N)finite_sum->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `ball(pastecart (y0:real^N) y0,ep1) SUBSET Q`) (concl th))) THEN
    REWRITE_TAC[IN_BALL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(y0:real^N,y) + dist(y0:real^N,y')` THEN
    REWRITE_TAC[DIST_PASTECART_LE] THEN
    UNDISCH_TAC `(y:real^N) IN ball(y0,min rho1 (ep1 / &2))` THEN
    UNDISCH_TAC `(y':real^N) IN ball(y0,min rho1 (ep1 / &2))` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM; GEOL_IN_PCROSS] THEN
  STRIP_TAC THEN
  ABBREV_TAC `z = (Psi:real^(N,N)finite_sum->real^(N,N)finite_sum) (pastecart y y')` THEN
  SUBGOAL_THEN
   `(z:real^(N,N)finite_sum) IN Tz /\
    (Phi:real^(N,N)finite_sum->real^(N,N)finite_sum) z = pastecart y y'`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "z" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart (z:real^(N,N)finite_sum) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[FSTCART_PASTECART]; ALL_TAC] THEN
  EXISTS_TAC `sndcart (z:real^(N,N)finite_sum)` THEN
  SUBGOAL_THEN `pastecart (y:real^N) (sndcart (z:real^(N,N)finite_sum)) = z`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SNDCART_PASTECART]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `sndcart (z:real^(N,N)finite_sum)`] o
    check (fun th ->
      can (term_match [] `!y (v:real^N). y IN cball(y0:real^N,rho0) ==> P y v`)
          (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `M * norm(sndcart (z:real^(N,N)finite_sum)) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `M * norm(sndcart (z:real^(N,N)finite_sum)) pow 2 < M * dl pow 2`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
    UNDISCH_TAC `sndcart (z:real^(N,N)finite_sum) IN ball(vec 0,dl)` THEN
    REWRITE_TAC[IN_BALL_0];
    ASM_REWRITE_TAC[]]);;

(* Uniformly normal neighbourhoods. *)

let MFD_UNIFORMLY_NORMAL = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> ?W r. open_in top W /\ x IN W /\ &0 < r /\
                  !y. y IN W
                      ==> mfd_inj_ball (top,atlas) g y r /\
                          W SUBSET IMAGE (mfd_exp (top,atlas) g y) (mfd_tball g y r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOF_UNORMAL_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `E = mfd_exp_chart (top,atlas) (g:A->real^N^N) c` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^N)) x` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ABBREV_TAC `Phi = \z:real^(N,N)finite_sum.
                       pastecart (fstcart z)
                                 (SND (c:(A->bool)#(A->real^N)) ((E:real^(N,N)finite_sum->A) z))` THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on] o
    check (fun th -> can (term_match []
      `diffeomorphism_on (Tz:real^(N,N)finite_sum->bool) (U:real^(N,N)finite_sum->bool)
         (f:real^(N,N)finite_sum->real^(N,N)finite_sum)
         (h:real^(N,N)finite_sum->real^(N,N)finite_sum)`) (concl th))) THEN
  SUBGOAL_THEN
   `!z. fstcart((Phi:real^(N,N)finite_sum->real^(N,N)finite_sum) z) = fstcart z /\
        sndcart(Phi z) = SND (c:(A->bool)#(A->real^N)) ((E:real^(N,N)finite_sum->A) z)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN Tz
        ==> z IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c /\
            (E:real^(N,N)finite_sum->A) z IN FST (c:(A->bool)#(A->real^N)) /\
            chart_inv c (SND c (E z)) = E z`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(z:real^(N,N)finite_sum) IN
      {z | z IN mfd_exp_chart_dom (top,atlas) (g:A->real^N^N) c /\
           (E:real^(N,N)finite_sum->A) z IN FST (c:(A->bool)#(A->real^N))}`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{p:A | p IN FST (c:(A->bool)#(A->real^N)) /\ SND c p IN ball(y0,rho)}` THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `ball(y0:real^N,rho)`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; OPEN_BALL];
    ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the linear chart change at p and its inverse *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `p:A`] CHART_JAC_INVERSE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `p:A`] CHART_JAC_INVERSE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `p:A`] CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `p:A`] CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `p:A`] GEOF_QUAD_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `p:A`] GEOF_CDATA_CHART) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN
  ABBREV_TAC `y = SND (c:(A->bool)#(A->real^N)) p` THEN
  ABBREV_TAC `L = chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))
                            (c:(A->bool)#(A->real^N)) p` THEN
  ABBREV_TAC `J = chart_jac (c:(A->bool)#(A->real^N))
                            (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)) p` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!v. mfd_exp (top,atlas) (g:A->real^N^N) p v =
        (E:real^(N,N)finite_sum->A) (pastecart (y:real^N) ((L:real^N->real^N) v))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "E" THEN REWRITE_TAC[GEOF_EXP_CHART_EQ; mfd_exp] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN mfd_tball (g:A->real^N^N) p r <=> v dot (g p ** v) < r pow 2`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GEOF_TBALL_ALT; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN mfd_tball (g:A->real^N^N) p r
        ==> pastecart (y:real^N) ((L:real^N->real^N) v) IN Tz`
  (LABEL_TAC "tb") THENL
   [X_GEN_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!y w. y IN ball(y0:real^N,rho) /\ w dot ((G:real^N->real^N^N) y ** w) < r pow 2
             ==> pastecart y w IN (Tz:real^(N,N)finite_sum->bool)`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    (* W is inside the image of the tangent ball *)
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `SND (c:(A->bool)#(A->real^N)) q`] o
      check (fun th -> can (term_match []
        `!y y'. y IN ball(y0:real^N,rho) /\ y' IN ball(y0,rho) ==> P y y'`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(J:real^N->real^N) w` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y:real^N) (w:real^N)` o check (fun th ->
      can (term_match [] `!z. z IN (Tz:real^(N,N)finite_sum->bool) ==> P z`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[mfd_inj_ball] THEN CONJ_TAC THENL
   [(* the tangent ball lies in the domain of exp *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "tb" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(v:real^N) IN mfd_tball (g:A->real^N^N) p r`))) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (y:real^N) ((L:real^N->real^N) v)` o
      check (fun th -> can (term_match []
        `!z. z IN (Tz:real^(N,N)finite_sum->bool) ==> P z`) (concl th))) THEN
    ASM_REWRITE_TAC[GEOF_EXP_CHART_DOM; mfd_exp_dom; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* exp at p is a parametrization of the tangent ball *)
  ABBREV_TAC `S = {w:real^N | pastecart (y:real^N) w IN Tz}` THEN
  ABBREV_TAC `S' = {w:real^N | pastecart (y:real^N) w IN U}` THEN
  MP_TAC(ISPECL [`Tz:real^(N,N)finite_sum->bool`; `U:real^(N,N)finite_sum->bool`;
                 `Phi:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                 `Psi:real^(N,N)finite_sum->real^(N,N)finite_sum`; `y:real^N`]
    GEOF_SLICE_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (S:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^N`; `J:real^N->real^N`; `S:real^N->bool`]
    GEOF_LINEAR_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{v | (L:real^N->real^N) v IN S}`; `S:real^N->bool`; `S':real^N->bool`;
                 `L:real^N->real^N`; `J:real^N->real^N`;
                 `\w:real^N. sndcart((Phi:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                      (pastecart (y:real^N) w))`;
                 `\w:real^N. sndcart((Psi:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                      (pastecart (y:real^N) w))`]
    DIFFEOMORPHISM_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(S':real^N->bool) SUBSET IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S'" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?z. z IN Tz /\
          pastecart (y:real^N) (u:real^N) = (Phi:real^(N,N)finite_sum->real^(N,N)finite_sum) z`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `u = SND (c:(A->bool)#(A->real^N)) ((E:real^(N,N)finite_sum->A) z)`
    SUBST1_TAC THENL [ASM_MESON_TAC[SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param top atlas {v | (L:real^N->real^N) v IN S}
      (chart_inv (c:(A->bool)#(A->real^N)) o
       ((\w:real^N. sndcart((Phi:real^(N,N)finite_sum->real^(N,N)finite_sum)
                              (pastecart (y:real^N) w))) o L))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `S':real^N->bool`;
      `(J:real^N->real^N) o
       (\w:real^N. sndcart((Psi:real^(N,N)finite_sum->real^(N,N)finite_sum)
                             (pastecart (y:real^N) w)))`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
      MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC
   `chart_inv (c:(A->bool)#(A->real^N)) o
    ((\w:real^N. sndcart((Phi:real^(N,N)finite_sum->real^(N,N)finite_sum)
                           (pastecart (y:real^N) w))) o (L:real^N->real^N))` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `{v | (L:real^N->real^N) v IN S}` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC GEOF_TBALL_OPEN THEN FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN USE_THEN "tb" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "tb" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(v:real^N) IN mfd_tball (g:A->real^N^N) p r`))) THEN
    DISCH_TAC THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]]);;

