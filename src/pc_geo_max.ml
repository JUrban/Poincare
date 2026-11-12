(* ========================================================================= *)
(* pc_geo_max: maximal geodesics.  On a Hausdorff manifold the geodesics     *)
(* with given initial data glue to a maximal one (mfd_geo on mfd_geo_maxint), *)
(* with the shift (group) and rescaling laws, and geodesics on compact time  *)
(* intervals are C^1 curves (mfd_c1_curve of pc_grg_dist) with length        *)
(* (b - a) times the speed.  Its theorems belong to the geodesics API        *)
(* pc_geo_iface.                                                             *)
(*                                                                           *)
(* Gluing geodesics that agree on overlaps.                                  *)
(* ========================================================================= *)

needs "src/pc_geo_local.ml";;

prioritize_real();;
type_invention_error := true;;

(* mfd_vel at t only depends on the curve near t. *)

let GEOM_VEL_LOCAL = prove
 (`!atlas (gamma1:real->A) gamma2 t d.
        &0 < d /\ (!s. abs(s - t) < d ==> gamma1 s = gamma2 s)
        ==> mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gamma1 t =
            mfd_vel atlas gamma2 t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_vel; vector_derivative] THEN
  SUBGOAL_THEN `(gamma1:real->A) t = gamma2 t` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `\s. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                  ((gamma2:real->A) t)) ((gamma1:real->A)(drop s))`;
    EXISTS_TAC `\s. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                  ((gamma2:real->A) t)) ((gamma2:real->A)(drop s))`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[]);;

let MFD_GEO_MAXINT_OUTSIDE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        ~(x IN topspace top) ==> mfd_geo_maxint (top,atlas) g x v = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_geo_maxint] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `t:real` THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `J:real->bool` THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  ASM_CASES_TAC `&0 IN (J:real->bool)` THEN ASM_REWRITE_TAC[] THEN
  DISJ1_TAC THEN X_GEN_TAC `gamma:real->A` THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  ASM_CASES_TAC `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) J` THEN
  ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `~((gamma:real->A)(&0) IN topspace top)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                        `J:real->bool`] THEN ASM_REWRITE_TAC[]);;

(* A family of geodesics on open intervals whose union is an interval, all  *)
(* agreeing with one curve G, makes G a geodesic on the union.               *)

let GEOM_GEODESIC_GLUE = prove
 (`!top atlas (g:A->real^N^N) (fam:(real->bool)->bool)
    (gam:(real->bool)->real->A) (G:real->A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (!J. J IN fam ==> mfd_geodesic (top,atlas) g (gam J) J) /\
        is_realinterval (UNIONS fam) /\
        (!J t. J IN fam /\ t IN J ==> G t = gam J t)
        ==> mfd_geodesic (top,atlas) g G (UNIONS fam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!J. J IN fam ==> real_open J` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_BASIC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!J t. J IN fam /\ t IN J
          ==> ?d. &0 < d /\
                  !s. abs(s - t) < d ==> s IN J /\ (G:real->A) s = gam J s`
  (LABEL_TAC "near") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `J:real->bool` o check (fun th ->
      can (term_match [] `!J. J IN fam ==> real_open J`) (concl th))) THEN
    ASM_REWRITE_TAC[real_open] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_geodesic] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_OPEN_UNIONS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_UNIONS] THEN
    X_GEN_TAC `z:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `J:real->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(J:real->bool) SUBSET UNIONS fam` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `J:real->bool` THEN
      REWRITE_TAC[GSYM REAL_OPEN_IN] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `UNIONS fam INTER J:real->bool = J` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `(gam:(real->bool)->real->A) J` THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gam:(real->bool)->real->A) J`; `J:real->bool`]
      GEOL_GEODESIC_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  EXISTS_TAC `\t. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                     ((G:real->A) t)) c (G t)
                            (mfd_vel atlas G t)` THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `J:real->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  ABBREV_TAC `gamma = (gam:(real->bool)->real->A) J` THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) gamma J` ASSUME_TAC THENL
   [EXPAND_TAC "gamma" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real->A) t = gamma t` ASSUME_TAC THENL
   [EXPAND_TAC "gamma" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real->real^N`) THEN
  USE_THEN "near" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `(J:real->bool) IN fam`) (ASSUME `(t:real) IN J`)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `t:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC)] THEN
  (* on a common ball the two chart velocities agree *)
  SUBGOAL_THEN
   `!s. abs(s - t) < min d1 d2
        ==> s IN J /\ (G:real->A) s = gamma s /\ gamma s IN FST c /\
            chart_jac (chart_at atlas (G s)) c (G s) (mfd_vel atlas G s) =
            (v:real->real^N) s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `s IN J /\ (G:real->A) s = gamma s /\ gamma s IN FST (c:(A->bool)#(A->real^N))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (G:real->A) s =
      mfd_vel atlas gamma s`
    SUBST1_TAC THENL
     [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `d1 - abs(s - t)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(r - t) < d1` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_CHART_VEL_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
    `!t. t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N)) ==> P t`)
    (concl th))) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `chart_jac (chart_at atlas ((gamma:real->A) t)) c (gamma t)
              (mfd_vel atlas (G:real->A) t) =
    (v:real->real^N) t`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LT_MIN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
    EXISTS_TAC `\s. (v:real->real^N)(drop s)`] THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th -> can (term_match []
    `!s. abs(s - t) < min d1 d2 ==> P s`) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The maximal geodesic (MFD_GEO_MAXIMAL, MFD_GEO_MAXIMAL_UNIQUE).           *)
(* ========================================================================= *)

(* A union of intervals with a common point is an interval. *)

let GEOM_UNIONS_INTERVAL = prove
 (`!(fam:(real->bool)->bool) a.
        (!J. J IN fam ==> is_realinterval J /\ a IN J)
        ==> is_realinterval (UNIONS fam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_realinterval; IN_UNIONS] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `J1:real->bool` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `J2:real->bool` STRIP_ASSUME_TAC)
     STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `is_realinterval (J1:real->bool) /\ a IN J1 /\
    is_realinterval (J2:real->bool) /\ a IN J2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `r <= a` THENL
   [EXISTS_TAC `J1:real->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `is_realinterval (J1:real->bool)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:real`; `a:real`] THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `J2:real->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `is_realinterval (J2:real->bool)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `q:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* The geodesics with data (x,v) glue to one geodesic on mfd_geo_maxint. *)

let GEOM_MAXINT_FACTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> &0 IN mfd_geo_maxint (top,atlas) g x v /\
            ?G. mfd_geodesic (top,atlas) g G (mfd_geo_maxint (top,atlas) g x v) /\
                G(&0) = x /\ mfd_vel atlas G (&0) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `fam = {J | &0 IN J /\
               ?gamma. mfd_geodesic (top,atlas) (g:A->real^N^N) gamma J /\
                       gamma(&0) = (x:A) /\ mfd_vel atlas gamma (&0) = v}` THEN
  SUBGOAL_THEN `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v = UNIONS fam`
  SUBST1_TAC THENL [EXPAND_TAC "fam" THEN REWRITE_TAC[mfd_geo_maxint]; ALL_TAC] THEN
  ABBREV_TAC
   `gam = \J. @gamma. mfd_geodesic (top,atlas) (g:A->real^N^N) gamma J /\
                      gamma(&0) = (x:A) /\ mfd_vel atlas gamma (&0) = v` THEN
  SUBGOAL_THEN
   `!J. J IN fam
        ==> &0 IN J /\ mfd_geodesic (top,atlas) (g:A->real^N^N) (gam J) J /\
            gam J (&0) = (x:A) /\ mfd_vel atlas (gam J) (&0) = v`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "fam" THEN EXPAND_TAC "gam" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o SELECT_RULE);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!J1 J2 t. J1 IN fam /\ J2 IN fam /\ t IN J1 /\ t IN J2
              ==> (gam:(real->bool)->real->A) J1 t = gam J2 t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gam:(real->bool)->real->A) J1`;
                   `(gam:(real->bool)->real->A) J2`; `J1:real->bool`;
                   `J2:real->bool`; `&0`] MFD_GEODESIC_UNIQUE) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `G = \t. (gam:(real->bool)->real->A) (@J. J IN fam /\ t IN J) t` THEN
  SUBGOAL_THEN `!J t. J IN fam /\ t IN J ==> (G:real->A) t = gam J t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `?J':real->bool. J' IN fam /\ t IN J'` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEODESIC_EXISTS_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `gamma0:real->A`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `real_interval(--e,e) IN fam` ASSUME_TAC THENL
   [EXPAND_TAC "fam" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `real_interval(--e,e)` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `G:real->A` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOM_GEODESIC_GLUE THEN
    EXISTS_TAC `gam:(real->bool)->real->A` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC GEOM_UNIONS_INTERVAL THEN EXISTS_TAC `&0` THEN
    ASM_MESON_TAC[GEOL_GEODESIC_BASIC];
    SUBGOAL_THEN `&0 IN real_interval(--e,e)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    TRANS_TAC EQ_TRANS
     `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
              ((gam:(real->bool)->real->A) (real_interval(--e,e))) (&0)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `e:real` THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC]);;

let MFD_GEO_MAXIMAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> real_open(mfd_geo_maxint (top,atlas) g x v) /\
            is_realinterval(mfd_geo_maxint (top,atlas) g x v) /\
            &0 IN mfd_geo_maxint (top,atlas) g x v /\
            mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g x v)
                         (mfd_geo_maxint (top,atlas) g x v) /\
            mfd_geo (top,atlas) g x v (&0) = x /\
            mfd_vel atlas (mfd_geo (top,atlas) g x v) (&0) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] GEOM_MAXINT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM mfd_geo] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_SIMP_TAC[]);;

let MFD_GEO_MAXIMAL_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J x v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ &0 IN J /\
        gamma(&0) = x /\ mfd_vel atlas gamma (&0) = v
        ==> J SUBSET mfd_geo_maxint (top,atlas) g x v /\
            !t. t IN J ==> gamma t = mfd_geo (top,atlas) g x v t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `J SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_geo_maxint] THEN
    MATCH_MP_TAC(SET_RULE `(s:real->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) x v`; `J:real->bool`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v`; `&0`]
    MFD_GEODESIC_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* The group law (MFD_GEO_SHIFT) and rescaling (MFD_GEO_RESCALE).            *)
(* ========================================================================= *)

(* Two geodesics on intervals with a common time where they have the same   *)
(* point and velocity glue to a geodesic on the union.                      *)

let GEOM_GLUE_TWO = prove
 (`!top atlas (g:A->real^N^N) (gamma1:real->A) gamma2 J1 J2 s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma1 J1 /\
        mfd_geodesic (top,atlas) g gamma2 J2 /\
        s IN J1 /\ s IN J2 /\ gamma1 s = gamma2 s /\
        mfd_vel atlas gamma1 s = mfd_vel atlas gamma2 s
        ==> mfd_geodesic (top,atlas) g
              (\t. if t IN J1 then gamma1 t else gamma2 t) (J1 UNION J2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma1:real->A`; `gamma2:real->A`;
                 `J1:real->bool`; `J2:real->bool`; `s:real`] MFD_GEODESIC_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `J1 UNION J2 = UNIONS {J1,J2:real->bool}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GEOM_GEODESIC_GLUE THEN
  EXISTS_TAC `\J:real->bool. if J = J1 then (gamma1:real->A) else gamma2` THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC GEOM_UNIONS_INTERVAL THEN EXISTS_TAC `s:real` THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma1:real->A`; `J1:real->bool`]
      GEOL_GEODESIC_BASIC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma2:real->A`; `J2:real->bool`]
      GEOL_GEODESIC_BASIC) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`J:real->bool`; `t:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(t:real) IN J1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `J2:real->bool = J1` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_INTER]]);;

let MFD_GEO_SHIFT = prove
 (`!top atlas (g:A->real^N^N) (x:A) v s.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        s IN mfd_geo_maxint (top,atlas) g x v
        ==> mfd_geo_maxint (top,atlas) g (mfd_geo (top,atlas) g x v s)
              (mfd_vel atlas (mfd_geo (top,atlas) g x v) s) =
            {t | s + t IN mfd_geo_maxint (top,atlas) g x v} /\
            !t. s + t IN mfd_geo_maxint (top,atlas) g x v
                ==> mfd_geo (top,atlas) g (mfd_geo (top,atlas) g x v s)
                      (mfd_vel atlas (mfd_geo (top,atlas) g x v) s) t =
                    mfd_geo (top,atlas) g x v (s + t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  ABBREV_TAC `y = (gam:real->A) s` THEN
  ABBREV_TAC `w = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) s` THEN
  (* the shifted curve *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `M:real->bool`; `&1`; `s:real`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; VECTOR_MUL_LID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{t | t + s IN M} = {t | s + t IN (M:real->bool)}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; REAL_ADD_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. (gam:real->A)(t + s)`;
                 `{t | t + s IN (M:real->bool)}`; `y:A`; `w:real^N`]
    MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ADD_LID] THEN ASM_SIMP_TAC[REAL_ADD_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `M:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
      `!t. t IN {t | s + t IN (M:real->bool)}
           ==> (gam:real->A)(t + s) = mfd_geo (top,atlas) (g:A->real^N^N) y w t`)
      (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[REAL_ADD_SYM]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  (* the converse: glue gam with the back-shifted maximal geodesic from y *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `w:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M' = mfd_geo_maxint (top,atlas) (g:A->real^N^N) y w` THEN
  ABBREV_TAC `gam' = mfd_geo (top,atlas) (g:A->real^N^N) y w` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam':real->A`; `M':real->bool`; `&1`; `--s`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; VECTOR_MUL_LID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `\t. (gam':real->A)(t + --s)`;
                 `M:real->bool`; `{t | t + --s IN (M':real->bool)}`; `s:real`]
    GEOM_GLUE_TWO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_ADD_RINV] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ADD_RINV];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`;
                 `\t. if t IN M then (gam:real->A) t else gam'(t + --s)`;
                 `(M:real->bool) UNION {t | t + --s IN (M':real->bool)}`;
                 `x:A`; `v:real^N`] MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                   `\t. if t IN M then (gam:real->A) t else gam'(t + --s)`;
                   `gam:real->A`; `&0`] GEOM_VEL_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `&0` o GEN_REWRITE_RULE I [real_open] o
      check (fun th -> aconv (concl th) `real_open (M:real->bool)`)) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s + t`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `(s + t) + --s = t`]);;

let MFD_GEO_RESCALE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v a.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> mfd_geo_maxint (top,atlas) g x (a % v) =
            {t | a * t IN mfd_geo_maxint (top,atlas) g x v} /\
            !t. a * t IN mfd_geo_maxint (top,atlas) g x v
                ==> mfd_geo (top,atlas) g x (a % v) t =
                    mfd_geo (top,atlas) g x v (a * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `M:real->bool`; `a:real`; `&0`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. (gam:real->A)(a * t)`;
                 `{t | a * t IN (M:real->bool)}`; `x:A`; `a % v:real^N`]
    MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_RZERO];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
      `!t. t IN {t | a * t IN (M:real->bool)}
           ==> (gam:real->A)(a * t) = mfd_geo (top,atlas) (g:A->real^N^N) x w t`)
      (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `a % v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M' = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x (a % v)` THEN
  ABBREV_TAC `gam' = mfd_geo (top,atlas) (g:A->real^N^N) x (a % v)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam':real->A`; `M':real->bool`; `inv a`; `&0`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. (gam':real->A)(inv a * t)`;
                 `{t | inv a * t IN (M':real->bool)}`; `x:A`; `v:real^N`]
    MFD_GEO_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_MUL_RZERO; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
                 VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV;
                                               REAL_MUL_LID]);;

(* ========================================================================= *)
(* Geodesics as C^1 curves (mfd_c1_curve); their length is (b - a)           *)
(* times the constant speed (MFD_GEODESIC_C1_CURVE).                         *)
(* ========================================================================= *)

(* On a compact time interval inside J the velocity mfd_velocity of
   pc_grg_dist is mfd_vel. *)

let GEOM_VELOCITY_EQ = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J a b t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        real_interval[a,b] SUBSET J /\ a < b /\ t IN real_interval[a,b]
        ==> mfd_velocity atlas gamma a b t = mfd_vel atlas gamma t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t IN J /\ (gamma:real->A) t IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real->real^N`
    (MP_TAC o SPEC `t:real`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_velocity; mfd_vel] THEN
  TRANS_TAC EQ_TRANS `(v:real->real^N) t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN; LIFT_DROP] THEN
    REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[]]);;

let MFD_GEODESIC_C1_CURVE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        real_interval[a,b] SUBSET J /\ a <= b
        ==> mfd_c1_curve (top,atlas) gamma a b /\
            (a < b
             ==> !t. t IN real_interval[a,b]
                     ==> mfd_velocity atlas gamma a b t = mfd_vel atlas gamma t) /\
            mfd_length atlas g gamma a b =
            (b - a) * mfd_tnorm g (gamma a) (mfd_vel atlas gamma a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. a < b /\ t IN real_interval[a,b]
        ==> mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b t =
            mfd_vel atlas gamma t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOM_VELOCITY_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[mfd_c1_curve] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                     `c:(A->bool)#(A->real^N)`] MFD_GEODESIC_SMOOTH) THEN
      ASM_REWRITE_TAC[smooth_map_on] THEN
      DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT2) THEN
      DISCH_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `{lift t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
      X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN EXISTS_TAC `drop s` THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s IN IMAGE lift (real_interval[a,b])` THEN
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN ASM SET_TAC[]];
    ASM_SIMP_TAC[];
    ASM_CASES_TAC `a:real = b` THENL
     [ASM_REWRITE_TAC[REAL_INTEGRAL_REFL; mfd_length; REAL_SUB_REFL; REAL_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_length] THEN
    TRANS_TAC EQ_TRANS
     `real_integral (real_interval[a,b])
        (\t. mfd_tnorm (g:A->real^N^N) ((gamma:real->A) a)
                       (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gamma a))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      REWRITE_TAC[mfd_speed] THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[GSYM mfd_tnorm] THEN
      MATCH_MP_TAC MFD_GEODESIC_SPEED THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a IN real_interval[a,b]` MP_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC]]);;

