(* ========================================================================= *)
(* Restrictions of metrics that are Riemannian only on an open set W, e.g.   *)
(* limit metrics (rfs_limit_metric) on Omega.  If restrict_metric atlas W g  *)
(* is a Riemannian metric of (W, restrict_atlas atlas W), its scalar         *)
(* curvature, its sectional curvatures (up to the chart Jacobian) and its    *)
(* least sectional curvature at points of W are those of g in the full       *)
(* atlas.  MFD_SCALAR_RESTRICT, MFD_SECTIONAL_RESTRICT and                   *)
(* MFD_SEC_MIN_RESTRICT (pc_mfd_restrict) need g Riemannian on the whole     *)
(* manifold.                                                                 *)
(*  - LIM_RESTRICT_RIEMANNIAN(_SUB): a limit metric restricts to a           *)
(*    Riemannian metric on open subsets of Om (the lemmas                    *)
(*    P3H_LIMIT_RESTRICT_RIEMANNIAN(_SUB) of pc_p3_c17vol under new names,   *)
(*    which keeps the load closure of this file small);                      *)
(*  - LIM_SCALAR_RESTRICT_LOCAL, LIM_SECTIONAL_RESTRICT_LOCAL,               *)
(*    LIM_SECTIONAL_SET_RESTRICT_LOCAL, LIM_SEC_MIN_RESTRICT_LOCAL;          *)
(*  - LIM_RESTRICT_CURV: for a limit metric gl on Om, the scalar curvature   *)
(*    and the least sectional curvature of restrict_metric atlas Om gl      *)
(*    equal those of gl on Om (used for the maximal extension at the        *)
(*    singular time, MT Thm 11.19, and for MT Lemma 15.11).                 *)
(* ========================================================================= *)

needs "src/pc_rfs_history.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Restricted limit metrics are Riemannian; scalar, sectional and least      *)
(* sectional curvature of a metric that is Riemannian on W only, read in the *)
(* restricted atlas.                                                         *)
(* ========================================================================= *)

(* Copies of P3H_LIMIT_RESTRICT_RIEMANNIAN_SUB and                           *)
(* P3H_LIMIT_RESTRICT_RIEMANNIAN (pc_p3_c17vol) under new names.             *)

let LIM_RESTRICT_RIEMANNIAN_SUB = prove
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

let LIM_RESTRICT_RIEMANNIAN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) Om ts g gl.
        smooth_manifold_atlas top atlas /\ open_in top Om /\
        rfs_limit_metric (top,atlas) Om ts g gl
        ==> riemannian_metric (restrict_atlas atlas Om) (restrict_metric atlas Om gl)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_RESTRICT_RIEMANNIAN_SUB THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `Om:A->bool`; `ts:real`; `g:real->A->real^3^3`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* Scalar curvature of a metric that is Riemannian on W only.               *)

let LIM_SCALAR_RESTRICT_LOCAL = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
        riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W g)
        ==> mfd_scalar (restrict_atlas atlas W) (restrict_metric atlas W g) x =
            mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[SND] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top W)
                  (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W) /\
                (U INTER W,(phi:A->real^N)) IN restrict_atlas atlas W /\
                (V INTER W,(psi:A->real^N)) IN restrict_atlas atlas W`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lscalar (metric_local (restrict_atlas atlas W) (V INTER W,psi)
                (restrict_metric atlas W (g:A->real^N^N)))
            ((psi:A->real^N) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_CHART_TRANS THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC LSCALAR_LOCAL THEN
  EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER W)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* Sectional curvatures of a metric that is Riemannian on W only.           *)

let LIM_SECTIONAL_RESTRICT_LOCAL = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
        riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W g)
        ==> mfd_sectional (restrict_atlas atlas W) (restrict_metric atlas W g) x u v =
            mfd_sectional atlas g x
              (chart_jac (chart_at (restrict_atlas atlas W) x) (chart_at atlas x) x u)
              (chart_jac (chart_at (restrict_atlas atlas W) x) (chart_at atlas x) x v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `g:A->real^N^N`; `x:A`] MFDR_RESTRICT_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[mfd_sectional] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top W)
                  (restrict_atlas (atlas:((A->bool)#(A->real^N))->bool) W) /\
                (U INTER W,(phi:A->real^N)) IN restrict_atlas atlas W /\
                (V INTER W,(psi:A->real^N)) IN restrict_atlas atlas W`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_RESTRICT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_RESTRICT_ATLAS] THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_jac (U INTER W,phi) (V,psi) (x:A) =
    chart_jac (U INTER W,(phi:A->real^N)) (V INTER W,psi) x`
  SUBST1_TAC THENL [REWRITE_TAC[MFDR_CHART_JAC_RESTRICT_R]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lsectional (metric_local (restrict_atlas atlas W) (V INTER W,psi)
                  (restrict_metric atlas W (g:A->real^N^N)))
               ((psi:A->real^N) x)
               (chart_jac (U INTER W,(phi:A->real^N)) (V INTER W,psi) x u)
               (chart_jac (U INTER W,phi) (V INTER W,psi) x v)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSECTIONAL_CHART_TRANS THEN EXISTS_TAC `subtopology top (W:A->bool)` THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDR_LSECTIONAL_LOCAL THEN
  EXISTS_TAC `IMAGE (psi:A->real^N) (V INTER W)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* The set of sectional curvatures at x is the same in both atlases.        *)

let LIM_SECTIONAL_SET_RESTRICT_LOCAL = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
        riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W g)
        ==> {mfd_sectional (restrict_atlas atlas W) (restrict_metric atlas W g) x u v |
             u,v | ~collinear {vec 0,u,v}} =
            {mfd_sectional atlas g x u v | u,v | ~collinear {vec 0,u,v}}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `W:A->bool`; `x:A`] MFDR_RESTRICT_JAC_ISO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = chart_jac (chart_at (restrict_atlas atlas W) x)
                            (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)
                            (x:A)` THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->real^N` STRIP_ASSUME_TAC) THEN
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
  SUBGOAL_THEN
   `!u v. mfd_sectional (restrict_atlas atlas W) (restrict_metric atlas W g) x u v =
          mfd_sectional atlas (g:A->real^N^N) x ((J:real^N->real^N) u) (J v)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "J" THEN
    MATCH_MP_TAC LIM_SECTIONAL_RESTRICT_LOCAL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(J:real^N->real^N) u`; `(J:real^N->real^N) v`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(K:real^N->real^N) u`; `(K:real^N->real^N) v`] THEN
    ASM_REWRITE_TAC[]]);;

let LIM_SEC_MIN_RESTRICT_LOCAL = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ open_in top W /\ x IN W /\
        riemannian_metric (restrict_atlas atlas W) (restrict_metric atlas W g)
        ==> mfd_sec_min (restrict_atlas atlas W) (restrict_metric atlas W g) x =
            mfd_sec_min atlas g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_sec_min] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIM_SECTIONAL_SET_RESTRICT_LOCAL THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* For a limit metric gl on Om: scalar curvature and least sectional         *)
(* curvature of the restricted limit metric equal those of gl on Om.         *)

let LIM_RESTRICT_CURV = prove
 (`!(top:A topology) atlas Om ts (g:real->A->real^3^3) gl y.
     smooth_manifold_atlas top atlas /\ open_in top Om /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ y IN Om
     ==> mfd_scalar (restrict_atlas atlas Om) (restrict_metric atlas Om gl) y =
         mfd_scalar atlas gl y /\
         mfd_sec_min (restrict_atlas atlas Om) (restrict_metric atlas Om gl) y =
         mfd_sec_min atlas gl y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (restrict_atlas atlas Om)
                  (restrict_metric (atlas:((A->bool)#(A->real^3))->bool) Om gl)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_RESTRICT_RIEMANNIAN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ts:real`; `g:real->A->real^3^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SCALAR_RESTRICT_LOCAL; MATCH_MP_TAC LIM_SEC_MIN_RESTRICT_LOCAL] THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

