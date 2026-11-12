(* ========================================================================= *)
(* pc_geo_hr: the Hopf-Rinow theorem.  Local Hopf-Rinow                      *)
(* (MFD_LOCAL_HOPF_RINOW; Milnor, Morse Theory, Lemma 10.9), minimizing      *)
(* geodesics from a point with total exponential map, metric completeness    *)
(* implies geodesic completeness, and the Hopf-Rinow equivalences.  Its      *)
(* theorems belong to the geodesics API pc_geo_iface.                        *)
(*                                                                           *)
(* Continuity of the distance, spheres in T_xM, exit points.                 *)
(* ========================================================================= *)

needs "src/pc_geo_dist.ml";;

prioritize_real();;
type_invention_error := true;;

(* The distance to a fixed point is continuous along continuous maps. *)

let GEOH_DIST_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (Z:B topology) (h:B->A) y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ continuous_map (Z,top) h /\
        (!z. z IN topspace Z ==> mfd_joinable (top,atlas) (h z) y)
        ==> continuous_map (Z,euclideanreal)
                           (\z. mfd_dist (top,atlas) g (h z) y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; CONTINUOUS_MAP_TO_METRIC] THEN
  REWRITE_TAC[IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  X_GEN_TAC `z0:B` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:B->A) z0 IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o
      check (fun th -> can (term_match [] `continuous_map (Z,top:A topology) (h:B->A)`)
                           (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(h:B->A) z0`; `e:real`] GRGD_DIST_SMALL_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{z | z IN topspace Z /\ (h:B->A) z IN T0}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((h:B->A) z0) (h z) /\
                mfd_dist (top,atlas) (g:A->real^N^N) (h z0) (h z) < e`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((h:B->A) z) (h z0)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(h:B->A) z0`; `(h:B->A) z`; `y:A`]
    MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(h:B->A) z`; `(h:B->A) z0`; `y:A`]
    MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(h:B->A) z0`; `(h:B->A) z`] MFD_DIST_SYM) THEN
  ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Spheres for |.|_x. *)

let GEOH_SPHERE = prove
 (`!top atlas (g:A->real^N^N) (x:A) d.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ &0 < d
        ==> compact {w:real^N | mfd_tnorm g x w = d} /\
            ~({w:real^N | mfd_tnorm g x w = d} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{w:real^N | mfd_tnorm (g:A->real^N^N) x w = d} =
      {w | mfd_tnorm g x w <= d} DIFF mfd_tball g x d`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; mfd_tball] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_DIFF THEN ASM_SIMP_TAC[GEOF_TBALL_OPEN] THEN
    MATCH_MP_TAC GEOD_TCBALL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_tnorm (g:A->real^N^N) x (basis 1:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ ~(a = &0) ==> &0 < a`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `basis 1:real^N`] GEOD_TNORM_EQ_0) THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `(d / mfd_tnorm (g:A->real^N^N) x (basis 1:real^N)) % basis 1:real^N` THEN
  ASM_REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_DIV_RMUL; REAL_LT_IMP_NZ]);;

(* A C^1 curve from x on [0,1] which leaves exp_x(tball d) meets the image  *)
(* of the sphere of radius d at a first time t1.                            *)

let GEOH_EXIT_POINT = prove
 (`!top atlas (g:A->real^N^N) (x:A) r d (gamma:real->A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_inj_ball (top,atlas) g x r /\ &0 < d /\ d < r /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
        (?t. t IN real_interval[&0,&1] /\
             ~(gamma t IN IMAGE (mfd_exp (top,atlas) g x) (mfd_tball g x d)))
        ==> ?t1 w. &0 < t1 /\ t1 <= &1 /\ mfd_tnorm g x w = d /\
                   gamma t1 = mfd_exp (top,atlas) g x w /\
                   (!s. &0 <= s /\ s < t1
                        ==> gamma s IN IMAGE (mfd_exp (top,atlas) g x)
                                             (mfd_tball g x d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x d SUBSET mfd_tball g x r` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x) (mfd_tball g x d))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`atlas:((A->bool)#(A->real^N))->bool`; `mfd_tball (g:A->real^N^N) x r`] THEN
    ASM_SIMP_TAC[GEOF_TBALL_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x) (mfd_tball g x d)`]
    GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
      ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                        {v | mfd_tnorm g x v <= d}`; `t1:real`]
    GRGD_CLOSED_LEFT_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_c1_curve];
      MATCH_MP_TAC GEOD_EXP_IMAGE_CLOSED THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(gamma:real->A) u IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                   (mfd_tball g x d)`
      MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t
                             ==> (y:A) IN IMAGE (f:real^N->A) s ==> y IN IMAGE f t`) THEN
      REWRITE_TAC[SUBSET; mfd_tball; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[IN_IMAGE; IN_ELIM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t1:real`; `w:real^N`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `~((gamma:real->A) t1 IN IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x)
                                  (mfd_tball g x d))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM]);;

(* Milnor's Lemma 10.9, first step: on the sphere of radius d < d(q,y) in a *)
(* normal ball at q there is a point w with d(exp_q w,y) = d(q,y) - d.       *)

let GEOH_SPHERE_MIN = prove
 (`!top atlas (g:A->real^N^N) (q:A) d0 d y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ q IN topspace top /\
        mfd_inj_ball (top,atlas) g q d0 /\ &0 < d /\ d < d0 /\
        mfd_joinable (top,atlas) q y /\ d < mfd_dist (top,atlas) g q y
        ==> ?w. mfd_tnorm g q w = d /\
                mfd_dist (top,atlas) g (mfd_exp (top,atlas) g q w) y =
                mfd_dist (top,atlas) g q y - d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) q d0`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) q`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `E = mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) q` THEN
  ABBREV_TAC `rho = mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) q y` THEN
  SUBGOAL_THEN
   `!w. mfd_tnorm (g:A->real^N^N) q w < d0
        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) q ((E:real^N->A) w) /\
            mfd_dist (top,atlas) g q (E w) = mfd_tnorm g q w /\
            mfd_joinable (top,atlas) (E w) y`
  (LABEL_TAC "sph") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `d0:real`; `w:real^N`] MFD_EXP_DIST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `q:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `d:real`] GEOH_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean {w:real^N | mfd_tnorm (g:A->real^N^N) q w = d},
                    euclideanreal)
                   (\w. mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) g
                          ((E:real^N->A) w) y)`
  MP_TAC THENL
   [MATCH_MP_TAC GEOH_DIST_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `mfd_tball (g:A->real^N^N) q d0` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; mfd_tball] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      USE_THEN "sph" (MP_TAC o SPEC `w:real^N`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\w. mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                        ((E:real^N->A) w) y`;
                 `{w:real^N | mfd_tnorm (g:A->real^N^N) q w = d}`]
    CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  EXISTS_TAC `w0:real^N` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "sph" (MP_TAC o SPEC `w0:real^N`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `(E:real^N->A) w0`; `y:A`]
      MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  (* the minimum is at most rho - d *)
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
      mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma (&0) (&1) /\
      gamma(&0) = (q:A) /\ gamma(&1) = y}`;
    `d + mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             ((E:real^N->A) w0) y`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      ASM_MESON_TAC[mfd_joinable];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE];
      REWRITE_TAC[GSYM mfd_dist] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GRGD_IN_LENGTHS] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `d0:real`; `d:real`; `gamma:real->A`]
    GEOH_EXIT_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[IN_IMAGE; mfd_tball; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "sph" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `y = (E:real^N->A) w` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t1:real`; `&1`]
    MFD_LENGTH_COMBINE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t1:real`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `t1:real`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "sph" (MP_TAC o SPEC `w1:real^N`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "min" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `mfd_tnorm (g:A->real^N^N) q w1 = d`))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Unit speed rays and the extension step of Milnor's Lemma                  *)
(* 10.9.                                                                     *)
(* ========================================================================= *)

(* The maximal geodesic t |-> exp_x(t u) for |u|_x = 1 on [0,R]. *)

let GEOH_RAY_FACTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) u R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_tnorm g x u = &1 /\
        (!t. &0 <= t /\ t <= R ==> t % u IN mfd_exp_dom (top,atlas) g x)
        ==> real_interval[&0,R] SUBSET mfd_geo_maxint (top,atlas) g x u /\
            (!t. &0 <= t /\ t <= R
                 ==> mfd_geo (top,atlas) g x u t = mfd_exp (top,atlas) g x (t % u)) /\
            (!t. t IN mfd_geo_maxint (top,atlas) g x u
                 ==> mfd_geo (top,atlas) g x u t IN topspace top /\
                     mfd_tnorm g (mfd_geo (top,atlas) g x u t)
                       (mfd_vel atlas (mfd_geo (top,atlas) g x u) t) = &1) /\
            (!a b. &0 <= a /\ a <= b /\ b <= R
                   ==> mfd_c1_curve (top,atlas) (mfd_geo (top,atlas) g x u) a b /\
                       mfd_length atlas g (mfd_geo (top,atlas) g x u) a b = b - a /\
                       mfd_joinable (top,atlas) (mfd_geo (top,atlas) g x u a)
                                                (mfd_geo (top,atlas) g x u b) /\
                       mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u a)
                                (mfd_geo (top,atlas) g x u b) <= b - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= R
        ==> t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u /\
            mfd_geo (top,atlas) g x u t = mfd_exp (top,atlas) g x (t % u)`
  (LABEL_TAC "ray") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_interval[&0,R] SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "ray" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&0 <= t /\ t <= R`)]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u
        ==> mfd_geo (top,atlas) g x u t IN topspace top /\
            mfd_tnorm g (mfd_geo (top,atlas) g x u t)
              (mfd_vel atlas (mfd_geo (top,atlas) g x u) t) = &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th -> can (term_match []
          `mfd_geodesic (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x u)
                        (mfd_geo_maxint (top,atlas) g x u)`) (concl th))) THEN
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x u`;
                     `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`; `t:real`; `&0`]
        MFD_GEODESIC_SPEED) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `real_interval[a,b] SUBSET mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,R]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x u`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u` ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[a,b] SUBSET
                 mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RID; MFD_C1_CURVE_JOINABLE] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x u`;
                 `a:real`; `b:real`] MFD_DIST_LE_LENGTH) THEN
  ASM_SIMP_TAC[REAL_MUL_RID]);;

(* A broken radial path p -> q -> z of length d(p,z) inside a normal ball   *)
(* at p is unbroken: z lies on the ray from p through q.                     *)

let GEOH_BROKEN_RADIAL = prove
 (`!top atlas (g:A->real^N^N) (p:A) dd up eta d (q:A) (w0:real^N) (z:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ p IN topspace top /\
        mfd_inj_ball (top,atlas) g p dd /\ mfd_tnorm g p up = &1 /\
        &0 < eta /\ &0 < d /\ eta + d < dd /\
        q = mfd_exp (top,atlas) g p (eta % up) /\ q IN topspace top /\
        (!t. &0 <= t /\ t <= &1 ==> t % w0 IN mfd_exp_dom (top,atlas) g q) /\
        mfd_tnorm g q w0 = d /\ z = mfd_exp (top,atlas) g q w0 /\
        mfd_joinable (top,atlas) p z /\ mfd_dist (top,atlas) g p z = eta + d
        ==> z = mfd_exp (top,atlas) g p ((eta + d) % up)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `q:A`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `z:A`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_tball (g:A->real^N^N) p dd`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) p`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* z = exp_p w with |w|_p = eta + d *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `dd:real`] MFD_EXP_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z:A` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p w = eta + d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `dd:real`; `w:real^N`] MFD_EXP_DIST) THEN
    UNDISCH_TAC `(w:real^N) IN mfd_tball (g:A->real^N^N) p dd` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z = mfd_exp (top,atlas) (g:A->real^N^N) p w` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the two radial pieces *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `eta % up:real^N`] GEOD_RADIAL_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `mfd_tball (g:A->real^N^N) p dd SUBSET
                          mfd_exp_dom (top,atlas) g p`) (concl th))) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    SUBGOAL_THEN `abs t * abs eta * &1 <= eta` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < eta ==> abs eta = eta`;
                   REAL_ARITH `&0 <= t ==> abs t = t`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `w0:real^N`] GEOD_RADIAL_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s1 = mfd_geo (top,atlas) (g:A->real^N^N) p (eta % up)` THEN
  ABBREV_TAC `s2 = mfd_geo (top,atlas) (g:A->real^N^N) q w0` THEN
  SUBGOAL_THEN `(s1:real->A)(&1) = s2(&0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s1:real->A`; `s2:real->A`] GRGD_CONCAT_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s1:real->A`; `s2:real->A`] GRGD_CONCAT_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the equality case at p *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `dd:real`; `w:real^N`;
                 `grgd_concat (s1:real->A) s2`] MFD_EXP_DIST_EQUALITY) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN mfd_tball (g:A->real^N^N) p dd` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < eta ==> abs eta = eta`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `grgd_concat (s1:real->A) s2 (&1 / &2) = q` ASSUME_TAC THENL
   [REWRITE_TAC[grgd_concat; grgd_ss] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* injectivity of exp_p *)
  SUBGOAL_THEN `s % (w:real^N) = eta % up` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `s % (w:real^N) IN mfd_tball (g:A->real^N^N) p dd /\ eta % up IN mfd_tball g p dd`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < eta ==> abs eta = eta`;
                   REAL_ARITH `&0 <= s ==> abs s = s`] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `eta + d` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(e':A->real^N) (mfd_exp (top,atlas) (g:A->real^N^N) p (s % w)) =
      e' (mfd_exp (top,atlas) g p (eta % up))`
    MP_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * (eta + d) = eta` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `mfd_tnorm (g:A->real^N^N) p`) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < eta ==> abs eta = eta`;
                 REAL_ARITH `&0 <= s ==> abs s = s`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) = (eta + d) % up` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= s /\ ~(s = &0) ==> &0 < s`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `s * (eta + d) = eta` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LCANCEL]
     `~(s = &0) /\ s % (w:real^N) = s % v ==> w = v`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* The extension step: if t |-> exp_x(t u) realizes d(.,y) = R - t at T,   *)
(* it does so a little further.                                             *)

let GEOH_EXTEND = prove
 (`!top atlas (g:A->real^N^N) (x:A) u y R tt.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_tnorm g x u = &1 /\
        (!t. &0 <= t /\ t <= R ==> t % u IN mfd_exp_dom (top,atlas) g x) /\
        mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y = R /\
        &0 < tt /\ tt < R /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u tt) y = R - tt
        ==> ?d. &0 < d /\ tt + d <= R /\
                mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u (tt + d)) y =
                R - (tt + d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `R:real`] GEOH_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "exp")
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") (LABEL_TAC "seg")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ga = mfd_geo (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u` THEN
  ABBREV_TAC `I0 = mfd_geo_maxint (top,atlas:((A->bool)#(A->real^N))->bool)
                     (g:A->real^N^N) x u` THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= R ==> t IN I0` (LABEL_TAC "inI") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `real_interval[&0,R] SUBSET I0` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tt:real) IN I0` ASSUME_TAC THENL
   [USE_THEN "inI" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(ga:real->A) tt IN topspace top` ASSUME_TAC THENL
   [USE_THEN "unit" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(tt:real) IN I0`)]); ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x ((ga:real->A) tt)`
  ASSUME_TAC THENL
   [USE_THEN "seg" (MP_TAC o SPECL [`&0`; `tt:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((ga:real->A) tt) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  (* a uniformly normal neighbourhood of q = ga tt *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(ga:real->A) tt`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `dd:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))) THEN
  USE_THEN "unif" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(ga:real->A) tt IN W`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  ABBREV_TAC `d = min (dd / &3) ((R - tt) / &2)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= dd / &3 /\ d <= (R - tt) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(ga:real->A) tt`; `dd:real`; `d:real`; `y:A`]
    GEOH_SPHERE_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `z = mfd_exp (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                    ((ga:real->A) tt) w0` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(ga:real->A) tt`; `dd:real`; `w0:real^N`] MFD_EXP_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* a point p = ga(tt - eta) before q, still in W *)
  MP_TAC(ISPECL [`top:A topology`; `ga:real->A`; `I0:real->bool`; `W:A->bool`; `tt:real`]
    GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th -> can (term_match []
        `mfd_geodesic (top,atlas) (g:A->real^N^N) (ga:real->A) I0`) (concl th))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  ABBREV_TAC `eta = min (e / &2) (min (tt / &2) (dd / &3))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta < e /\ eta < tt /\ eta <= dd / &3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `tt - eta`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `p = (ga:real->A) (tt - eta)` THEN
  ABBREV_TAC `up = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (ga:real->A) (tt - eta)` THEN
  USE_THEN "unif" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p:A) IN W`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  USE_THEN "unit" (fun th -> MP_TAC(MATCH_MP th (ASSUME `tt - eta IN I0`))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* distances *)
  USE_THEN "seg" (MP_TAC o SPECL [`&0`; `tt - eta`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`tt - eta`; `tt:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (p:A) z /\
                mfd_joinable (top,atlas) (x:A) z /\
                mfd_joinable (top,atlas) z (y:A)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THENL
     [EXISTS_TAC `(ga:real->A) tt`; EXISTS_TAC `p:A`; EXISTS_TAC `(ga:real->A) tt`] THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) p z = eta + d` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `(ga:real->A) tt`; `z:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `z:A`; `y:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `p:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* q = exp_p(eta up) and the ray through p *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `tt - eta`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shift")) THEN
  SUBGOAL_THEN
   `!t. (tt - eta) + t IN I0
        ==> mfd_exp (top,atlas) (g:A->real^N^N) p (t % up) = (ga:real->A)((tt - eta) + t)`
  (LABEL_TAC "rayp") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `up:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "shift" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(tt - eta) + t IN I0`))]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) p (eta % up) = (ga:real->A) tt`
  ASSUME_TAC THENL
   [USE_THEN "rayp" (MP_TAC o SPEC `eta:real`) THEN
    REWRITE_TAC[REAL_ARITH `(tt - eta) + eta = tt`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `dd:real`; `up:real^N`; `eta:real`; `d:real`;
                 `(ga:real->A) tt`; `w0:real^N`; `z:A`] GEOH_BROKEN_RADIAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o CONJUNCT1 o
      GEN_REWRITE_RULE I [mfd_inj_ball] o check (fun th -> can (term_match []
        `mfd_inj_ball (top,atlas) (g:A->real^N^N) ((ga:real->A) tt) dd`) (concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(ga:real->A) tt`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d:real` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `d:real` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(ga:real->A)(tt + d) = z` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "rayp" (MP_TAC o SPEC `eta + d`) THEN
    REWRITE_TAC[REAL_ARITH `(tt - eta) + (eta + d) = tt + d`] THEN
    ANTS_TAC THENL [USE_THEN "inI" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Local Hopf-Rinow (MFD_LOCAL_HOPF_RINOW).                                  *)
(* ========================================================================= *)

let MFD_LOCAL_HOPF_RINOW = prove
 (`!top atlas (g:A->real^N^N) x r y.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\
       mfd_tball g x r SUBSET mfd_exp_dom (top,atlas) g x /\
       y IN mfd_ball (top,atlas) g x r
       ==> ?v. mfd_tnorm g x v = mfd_dist (top,atlas) g x y /\
               mfd_exp (top,atlas) g x v = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `R = mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x y` THEN
  ASM_CASES_TAC `R = &0` THENL
   [EXISTS_TAC `vec 0:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`] MFD_DIST_EQ_0) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_LOCAL_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `R < d0` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `d0:real`] MFD_EXP_BALL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:A` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `d0:real`; `w:real^N`] MFD_EXP_DIST) THEN
    UNDISCH_TAC `(w:real^N) IN mfd_tball (g:A->real^N^N) x d0` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y = mfd_exp (top,atlas) (g:A->real^N^N) x w` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* a direction u at distance delta = d0 / 2 *)
  ABBREV_TAC `dl = d0 / &2` THEN
  SUBGOAL_THEN `&0 < dl /\ dl < d0 /\ dl < R` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `d0:real`; `dl:real`; `y:A`] GEOH_SPHERE_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `u = inv dl % (w0:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) x u = &1 /\ dl % u = w0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < dl ==> abs dl = dl`; REAL_MUL_LINV; REAL_MUL_RINV;
                 REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= R ==> t % u IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `mfd_tball (g:A->real^N^N) x r SUBSET
                          mfd_exp_dom (top,atlas) g x`) (concl th))) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `R:real`] GEOH_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "exp")
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") (LABEL_TAC "seg")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ga = mfd_geo (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u` THEN
  (* all points of the ray are joinable to y *)
  SUBGOAL_THEN
   `!t. t IN real_interval[dl,R]
        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((ga:real->A) t) y`
  (LABEL_TAC "join") THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "seg" (MP_TAC o SPECL [`&0`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    ALL_TAC] THEN
  ABBREV_TAC
   `A0 = {t | t IN real_interval[dl,R] /\
              mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                       ((ga:real->A) t) y + t = R}` THEN
  SUBGOAL_THEN `(dl:real) IN A0` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    USE_THEN "exp" (MP_TAC o SPEC `dl:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `real_closed (A0:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[dl,R]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `A0 = {t | t IN topspace (subtopology euclideanreal (real_interval[dl,R])) /\
                (\t. mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                       ((ga:real->A) t) y + t) t IN {R}}`
    SUBST1_TAC THENL
     [EXPAND_TAC "A0" THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_SING] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    MATCH_MP_TAC GEOH_DIST_CONTINUOUS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `mfd_geo_maxint (top,atlas:((A->bool)#(A->real^N))->bool)
                    (g:A->real^N^N) x u` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
          GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th -> can (term_match []
            `mfd_geodesic (top,atlas) (g:A->real^N^N) (ga:real->A) J`) (concl th))) THEN
        SIMP_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval[&0,R]` THEN
        ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      USE_THEN "join" MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN (A0:real->bool) ==> dl <= t /\ t <= R` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN SIMP_TAC[IN_ELIM_THM; IN_REAL_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A0:real->bool`; `R:real`] REAL_CLOSED_CONTAINS_SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; DISCH_TAC] THEN
  MP_TAC(ISPEC `A0:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ABBREV_TAC `ts = sup (A0:real->bool)` THEN
  SUBGOAL_THEN `ts:real = R` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `dl <= ts /\
                  mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                    ((ga:real->A) ts) y = R - ts`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(ts:real) IN A0` THEN EXPAND_TAC "A0" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `y:A`; `R:real`; `ts:real`]
      GEOH_EXTEND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME
      `mfd_geo (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u = ga`])) THEN
    SUBGOAL_THEN `(ts + d:real) IN A0` ASSUME_TAC THENL
     [EXPAND_TAC "A0" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ts + d <= ts:real` MP_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
      ((ga:real->A) R) y = &0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(ts:real) IN A0` THEN EXPAND_TAC "A0" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `R % (u:real^N)` THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "exp" (MP_TAC o SPEC `R:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(ga:real->A) R`; `y:A`] MFD_DIST_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  USE_THEN "join" MATCH_MP_TAC THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Metric completeness implies geodesic completeness.                        *)
(* ========================================================================= *)

(* Distances along a geodesic are at most speed times parameter length. *)

let GEOH_GEO_SEG_DIST = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J s s'.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ s IN J /\ s' IN J
        ==> mfd_joinable (top,atlas) (gamma s) (gamma s') /\
            mfd_dist (top,atlas) g (gamma s) (gamma s') <=
            abs(s' - s) * mfd_tnorm g (gamma s) (mfd_vel atlas gamma s)`,
  SUBGOAL_THEN
   `!top atlas (g:A->real^N^N) (gamma:real->A) J s s'.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ s IN J /\ s' IN J /\ s <= s'
        ==> mfd_joinable (top,atlas) (gamma s) (gamma s') /\
            mfd_dist (top,atlas) g (gamma s) (gamma s') <=
            abs(s' - s) * mfd_tnorm g (gamma s) (mfd_vel atlas gamma s)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `real_interval[s,s'] SUBSET J` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [mfd_geodesic] o
        check (fun th -> can (term_match []
          `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) J`) (concl th))) THEN
      REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`s:real`; `s':real`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `s:real`; `s':real`]
      MFD_GEODESIC_C1_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MFD_C1_CURVE_JOINABLE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `s:real`; `s':real`]
      MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `s <= s' ==> abs(s' - s) = s' - s`];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= s' \/ s' <= s:real`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `gamma:real->A`; `J:real->bool`; `s':real`; `s:real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) s`; `(gamma:real->A) s'`] MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `s:real`; `s':real`]
    MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_REWRITE_TAC[]);;

(* Under metric completeness a maximal geodesic is not bounded above. *)

let GEOH_MCOMPLETE_NOT_BOUNDED = prove
 (`!top atlas (g:A->real^N^N) (x:A) v b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mcomplete (mfd_metric (top,atlas) g x)
        ==> ~(!t. t IN mfd_geo_maxint (top,atlas) g x v ==> t < b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ga = mfd_geo (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `I0 = mfd_geo_maxint (top,atlas:((A->bool)#(A->real^N))->bool)
                     (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN `!t. t IN I0 ==> (ga:real->A) t IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_geodesic] o check (fun th -> can (term_match []
        `mfd_geodesic (top,atlas) (g:A->real^N^N) (ga:real->A) I0`) (concl th))) THEN
    SIMP_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    ALL_TAC] THEN
  (* the supremum bs of I0 is positive and not in I0 *)
  MP_TAC(ISPEC `I0:real->bool` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `b:real` THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `bs = sup (I0:real->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN `?e. &0 < e /\ !t. abs(t - &0) < e ==> t IN I0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_open (I0:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < bs` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ub" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((bs:real) IN I0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `real_open (I0:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `bs:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e':real` STRIP_ASSUME_TAC) THEN
    USE_THEN "ub" (MP_TAC o SPEC `bs + e' / &2`) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < bs ==> t IN I0` (LABEL_TAC "below") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?t'. t' IN I0 /\ t < t'` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_FORALL_THM; TAUT `~(p ==> q) <=> p /\ ~q`] THEN
      GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
      PURE_REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "lub" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `is_realinterval (I0:real->bool)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `t':real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the sequence sq n = bs - bs / (n + 1) *)
  ABBREV_TAC `sq = \n:num. bs - bs * inv(&n + &1)` THEN
  SUBGOAL_THEN `!n:num. &0 <= (sq:num->real) n /\ sq n < bs /\ bs - bs * inv(&n + &1) = sq n`
  (LABEL_TAC "sq") THENL
   [GEN_TAC THEN EXPAND_TAC "sq" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv(&n + &1) /\ inv(&n + &1) <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x * i <= x * &1 ==> &0 <= x - x * i`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < x * i ==> x - x * i < x`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. (sq:num->real) n IN I0` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "below" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = mfd_tnorm (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN
   `!s s'. s IN I0 /\ s' IN I0
           ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                 ((ga:real->A) s) (ga s') /\
               mfd_dist (top,atlas) (g:A->real^N^N) (ga s) (ga s') <= abs(s' - s) * c`
  (LABEL_TAC "segd") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `ga:real->A`; `I0:real->bool`; `s:real`; `s':real`]
      GEOH_GEO_SEG_DIST) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `ga:real->A`; `I0:real->bool`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the points form a Cauchy sequence *)
  SUBGOAL_THEN
   `cauchy_in (mfd_metric (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x)
              (\n. (ga:real->A)((sq:num->real) n))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_METRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[cauchy_in; IN_ELIM_THM] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(ga:real->A)(&0) = x`)) THEN
      USE_THEN "segd" (MP_TAC o SPECL [`&0`; `(sq:num->real) n`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `ee:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?N. ~(N = 0) /\ &0 < inv(&N) /\ inv(&N) < ee / (bs * c + &1)`
    (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THENL
     [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `n':num`] THEN STRIP_TAC THEN
    USE_THEN "segd" (MP_TAC o SPECL [`(sq:num->real) n`; `(sq:num->real) n'`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs((sq:num->real) n' - sq n) * c` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs((sq:num->real) n' - sq n) <= bs * inv(&N)` ASSUME_TAC THENL
     [USE_THEN "sq" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(SPEC `n:num` th)));
                                          GSYM(CONJUNCT2(CONJUNCT2(SPEC `n':num` th)))]) THEN
      SUBGOAL_THEN `!k:num. N <= k ==> inv(&k + &1) <= inv(&N) /\ &0 < inv(&k + &1)`
      ASSUME_TAC THENL
       [X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
          UNDISCH_TAC `N:num <= k` THEN UNDISCH_TAC `~(N:num = 0)` THEN ARITH_TAC;
          MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(&n + &1) <= inv(&N) /\ inv(&n' + &1) <= inv(&N) /\
                    &0 < inv(&n + &1) /\ &0 < inv(&n' + &1)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `(b - b * i') - (b - b * i) = b * (i - i')`] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b = b`; REAL_LE_LMUL_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(bs * inv(&N)) * c` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(bs * c + &1) * inv(&N)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(b * i) * c = (b * c) * i`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < bs * c + &1` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `inv(&N) < ee / (bs * c + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* its limit and the escape from the compact set of its points *)
  FIRST_X_ASSUM(MP_TAC o SPEC `\n. (ga:real->A)((sq:num->real) n)` o
    GEN_REWRITE_RULE I [mcomplete] o check (fun th -> can (term_match []
      `mcomplete (mfd_metric (top,atlas:((A->bool)#(A->real^N))->bool)
                  (g:A->real^N^N) x)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_MTOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LIMIT_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`;
                 `(l:A) INSERT IMAGE (\n. (ga:real->A)((sq:num->real) n)) (:num)`; `b:real`]
    MFD_GEO_ESCAPE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_SEQUENCE_WITH_LIMIT THEN
    EXISTS_TAC `\n. (ga:real->A)((sq:num->real) n)` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "esc")) o
    REWRITE_RULE[ASSUME `mfd_geo (top,atlas:((A->bool)#(A->real^N))->bool)
                           (g:A->real^N^N) x v = ga`;
                 ASSUME `mfd_geo_maxint (top,atlas:((A->bool)#(A->real^N))->bool)
                           (g:A->real^N^N) x v = I0`]) THEN
  SUBGOAL_THEN `t1 < bs` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `t1 <= bs /\ ~(t1 = bs) ==> t1 < bs`) THEN
    CONJ_TAC THENL [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. ~(m = 0) /\ &0 < inv(&m) /\ inv(&m) < (bs - t1) / bs`
  (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[GSYM REAL_ARCH_INV] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "esc" (MP_TAC o SPEC `(sq:num->real) m`) THEN
  REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN
  MATCH_MP_TAC(TAUT `(p /\ q) /\ r ==> ~(p /\ q ==> ~r)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `inv(&m) * bs < bs - t1` ASSUME_TAC THENL
     [UNDISCH_TAC `inv(&m) < (bs - t1) / bs` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&m + &1) <= inv(&m)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `~(m:num = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `bs * inv(&m + &1) <= bs * inv(&m)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "sq" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(CONJUNCT2(SPEC `m:num` th)))]) THEN
    ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN EXISTS_TAC `m:num` THEN REWRITE_TAC[]]);;

let MFD_COMPLETE_GEO_COMPLETE = prove
 (`!top atlas (g:A->real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!x. x IN topspace top ==> mcomplete (mfd_metric (top,atlas) g x))
        ==> !x v. x IN topspace top ==> mfd_geo_maxint (top,atlas) g x v = (:real)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `--(&1)`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `(!b. ?s. s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v /\ b <= s) /\
    (!b. ?s. s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v /\ s <= b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `b:real` THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `v:real^N`; `b:real`]
        GEOH_MCOMPLETE_NOT_BOUNDED) THEN
      ASM_SIMP_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `--(&1) % v:real^N`; `--b`]
        GEOH_MCOMPLETE_NOT_BOUNDED) THEN
      ASM_SIMP_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `--(&1) * s` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `t:real` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC o SPEC `t:real`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC o SPEC `t:real`) THEN
  UNDISCH_TAC `is_realinterval (mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v)` THEN
  REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`s1:real`; `s2:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Minimizing geodesics from a point with total exponential                  *)
(* map; the Hopf-Rinow equivalences.                                        *)
(* ========================================================================= *)

let MFD_EXP_TOTAL_MINIMIZING = prove
 (`!top atlas (g:A->real^N^N) (x:A) y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_exp_dom (top,atlas) g x = (:real^N) /\ mfd_joinable (top,atlas) x y
        ==> ?v. mfd_exp (top,atlas) g x v = y /\
                mfd_tnorm g x v = mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`;
                 `mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x y + &1`;
                 `y:A`] MFD_LOCAL_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; mfd_ball; IN_ELIM_THM] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; MESON_TAC[]]);;

(* With total exp_x, every point of the class of x is exp_x of a vector of  *)
(* norm the distance, so closed balls are images of closed balls of T_xM.   *)

let GEOH_CBALL_IMAGE = prove
 (`!top atlas (g:A->real^N^N) (x:A) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_exp_dom (top,atlas) g x = (:real^N)
        ==> mfd_cball (top,atlas) g x R =
            IMAGE (mfd_exp (top,atlas) g x) {v | mfd_tnorm g x v <= R}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`] MFD_EXP_TOTAL_MINIMIZING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_RADIAL_GEODESIC) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) x v`; `&0`; `&1`]
      MFD_C1_CURVE_JOINABLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x v`;
                   `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let GEOH_CBALL_COMPACT = prove
 (`!top atlas (g:A->real^N^N) (x:A) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_exp_dom (top,atlas) g x = (:real^N)
        ==> compact_in top (mfd_cball (top,atlas) g x R)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOH_CBALL_IMAGE] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEAN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOD_TCBALL_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN SIMP_TAC[]]);;

(* Geodesic completeness gives total exponential maps. *)

let GEOH_GEO_COMPLETE_DOM = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        (!v. mfd_geo_maxint (top,atlas) g x v = (:real))
        ==> mfd_exp_dom (top,atlas) g x = (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIV] THEN
  X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `&1`] MFD_EXP_RADIAL) THEN
  ASM_SIMP_TAC[VECTOR_MUL_LID; IN_UNIV]);;

let MFD_HOPF_RINOW = prove
 (`!top atlas (g:A->real^N^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g
        ==> (mfd_complete (top,atlas) g <=>
             !x. x IN topspace top ==> mcomplete (mfd_metric (top,atlas) g x)) /\
            (mfd_complete (top,atlas) g <=>
             !x v. x IN topspace top ==> mfd_geo_maxint (top,atlas) g x v = (:real))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> q) /\ (q ==> s) /\ (s ==> p) ==> (p <=> q) /\ (p <=> s)`) THEN
  REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC MFD_COMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC MFD_COMPLETE_GEO_COMPLETE THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN REWRITE_TAC[mfd_complete] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `R:real`] THEN DISCH_TAC THEN
      MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_SIMP_TAC[]]);;

let MFD_HOPF_RINOW_POINT = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ connected_space top /\ x IN topspace top
        ==> (mfd_complete (top,atlas) g <=> mfd_exp_dom (top,atlas) g x = (:real^N))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[mfd_complete] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `R:real`] THEN DISCH_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x
                (mfd_dist (top,atlas) g x p + R)` THEN
  ASM_SIMP_TAC[GEOH_CBALL_COMPACT; MFD_CBALL_CLOSED] THEN
  REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x p`
  ASSUME_TAC THENL [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `p:A`; `y:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MFD_COMPLETE_MINIMIZING_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) (x:A) y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        mfd_joinable (top,atlas) x y
        ==> ?v. mfd_exp_dom (top,atlas) g x = (:real^N) /\
                mfd_exp (top,atlas) g x v = y /\
                mfd_tnorm g x v = mfd_dist (top,atlas) g x y /\
                mfd_length atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) =
                mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`] MFD_EXP_TOTAL_MINIMIZING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_RADIAL_GEODESIC) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[]);;

let MFD_COMPLETE_EXP_ONTO = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        connected_space top /\ x IN topspace top
        ==> IMAGE (mfd_exp (top,atlas) g x) (:real^N) = topspace top`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o CONJUNCT1) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `y:A`] MFD_EXP_TOTAL_MINIMIZING) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED] THEN MESON_TAC[]]);;

