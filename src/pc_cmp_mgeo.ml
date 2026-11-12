(* ========================================================================= *)
(* Unit pc_cmp_mgeo (comparison-geometry layer CMP): minimizing geodesics,   *)
(* MT Prop 1.20 (S5): along a minimizing radial geodesic exp_x(t v),         *)
(* t in [0,1], every interior point is reached minimally only by t v, the    *)
(* distance is t |v|, and d exp_x is injective at t v for t < 1.             *)
(* ========================================================================= *)

needs "src/pc_cmp_min.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Basic facts on a radial geodesic and the distance along a                 *)
(* minimizing one (S5 part (a)).                                             *)
(* ========================================================================= *)

let CMPS_RAY_FACTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x
        ==> real_interval[&0,&1] SUBSET mfd_geo_maxint (top,atlas) g x v /\
            mfd_geodesic (top,atlas) g (mfd_geo (top,atlas) g x v)
                         (mfd_geo_maxint (top,atlas) g x v) /\
            mfd_geo (top,atlas) g x v (&0) = x /\
            mfd_vel atlas (mfd_geo (top,atlas) g x v) (&0) = v /\
            (!s. &0 <= s /\ s <= &1
                 ==> s % v IN mfd_exp_dom (top,atlas) g x /\
                     mfd_exp (top,atlas) g x (s % v) = mfd_geo (top,atlas) g x v s) /\
            (!s. s IN mfd_geo_maxint (top,atlas) g x v
                 ==> mfd_tnorm g (mfd_geo (top,atlas) g x v s)
                       (mfd_vel atlas (mfd_geo (top,atlas) g x v) s) =
                     mfd_tnorm g x v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v`
  ASSUME_TAC THENL
   [UNDISCH_TAC `v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[&0,&1] SUBSET
                mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    UNDISCH_TAC `is_realinterval (mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `s:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v`
      (fun th -> SIMP_TAC[th]) THEN
    UNDISCH_TAC `real_interval[&0,&1] SUBSET
                 mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v`; `s:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[]]);;

(* S5 (a), in the two-point form: along a minimizing exp_x(t v), t in       *)
(* [0,1], the distance between the points at s <= t is (t - s) |v|.         *)

let CMPS_RAY_DIST = prove
 (`!top atlas (g:A->real^N^N) (x:A) v s t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
        &0 <= s /\ s <= t /\ t <= &1
        ==> mfd_joinable (top,atlas) (mfd_exp (top,atlas) g x (s % v))
                                     (mfd_exp (top,atlas) g x (t % v)) /\
            mfd_dist (top,atlas) g (mfd_exp (top,atlas) g x (s % v))
                     (mfd_exp (top,atlas) g x (t % v)) = (t - s) * mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `beta = mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v` THEN
  ABBREV_TAC `B = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ex") (LABEL_TAC "sp")))))) THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= &1 ==> (p:real) IN B` (LABEL_TAC "inB") THENL
   [UNDISCH_TAC `real_interval[&0,&1] SUBSET (B:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. &0 <= p /\ p <= q /\ q <= &1
          ==> mfd_joinable (top,atlas) ((beta:real->A) p) (beta q) /\
              mfd_dist (top,atlas) (g:A->real^N^N) (beta p) (beta q) <=
              (q - p) * mfd_tnorm g x v`
  (LABEL_TAC "seg") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `beta:real->A`; `B:real->bool`; `p:real`; `q:real`]
      GEOH_GEO_SEG_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "inB" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) ((beta:real->A) p) (mfd_vel atlas beta p) =
                  mfd_tnorm g x v` SUBST1_TAC THENL
     [USE_THEN "sp" MATCH_MP_TAC THEN USE_THEN "inB" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `p <= q ==> abs(q - p) = q - p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= &1
                    ==> mfd_exp (top,atlas) (g:A->real^N^N) (x:A) (p % v) = beta p`
  (LABEL_TAC "ex2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ex" (MP_TAC o SPEC `p:real`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) (x:A) v = beta (&1)` ASSUME_TAC THENL
   [USE_THEN "ex2" (MP_TAC o SPEC `&1`) THEN
    REWRITE_TAC[VECTOR_MUL_LID; REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  USE_THEN "ex2" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "ex2" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`&0`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "seg" (MP_TAC o SPECL [`t:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((beta:real->A) s) (beta(&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(beta:real->A) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(beta:real->A) (&0)`; `(beta:real->A) s`;
                 `(beta:real->A) (&1)`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(beta:real->A) s`; `(beta:real->A) t`;
                 `(beta:real->A) (&1)`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x (mfd_exp (top,atlas) g x v) =
               mfd_tnorm g x v` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`mfd_dist (top,atlas) (g:A->real^N^N) ((beta:real->A) (&0)) (beta s) <=
     (s - &0) * mfd_tnorm g x v`;
    `mfd_dist (top,atlas) (g:A->real^N^N) ((beta:real->A) s) (beta t) <=
     (t - s) * mfd_tnorm g x v`;
    `mfd_dist (top,atlas) (g:A->real^N^N) ((beta:real->A) t) (beta (&1)) <=
     (&1 - t) * mfd_tnorm g x v`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Helpers for S5 (b): injectivity of exp on an injectivity                  *)
(* ball, exp along a shifted geodesic, small parameters, (a) from 0.         *)
(* ========================================================================= *)

let CMPS_INJ_BALL_INJ = prove
 (`!top atlas (g:A->real^N^N) (x:A) r v1 v2.
        mfd_inj_ball (top,atlas) g x r /\
        mfd_tnorm g x v1 < r /\ mfd_tnorm g x v2 < r /\
        mfd_exp (top,atlas) g x v1 = mfd_exp (top,atlas) g x v2
        ==> v1 = v2`,
  REWRITE_TAC[mfd_inj_ball; mfd_param; mfd_diffeo; homeomorphic_maps] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; mfd_tball; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let CMPS_EXP_SHIFT = prove
 (`!top atlas (g:A->real^N^N) (x:A) v s c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        s IN mfd_geo_maxint (top,atlas) g x v
        ==> mfd_geo (top,atlas) g x v s IN topspace top /\
            (c % mfd_vel atlas (mfd_geo (top,atlas) g x v) s IN
               mfd_exp_dom (top,atlas) g (mfd_geo (top,atlas) g x v s) <=>
             s + c IN mfd_geo_maxint (top,atlas) g x v) /\
            (s + c IN mfd_geo_maxint (top,atlas) g x v
             ==> mfd_exp (top,atlas) g (mfd_geo (top,atlas) g x v s)
                   (c % mfd_vel atlas (mfd_geo (top,atlas) g x v) s) =
                 mfd_geo (top,atlas) g x v (s + c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v s IN topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `s:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v s`;
                 `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v) s`;
                 `c:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[]);;

let CMPS_SMALL = prove
 (`!e c r. &0 < e /\ &0 <= c /\ &0 < r ==> ?d. &0 < d /\ d < e /\ d * c < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * (c + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / (&2 * (c + &1))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  EXISTS_TAC `min (e / &2) (r / (&2 * (c + &1)))` THEN
  SUBGOAL_THEN `min (e / &2) (r / (&2 * (c + &1))) * (&2 * (c + &1)) <= r` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = min (e / &2) (r / (&2 * (c + &1)))` THEN
  SUBGOAL_THEN `&0 < d /\ d < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= d * c` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* S5 (a) from the base point. *)

let CMPS_RAY_DIST0 = prove
 (`!top atlas (g:A->real^N^N) (x:A) v t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
        &0 <= t /\ t <= &1
        ==> mfd_joinable (top,atlas) x (mfd_exp (top,atlas) g x (t % v)) /\
            mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (t % v)) =
            t * mfd_tnorm g x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `&0`; `t:real`] CMPS_RAY_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ex") ASSUME_TAC))))) THEN
  USE_THEN "ex" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO]);;

(* ========================================================================= *)
(* S5 (b), the corner step: if exp_x w = exp_x(t v) with                     *)
(* |w| = t |v| along a minimizing exp_x(s v), then the two geodesics arrive  *)
(* with proportional velocities (GEOH_BROKEN_RADIAL near the corner, then    *)
(* injectivity of exp at the corner point).                                  *)
(* ========================================================================= *)

let CMPS_CORNER = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
        &0 < t /\ t < &1 /\ &0 < mfd_tnorm g x v /\
        w IN mfd_exp_dom (top,atlas) g x /\
        mfd_exp (top,atlas) g x w = mfd_exp (top,atlas) g x (t % v) /\
        mfd_tnorm g x w = t * mfd_tnorm g x v
        ==> mfd_vel atlas (mfd_geo (top,atlas) g x w) (&1) =
            t % mfd_vel atlas (mfd_geo (top,atlas) g x v) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) (x:A) (mfd_exp (top,atlas) g x w) =
                mfd_tnorm g x w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] CMPS_RAY_DIST0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPS_RAY_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `w:real^N`] CMPS_RAY_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPS_EXP_SHIFT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `w:real^N`] CMPS_EXP_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `beta = mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v` THEN
  ABBREV_TAC `B = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v` THEN
  ABBREV_TAC `alpha = mfd_geo (top,atlas) (g:A->real^N^N) (x:A) w` THEN
  ABBREV_TAC `A = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w` THEN
  DISCH_THEN(LABEL_TAC "ash") THEN DISCH_THEN(LABEL_TAC "bsh") THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aI") (CONJUNCTS_THEN2 (LABEL_TAC "ageo")
    (CONJUNCTS_THEN2 (LABEL_TAC "a0") (CONJUNCTS_THEN2 (LABEL_TAC "av0")
      (CONJUNCTS_THEN2 (LABEL_TAC "aex") (LABEL_TAC "asp")))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bI") (CONJUNCTS_THEN2 (LABEL_TAC "bgeo")
    (CONJUNCTS_THEN2 (LABEL_TAC "b0") (CONJUNCTS_THEN2 (LABEL_TAC "bv0")
      (CONJUNCTS_THEN2 (LABEL_TAC "bex") (LABEL_TAC "bsp")))))) THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= &1 ==> (p:real) IN A /\ p IN B`
  (LABEL_TAC "inAB") THENL
   [UNDISCH_TAC `real_interval[&0,&1] SUBSET (A:real->bool)` THEN
    UNDISCH_TAC `real_interval[&0,&1] SUBSET (B:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(alpha:real->A) (&1) = (beta:real->A) t` (LABEL_TAC "ab") THENL
   [USE_THEN "aex" (MP_TAC o SPEC `&1`) THEN USE_THEN "bex" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL; VECTOR_MUL_LID] THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(beta:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `B:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "inAB" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(beta:real->A) t`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `r:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif")))))) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                  (alpha:real->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN EXISTS_TAC `A:real->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `alpha:real->A`; `A:real->bool`] GEOL_GEODESIC_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `alpha:real->A`; `&0`; `&1`; `U:A->bool`; `&1`]
    CMPM_CONT_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MP_TAC(ISPECL [`min (&1 / &2) e1`; `t * mfd_tnorm (g:A->real^N^N) (x:A) v`; `r / &3`]
    CMPS_SMALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`&1 - t`; `mfd_tnorm (g:A->real^N^N) (x:A) v`; `r / &3`] CMPS_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `delta2:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `&0 <= &1 - delta /\ &1 - delta <= &1 /\ abs((&1 - delta) - &1) < e1`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(alpha:real->A) (&1 - delta) IN U` ASSUME_TAC THENL
   [USE_THEN "near" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPEC `(alpha:real->A) (&1 - delta)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPEC `(beta:real->A) t`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= &1 ==> (p:real) IN A` (LABEL_TAC "inA") THENL
   [USE_THEN "inAB" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= &1 ==> (p:real) IN B` (LABEL_TAC "inB") THENL
   [USE_THEN "inAB" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - delta) IN A /\ &1 IN A /\ (t:real) IN B /\ t + delta2 IN B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "inA" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "inA" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "inB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "inB" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(alpha:real->A) (&1 - delta) IN topspace top` ASSUME_TAC THENL
   [USE_THEN "ash" (fun th -> MP_TAC(MATCH_MP (SPECL [`&1 - delta`; `&0`] th)
      (ASSUME `(&1 - delta) IN A`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(alpha:real->A) (&1 - delta)`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "psc")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(beta:real->A) t`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ysc")))) THEN
  SUBGOAL_THEN
   `mfd_tnorm (g:A->real^N^N) ((alpha:real->A) (&1 - delta))
      (mfd_vel atlas alpha (&1 - delta)) = t * mfd_tnorm g x v /\
    mfd_tnorm g ((beta:real->A) t) (mfd_vel atlas alpha (&1)) = t * mfd_tnorm g x v /\
    mfd_tnorm g (beta t) (mfd_vel atlas beta t) = mfd_tnorm g x v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "asp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ab" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "asp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "bsp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t * mfd_tnorm (g:A->real^N^N) (x:A) v` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t = &0) /\ ~(mfd_tnorm (g:A->real^N^N) (x:A) v = &0) /\ ~(delta2 = &0)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_tnorm (g:A->real^N^N) ((alpha:real->A) (&1 - delta))
      (inv(t * mfd_tnorm g x v) % mfd_vel atlas alpha (&1 - delta)) = &1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(delta * t * mfd_tnorm (g:A->real^N^N) (x:A) v) %
    (inv(t * mfd_tnorm g x v) %
     mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (alpha:real->A) (&1 - delta)) =
    delta % mfd_vel atlas alpha (&1 - delta)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(t = &0)`; `~(mfd_tnorm (g:A->real^N^N) (x:A) v = &0)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) (g:A->real^N^N) ((alpha:real->A) (&1 - delta))
      (delta % mfd_vel atlas alpha (&1 - delta)) = (beta:real->A) t`
  ASSUME_TAC THENL
   [USE_THEN "ash" (fun th -> MP_TAC(MATCH_MP (SPECL [`&1 - delta`; `delta:real`] th)
      (ASSUME `(&1 - delta) IN A`))) THEN
    REWRITE_TAC[REAL_ARITH `(&1 - delta) + delta = &1`] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s'. &0 <= s' /\ s' <= &1
         ==> s' % (delta2 % mfd_vel atlas (beta:real->A) t) IN
               mfd_exp_dom (top,atlas) (g:A->real^N^N) (beta t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s':real` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    USE_THEN "bsh" (fun th -> MP_TAC(MATCH_MP (SPECL [`t:real`; `s' * delta2`] th)
      (ASSUME `(t:real) IN B`))) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    USE_THEN "inB" MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < t /\ &0 <= x ==> &0 <= t + x`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      MATCH_MP_TAC(REAL_ARITH `x <= delta2 /\ delta2 < &1 - t ==> t + x <= &1`) THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) (g:A->real^N^N) ((beta:real->A) t)
      (delta2 % mfd_vel atlas beta t) = beta(t + delta2)`
  ASSUME_TAC THENL
   [USE_THEN "bsh" (fun th -> MP_TAC(MATCH_MP (SPECL [`t:real`; `delta2:real`] th)
      (ASSUME `(t:real) IN B`))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_tnorm (g:A->real^N^N) ((beta:real->A) t) (delta2 % mfd_vel atlas beta t) =
    delta2 * mfd_tnorm g x v`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. &0 <= p /\ p <= q /\ q <= &1
          ==> mfd_joinable (top,atlas) ((alpha:real->A) p) (alpha q) /\
              mfd_dist (top,atlas) (g:A->real^N^N) (alpha p) (alpha q) =
              (q - p) * (t * mfd_tnorm g x v)`
  (LABEL_TAC "adist") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `w:real^N`; `p:real`; `q:real`]
      CMPS_RAY_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "aex" (fun th -> MP_TAC(SPEC `p:real` th) THEN MP_TAC(SPEC `q:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. &0 <= p /\ p <= q /\ q <= &1
          ==> mfd_joinable (top,atlas) ((beta:real->A) p) (beta q) /\
              mfd_dist (top,atlas) (g:A->real^N^N) (beta p) (beta q) =
              (q - p) * mfd_tnorm g x v`
  (LABEL_TAC "bdist") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `p:real`; `q:real`]
      CMPS_RAY_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "bex" (fun th -> MP_TAC(SPEC `p:real` th) THEN MP_TAC(SPEC `q:real` th)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "adist" (MP_TAC o SPECL [`&0`; `&1 - delta`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "adist" (MP_TAC o SPECL [`&1 - delta`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "bdist" (MP_TAC o SPECL [`&0`; `t + delta2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "bdist" (MP_TAC o SPECL [`t:real`; `t + delta2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                  ((alpha:real->A) (&1 - delta)) ((beta:real->A) (t + delta2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(beta:real->A) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) ((alpha:real->A) (&1 - delta))
      ((beta:real->A) (t + delta2)) =
    delta * t * mfd_tnorm g x v + delta2 * mfd_tnorm g x v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `(alpha:real->A) (&1 - delta)`;
                   `(beta:real->A) (t + delta2)`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(alpha:real->A) (&1 - delta)`; `(beta:real->A) t`;
                   `(beta:real->A) (t + delta2)`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(alpha:real->A) (&1 - delta)`; `r:real`;
                 `inv(t * mfd_tnorm (g:A->real^N^N) (x:A) v) %
                  mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (alpha:real->A)
                    (&1 - delta)`;
                 `delta * t * mfd_tnorm (g:A->real^N^N) (x:A) v`;
                 `delta2 * mfd_tnorm (g:A->real^N^N) (x:A) v`;
                 `(beta:real->A) t`;
                 `delta2 % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (beta:real->A) t`;
                 `(beta:real->A) (t + delta2)`] GEOH_BROKEN_RADIAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_SIMP_TAC[REAL_LT_MUL] THEN NO_TAC) THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(delta * t * mfd_tnorm (g:A->real^N^N) (x:A) v + delta2 * mfd_tnorm g x v) %
    (inv(t * mfd_tnorm g x v) %
     mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (alpha:real->A) (&1 - delta)) =
    (delta + delta2 * inv t) % mfd_vel atlas alpha (&1 - delta)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(t = &0)`; `~(mfd_tnorm (g:A->real^N^N) (x:A) v = &0)`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < delta + delta2 * inv t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(delta + delta2 * inv t) %
    mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (alpha:real->A) (&1 - delta) IN
    mfd_exp_dom (top,atlas) (g:A->real^N^N) (alpha (&1 - delta))`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `mfd_inj_ball (top,atlas) (g:A->real^N^N)
                     ((alpha:real->A) (&1 - delta)) r`) THEN
    REWRITE_TAC[mfd_inj_ball; SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    USE_THEN "psc" (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    SUBGOAL_THEN `(delta + delta2 * inv t) * t * mfd_tnorm (g:A->real^N^N) (x:A) v =
                  delta * t * mfd_tnorm g x v + delta2 * mfd_tnorm g x v`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
      MAP_EVERY UNDISCH_TAC
       [`delta * t * mfd_tnorm (g:A->real^N^N) (x:A) v < r / &3`;
        `delta2 * mfd_tnorm (g:A->real^N^N) (x:A) v < r / &3`; `&0 < r`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ash" (fun th -> MP_TAC(MATCH_MP
    (SPECL [`&1 - delta`; `delta + delta2 * inv t`] th)
    (ASSUME `(&1 - delta) IN A`))) THEN
  REWRITE_TAC[REAL_ARITH `(&1 - delta) + delta + d = &1 + d`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(beta:real->A) (t + delta2) = alpha (&1 + delta2 * inv t)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `(beta:real->A) (t + delta2) =
      mfd_exp (top,atlas) (g:A->real^N^N) (alpha (&1 - delta))
        ((delta * t * mfd_tnorm g x v + delta2 * mfd_tnorm g x v) %
         inv (t * mfd_tnorm g x v) % mfd_vel atlas (alpha:real->A) (&1 - delta))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ash" (fun th -> MP_TAC(MATCH_MP (SPECL [`&1`; `delta2 * inv t`] th)
    (ASSUME `&1 IN A`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(delta2 * inv t) % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (alpha:real->A) (&1) =
    delta2 % mfd_vel atlas (beta:real->A) t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPS_INJ_BALL_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `(beta:real->A) t`; `r:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "ysc" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_MUL; REAL_LT_INV] THEN
      SUBGOAL_THEN `(delta2 * inv t) * t * mfd_tnorm (g:A->real^N^N) (x:A) v =
                    delta2 * mfd_tnorm g x v` SUBST1_TAC THENL
       [UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
        MAP_EVERY UNDISCH_TAC
         [`delta2 * mfd_tnorm (g:A->real^N^N) (x:A) v < r / &3`; `&0 < r`] THEN
        REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`delta2 * mfd_tnorm (g:A->real^N^N) (x:A) v < r / &3`; `&0 < r`] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (alpha:real->A) (&1) =
    (t * inv delta2) % ((delta2 * inv t) % mfd_vel atlas alpha (&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `(t * inv delta2) * delta2 * inv t = &1`
      (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    MAP_EVERY UNDISCH_TAC [`~(t = &0)`; `~(delta2 = &0)`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `~(delta2 = &0)` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* S5 (b), uniqueness: along a minimizing exp_x(s v), s in                   *)
(* [0,1], the point exp_x(t v) (t < 1) is reached by exp_x w with |w| <=     *)
(* t |v| only for w = t v.                                                   *)
(* ========================================================================= *)

let CMPS_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v t w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
        &0 <= t /\ t < &1 /\
        w IN mfd_exp_dom (top,atlas) g x /\
        mfd_exp (top,atlas) g x w = mfd_exp (top,atlas) g x (t % v) /\
        mfd_tnorm g x w <= t * mfd_tnorm g x v
        ==> w = t % v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `w:real^N`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x (mfd_exp (top,atlas) g x w) <=
                mfd_tnorm g x w` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) w`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w`; `&0`; `&1`]
      GEOH_GEO_SEG_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `real_interval[&0,&1] SUBSET
                    mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w`)) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM mfd_exp] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) (x:A) w = t * mfd_tnorm g x v` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b <= a /\ a <= b ==> a = b`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] CMPS_RAY_DIST0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x (mfd_exp (top,atlas) g x w) <=
                 mfd_tnorm g x w` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t = &0 \/ mfd_tnorm (g:A->real^N^N) (x:A) v = &0` THENL
   [SUBGOAL_THEN `w:real^N = vec 0` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `w:real^N`] GEOD_TNORM_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `mfd_tnorm (g:A->real^N^N) (x:A) w = t * mfd_tnorm g x v` THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `&0 < t /\ &0 < mfd_tnorm (g:A->real^N^N) (x:A) v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`; `t:real`] CMPS_CORNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v`; `t:real`; `&0`]
    MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tvel")) THEN
  SUBGOAL_THEN
   `!p. &0 <= p /\ p <= &1
        ==> p IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w /\
            p IN mfd_geo_maxint (top,atlas) g x v`
  (LABEL_TAC "inAB") THENL
   [UNDISCH_TAC `real_interval[&0,&1] SUBSET
                 mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w` THEN
    UNDISCH_TAC `real_interval[&0,&1] SUBSET
                 mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w INTER
             {s | t * s IN mfd_geo_maxint (top,atlas) g x v}
        ==> mfd_geo (top,atlas) g x w s = (\s. mfd_geo (top,atlas) g x v (t * s)) s`
  (LABEL_TAC "agree") THENL
   [MATCH_MP_TAC MFD_GEODESIC_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `&1`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RID] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "inAB" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
      SIMP_TAC[];
      USE_THEN "inAB" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[GSYM mfd_exp] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)`)) (concl th) &&
        can (find_term ((=) `v:real^N`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "tvel" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_MUL_RID] THEN
      ANTS_TAC THENL
       [USE_THEN "inAB" (MP_TAC o SPEC `t:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        DISCH_THEN SUBST1_TAC THEN REFL_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0:real) IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w /\
                &0 IN mfd_geo_maxint (top,atlas) g x v` STRIP_ASSUME_TAC THENL
   [USE_THEN "inAB" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_open (mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w INTER
               {s | t * s IN mfd_geo_maxint (top,atlas) g x v})`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_OPEN_INTER THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) w`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) w`]
      GEOL_GEODESIC_BASIC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\s. mfd_geo (top,atlas) (g:A->real^N^N) (x:A) v (t * s)`;
                   `{s | t * s IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) v}`]
      GEOL_GEODESIC_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_open] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; REAL_MUL_RZERO]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eb"))) THEN
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
      (mfd_geo (top,atlas) (g:A->real^N^N) (x:A) w) (&0) =
    mfd_vel atlas (\s. mfd_geo (top,atlas) g x v (t * s)) (&0)`
  MP_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "agree" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL
     [USE_THEN "eb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "tvel" (MP_TAC o SPEC `&0`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Closure properties of smooth fields along curves                          *)
(* (cmp_sfield): congruence, linear combinations, slices of smooth fields   *)
(* along smooth families.                                                    *)
(* ========================================================================= *)

let CMPS_SFIELD_CONG = prove
 (`!atlas (gamma:real->A) gamma' J (X:real->real^N) X'.
        (!t. t IN J ==> gamma' t = gamma t /\ X' t = X t) /\
        cmp_sfield atlas gamma J X
        ==> cmp_sfield atlas gamma' J X'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_sfield] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{lift t | t IN J /\ (gamma':real->A) t IN FST (c:(A->bool)#(A->real^N))} =
                {lift t | t IN J /\ (gamma:real->A) t IN FST c}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\s. mfd_field_rep atlas (gamma:real->A) (X:real->real^N) c (drop s)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; LIFT_DROP; mfd_field_rep] THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let CMPS_SFIELD_LIN = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) Y a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        cmp_sfield atlas gamma J X /\ cmp_sfield atlas gamma J Y
        ==> cmp_sfield atlas gamma J (\t. a % X t + b % Y t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cmp_sfield atlas (gamma:real->A) J (X:real->real^N)` THEN
  UNDISCH_TAC `cmp_sfield atlas (gamma:real->A) J (Y:real->real^N)` THEN
  REWRITE_TAC[cmp_sfield] THEN DISCH_THEN(LABEL_TAC "sy") THEN
  DISCH_THEN(LABEL_TAC "sx") THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] MFD_GEODESIC_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\s. a % mfd_field_rep atlas (gamma:real->A) (X:real->real^N)
                       (c:(A->bool)#(A->real^N)) (drop s) +
                  b % mfd_field_rep atlas gamma (Y:real->real^N) c (drop s)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; LIFT_DROP] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_field_rep] THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `linear (chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    ((gamma:real->A) t)) (c:(A->bool)#(A->real^N)) (gamma t))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CMPI_CHART_JAC_LINEAR THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_SIMP_TAC[]]);;

let CMPS_FFIELD_SLICE = prove
 (`!top atlas (f:real->real->A) S0 J (Z:real->real->real^N).
        smooth_manifold_atlas top atlas /\ cmp_family (top,atlas) f S0 J /\
        &0 IN S0 /\ cmp_ffield atlas f S0 J Z
        ==> cmp_sfield atlas (f (&0)) J (Z (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmp_sfield] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] CMPV_FAMILY_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `cmp_ffield atlas (f:real->real->A) S0 J (Z:real->real->real^N)` THEN
  REWRITE_TAC[cmp_ffield] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `TS = {pastecart (lift s) (lift t) |
                   s IN S0 /\ t IN J /\
                   (f:real->real->A) s t IN FST (c:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `{lift t | t IN J /\ (f:real->real->A) (&0) t IN
                          FST (c:(A->bool)#(A->real^N))} =
                {y | pastecart (lift(&0)) y IN TS}` SUBST1_TAC THENL
   [EXPAND_TAC "TS" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; PASTECART_INJ] THEN
    X_GEN_TAC `y:real^1` THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`&0`; `t:real`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_EQ] THEN STRIP_TAC THEN EXISTS_TAC `t:real` THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y | pastecart (lift(&0)) (y:real^1) IN TS}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `(\z. chart_jac (chart_at atlas ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z))))
                   (c:(A->bool)#(A->real^N)) (f (drop(fstcart z)) (drop(sndcart z)))
                   ((Z:real->real->real^N) (drop(fstcart z)) (drop(sndcart z)))) o
    (\y:real^1. pastecart (lift(&0)) y)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                mfd_field_rep];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `TS:real^(1,1)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

(* ========================================================================= *)
(* A Jacobi field with Y(0) = 0 along t -> exp_x(t u) is a                   *)
(* smooth field (cmp_sfield) on any open interval J around 0 on which the    *)
(* exp family t (u + s w) stays in the domain: it agrees there with the      *)
(* variation field of that smooth family.                                    *)
(* ========================================================================= *)

let CMPS_JACOBI_SFIELD = prove
 (`!top atlas (g:A->real^N^N) (x:A) u w (Y:real->real^N) d J.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < d /\
        real_open J /\ is_realinterval J /\ &0 IN J /\
        (!s r. abs s < d /\ r IN J ==> r % (u + s % w) IN mfd_exp_dom (top,atlas) g x) /\
        mfd_jacobi atlas g (mfd_geo (top,atlas) g x u)
                   (mfd_geo_maxint (top,atlas) g x u) Y /\
        Y(&0) = vec 0 /\ mfd_covd atlas g (mfd_geo (top,atlas) g x u) Y (&0) = w
        ==> cmp_sfield atlas (mfd_geo (top,atlas) g x u) J Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `fam = \s r. mfd_exp (top,atlas) (g:A->real^N^N) (x:A) (r % (u + s % w))` THEN
  SUBGOAL_THEN `!r. r IN J ==> r % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  (LABEL_TAC "dom0") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`&0`; `r:real`] (ASSUME
      `!s r. abs s < d /\ r IN J
             ==> r % ((u:real^N) + s % w) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_0]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (fam:real->real->A)
                  (real_interval(--d,d)) J`
  ASSUME_TAC THENL
   [EXPAND_TAC "fam" THEN
    REWRITE_TAC[cmp_family; REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `w:real^N`;
                   `real_interval(--d,d)`; `J:real->bool`] GEOJV_EXP_FAMILY_CHARTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ASSUME
        `!s r. abs s < d /\ r IN J
               ==> r % ((u:real^N) + s % w) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `fam:real->real->A`; `real_interval(--d,d)`; `J:real->bool`]
    CMPV_VEL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `fam:real->real->A`; `real_interval(--d,d)`; `J:real->bool`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                          (\s'. (fam:real->real->A) s' t) s`] CMPS_FFIELD_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC CMPS_SFIELD_CONG THEN
  EXISTS_TAC `(fam:real->real->A) (&0)` THEN
  EXISTS_TAC `(\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                       (\s'. (fam:real->real->A) s' t) s) (&0)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  EXPAND_TAC "fam" THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `r:real`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `w:real^N`; `Y:real->real^N`;
                 `r:real`] MFD_EXP_DIFFERENTIAL_JACOBI_RAY) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `\s:real. r % ((u:real^N) + s % w)`;
                 `r % (w:real^N)`; `&0`] GEOG_DEXP_CURVE) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN
   `(\s:real^1. r % ((u:real^N) + drop s % w)) = (\s. r % u + drop s % (r % w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GEOG_AFFINE_VD] THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Index-form identities along a geodesic: the bilinear                      *)
(* splitting of the index density, and the integration by parts for a        *)
(* Jacobi field (the integrand of I(Y,W) is d/dt g(DY, W)).                  *)
(* ========================================================================= *)

let CMPS_G_SYM = prove
 (`!top atlas (g:A->real^N^N) (p:A) u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        p IN topspace top
        ==> u dot (g p ** v) = v dot (g p ** u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] RIEMANNIAN_METRIC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC DOT_SYM);;

let CMPS_JACOBI_PAIR_FTC = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) W a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ mfd_jacobi atlas g gamma J Y /\
        mfd_field_diff atlas gamma W J /\ a <= b /\ real_interval[a,b] SUBSET J
        ==> ((\t. mfd_covd atlas g gamma Y t dot
                  (g(gamma t) ** mfd_covd atlas g gamma W t) -
                  W t dot (g(gamma t) **
                           mfd_riemann atlas g (gamma t) (Y t)
                             (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)))
             has_real_integral
             (mfd_covd atlas g gamma Y b dot (g(gamma b) ** W b) -
              mfd_covd atlas g gamma Y a dot (g(gamma a) ** W a)))
            (real_interval[a,b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t dot
         (g(gamma t) ** (W:real->real^N) t)`;
    `\t. mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t dot
         (g(gamma t) ** mfd_covd atlas g gamma (W:real->real^N) t) -
         W t dot (g(gamma t) **
                  mfd_riemann atlas g (gamma t) (Y t)
                    (mfd_vel atlas gamma t) (mfd_vel atlas gamma t))`;
    `a:real`; `b:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN `(t:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N)` THEN
  REWRITE_TAC[mfd_jacobi] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `t:real`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (VECTOR_ARITH `a + b:real^N = vec 0 ==> a = --b`)) THEN
  SUBGOAL_THEN
   `lift(mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t dot
         (g(gamma t) ** mfd_covd atlas g gamma (W:real->real^N) t) -
         W t dot (g(gamma t) **
                  mfd_riemann atlas g (gamma t) (Y t)
                    (mfd_vel atlas gamma t) (mfd_vel atlas gamma t))) =
    lift(mfd_covd atlas g gamma (mfd_covd atlas g gamma Y) t dot (g(gamma t) ** W t) +
         mfd_covd atlas g gamma Y t dot (g(gamma t) ** mfd_covd atlas g gamma W t))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_REWRITE_TAC[DOT_LNEG] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`;
                   `mfd_riemann atlas (g:A->real^N^N) ((gamma:real->A) t)
                      ((Y:real->real^N) t) (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)`;
                   `(W:real->real^N) t`] CMPS_G_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_COVD_METRIC THEN EXISTS_TAC `top:A topology` THEN
  EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] GEOL_GEODESIC_BASIC) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a':real`; `b':real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_SIMP_TAC[]);;

let CMPS_IDENS_SPLIT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) W e t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        mfd_field_diff atlas gamma Y J /\ mfd_field_diff atlas gamma W J /\ t IN J
        ==> cmp_idens atlas g gamma (\s. Y s + e % W s) t =
            cmp_idens atlas g gamma Y t +
            &2 * e * (mfd_covd atlas g gamma Y t dot
                      (g(gamma t) ** mfd_covd atlas g gamma W t) -
                      W t dot (g(gamma t) **
                               mfd_riemann atlas g (gamma t) (Y t)
                                 (mfd_vel atlas gamma t) (mfd_vel atlas gamma t))) +
            e pow 2 * cmp_idens atlas g gamma W t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. (Y:real->real^N) s + e % W s) = (\s. &1 % Y s + e % W s)`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[cmp_idens] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `W:real->real^N`; `&1`; `e:real`; `t:real`] CMPG_COVD_LIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] GEOL_GEODESIC_BASIC) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a:real`; `b:real`]
      MFD_GEODESIC_C1_CURVE) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    CMPF_RIEMANN_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_riemann atlas (g:A->real^N^N) ((gamma:real->A) t) ((Y:real->real^N) t + e % W t)
      (mfd_vel atlas gamma t) (mfd_vel atlas gamma t) =
    mfd_riemann atlas g (gamma t) (Y t) (mfd_vel atlas gamma t) (mfd_vel atlas gamma t) +
    e % mfd_riemann atlas g (gamma t) (W t) (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_ADD th)]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL th)]);
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`;
                 `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (W:real->real^N) t`;
                 `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t`]
    CMPS_G_SYM) THEN
  MP_TAC(INST [`mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`,
               `w:real^N`]
    (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
             `g:A->real^N^N`; `(gamma:real->A) t`; `(Y:real->real^N) t`;
             `(W:real->real^N) t`] CMPF_RIEMANN_PAIR_SYM)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Ingredients of Jacobi's theorem: restriction of smooth                    *)
(* fields, vanishing of Jacobi fields with zero data, and the second         *)
(* variation of the two pieces of the broken test field.                     *)
(* ========================================================================= *)

let CMPS_SFIELD_SUBSET = prove
 (`!atlas (gamma:real->A) J J' (X:real->real^N).
        cmp_sfield atlas gamma J X /\ J' SUBSET J ==> cmp_sfield atlas gamma J' X`,
  REWRITE_TAC[cmp_sfield] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `{lift t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let CMPS_GEODESIC_CURVES = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J
        ==> real_open J /\ is_realinterval J /\
            !a b. a <= b /\ real_interval[a,b] SUBSET J
                  ==> mfd_c1_curve (top,atlas) gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] GEOL_GEODESIC_BASIC) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_SIMP_TAC[]);;

let CMPS_JACOBI_VANISH = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) s0 t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ mfd_jacobi atlas g gamma J Y /\
        s0 IN J /\ Y s0 = vec 0 /\ mfd_covd atlas g gamma Y s0 = vec 0 /\ t IN J
        ==> mfd_covd atlas g gamma Y t = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPS_GEODESIC_CURVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN J ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
                                 (\s. vec 0:real^N) s = vec 0`
  (LABEL_TAC "c0") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOJ_COVD_ZERO THEN
    EXISTS_TAC `top:A topology` THEN EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN J ==> ?d. &0 < d /\ !r. abs(r - s) < d ==> r IN J`
  (LABEL_TAC "op") THENL
   [UNDISCH_TAC `real_open J` THEN REWRITE_TAC[real_open] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) J (\s. vec 0:real^N)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_jacobi] THEN
    SUBGOAL_THEN `mfd_field_diff atlas (gamma:real->A) (\s. vec 0:real^N) J` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOJ_FIELD_DIFF_ZERO THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN EXISTS_TAC `\s:real. vec 0:real^N` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) s IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) s`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) s`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) s`]
      CMPF_RIEMANN_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_ADD_RID] THEN
    USE_THEN "op" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(s:real) IN J`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\s. vec 0:real^N) s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN USE_THEN "c0" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `s0:real`;
                 `vec 0:real^N`; `vec 0:real^N`] MFD_JACOBI_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y0:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "u0"))))) THEN
  SUBGOAL_THEN `!s. s IN J ==> (Y:real->real^N) s = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "u0" (MP_TAC o SPEC `Y:real->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `s:real`)] THEN
    USE_THEN "u0" (MP_TAC o SPEC `\s:real. vec 0:real^N`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o SPEC `s:real`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "op" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(t:real) IN J`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\s. vec 0:real^N) t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

(* The first piece Y + e W on [0,sc], for a Jacobi field Y vanishing at 0    *)
(* and sc and a field W with W(0) = 0.                                       *)

let CMPS_FIRST_PIECE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) W sc.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ mfd_jacobi atlas g gamma J Y /\
        mfd_field_diff atlas gamma W J /\ &0 <= sc /\ real_interval[&0,sc] SUBSET J /\
        Y(&0) = vec 0 /\ Y sc = vec 0 /\ W(&0) = vec 0 /\
        (\r. cmp_idens atlas g gamma W r) real_integrable_on real_interval[&0,sc]
        ==> !e. ((\r. &2 * cmp_idens atlas g gamma (\s. Y s + e % W s) r)
                 has_real_integral
                 (&4 * e * (mfd_covd atlas g gamma Y sc dot (g(gamma sc) ** W sc)) +
                  e pow 2 * (&2 * real_integral (real_interval[&0,sc])
                                    (\r. cmp_idens atlas g gamma W r))))
                (real_interval[&0,sc])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN
  SUBGOAL_THEN `mfd_field_diff atlas (gamma:real->A) (Y:real->real^N) J` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_jacobi]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `Y:real->real^N`; `&0`; `sc:real`] CMPS_JACOBI_PAIR_FTC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_SUB_REFL] THEN
  DISCH_THEN(LABEL_TAC "iy") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `W:real->real^N`; `&0`; `sc:real`] CMPS_JACOBI_PAIR_FTC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_SUB_RZERO] THEN
  DISCH_THEN(LABEL_TAC "iw") THEN
  FIRST_X_ASSUM(LABEL_TAC "ii" o MATCH_MP REAL_INTEGRABLE_INTEGRAL o check (fun th ->
    can (find_term ((=) `real_integrable_on`)) (concl th))) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\r. (&2 * (mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) r dot
               (g(gamma r) ** mfd_covd atlas g gamma Y r) -
               Y r dot (g(gamma r) **
                        mfd_riemann atlas g (gamma r) (Y r)
                          (mfd_vel atlas gamma r) (mfd_vel atlas gamma r))) +
         (&4 * e) * (mfd_covd atlas g gamma Y r dot
                     (g(gamma r) ** mfd_covd atlas g gamma (W:real->real^N) r) -
                     W r dot (g(gamma r) **
                              mfd_riemann atlas g (gamma r) (Y r)
                                (mfd_vel atlas gamma r) (mfd_vel atlas gamma r)))) +
        e pow 2 * (&2 * cmp_idens atlas g gamma W r)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                   `W:real->real^N`; `e:real`; `r:real`] CMPS_IDENS_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[cmp_idens] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * e * (mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) sc dot
              (g(gamma sc) ** (W:real->real^N) sc)) +
    e pow 2 * (&2 * real_integral (real_interval[&0,sc])
                      (\r. cmp_idens atlas g gamma W r)) =
    (&2 * &0 + (&4 * e) * (mfd_covd atlas g gamma Y sc dot (g(gamma sc) ** W sc))) +
    e pow 2 * (&2 * real_integral (real_interval[&0,sc])
                      (\r. cmp_idens atlas g gamma W r))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    USE_THEN "ii" (ACCEPT_TAC o BETA_RULE)]);;

let CMPS_SECOND_PIECE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Fr:num->real->real^N) j a b p q e.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J Fr /\
        1 <= j /\ j <= dimindex(:N) /\ p <= q /\ real_interval[p,q] SUBSET J
        ==> real_integral (real_interval[p,q])
              (\t. &2 * cmp_idens atlas g gamma (\t. (e * a + e * b * t) % Fr j t) t) =
            e pow 2 * real_integral (real_interval[p,q])
              (\t. &2 * cmp_idens atlas g gamma (\t. (a + b * t) % Fr j t) t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `Fr:num->real->real^N`; `j:num`; `e * a`; `e * b`; `p:real`; `q:real`]
    CMPI_PIECE_INTEGRAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `Fr:num->real->real^N`; `j:num`; `a:real`; `b:real`; `p:real`; `q:real`]
    CMPI_PIECE_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `e * a + (e * b) * t = e * a + e * b * t`] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[p,q])
      (\t. (e * a + e * b * t) pow 2 *
           cmp_rmat atlas (g:A->real^N^N) (gamma:real->A) (Fr:num->real->real^N) t$j$j) =
    e pow 2 * real_integral (real_interval[p,q])
      (\t. (a + b * t) pow 2 * cmp_rmat atlas g gamma Fr t$j$j)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[p,q])
      (\t. e pow 2 * ((a + b * t) pow 2 *
           cmp_rmat atlas (g:A->real^N^N) (gamma:real->A) (Fr:num->real->real^N) t$j$j))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC REAL_RING;
      MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]];
    CONV_TAC REAL_RING]);;

(* ========================================================================= *)
(* S5 (c), Jacobi's theorem: along a minimizing exp_x(s v),                  *)
(* s in [0,1], d exp_x is injective at t v for t < 1.  A kernel vector gives *)
(* a nontrivial Jacobi field Y with Y(0) = Y(sc) = 0, sc = t |v| < |v|; the  *)
(* broken field Y + e W1 on [0,sc], e W2 after sc has negative second        *)
(* variation for small e > 0, contradicting CMPI_SECVAR_NONNEG.              *)
(* ========================================================================= *)

let CMPS_QUAD_NEG = prove
 (`!k c. k < &0 ==> ?e. &0 < e /\ &4 * e * k + e pow 2 * c < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < abs c + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `--k / (abs c + &1)` THEN
  SUBGOAL_THEN `&0 < --k / (abs c + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `--k / (abs c + &1) * (abs c + &1) = --k` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ABBREV_TAC `e = --k / (abs c + &1)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `e * c <= e * abs c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * k + e * c < &0` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`e * (abs c + &1) = --k`; `e * c <= e * abs c`;
                           `k < &0`; `&0 < e`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`e:real`; `--(&4 * k + e * c)`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC);;

let CMPS_SUM_TWO = prove
 (`!f. sum(1..2) f = f 1 + f 2`,
  GEN_TAC THEN REWRITE_TAC[num_CONV `2`; num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let CMPS_NO_CONJUGATE = prove
 (`!top atlas (g:A->real^N^N) (x:A) v t h.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v /\
        &0 <= t /\ t < &1 /\
        mfd_differential (open_set_atlas (:real^N)) atlas
          (mfd_exp (top,atlas) g x) (t % v) h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0 \/ mfd_tnorm (g:A->real^N^N) (x:A) v = &0` THENL
   [SUBGOAL_THEN `t % (v:real^N) = vec 0` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_differential (open_set_atlas (:real^N)) atlas
                   (mfd_exp (top,atlas) (g:A->real^N^N) (x:A)) (t % v) h = vec 0` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM] o
                check (is_neg o concl)) THEN
  SUBGOAL_THEN `&0 < t /\ &0 < mfd_tnorm (g:A->real^N^N) (x:A) v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `u = inv(mfd_tnorm (g:A->real^N^N) (x:A) v) % v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] CMPI_UNIT_GEO) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) (x:A) u` THEN
  ABBREV_TAC `G = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ggeo") (CONJUNCTS_THEN2 (LABEL_TAC "gI")
    (CONJUNCTS_THEN2 (LABEL_TAC "g0") (CONJUNCTS_THEN2 (LABEL_TAC "gL")
      (CONJUNCTS_THEN2 (LABEL_TAC "gv0") (CONJUNCTS_THEN2 (LABEL_TAC "gunit")
        (CONJUNCTS_THEN2 (LABEL_TAC "vI") (LABEL_TAC "vrel")))))))) THEN
  ABBREV_TAC `sc = t * mfd_tnorm (g:A->real^N^N) (x:A) v` THEN
  SUBGOAL_THEN `&0 < sc /\ sc < mfd_tnorm (g:A->real^N^N) (x:A) v` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sc" THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sc % (u:real^N) = t % v` ASSUME_TAC THENL
   [EXPAND_TAC "sc" THEN
    SUBST1_TAC(SYM(ASSUME `inv(mfd_tnorm (g:A->real^N^N) (x:A) v) % v = u`)) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(mfd_tnorm (g:A->real^N^N) (x:A) v = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `w = inv sc % (h:real^N)` THEN
  SUBGOAL_THEN `~(w:real^N = vec 0) /\ sc % w = h` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC;
                 REAL_MUL_RINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= mfd_tnorm (g:A->real^N^N) (x:A) v ==> (p:real) IN G`
  (LABEL_TAC "inG") THENL
   [USE_THEN "gI" (fun th -> REWRITE_TAC[REWRITE_RULE[SUBSET; IN_REAL_INTERVAL] th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 IN G /\ sc IN G` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`; `&0`;
                 `vec 0:real^N`; `w:real^N`] MFD_JACOBI_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  SUBGOAL_THEN `t % (v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real->real^N) sc = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `w:real^N`; `Y:real->real^N`;
                   `sc:real`] MFD_EXP_DIFFERENTIAL_JACOBI_RAY) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) sc = vec 0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`; `Y:real->real^N`;
                   `sc:real`; `&0`] CMPS_JACOBI_VANISH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) (x:A) u = &1` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `inv(mfd_tnorm (g:A->real^N^N) (x:A) v) % v = u`)) THEN
    ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPI_FRAME_UNIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?j. 1 <= j /\ j <= dimindex(:N) /\
        ~((Fr:num->real->real^N) j sc dot
          ((g:A->real^N^N) ((gamma:real->A) sc) **
           mfd_covd atlas g gamma (Y:real->real^N) sc) = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[TAUT `a /\ b /\ ~c <=> ~(a /\ b ==> c)`; GSYM NOT_FORALL_THM] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) sc =
                   vec 0)` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `G:real->bool`; `Fr:num->real->real^N`;
                   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N)`;
                   `sc:real`] CMPF_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `cmp_fcoord (g:A->real^N^N) (gamma:real->A) (Fr:num->real->real^N)
        (mfd_covd atlas g gamma (Y:real->real^N)) sc = vec 0`
    SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[CMPF_FCOORD_COMPONENT];
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  ABBREV_TAC
   `cj = (Fr:num->real->real^N) j sc dot
         ((g:A->real^N^N) ((gamma:real->A) sc) **
          mfd_covd atlas g gamma (Y:real->real^N) sc)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)`; `sc % (u:real^N)`;
                 `sc % (w:real^N)`] GEOG_FAMILY_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `e0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "famd")))))) THEN
  SUBGOAL_THEN `&0 < e0 * sc` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s r. abs s < d0 /\ r IN real_interval(--(e0 * sc),(&1 + e0) * sc)
          ==> r % ((u:real^N) + s % w) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) (x:A)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `r % ((u:real^N) + s % w) = (r / sc) % (t % v + s % h)`
    SUBST1_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `sc % (u:real^N) = t % v`)) THEN
      SUBST1_TAC(SYM(ASSUME `sc % (w:real^N) = h`)) THEN
      REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < sc` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "famd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `w:real^N`; `Y:real->real^N`;
                 `d0:real`; `real_interval(--(e0 * sc),(&1 + e0) * sc)`]
    CMPS_JACOBI_SFIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL;
                    IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ABBREV_TAC `dd = min (mfd_tnorm (g:A->real^N^N) (x:A) v) ((&1 + e0 / &2) * sc)` THEN
  SUBGOAL_THEN `sc < dd /\ dd <= mfd_tnorm (g:A->real^N^N) (x:A) v /\
                dd < (&1 + e0) * sc /\ &0 < dd`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN
    MAP_EVERY UNDISCH_TAC [`&0 < e0 * sc`; `&0 < sc`;
                           `sc < mfd_tnorm (g:A->real^N^N) (x:A) v`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `JJ = real_interval(--(e0 * sc),(&1 + e0) * sc) INTER (G:real->bool)` THEN
  SUBGOAL_THEN
   `real_open JJ /\ is_realinterval JJ /\ JJ SUBSET G /\
    JJ SUBSET real_interval(--(e0 * sc),(&1 + e0) * sc) /\
    real_interval[&0,dd] SUBSET JJ`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`] GEOL_GEODESIC_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "JJ" THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_OPEN_INTER THEN ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IS_REALINTERVAL_INTER THEN ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) JJ` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `G:real->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) (&0)) (gamma dd) = dd`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= dd / mfd_tnorm (g:A->real^N^N) (x:A) v /\
                  dd / mfd_tnorm g x v <= &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) (x:A)
                    ((dd / mfd_tnorm g x v) % v) = (gamma:real->A) dd`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `dd / mfd_tnorm (g:A->real^N^N) (x:A) v IN
                    mfd_geo_maxint (top,atlas) g x v` ASSUME_TAC THENL
       [USE_THEN "vI" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `v:real^N`;
                     `dd / mfd_tnorm (g:A->real^N^N) (x:A) v`] MFD_EXP_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
      USE_THEN "vrel" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `dd / mfd_tnorm (g:A->real^N^N) (x:A) v IN
                 mfd_geo_maxint (top,atlas) g x v`))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
      AP_TERM_TAC THEN
      UNDISCH_TAC `~(mfd_tnorm (g:A->real^N^N) (x:A) v = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`;
                   `dd / mfd_tnorm (g:A->real^N^N) (x:A) v`] CMPS_RAY_DIST0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `~(mfd_tnorm (g:A->real^N^N) (x:A) v = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the frame field Fr j and the fields along gamma on JJ *)
  SUBGOAL_THEN `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) G
                  ((Fr:num->real->real^N) j)` ASSUME_TAC THENL
   [UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) G
                   (Fr:num->real->real^N)` THEN
    REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_sfield atlas (gamma:real->A) G ((Fr:num->real->real^N) j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPI_PARALLEL_SFIELD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. cmp_sfield atlas (gamma:real->A) JJ
                        (\r. (a + b * r) % (Fr:num->real->real^N) j r)`
  (LABEL_TAC "aff") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CMPS_SFIELD_SUBSET THEN
    EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPI_SFIELD_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_sfield atlas (gamma:real->A) JJ (Y:real->real^N) /\
                mfd_jacobi atlas (g:A->real^N^N) gamma JJ Y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CMPS_SFIELD_SUBSET THEN
      EXISTS_TAC `real_interval(--(e0 * sc),(&1 + e0) * sc)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC GEOJV_JACOBI_SUBSET THEN EXISTS_TAC `G:real->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. mfd_field_diff atlas (gamma:real->A)
                        (\r. (a + b * r) % (Fr:num->real->real^N) j r) JJ`
  (LABEL_TAC "affd") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `JJ:real->bool`] CMPS_GEODESIC_CURVES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) G
                     ((Fr:num->real->real^N) j)` THEN
      REWRITE_TAC[mfd_parallel; mfd_field_diff] THEN
      DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT1 th)) THEN
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ADD THEN
      REWRITE_TAC[REAL_DIFFERENTIABLE_CONST] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_MUL_ATREAL THEN
      REWRITE_TAC[REAL_DIFFERENTIABLE_CONST; REAL_DIFFERENTIABLE_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r <= dd ==> (r:real) IN JJ` (LABEL_TAC "inJJ") THENL
   [UNDISCH_TAC `real_interval[&0,dd] SUBSET JJ` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sc = &0) /\ ~(dd - sc = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b1 = --cj / sc` THEN
  ABBREV_TAC `a2 = --cj * dd / (dd - sc)` THEN
  ABBREV_TAC `b2 = cj / (dd - sc)` THEN
  SUBGOAL_THEN
   `!r. r IN real_interval[&0,sc]
        ==> cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
              (\r. (&0 + b1 * r) % (Fr:num->real->real^N) j r) r =
            b1 pow 2 - (&0 + b1 * r) pow 2 * cmp_rmat atlas g gamma Fr r$j$j`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMPI_IDENS_FRAME THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `G:real->bool`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
           (\r. (&0 + b1 * r) % (Fr:num->real->real^N) j r) r)
    real_integrable_on real_interval[&0,sc]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC `\r. b1 pow 2 - (&0 + b1 * r) pow 2 *
                    cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                      (Fr:num->real->real^N) r$j$j` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`;
                   `Fr:num->real->real^N`; `j:num`; `&0`; `b1:real`; `&0`; `sc:real`]
      CMPI_PIECE_INTEGRAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `JJ:real->bool`; `Y:real->real^N`;
                 `\r. (&0 + b1 * r) % (Fr:num->real->real^N) j r`; `sc:real`]
    CMPS_FIRST_PIECE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inJJ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "p1" o BETA_RULE)] THEN
  SUBGOAL_THEN `(gamma:real->A) sc IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `G:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) sc dot
    (g(gamma sc) ** ((&0 + b1 * sc) % (Fr:num->real->real^N) j sc)) = --(cj * cj)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `&0 + b1 * sc = --cj` SUBST1_TAC THENL
     [EXPAND_TAC "b1" THEN UNDISCH_TAC `~(sc = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) sc`;
                   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) sc`;
                   `(Fr:num->real->real^N) j sc`] CMPS_G_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`--(cj * cj)`;
    `&2 * real_integral (real_interval[&0,sc])
            (\t. cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
                   (\r. (&0 + b1 * r) % (Fr:num->real->real^N) j r) t) +
     real_integral (real_interval[sc,dd])
       (\t. &2 * cmp_idens atlas g gamma (\t. (a2 + b2 * t) % Fr j t) t)`]
    CMPS_QUAD_NEG) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < &0`) THEN ASM_REWRITE_TAC[REAL_LT_SQUARE];
    DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `gamma:real->A`; `JJ:real->bool`; `dd:real`; `2`;
    `\i. if i = 0 then &0 else if i = 1 then sc else dd`;
    `\i. if i = 1 then (\s. (Y:real->real^N) s +
                            eps % ((&0 + b1 * s) % (Fr:num->real->real^N) j s))
         else (\r. (eps * a2 + eps * b2 * r) % Fr j r)`]
    CMPI_SECVAR_NONNEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "gunit" MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[cmp_pwfield] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
       [ASM_ARITH_TAC; DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC CMPS_SFIELD_CONG THEN
        MAP_EVERY EXISTS_TAC
         [`gamma:real->A`;
          `\t. &1 % (Y:real->real^N) t +
               eps % (\r. (&0 + b1 * r) % (Fr:num->real->real^N) j r) t`] THEN
        CONJ_TAC THENL [REWRITE_TAC[VECTOR_MUL_LID]; ALL_TAC] THEN
        MATCH_MP_TAC CMPS_SFIELD_LIN THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN
        ASM_REWRITE_TAC[];
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]];
      GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MAP_EVERY EXPAND_TAC ["b1"; "a2"; "b2"] THEN
      MAP_EVERY UNDISCH_TAC [`~(sc = &0)`; `~(dd - sc = &0)`] THEN
      CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; VECTOR_MUL_LZERO;
                      VECTOR_MUL_RZERO; VECTOR_ADD_LID];
      SUBGOAL_THEN `eps * a2 + eps * b2 * dd = &0` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["a2"; "b2"] THEN
        UNDISCH_TAC `~(dd - sc = &0)` THEN CONV_TAC REAL_FIELD;
        REWRITE_TAC[VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_secvar; CMPS_SUM_TWO] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  USE_THEN "p1" (fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_UNIQUE (SPEC `eps:real` th)]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`;
                 `Fr:num->real->real^N`; `j:num`; `a2:real`; `b2:real`; `sc:real`;
                 `dd:real`; `eps:real`] CMPS_SECOND_PIECE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&4 * eps * --(cj * cj) +
               eps pow 2 *
               (&2 * real_integral (real_interval[&0,sc])
                       (\t. cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
                              (\r. (&0 + b1 * r) % (Fr:num->real->real^N) j r) t) +
                real_integral (real_interval[sc,dd])
                  (\t. &2 * cmp_idens atlas g gamma (\t. (a2 + b2 * t) % Fr j t) t)) <
               &0` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The headline S5, MT Prop 1.20.                                            *)
(* ========================================================================= *)

let CMP_MINIMIZING_GEODESIC = prove
 (`!u n. CMP_MINIMIZING_GEODESIC_STATEMENT (u:A->bool) (n:N->bool)`,
  REWRITE_TAC[CMP_MINIMIZING_GEODESIC_STATEMENT] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] CMPS_RAY_DIST0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`; `w:real^N`]
      CMPS_UNIQUE) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`; `h:real^N`]
      CMPS_NO_CONJUGATE) THEN
    ASM_REWRITE_TAC[]]);;

