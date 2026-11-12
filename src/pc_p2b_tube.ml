(* ========================================================================= *)
(* pc_p2b_tube: Part I of the bad-tube half of MT Thm 10.2 (Sec 10.3).  MT   *)
(* Claim 10.3 in incomplete slices: a constant-speed shortest curve between  *)
(* a point of low and a point of high curvature, obtained by confining the   *)
(* points between them (A.1 at separating necks) to a compact region and a   *)
(* local Hopf-Rinow argument for such pairs.                                 *)
(* ========================================================================= *)

needs "src/pc_p2b_tubestmts.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_cmp_mgeo.ml";;
needs "src/pc_cmp_seg.ml";;
needs "src/pc_apx_a13.ml";;
needs "src/pc_apx_a21.ml";;
needs "src/pc_p2b_scalpos.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* A local Hopf-Rinow theorem for pairs whose between points lie in a        *)
(* compact set.  P2BT_GEOH_EXTEND_T and P2BT_HR_BETWEEN are variants of      *)
(* GEOH_EXTEND and MFD_LOCAL_HOPF_RINOW of pc_geo_hr: the exponential domain *)
(* is only assumed on [0,T] instead of [0,R] in the first, and is derived    *)
(* from the compactness of the between set in the second.                    *)
(* ========================================================================= *)

let P2BT_GEOH_EXTEND_T = prove
 (`!top atlas (g:A->real^N^N) (x:A) u y R Tm tt.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_tnorm g x u = &1 /\
        (!t. &0 <= t /\ t <= Tm ==> t % u IN mfd_exp_dom (top,atlas) g x) /\
        mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y = R /\
        &0 < tt /\ tt < R /\ tt < Tm /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u tt) y = R - tt
        ==> ?d. &0 < d /\ tt + d <= R /\ tt + d <= Tm /\
                mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u (tt + d)) y =
                R - (tt + d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `Tm:real`] GEOH_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "exp")
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") (LABEL_TAC "seg")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `ga = mfd_geo (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x u` THEN
  ABBREV_TAC `I0 = mfd_geo_maxint (top,atlas:((A->bool)#(A->real^N))->bool)
                     (g:A->real^N^N) x u` THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= Tm ==> t IN I0` (LABEL_TAC "inI") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `real_interval[&0,Tm] SUBSET I0` THEN
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
  ABBREV_TAC `d = min (dd / &3) (min ((R - tt) / &2) (Tm - tt))` THEN
  SUBGOAL_THEN `&0 < d /\ d <= dd / &3 /\ d <= (R - tt) / &2 /\ d <= Tm - tt` STRIP_ASSUME_TAC THENL
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
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(ga:real->A)(tt + d) = z` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "rayp" (MP_TAC o SPEC `eta + d`) THEN
    REWRITE_TAC[REAL_ARITH `(tt - eta) + (eta + d) = tt + d`] THEN
    ANTS_TAC THENL [USE_THEN "inI" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Local Hopf-Rinow.                                                         *)
(* ========================================================================= *)

(* Membership in the maximal interval of the geodesic in direction u is   *)
(* membership of the multiple in the exponential domain.                   *)

let P2BT_IN_MAXINT = prove
 (`!top atlas (g:A->real^N^N) (x:A) u t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top
     ==> (t IN mfd_geo_maxint (top,atlas) g x u <=> t % u IN mfd_exp_dom (top,atlas) g x)`,
  SIMP_TAC[MFD_EXP_RADIAL]);;

(* The ray in a unit direction u that starts towards y and stays minimizing *)
(* towards y as long as it is defined reaches y at time R = d(x,y), if all  *)
(* points between x and y lie in a compact set K (the exponential domain on *)
(* [0,R] follows: the ray cannot escape K while it is minimizing).          *)

let P2BT_RAY_REACH = prove
 (`!top atlas (g:A->real^N^N) (x:A) u y K R dl.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\ mfd_tnorm g x u = &1 /\
     mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y = R /\
     compact_in top K /\
     (!b. mfd_joinable (top,atlas) x b /\ mfd_joinable (top,atlas) b y /\
          mfd_dist (top,atlas) g x b + mfd_dist (top,atlas) g b y = R ==> b IN K) /\
     &0 < dl /\ dl < R /\
     (!t. &0 <= t /\ t <= dl ==> t % u IN mfd_exp_dom (top,atlas) g x) /\
     mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u dl) y = R - dl
     ==> (!t. &0 <= t /\ t <= R ==> t % u IN mfd_exp_dom (top,atlas) g x) /\
         mfd_geo (top,atlas) g x u R = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the facts along an initial segment on which the ray is defined *)
  SUBGOAL_THEN
   `!t. &0 <= t /\ (!s. &0 <= s /\ s <= t ==> s % u IN mfd_exp_dom (top,atlas) g x)
        ==> mfd_joinable (top,atlas) x (mfd_geo (top,atlas) (g:A->real^N^N) x u t) /\
            mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x u t) <= t`
  (LABEL_TAC "seg") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `t:real`] GEOH_RAY_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `t:real`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_SUB_RZERO] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ (!s. &0 <= s /\ s <= t ==> s % u IN mfd_exp_dom (top,atlas) g x) /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) (g:A->real^N^N) x u t) y = R - t
        ==> mfd_geo (top,atlas) g x u t IN K`
  (LABEL_TAC "inK") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas) (mfd_geo (top,atlas) (g:A->real^N^N) x u t) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN
      ASM_MESON_TAC[MFD_JOINABLE_SYM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `mfd_geo (top,atlas) (g:A->real^N^N) x u t`;
                   `y:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `S = {t | dl <= t /\ t <= R /\
             (!s. &0 <= s /\ s <= t ==> s % u IN mfd_exp_dom (top,atlas) g x) /\
             mfd_dist (top,atlas) g (mfd_geo (top,atlas) (g:A->real^N^N) x u t) y = R - t}` THEN
  SUBGOAL_THEN `(dl:real) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN S ==> dl <= t /\ t <= R /\
                     (!s. &0 <= s /\ s <= t ==> s % u IN mfd_exp_dom (top,atlas) g x) /\
                     mfd_dist (top,atlas) g (mfd_geo (top,atlas) (g:A->real^N^N) x u t) y =
                     R - t`
  (LABEL_TAC "Sdef") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `R:real` THEN ASM_MESON_TAC[]]; ALL_TAC] THEN
  ABBREV_TAC `ts = sup (S:real->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN `dl <= ts /\ ts <= R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* below ts the ray is defined *)
  SUBGOAL_THEN `!s. &0 <= s /\ s < ts ==> s % u IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  (LABEL_TAC "below") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?t. t IN S /\ s < t` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      SUBGOAL_THEN `ts <= s:real` MP_TAC THENL
       [USE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "Sdef" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* ts is in the maximal interval: otherwise the ray escapes K *)
  SUBGOAL_THEN `ts IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `!t. t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u ==> t < ts`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(ts IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u)` THEN
      REWRITE_TAC[] THEN
      UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u)` THEN
      REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`&0`; `t:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `K:A->bool`; `ts:real`]
      MFD_GEO_ESCAPE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "esc"))) THEN
    SUBGOAL_THEN `t1 < ts` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?t. t IN S /\ t1 < t` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      SUBGOAL_THEN `ts <= t1:real` MP_TAC THENL
       [USE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "Sdef" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "esc" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[P2BT_IN_MAXINT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN USE_THEN "inK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= ts ==> s % u IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  (LABEL_TAC "upto") THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real = ts` THENL
     [ASM_SIMP_TAC[GSYM P2BT_IN_MAXINT];
      USE_THEN "below" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* ts is in S: closedness of the minimizing set on [dl,ts] *)
  ABBREV_TAC
   `A0 = {t | t IN real_interval[dl,ts] /\
              mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                       (mfd_geo (top,atlas) g x u t) y + t = R}` THEN
  SUBGOAL_THEN `real_closed (A0:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[dl,ts]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `A0 = {t | t IN topspace (subtopology euclideanreal (real_interval[dl,ts])) /\
                (\t. mfd_dist (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                       (mfd_geo (top,atlas) g x u t) y + t) t IN {R}}`
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
            `mfd_geodesic (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x u) J`)
            (concl th))) THEN
        REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[P2BT_IN_MAXINT] THEN USE_THEN "upto" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      USE_THEN "seg" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
        USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        STRIP_TAC] THEN
      ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real->bool) SUBSET A0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "Sdef" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXPAND_TAC "A0" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN (A0:real->bool) ==> dl <= t /\ t <= ts` ASSUME_TAC THENL
   [EXPAND_TAC "A0" THEN SIMP_TAC[IN_ELIM_THM; IN_REAL_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A0:real->bool`; `ts:real`] REAL_CLOSED_CONTAINS_SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY; SUBSET]; DISCH_TAC] THEN
  MP_TAC(ISPEC `A0:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ubA") (LABEL_TAC "lubA")) THEN
  SUBGOAL_THEN `sup (A0:real->bool) = ts` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [USE_THEN "lubA" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "lub" MATCH_MP_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "ubA" MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x u ts) y = R - ts`
  ASSUME_TAC THENL
   [UNDISCH_TAC `sup (A0:real->bool) IN A0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "A0" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* ts = R, else the ray extends beyond ts *)
  SUBGOAL_THEN `ts:real = R` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `real_open(mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u)` THEN
    REWRITE_TAC[real_open] THEN DISCH_THEN(MP_TAC o SPEC `ts:real`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!t. &0 <= t /\ t <= ts + eta / &2
                      ==> t % u IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_CASES_TAC `t <= ts:real` THENL
       [USE_THEN "upto" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[GSYM P2BT_IN_MAXINT] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `y:A`; `R:real`; `ts + eta / &2`;
                   `ts:real`] P2BT_GEOH_EXTEND_T) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ts + d IN (S:real->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ts + d <= ts:real` MP_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_joinable (top,atlas) (mfd_geo (top,atlas) (g:A->real^N^N) x u R) y`
  ASSUME_TAC THENL
   [USE_THEN "seg" (MP_TAC o SPEC `R:real`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
      USE_THEN "upto" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x u R`; `y:A`]
    MFD_DIST_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x u ts) y = R - ts` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Local Hopf-Rinow for a pair whose between points lie in a compact set   *)
(* (adapted from MFD_LOCAL_HOPF_RINOW of pc_geo_hr): a minimizing          *)
(* geodesic exp_x(t v), t in [0,1], from x to y.                            *)

let P2BT_HR_BETWEEN = prove
 (`!top atlas (g:A->real^N^N) x y K.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
       riemannian_metric atlas g /\ x IN topspace top /\
       mfd_joinable (top,atlas) x y /\ compact_in top K /\
       (!b. mfd_joinable (top,atlas) x b /\ mfd_joinable (top,atlas) b y /\
            mfd_dist (top,atlas) g x b + mfd_dist (top,atlas) g b y =
            mfd_dist (top,atlas) g x y
            ==> b IN K)
       ==> ?v. v IN mfd_exp_dom (top,atlas) g x /\
               mfd_tnorm g x v = mfd_dist (top,atlas) g x y /\
               mfd_exp (top,atlas) g x v = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x d0 SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:A->real^N^N) x d0` THEN
    SIMP_TAC[mfd_inj_ball];
    ALL_TAC] THEN
  ASM_CASES_TAC `R < d0` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `d0:real`] MFD_EXP_BALL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:A` o REWRITE_RULE[EXTENSION]) THEN
    ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `d0:real`; `w:real^N`] MFD_EXP_DIST) THEN
    UNDISCH_TAC `(w:real^N) IN mfd_tball (g:A->real^N^N) x d0` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y = mfd_exp (top,atlas) (g:A->real^N^N) x w` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
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
  SUBGOAL_THEN `!t. &0 <= t /\ t <= dl ==> t % u IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (term_match [] `mfd_tball (g:A->real^N^N) x r SUBSET
                          mfd_exp_dom (top,atlas) g x`) (concl th))) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dl % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_geo (top,atlas) (g:A->real^N^N) x u dl = mfd_exp (top,atlas) g x (dl % u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `dl:real`] MFD_EXP_RADIAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o fst o EQ_IMP_RULE) ASSUME_TAC) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x u dl) y = R - dl`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `y:A`; `K:A->bool`; `R:real`;
                 `dl:real`] P2BT_RAY_REACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `K:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `R % (u:real^N)` THEN
  SUBGOAL_THEN `R % (u:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`; REAL_MUL_RID]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `R:real`] MFD_EXP_RADIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o fst o EQ_IMP_RULE) ASSUME_TAC) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_TAC THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* The sides of a neck sphere, and a curve that leaves the closed upper      *)
(* region of a neck through its negative side crosses the negative quarter.  *)
(* p2bt_half: the lower half of the neck from the level -1/(2 eps) up to the *)
(* central sphere; p2bt_conf: the central sphere, its positive side and that *)
(* half (the region where points between the centre of a separating neck and *)
(* a point on its positive side lie, by A.1).                                *)
(* ========================================================================= *)

let p2bt_half = new_definition
 `p2bt_half (e:real^3->A) (eps:real) =
    IMAGE e {y:real^3 | exp(--inv(&2 * eps) / sqrt(&2)) <= norm y /\ norm y < &1}`;;

let p2bt_conf = new_definition
 `p2bt_conf (top:A topology) (e:real^3->A) (eps:real) =
    IMAGE e (sphere(vec 0,&1)) UNION apx_pos_side top e UNION p2bt_half e eps`;;

(* Basic facts of an eps-neck for small eps: the parametrization, the     *)
(* radii of its domain and the compact central sphere.                    *)

let P2BT_NECK_BASICS = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024
     ==> smooth_manifold_atlas top atlas /\ &0 < eps /\
         mfd_param top atlas (rfs_neck_dom eps) e /\
         exp(--inv eps / sqrt(&2)) < &1 / &4 /\
         exp(--inv eps / sqrt(&2)) < exp(--inv(&2 * eps) / sqrt(&2)) /\
         exp(--inv(&2 * eps) / sqrt(&2)) < &1 /\
         &4 < exp(inv eps / sqrt(&2)) /\
         sphere(vec 0,&1) SUBSET rfs_neck_dom eps /\
         compact_in top (IMAGE e (sphere(vec 0,&1))) /\
         closed_in top (IMAGE e (sphere(vec 0,&1))) /\
         IMAGE e (rfs_neck_dom eps) SUBSET topspace top`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                &0 < eps /\ mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `exp(--(inv(sqrt(&2) * eps))) < &1 / &4` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG];
    REWRITE_TAC[REAL_EXP_MONO_LT; real_div; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&4 < exp(inv(sqrt(&2) * eps))` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_SIMP_TAC[COMPACT_SPHERE; APX_UNIT_SPHERE_NECK_DOM];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_SIMP_TAC[COMPACT_SPHERE; APX_UNIT_SPHERE_NECK_DOM];
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET]]);;

(* A connected set missing the central sphere and meeting the component of *)
(* a point lies in that component (component maximality).                 *)

let P2BT_COMPONENT_ABSORB = prove
 (`!top (S:A->bool) p Tc.
     connected_in top Tc /\ Tc SUBSET topspace top DIFF S /\
     ~(Tc INTER connected_component_of (subtopology top (topspace top DIFF S)) p = {})
     ==> Tc SUBSET connected_component_of (subtopology top (topspace top DIFF S)) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `connected_in (subtopology top (topspace top DIFF S)) (Tc:A->bool)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`; `Tc:A->bool`; `q:A`]
    CONNECTED_COMPONENT_OF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top (topspace top DIFF S)) (q:A) =
    connected_component_of (subtopology top (topspace top DIFF S)) p`
  (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`; `p:A`; `q:A`]
    CONNECTED_COMPONENT_OF_EQUIV) THEN
  UNDISCH_TAC `(q:A) IN connected_component_of (subtopology top (topspace top DIFF S)) p` THEN
  REWRITE_TAC[IN] THEN MESON_TAC[]);;

(* All image points of an annulus of the neck domain that misses the unit *)
(* sphere lie in one component of the complement of the central sphere.  *)

let P2BT_NECK_ANNULUS_COMPONENT = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) a b z.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024 /\
     annulus a b SUBSET rfs_neck_dom eps /\ &0 <= a /\ a < b /\ (&1 <= a \/ b <= &1) /\
     z IN annulus a b
     ==> connected_component_of
           (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
           (e z) = connected_component_of
           (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
           (e(((a + b) / &2) % basis 1))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((a + b) / &2) % basis 1 IN annulus a b :real^3->bool` ASSUME_TAC THENL
   [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) (annulus a b) SUBSET topspace top DIFF IMAGE e (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; NOT_EXISTS_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `w:real^3`; `v:real^3`]
      MFD_PARAM_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    UNDISCH_TAC `(w:real^3) IN annulus a b` THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `annulus a b:real^3->bool`; `e:real^3->A`]
    APX_PARAM_CONNECTED_IMAGE) THEN
  ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3] THEN DISCH_TAC THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ] THEN DISJ2_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    REWRITE_TAC[connected_component_of] THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (annulus a b)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM SET_TAC[]]);;

(* Points of the neck above, resp. below, the central sphere lie on its   *)
(* positive, resp. negative side.                                         *)

let P2BT_NECK_UPPER_LOWER = prove
 (`!top atlas (g:A->real^3^3) eps x e y.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024 /\
     y IN rfs_neck_dom eps
     ==> (&1 < norm y ==> e y IN apx_pos_side top e) /\
         (norm y < &1 ==> e y IN apx_neg_side top e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) \/
                norm(y:real^3) = &1`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `norm(y:real^3) = &1` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; NOT_EXISTS_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`; `y:real^3`; `v:real^3`] MFD_PARAM_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(norm(y:real^3) = &1)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `r0 = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `r1 = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus r0 r1` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN EXPAND_TAC "r0" THEN EXPAND_TAC "r1" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r0 /\ r0 < &1 / &4 /\ &4 < r1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "r0" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) r1 SUBSET rfs_neck_dom eps /\
                annulus r0 (&1) SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN CONJ_TAC THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[apx_pos_side] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `&1`; `r1:real`; `y:real^3`]
      P2BT_NECK_ANNULUS_COMPONENT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `&1`; `r1:real`; `&4 / &3 % basis 1:real^3`]
      P2BT_NECK_ANNULUS_COMPONENT);
    REWRITE_TAC[apx_neg_side] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `r0:real`; `&1`; `y:real^3`]
      P2BT_NECK_ANNULUS_COMPONENT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `r0:real`; `&1`; `&3 / &4 % basis 1:real^3`]
      P2BT_NECK_ANNULUS_COMPONENT)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
     ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
     REWRITE_TAC[ASSUME `rfs_neck_dom eps = annulus r0 r1`; annulus; IN_ELIM_THM] THEN
     ASM_REAL_ARITH_TAC;
     DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  GEN_REWRITE_TAC I [IN] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  UNDISCH_TAC `(e:real^3->A) y IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) \/
               norm(y:real^3) = &1` THEN
  REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) MP_TAC) THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_REAL_ARITH_TAC);;

(* Sphere separation makes the two sides of a neck sphere disjoint.        *)

let P2BT_SIDES_DISJOINT = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     hausdorff_space top /\ apx_sphere_sep top atlas /\
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024
     ==> DISJOINT (apx_pos_side top e) (apx_neg_side top e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_neck_chart top (atlas:((A->bool)#(A->real^3))->bool) (e:real^3->A)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    MP_TAC(SPEC `eps:real` APX22_COLLAR_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET b ==> b SUBSET c ==> a SUBSET c`) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `apx_sphere_sep top (atlas:((A->bool)#(A->real^3))->bool)` THEN
  REWRITE_TAC[apx_sphere_sep] THEN DISCH_THEN(MP_TAC o SPEC `e:real^3->A`) THEN
  ASM_REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN
  REWRITE_TAC[apx_pos_side; apx_neg_side; DISJOINT] THEN
  REWRITE_TAC[CONNECTED_COMPONENT_OF_NONOVERLAP] THEN
  REPEAT DISJ2_TAC THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_EQ] THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  UNDISCH_TAC `(e:real^3->A)(&3 / &4 % basis 1) IN topspace top DIFF
               IMAGE e (sphere(vec 0,&1))` THEN
  UNDISCH_TAC `(e:real^3->A)(&4 / &3 % basis 1) IN topspace top DIFF
               IMAGE e (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_DIFF] THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_OF_SYM]);;

(* The lower half of the neck is open and closed in the complement of the *)
(* central sphere and the negative quarter.                                *)

let P2BT_HALF_CLOPEN = prove
 (`!top atlas (g:A->real^3^3) eps x e.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024
     ==> open_in (subtopology top (topspace top DIFF
                    (IMAGE e (sphere(vec 0,&1)) UNION
                     IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps))))))
                 (p2bt_half e eps) /\
         closed_in (subtopology top (topspace top DIFF
                    (IMAGE e (sphere(vec 0,&1)) UNION
                     IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps))))))
                 (p2bt_half e eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bt_half; apx_slab] THEN
  ABBREV_TAC `r0 = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `rq = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `r1 = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps <=> r0 < norm y /\ norm y < r1`
  (LABEL_TAC "dom") THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z:real^3. r0 < norm y /\ norm y < r1 /\ r0 < norm z /\ norm z < r1 /\
                 (e:real^3->A) y = e z ==> y = z`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `e:real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. r0 < norm y /\ norm y < r1 ==> (e:real^3->A) y IN topspace top`
  (LABEL_TAC "top") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check
      (fun th -> can (find_term (fun t -> t = `topspace (top:A topology)`)) (concl th) &&
                 can (find_term (fun t -> t = `rfs_neck_dom eps`)) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 < rq /\ rq < &1 /\ &1 < r1 /\ &0 < r0` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "r0" THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) {y | rq <= norm y /\ norm y < &1} =
    IMAGE e (annulus r0 (&1)) INTER
    (topspace top DIFF (IMAGE e (sphere(vec 0,&1)) UNION IMAGE e (annulus r0 rq)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNION; IN_IMAGE; IN_ELIM_THM;
                annulus; IN_SPHERE_0; TAUT `~(p \/ q) <=> ~p /\ ~q`; NOT_EXISTS_THM] THEN
    X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
      REPEAT CONJ_TAC THENL
       [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "top" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `p:A`)) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `rq:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (e:real^3->A) {y | rq <= norm y /\ norm y < &1} =
    IMAGE e {y | rq <= norm y /\ norm y <= &1} INTER
    (topspace top DIFF (IMAGE e (sphere(vec 0,&1)) UNION IMAGE e (annulus r0 rq)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNION; IN_IMAGE; IN_ELIM_THM;
                annulus; IN_SPHERE_0; TAUT `~(p \/ q) <=> ~p /\ ~q`; NOT_EXISTS_THM] THEN
    X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
      REPEAT CONJ_TAC THENL
       [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "top" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `p:A`)) THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `&1`)) (concl th) &&
        not (can (find_term (fun t -> t = `rq:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (annulus r0 (&1))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM(K ALL_TAC) THEN FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `IMAGE (e:real^3->A) {y | rq <= norm y /\ norm y <= &1}` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{y:real^3 | rq <= norm y /\ norm y <= &1} =
                    cball(vec 0,&1) DIFF ball(vec 0,rq)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
      GEN_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* A curve that starts on the central sphere and ends outside the closed   *)
(* upper region (sphere, positive side, lower half) passes through the     *)
(* negative quarter of the neck.                                           *)

let P2BT_NEG_DIP = prove
 (`!top atlas (g:A->real^3^3) eps x e (c:real->A) a b.
     hausdorff_space top /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &1024 /\
     mfd_c1_curve (top,atlas) c a b /\ c a IN IMAGE e (sphere(vec 0,&1)) /\
     ~(c b IN p2bt_conf top e eps)
     ==> ?t. a <= t /\ t <= b /\ c t IN IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= b /\
                continuous_map (subtopology euclideanreal (real_interval[a,b]),top) (c:real->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (c:real->A) a b` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN IMAGE (e:real^3->A) (sphere(vec 0,&1)) ==> z IN p2bt_conf top e eps`
  ASSUME_TAC THENL [REWRITE_TAC[p2bt_conf] THEN SET_TAC[]; ALL_TAC] THEN
  (* the last time on the central sphere *)
  ABBREV_TAC `T0 = {t | t IN real_interval[a,b] /\ (c:real->A) t IN IMAGE (e:real^3->A) (sphere(vec 0,&1))}` THEN
  SUBGOAL_THEN `real_closed (T0:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `T0 = {t | t IN topspace (subtopology euclideanreal (real_interval[a,b])) /\
                (c:real->A) t IN IMAGE (e:real^3->A) (sphere(vec 0,&1))}`
    SUBST1_TAC THENL
     [EXPAND_TAC "T0" THEN REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real) IN T0 /\ (!t. t IN T0 ==> a <= t /\ t <= b)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`T0:real->bool`; `b:real`] REAL_CLOSED_CONTAINS_SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; DISCH_TAC] THEN
  MP_TAC(ISPEC `T0:real->bool` SUP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  ABBREV_TAC `ts = sup (T0:real->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (K ALL_TAC)) THEN
  SUBGOAL_THEN `a <= ts /\ ts <= b /\ (c:real->A) ts IN IMAGE (e:real^3->A) (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(ts:real) IN T0` THEN EXPAND_TAC "T0" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts < b:real` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((c:real->A) b IN p2bt_conf top e eps)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bt_conf")) (concl th))) THEN
    UNDISCH_TAC `(c:real->A) ts IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ts < t /\ t <= b ==> ~((c:real->A) t IN IMAGE (e:real^3->A) (sphere(vec 0,&1)))`
  (LABEL_TAC "after") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(t:real) IN T0` (fun th -> USE_THEN "ub" (MP_TAC o C MATCH_MP th)) THENL
     [EXPAND_TAC "T0" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the curve after the last crossing *)
  ABBREV_TAC `Gm = IMAGE (c:real->A) {t | ts < t /\ t <= b}` THEN
  SUBGOAL_THEN `connected_in top (Gm:A->bool) /\
                Gm SUBSET topspace top DIFF IMAGE (e:real^3->A) (sphere(vec 0,&1)) /\
                (c:real->A) b IN Gm`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Gm" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal {t | ts < t /\ t <= b}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
        REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL] THEN
        REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_DIFF] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                       (c:real->A)` THEN
        REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        USE_THEN "after" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `b:real` THEN
      ASM_REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* a time just after ts at which the curve is still in the neck near S *)
  ABBREV_TAC `r0 = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `rq = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `r1 = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `!y:real^3. y IN rfs_neck_dom eps <=> r0 < norm y /\ norm y < r1`
  (LABEL_TAC "dom") THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->A) (annulus rq (&2)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->A) ts IN IMAGE (e:real^3->A) (annulus rq (&2))` ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real->A) ts IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> (x:A) IN IMAGE (e:real^3->A) s ==> x IN IMAGE e t`) THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real->A`; `subtopology euclideanreal (real_interval[a,b])`;
                 `top:A topology`; `IMAGE (e:real^3->A) (annulus rq (&2))`]
    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Ueq"))) THEN
  SUBGOAL_THEN `?d. &0 < d /\ !t. abs(t - ts) < d ==> t IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in euclideanreal (U:real->bool)` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; real_open] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `(ts:real) IN {t | t IN real_interval[a,b] /\
                                    (c:real->A) t IN IMAGE (e:real^3->A) (annulus rq (&2))}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL]; ALL_TAC] THEN
    USE_THEN "Ueq" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = min b (ts + d / &2)` THEN
  SUBGOAL_THEN `ts < t1 /\ t1 <= b /\ a <= t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->A) t1 IN IMAGE (e:real^3->A) (annulus rq (&2))` MP_TAC THENL
   [SUBGOAL_THEN `(t1:real) IN U INTER real_interval[a,b]` MP_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "t1" THEN ASM_REAL_ARITH_TAC;
      USE_THEN "Ueq" (fun th -> REWRITE_TAC[GSYM th]) THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC o
             REWRITE_RULE[IN_IMAGE; annulus; IN_ELIM_THM]) THEN
  SUBGOAL_THEN `(c:real->A) t1 IN Gm` ASSUME_TAC THENL
   [EXPAND_TAC "Gm" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(y1:real^3) = &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "after" (MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    EXISTS_TAC `y1:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `y1:real^3`] P2BT_NECK_UPPER_LOWER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 < norm(y1:real^3)` THENL
   [UNDISCH_TAC `~((c:real->A) b IN p2bt_conf top e eps)` THEN
    REWRITE_TAC[p2bt_conf; IN_UNION] THEN
    SUBGOAL_THEN `(Gm:A->bool) SUBSET apx_pos_side top (e:real^3->A)`
    (fun th -> MP_TAC(SPEC `(c:real->A) b` (REWRITE_RULE[SUBSET] th))) THENL
     [REWRITE_TAC[apx_pos_side] THEN MATCH_MP_TAC P2BT_COMPONENT_ABSORB THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(c:real->A) t1` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&1 < norm(y1:real^3) ==> (e:real^3->A) y1 IN apx_pos_side top e` THEN
      ASM_REWRITE_TAC[apx_pos_side];
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->A) t1 IN p2bt_half (e:real^3->A) eps` ASSUME_TAC THENL
   [REWRITE_TAC[p2bt_half; IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `y1:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_HALF_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF
                    (IMAGE (e:real^3->A) (sphere(vec 0,&1)) UNION
                     IMAGE (e:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps)))))`;
                 `Gm:A->bool`; `p2bt_half (e:real^3->A) eps`] CONNECTED_IN_CLOPEN_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; TAUT `~(p \/ q) <=> ~p /\ ~q`] THEN
    X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?t. ts < t /\ t <= b /\ q = (c:real->A) t` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(q:A) IN Gm` THEN EXPAND_TAC "Gm" THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      USE_THEN "after" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `a <= t:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (--inv(&2 * eps))`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `~((c:real->A) b IN p2bt_conf top e eps)` THEN
    REWRITE_TAC[p2bt_conf; IN_UNION] THEN
    SUBGOAL_THEN `(c:real->A) b IN p2bt_half (e:real^3->A) eps` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(Gm:A->bool) SUBSET p2bt_half (e:real^3->A) eps` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `DISJOINT (Gm:A->bool) (p2bt_half (e:real^3->A) eps)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(c:real->A) t1`) THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Confinement of the points between the centre of a separating neck and a   *)
(* point on the closed positive side of its sphere (MT Lemma A.1): they lie  *)
(* in p2bt_conf.                                                             *)
(* ========================================================================= *)

(* The smooth reparametrization of the first half of a concatenation is    *)
(* onto [0,1].                                                             *)

let P2BT_SS0_ONTO = prove
 (`!t. &0 <= t /\ t <= &1 ==> ?s. &0 <= s /\ s <= &1 / &2 /\ grgd_ss (&0) s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`grgd_ss (&0)`; `&0`; `&1 / &2`; `t:real`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [REWRITE_TAC[grgd_ss] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC `&0` GRGD_SS_ALT)] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    MESON_TAC[]]);;

(* A curve visiting a set gives a concatenation visiting it.               *)

let P2BT_CONCAT_VISITS = prove
 (`!(gamma1:real->A) gamma2 s t.
     &0 <= t /\ t <= &1 /\ gamma1 t IN s
     ==> ?u. &0 <= u /\ u <= &1 /\ grgd_concat gamma1 gamma2 u IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` P2BT_SS0_ONTO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real` THEN
  SUBGOAL_THEN `v <= &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[grgd_concat]);;

(* MT Lemma A.1 confines the between points.  With A.1 at eps <= eps1:    *)
(* if b lies between the centre x of a separating eps-neck and a point q  *)
(* on the closed positive side of its central sphere, then b lies on the  *)
(* sphere, on the positive side or in the lower half of the neck.          *)

let P2BT_BETWEEN_CONF = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u
     ==> ?eps1. &0 < eps1 /\
           !top atlas (g:A->real^3^3) eps x e q b.
              &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              rfs_neck (top,atlas) g eps x e /\
              (q IN IMAGE e (sphere(vec 0,&1)) \/ apx_pos_side top e q) /\
              mfd_joinable (top,atlas) x b /\ mfd_joinable (top,atlas) b q /\
              mfd_dist (top,atlas) g x b + mfd_dist (top,atlas) g b q =
              mfd_dist (top,atlas) g x q
              ==> b IN p2bt_conf top e eps`,
  GEN_TAC THEN REWRITE_TAC[APX_A1_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a1"))) THEN
  EXISTS_TAC `min eps1 (&1 / &1024)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x /\
                (x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ABBREV_TAC `h = inv(&2 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `b:A`;
                 `mfd_dist (top,atlas) (g:A->real^3^3) x b + h / &2`] APX_DIST_SHORT_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `b:A`; `q:A`;
                 `mfd_dist (top,atlas) (g:A->real^3^3) b q + h / &2`] APX_DIST_SHORT_CURVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real->A` STRIP_ASSUME_TAC) THEN
  (* the first curve dips into the negative quarter *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `g1:real->A`; `&0`; `&1`] P2BT_NEG_DIP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `td:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g1:real->A`; `g2:real->A`;
                 `IMAGE (e:real^3->A) (apx_slab (--inv eps) (--inv(&2 * eps)))`; `td:real`]
    P2BT_CONCAT_VISITS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ud:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g1:real->A`; `g2:real->A`] GRGD_CONCAT_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g1:real->A`; `g2:real->A`] GRGD_CONCAT_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* A.1 shortens the concatenation below the distance *)
  USE_THEN "a1" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`;
     `x:A`; `e:real^3->A`; `q:A`; `grgd_concat (g1:real->A) g2`; `&0`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ud:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g3:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g3:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The region between two level spheres of a parametrized annulus.  A point  *)
(* off both spheres that is not connected (avoiding the inner sphere) to the *)
(* inner region, not connected (avoiding the outer sphere) to the outer      *)
(* region, but connected (avoiding the inner sphere) to a point between them *)
(* lies between them.                                                        *)
(* ========================================================================= *)

let P2BT_SUB_COMPONENT_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) s (z:A).
     smooth_manifold_atlas top atlas /\ open_in top s
     ==> open_in top (connected_component_of (subtopology top s) z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE THEN
  MATCH_MP_TAC LOCALLY_CONNECTED_SPACE_OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
  MATCH_MP_TAC GEO_MANIFOLD_LOCALLY_PATH_CONNECTED THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]);;

let P2BT_ANNULUS_REGION = prove
 (`!top atlas (E:real^3->A) r0 r1 r2 r3 z w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas (annulus r0 r3) E /\
     &0 <= r0 /\ r0 < r1 /\ r1 < r2 /\ r2 < r3 /\
     z IN topspace top /\
     ~(z IN IMAGE E (sphere(vec 0,r1))) /\ ~(z IN IMAGE E (sphere(vec 0,r2))) /\
     ~(connected_component_of
         (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1))))
         z (E(((r0 + r1) / &2) % basis 1))) /\
     ~(connected_component_of
         (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r2))))
         z (E(((r2 + r3) / &2) % basis 1))) /\
     w IN annulus r1 r2 /\
     connected_component_of
       (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) z (E w)
     ==> z IN IMAGE E (annulus r1 r2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `S1 = IMAGE (E:real^3->A) (sphere(vec 0,r1))` THEN
  ABBREV_TAC `S2 = IMAGE (E:real^3->A) (sphere(vec 0,r2))` THEN
  ABBREV_TAC `G = IMAGE (E:real^3->A) (annulus r1 r2)` THEN
  ABBREV_TAC `X = topspace top DIFF ((S1:A->bool) UNION S2)` THEN
  (* point-set facts about the parametrized annulus *)
  SUBGOAL_THEN
   `!y v:real^3. y IN annulus r0 r3 /\ v IN annulus r0 r3 /\ (E:real^3->A) y = E v
                 ==> y = v`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus r0 r3:real^3->bool`; `E:real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. compact (k:real^3->bool) /\ k SUBSET annulus r0 r3
                    ==> closed_in top (IMAGE (E:real^3->A) k)`
  (LABEL_TAC "cl") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus r0 r3:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. open (t:real^3->bool) /\ t SUBSET annulus r0 r3
                    ==> open_in top (IMAGE (E:real^3->A) t)`
  (LABEL_TAC "op") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus r0 r3:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (annulus r0 r3) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET THEN USE_THEN "op" MATCH_MP_TAC THEN
    REWRITE_TAC[OPEN_ANNULUS; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (S1:A->bool) /\ closed_in top (S2:A->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN CONJ_TAC THEN
    USE_THEN "cl" MATCH_MP_TAC THEN REWRITE_TAC[COMPACT_SPHERE] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (X:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_UNION];
    ALL_TAC] THEN
  (* the three regions avoid the spheres, are connected, G is clopen in X *)
  SUBGOAL_THEN
   `!a b. r0 <= a /\ a < b /\ b <= r3 /\ (b <= r1 \/ r1 <= a) /\ (b <= r2 \/ r2 <= a)
          ==> connected_in top (IMAGE (E:real^3->A) (annulus a b)) /\
              open_in top (IMAGE E (annulus a b)) /\
              IMAGE E (annulus a b) SUBSET X`
  (LABEL_TAC "reg") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `annulus a b SUBSET annulus r0 r3:real^3->bool` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus r0 r3:real^3->bool`] THEN
      ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
      USE_THEN "op" MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
      MAP_EVERY EXPAND_TAC ["X"; "S1"; "S2"] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNION;
                  TAUT `~(p \/ q) <=> ~p /\ ~q`] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; NOT_EXISTS_THM] THEN
        X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `(v:real^3) IN annulus a b` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
        REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; NOT_EXISTS_THM] THEN
        X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `(v:real^3) IN annulus a b` THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  USE_THEN "reg" (MP_TAC o SPECL [`r1:real`; `r2:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "reg" (MP_TAC o SPECL [`r0:real`; `r1:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "reg" (MP_TAC o SPECL [`r2:real`; `r3:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology top X) (G:A->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `IMAGE (E:real^3->A) {y | r1 <= norm y /\ norm y <= r2}` THEN CONJ_TAC THENL
     [USE_THEN "cl" MATCH_MP_TAC THEN CONJ_TAC THENL
       [SUBGOAL_THEN `{y:real^3 | r1 <= norm y /\ norm y <= r2} =
                      cball(vec 0,r2) DIFF ball(vec 0,r1)` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
          REAL_ARITH_TAC;
          SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
      MAP_EVERY EXPAND_TAC ["G"; "X"; "S1"; "S2"] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNION; IN_IMAGE; IN_ELIM_THM; annulus;
                  IN_SPHERE_0; TAUT `~(p \/ q) <=> ~p /\ ~q`; NOT_EXISTS_THM] THEN
      X_GEN_TAC `p:A` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
        CONJ_TAC THENL
         [EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(G:A->bool) SUBSET X` THEN
        MAP_EVERY EXPAND_TAC ["G"; "X"; "S1"; "S2"] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNION; IN_IMAGE; IN_SPHERE_0;
                    TAUT `~(p \/ q) <=> ~p /\ ~q`; NOT_EXISTS_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)
                                   STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
          is_eq(concl th) && lhs(concl th) = `p:A`)) THEN
        EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN DISCH_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
            is_forall(concl th) && can (find_term (fun t -> t = `r1:real`)) (concl th) &&
            not(can (find_term (fun t -> t = `r2:real`)) (concl th))));
          FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
            is_forall(concl th) && can (find_term (fun t -> t = `r2:real`)) (concl th) &&
            not(can (find_term (fun t -> t = `r1:real`)) (concl th))))] THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the component Z of z in X *)
  ABBREV_TAC `Z = connected_component_of (subtopology top X) (z:A)` THEN
  SUBGOAL_THEN `(z:A) IN X` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "S1"; "S2"] THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (Z:A->bool) /\ Z SUBSET X /\ (z:A) IN Z /\ open_in top Z /\
                closed_in (subtopology top X) Z`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology top X:A topology`; `z:A`]
        CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
      MP_TAC(ISPECL [`subtopology top X:A topology`; `z:A`]
        CONNECTED_IN_CONNECTED_COMPONENT_OF) THEN SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
      REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
      ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      UNDISCH_TAC `(z:A) IN X` THEN EXPAND_TAC "X" THEN SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `X:A->bool`; `z:A`] P2BT_SUB_COMPONENT_OPEN) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[CLOSED_IN_CONNECTED_COMPONENT_OF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Z:A->bool) G` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top X:A topology`; `Z:A->bool`; `G:A->bool`]
      CONNECTED_IN_CLOPEN_CASES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; OPEN_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `G:A->bool` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S a b c. (S:A->bool) SUBSET topspace top /\ X SUBSET topspace top DIFF S /\
              IMAGE (E:real^3->A) (annulus a b) SUBSET X /\
              connected_in top (IMAGE E (annulus a b)) /\
              c IN annulus a b /\
              ~(connected_component_of (subtopology top (topspace top DIFF S)) z (E c))
              ==> DISJOINT Z (IMAGE E (annulus a b))`
  (LABEL_TAC "dis") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(connected_component_of (subtopology top (topspace top DIFF S))
                    (z:A) (E(c:real^3)))` THEN
    REWRITE_TAC[connected_component_of; NOT_CLAUSES] THEN
    EXISTS_TAC `(Z:A->bool) UNION IMAGE (E:real^3->A) (annulus a b)` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; IN_UNION] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Z:A->bool) (IMAGE (E:real^3->A) (annulus r0 r1)) /\
                DISJOINT (Z:A->bool) (IMAGE (E:real^3->A) (annulus r2 r3))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "dis" MATCH_MP_TAC THENL
     [EXISTS_TAC `S1:A->bool` THEN EXISTS_TAC `((r0 + r1) / &2) % basis 1:real^3`;
      EXISTS_TAC `S2:A->bool` THEN EXISTS_TAC `((r2 + r3) / &2) % basis 1:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_IN_SUBSET]; ALL_TAC]) THEN
    (CONJ_TAC THENL [EXPAND_TAC "X" THEN SET_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Z:A->bool) (IMAGE (E:real^3->A) (annulus r0 r3))` ASSUME_TAC THENL
   [SUBGOAL_THEN `annulus r0 r3:real^3->bool =
                  annulus r0 r1 UNION sphere(vec 0,r1) UNION annulus r1 r2 UNION
                  sphere(vec 0,r2) UNION annulus r2 r3` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (Z:A->bool) (IMAGE (E:real^3->A) (annulus r0 r1))`;
      `DISJOINT (Z:A->bool) (IMAGE (E:real^3->A) (annulus r2 r3))`;
      `DISJOINT (Z:A->bool) G`; `(Z:A->bool) SUBSET X`] THEN
    MAP_EVERY EXPAND_TAC ["X"; "G"; "S1"; "S2"] THEN SET_TAC[];
    ALL_TAC] THEN
  (* Z is closed in top, hence clopen, and the connection to G contradicts *)
  SUBGOAL_THEN `closed_in top (Z:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `closed_in (subtopology top X) (Z:A->bool)` THEN
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(S1:A->bool) UNION S2 SUBSET IMAGE (E:real^3->A) (annulus r0 r3)`
    ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["S1"; "S2"] THEN
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Z = (C:A->bool) INTER (topspace top DIFF IMAGE (E:real^3->A) (annulus r0 r3))`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(S1:A->bool) UNION S2 SUBSET IMAGE (E:real^3->A) (annulus r0 r3)`;
        `(Z:A->bool) = C INTER X`;
        `DISJOINT (Z:A->bool) (IMAGE (E:real^3->A) (annulus r0 r3))`;
        `(Z:A->bool) SUBSET X`] THEN
      EXPAND_TAC "X" THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
      USE_THEN "op" MATCH_MP_TAC THEN REWRITE_TAC[OPEN_ANNULUS; SUBSET_REFL]];
    ALL_TAC] THEN
  UNDISCH_TAC `connected_component_of
                 (subtopology top (topspace top DIFF S1)) (z:A) ((E:real^3->A) w)` THEN
  REWRITE_TAC[connected_component_of; CONNECTED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `T1:A->bool`; `Z:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->A) w IN G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(z:A) IN T1`; `(z:A) IN Z`; `(E:real^3->A) w IN T1`; `(E:real^3->A) w IN G`;
    `DISJOINT (Z:A->bool) G`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* The region between the end necks of a finite chain (via the A13 chart) is *)
(* compact; with A.1 it contains every point between the end centres, so a   *)
(* constant-speed shortest curve joins them.                                 *)
(* ========================================================================= *)

(* Two points of a parametrized annulus band that avoids a level sphere     *)
(* are joinable avoiding that sphere.                                      *)

let P2BT_PARAM_CCOF = prove
 (`!top atlas (E:real^3->A) r0 r3 a b r y1 y2.
     mfd_param top atlas (annulus r0 r3) E /\
     r0 <= a /\ a < b /\ b <= r3 /\ r0 < r /\ r < r3 /\ (b <= r \/ r <= a) /\
     y1 IN annulus a b /\ y2 IN annulus a b
     ==> connected_component_of
           (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r)))) (E y1) (E y2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `annulus a b SUBSET annulus r0 r3:real^3->bool` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[connected_component_of] THEN
  EXISTS_TAC `IMAGE (E:real^3->A) (annulus a b)` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus r0 r3:real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus r0 r3:real^3->bool`; `annulus r0 r3:real^3->bool`;
                   `E:real^3->A`] MFD_PARAM_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; SUBSET_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; NOT_EXISTS_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `y:real^3 = v` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `annulus r0 r3:real^3->bool`; `E:real^3->A`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(v:real^3) IN annulus a b` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]]);;

(* The far end of the A13 chart: e n w = E(rho L % radial_ext f' w).        *)

let P2BT_REV_CORRESP = prove
 (`!(E:real^3->A) en f f' L eps.
     &0 < eps /\ sphere_diffeo f f' /\
     (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
          ==> E y = en (radial_ext f (exp(--L / sqrt(&2)) % y)))
     ==> !w. exp(--inv(&8 * eps) / sqrt(&2)) < norm w /\ norm w < exp(inv eps / sqrt(&2))
             ==> en w = E(exp(L / sqrt(&2)) % radial_ext f' w) /\
                 norm(exp(L / sqrt(&2)) % radial_ext f' w) = exp(L / sqrt(&2)) * norm w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_diffeo] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(radial_ext (f':real^3->real^3) w) = norm w` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(exp(L / sqrt(&2)) % radial_ext (f':real^3->real^3) w) =
                exp(L / sqrt(&2)) * norm w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[REAL_EXP_POS_LT; REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `exp(L / sqrt(&2)) % radial_ext (f':real^3->real^3) w`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_SUB_RDISTRIB; REAL_EXP_ADD;
                real_sub; GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LT_LMUL_EQ; REAL_EXP_POS_LT] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `exp(--L / sqrt(&2)) * exp(L / sqrt(&2)) = &1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; real_div; GSYM REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[REAL_ADD_LINV; REAL_MUL_LZERO; REAL_EXP_0];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN ASM_SIMP_TAC[]);;

(* Two level spheres S1 = E(r1), S2 = E(r2) of a parametrized annulus,     *)
(* r1 <= r2, with sides separated: the outer side of S1 meets the inner    *)
(* side of S2 only between them, and if r1 < r2 each sphere lies on the    *)
(* inner side of the other.                                                *)

let P2BT_TWO_SPHERE_REGION = prove
 (`!top atlas (E:real^3->A) r0 r1 r2 r3 p1 n1 p2 n2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_param top atlas (annulus r0 r3) E /\
     &0 <= r0 /\ r0 < r1 /\ r1 <= r2 /\ r2 < r3 /\
     p1 IN annulus r1 r3 /\ n1 IN annulus r0 r1 /\
     p2 IN annulus r0 r2 /\ n2 IN annulus r2 r3 /\
     DISJOINT
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) (E p1))
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) (E n1)) /\
     DISJOINT
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r2)))) (E p2))
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r2)))) (E n2))
     ==> (connected_component_of
           (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) (E p1) INTER
          connected_component_of
           (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r2)))) (E p2)
          SUBSET IMAGE E (annulus r1 r2)) /\
         (r1 < r2
          ==> !y. y IN sphere(vec 0,r2)
                  ==> connected_component_of
                        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1))))
                        (E p1) (E y)) /\
         (r1 < r2
          ==> !y. y IN sphere(vec 0,r1)
                  ==> connected_component_of
                        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r2))))
                        (E p2) (E y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a b r y1 y2. r0 <= a /\ a < b /\ b <= r3 /\ r0 < r /\ r < r3 /\ (b <= r \/ r <= a) /\
                  y1 IN annulus a b /\ y2 IN annulus a b
                  ==> connected_component_of
                        (subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r))))
                        (E y1) (E y2)`
  (LABEL_TAC "cc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BT_PARAM_CCOF THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `r0:real`; `r3:real`;
                          `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus r0 r3 <=> r0 < norm y /\ norm y < r3`
  (LABEL_TAC "ann") THENL [REWRITE_TAC[annulus; IN_ELIM_THM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    USE_THEN "cc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r1:real`; `r3:real`] THEN
    UNDISCH_TAC `(p1:real^3) IN annulus r1 r3` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    USE_THEN "cc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r0:real`; `r2:real`] THEN
    UNDISCH_TAC `(p2:real^3) IN annulus r0 r2` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:A` THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [IN] THEN STRIP_TAC THEN
  ASM_CASES_TAC `r1:real = r2` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN
     `connected_component_of
        (subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r1)))) (E p2) =
      connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) (E n1)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r1)))`;
        `(E:real^3->A) p2`; `(E:real^3->A) n1`] CONNECTED_COMPONENT_OF_EQUIV) THEN
      MATCH_MP_TAC(TAUT `a ==> (a <=> b /\ c /\ d) ==> d`) THEN
      USE_THEN "cc" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`r0:real`; `r1:real`] THEN
      MAP_EVERY UNDISCH_TAC [`(p2:real^3) IN annulus r0 r1`; `(n1:real^3) IN annulus r0 r1`] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `DISJOINT
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r1)))) (E p1))
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) (E n1))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [IN] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r1 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2BT_ANNULUS_REGION THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `r0:real`; `r3:real`; `((r1 + r2) / &2) % basis 1:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:A) IN topspace top /\ ~(z IN IMAGE (E:real^3->A) (sphere(vec 0,r1))) /\
                ~(z IN IMAGE (E:real^3->A) (sphere(vec 0,r2)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL
      [`subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r1)))`;
       `(E:real^3->A) p1`; `z:A`] CONNECTED_COMPONENT_IN_TOPSPACE) THEN
    MP_TAC(ISPECL
      [`subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r2)))`;
       `(E:real^3->A) p2`; `z:A`] CONNECTED_COMPONENT_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((r1 + r2) / &2) % basis 1:real^3 IN annulus r1 r2 /\
                norm(((r1 + r2) / &2) % basis 1:real^3) = (r1 + r2) / &2 /\
                norm(((r0 + r1) / &2) % basis 1:real^3) = (r0 + r1) / &2 /\
                norm(((r2 + r3) / &2) % basis 1:real^3) = (r2 + r3) / &2`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* not joinable to the inner region of S1 *)
    DISCH_TAC THEN
    UNDISCH_TAC
     `DISJOINT
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r1)))) (E p1))
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r1)))) (E n1))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [IN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN
    EXISTS_TAC `(E:real^3->A)(((r0 + r1) / &2) % basis 1)` THEN
    CONJ_TAC THENL
     [USE_THEN "cc" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`r0:real`; `r1:real`] THEN
      UNDISCH_TAC `(n1:real^3) IN annulus r0 r1` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN ASM_REWRITE_TAC[]];
    (* not joinable to the outer region of S2 *)
    DISCH_TAC THEN
    UNDISCH_TAC
     `DISJOINT
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE (E:real^3->A) (sphere(vec 0,r2)))) (E p2))
      (connected_component_of
        (subtopology top (topspace top DIFF IMAGE E (sphere(vec 0,r2)))) (E n2))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [IN] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN
    EXISTS_TAC `(E:real^3->A)(((r2 + r3) / &2) % basis 1)` THEN
    CONJ_TAC THENL
     [USE_THEN "cc" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`r2:real`; `r3:real`] THEN
      UNDISCH_TAC `(n2:real^3) IN annulus r2 r3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN ASM_REWRITE_TAC[]];
    (* joinable to the middle point *)
    ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_TRANS THEN
    EXISTS_TAC `(E:real^3->A) p1` THEN CONJ_TAC THENL
     [USE_THEN "cc" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`r1:real`; `r3:real`] THEN
      UNDISCH_TAC `(p1:real^3) IN annulus r1 r3` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

(* The radii of the neck levels used below, for eps <= 1/1024.             *)

let P2BT_EPS_RADII = prove
 (`!eps. &0 < eps /\ eps <= &1 / &1024
         ==> exp(--inv eps / sqrt(&2)) < &1 / &4 /\
             exp(--inv eps / sqrt(&2)) < exp(--inv(&2 * eps) / sqrt(&2)) /\
             exp(--inv(&2 * eps) / sqrt(&2)) < &1 /\
             exp(--inv eps / sqrt(&2)) < exp(--inv(&8 * eps) / sqrt(&2)) /\
             exp(--inv(&8 * eps) / sqrt(&2)) < &3 / &4 /\
             &4 / &3 < exp(inv(&8 * eps) / sqrt(&2)) /\
             &1 < exp(inv(&2 * eps) / sqrt(&2)) /\
             exp(inv(&2 * eps) / sqrt(&2)) < exp(inv eps / sqrt(&2)) /\
             &4 < exp(inv eps / sqrt(&2)) /\
             exp(--inv(&2 * eps) / sqrt(&2)) * exp(inv(&2 * eps) / sqrt(&2)) = &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ABBREV_TAC `t = inv eps / sqrt(&2)` THEN
  SUBGOAL_THEN `&8 <= t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `&1024 <= inv eps` MP_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps / sqrt(&2) = --t /\ --inv(&2 * eps) / sqrt(&2) = --(t / &2) /\
                --inv(&8 * eps) / sqrt(&2) = --(t / &8) /\
                inv(&8 * eps) / sqrt(&2) = t / &8 /\ inv(&2 * eps) / sqrt(&2) = t / &2 /\
                inv eps / sqrt(&2) = t`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&1 + t / &8 <= exp(t / &8) /\ &1 + t / &2 <= exp(t / &2) /\
                &1 + t <= exp t /\ exp(t / &2) < exp t /\ exp(t / &8) < exp t`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_LE_X; REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(t / &8) /\ &0 < exp(t / &2) /\ &0 < exp t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_LINV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_LINV THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC]);;

(* The A13 chart of a finite chain: the far centre lies on the closed      *)
(* positive side of the first neck and conversely, and the two confinement *)
(* regions meet inside a closed band of the chart.                         *)

let P2BT_A13_REGION = prove
 (`!top atlas (g:A->real^3^3) eps x0 e0 xn en (E:real^3->A) L f f'.
     hausdorff_space top /\ riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
     eps <= &1 / &1024 /\
     rfs_neck (top,atlas) g eps x0 e0 /\ rfs_neck (top,atlas) g eps xn en /\
     &0 <= L /\ sphere_diffeo f f' /\
     mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
     (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e0 y) /\
     (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
          ==> E y = en (radial_ext f (exp(--L / sqrt(&2)) % y)))
     ==> (xn IN IMAGE e0 (sphere(vec 0,&1)) \/ apx_pos_side top e0 xn) /\
         (x0 IN IMAGE (apx_rev en) (sphere(vec 0,&1)) \/
          apx_pos_side top (apx_rev en) x0) /\
         p2bt_conf top e0 eps INTER p2bt_conf top (apx_rev en) eps SUBSET
         IMAGE E {y | exp(--inv(&2 * eps) / sqrt(&2)) <= norm y /\
                      norm y <= exp((L + inv(&2 * eps)) / sqrt(&2))}`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x0:A`; `e0:real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` P2BT_EPS_RADII) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`E:real^3->A`; `en:real^3->A`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `L:real`; `eps:real`] P2BT_REV_CORRESP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "corr") THEN
  UNDISCH_TAC `!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> (E:real^3->A) y = e0 y` THEN
  REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN DISCH_THEN(LABEL_TAC "e4") THEN
  UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN REWRITE_TAC[sphere_diffeo] THEN
  DISCH_THEN(LABEL_TAC "sd" o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `exp((L + inv eps) / sqrt(&2)) = exp(L / sqrt(&2)) * exp(inv eps / sqrt(&2)) /\
                exp((L + inv(&2 * eps)) / sqrt(&2)) =
                exp(L / sqrt(&2)) * exp(inv(&2 * eps) / sqrt(&2)) /\
                exp((L - inv(&8 * eps)) / sqrt(&2)) =
                exp(L / sqrt(&2)) * exp(--inv(&8 * eps) / sqrt(&2)) /\
                exp(--L / sqrt(&2)) = inv(exp(L / sqrt(&2))) /\
                &1 <= exp(L / sqrt(&2))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_ADD; GSYM REAL_EXP_NEG] THEN
    REWRITE_TAC[real_div; real_sub; REAL_ADD_RDISTRIB; REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + L * inv(sqrt(&2))` THEN
    REWRITE_TAC[REAL_EXP_LE_X; REAL_LE_ADDR] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) (E:real^3->A)` THEN
  ASM_REWRITE_TAC[apx_slab] THEN DISCH_TAC THEN
  UNDISCH_TAC `!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                   ==> (E:real^3->A) y = en (radial_ext f (exp(--L / sqrt(&2)) % y))` THEN
  ASM_REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN DISCH_THEN(LABEL_TAC "e5") THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `rL = exp(L / sqrt(&2))` THEN
  ABBREV_TAC `a0 = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `ah = exp(--inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `a8 = exp(--inv(&8 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `A8 = exp(inv(&8 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `Ah = exp(inv(&2 * eps) / sqrt(&2))` THEN
  ABBREV_TAC `A1 = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < rL /\ &0 < a0 /\ &0 < A1 /\ &0 < Ah` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rL"; "a0"; "A1"; "Ah"] THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `rL < rL * A1 /\ rL * &4 / &3 < rL * A1 /\ &4 < rL * A1 /\
                rL <= rL * Ah /\ &1 <= rL * Ah /\ rL * a8 < rL`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `A1:real` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ah:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the level spheres and base points in the chart E *)
  SUBGOAL_THEN `!v:real^3. norm v = &1 ==> apx_rev (en:real^3->A) v = en v`
  (LABEL_TAC "rev1") THENL
   [REWRITE_TAC[apx_rev] THEN SIMP_TAC[REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e0:real^3->A) (sphere(vec 0,&1)) = IMAGE (E:real^3->A) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!y:real^3. y IN s ==> (f:real^3->A) y = g y)
                           ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "e4" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (en:real^3->A) (sphere(vec 0,&1)) = IMAGE (E:real^3->A) (sphere(vec 0,rL))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `p:A` THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THENL
     [USE_THEN "corr" (MP_TAC o SPEC `w:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      EXISTS_TAC `rL % radial_ext (f':real^3->real^3) w` THEN
      ASM_REWRITE_TAC[REAL_MUL_RID];
      EXISTS_TAC `radial_ext (f:real^3->real^3) (inv rL % w)` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "e5" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`f:real^3->real^3`; `inv rL % (w:real^3)`] SMT_RADIAL_EXT_NORM) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (apx_rev (en:real^3->A)) (sphere(vec 0,&1)) = IMAGE (E:real^3->A) (sphere(vec 0,rL))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(!y:real^3. y IN s ==> (f:real^3->A) y = g y)
                           ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[IN_SPHERE_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(&4 / &3 % basis 1:real^3) = &4 / &3 /\
                norm(&3 / &4 % basis 1:real^3) = &3 / &4`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(e0:real^3->A)(&4 / &3 % basis 1) = (E:real^3->A)(&4 / &3 % basis 1) /\
                e0(&3 / &4 % basis 1) = E(&3 / &4 % basis 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "e4" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `apx_rev (en:real^3->A) (&4 / &3 % basis 1) =
    E(rL % radial_ext (f':real^3->real^3) (&3 / &4 % basis 1)) /\
    apx_rev en (&3 / &4 % basis 1) = E(rL % radial_ext f' (&4 / &3 % basis 1)) /\
    norm(rL % radial_ext (f':real^3->real^3) (&3 / &4 % basis 1)) = rL * &3 / &4 /\
    norm(rL % radial_ext (f':real^3->real^3) (&4 / &3 % basis 1)) = rL * &4 / &3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[apx_rev] THEN
    REWRITE_TAC[ASSUME `norm(&4 / &3 % basis 1:real^3) = &4 / &3`;
                ASSUME `norm(&3 / &4 % basis 1:real^3) = &3 / &4`; VECTOR_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    USE_THEN "corr" (MP_TAC o SPEC `&3 / &4 % basis 1:real^3`) THEN
    USE_THEN "corr" (MP_TAC o SPEC `&4 / &3 % basis 1:real^3`) THEN
    REWRITE_TAC[ASSUME `norm(&4 / &3 % basis 1:real^3) = &4 / &3`;
                ASSUME `norm(&3 / &4 % basis 1:real^3) = &3 / &4`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xn:A) IN IMAGE (E:real^3->A) (sphere(vec 0,rL)) /\
                (x0:A) IN IMAGE (E:real^3->A) (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(rhs(concl th)) = `sphere(vec 0:real^3,rL:real)` &&
      not(can (find_term (fun t -> t = `apx_rev:(real^3->A)->real^3->A`)) (concl th)))) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `IMAGE (E:real^3->A) (sphere(vec 0:real^3,&1))`)) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps xn en` THEN SIMP_TAC[rfs_neck];
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x0 e0` THEN SIMP_TAC[rfs_neck]];
    ALL_TAC] THEN
  (* the sides in the chart E *)
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps xn (apx_rev en)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_REV_NECK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x0:A`; `e0:real^3->A`] P2BT_SIDES_DISJOINT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `xn:A`; `apx_rev (en:real^3->A)`] P2BT_SIDES_DISJOINT) THEN
  ASM_REWRITE_TAC[apx_pos_side; apx_neg_side; p2bt_conf] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `E:real^3->A`;
                 `a0:real`; `&1`; `rL:real`; `rL * A1`;
                 `&4 / &3 % basis 1:real^3`; `&3 / &4 % basis 1:real^3`;
                 `rL % radial_ext (f':real^3->real^3) (&3 / &4 % basis 1)`;
                 `rL % radial_ext (f':real^3->real^3) (&4 / &3 % basis 1)`]
    P2BT_TWO_SPHERE_REGION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t1") (CONJUNCTS_THEN2 (LABEL_TAC "t2")
    (LABEL_TAC "t3"))) THEN
  (* the two half-necks and the level sets lie in the closed band *)
  SUBGOAL_THEN
   `p2bt_half (e0:real^3->A) eps SUBSET IMAGE (E:real^3->A) {y | ah <= norm y /\ norm y <= rL * Ah} /\
    p2bt_half (apx_rev (en:real^3->A)) eps SUBSET
    IMAGE (E:real^3->A) {y | ah <= norm y /\ norm y <= rL * Ah}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2bt_half] THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THENL
     [EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "e4" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `norm(inv(norm y pow 2) % y:real^3) = inv(norm y)` ASSUME_TAC THENL
       [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
        UNDISCH_TAC `&0 < norm(y:real^3)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 < inv(norm(y:real^3)) /\ inv(norm y) <= Ah` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `Ah = inv ah` SUBST1_TAC THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
            ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      USE_THEN "corr" (MP_TAC o SPEC `inv(norm y pow 2) % y:real^3`) THEN
      REWRITE_TAC[ASSUME `norm(inv(norm y pow 2) % y:real^3) = inv(norm y)`] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      REWRITE_TAC[apx_rev] THEN
      EXISTS_TAC `rL % radial_ext (f':real^3->real^3) (inv(norm y pow 2) % y)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `rL:real` THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (E:real^3->A) (sphere(vec 0,&1)) SUBSET
    IMAGE (E:real^3->A) {y | ah <= norm y /\ norm y <= rL * Ah} /\
    IMAGE (E:real^3->A) (sphere(vec 0,rL)) SUBSET
    IMAGE (E:real^3->A) {y | ah <= norm y /\ norm y <= rL * Ah} /\
    IMAGE (E:real^3->A) (annulus (&1) rL) SUBSET
    IMAGE (E:real^3->A) {y | ah <= norm y /\ norm y <= rL * Ah}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `rL = &1` THENL
     [DISJ1_TAC THEN
      UNDISCH_TAC `(xn:A) IN IMAGE (E:real^3->A) (sphere(vec 0,rL))` THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN SUBGOAL_THEN `&1 < rL` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(xn:A) IN IMAGE (E:real^3->A) (sphere(vec 0,rL))` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "t2" (fun th -> MATCH_MP_TAC(MP th (ASSUME `&1 < rL`))) THEN
      ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `rL = &1` THENL
     [DISJ1_TAC THEN
      UNDISCH_TAC `(x0:A) IN IMAGE (E:real^3->A) (sphere(vec 0,&1))` THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN SUBGOAL_THEN `&1 < rL` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(x0:A) IN IMAGE (E:real^3->A) (sphere(vec 0,&1))` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      USE_THEN "t3" (fun th -> MATCH_MP_TAC(MP th (ASSUME `&1 < rL`))) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(SET_RULE
     `!s0 p0 h0 sn pn hn k.
        s0 SUBSET k /\ sn SUBSET k /\ h0 SUBSET k /\ hn SUBSET k /\ p0 INTER pn SUBSET k
        ==> (s0 UNION p0 UNION h0) INTER (sn UNION pn UNION hn) SUBSET (k:A->bool)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (E:real^3->A) (annulus (&1) rL)` THEN ASM_REWRITE_TAC[]]);;

(* MT Claim 10.3, chain case, the compactness input: under A.1, the points *)
(* between the end centres of a finite chain lie in a compact part of the  *)
(* chain union.                                                            *)

let P2BT_CHAIN_BETWEEN = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas (g:A->real^3^3) eps n x e.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e
              ==> ?K. compact_in top K /\
                      K SUBSET apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
                      !b. mfd_joinable (top,atlas) (x(&0)) b /\
                          mfd_joinable (top,atlas) b (x(&n)) /\
                          mfd_dist (top,atlas) g (x(&0)) b +
                          mfd_dist (top,atlas) g b (x(&n)) =
                          mfd_dist (top,atlas) g (x(&0)) (x(&n))
                          ==> b IN K`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_BETWEEN_CONF) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bc"))) THEN
  MP_TAC(SPEC `u:A->bool` APX_A13_UNCOND) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a13"))) THEN
  EXISTS_TAC `min eps1 (min eps2 (&1 / &1024))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `n:num`; `x:int->A`;
                       `e:int->real^3->A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= eps2 /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "a13" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`; `n:num`; `x:int->A`;
                                  `e:int->real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(&0))
                         ((e:int->real^3->A)(&0)) /\
                rfs_neck (top,atlas) g eps (x(&n)) (e(&n))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | &0 <= i /\ i <= &n} x e` THEN
    REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
    REWRITE_TAC[INT_POS; INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(&0))
                         ((e:int->real^3->A)(&0))` THEN
    SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A)(&0)`; `(e:int->real^3->A)(&0)`;
                 `(x:int->A)(&n)`; `(e:int->real^3->A)(&n)`; `E:real^3->A`; `L:real`;
                 `f:real^3->real^3`; `f':real^3->real^3`] P2BT_A13_REGION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  MP_TAC(SPEC `eps:real` P2BT_EPS_RADII) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{y:real^3 | exp(--inv(&2 * eps) / sqrt(&2)) <= norm y /\
                norm y <= exp((L + inv(&2 * eps)) / sqrt(&2))} SUBSET
    apx_slab (--inv eps) (L + inv eps)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; apx_slab; annulus] THEN X_GEN_TAC `y:real^3` THEN
    SUBGOAL_THEN `exp((L + inv(&2 * eps)) / sqrt(&2)) < exp((L + inv eps) / sqrt(&2))`
    MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LADD] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (E:real^3->A)
                {y | exp(--inv(&2 * eps) / sqrt(&2)) <= norm y /\
                     norm y <= exp((L + inv(&2 * eps)) / sqrt(&2))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv eps) (L + inv eps)`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `!s t:real^3->bool. s = t /\ compact t ==> compact s`) THEN
    EXISTS_TAC `cball(vec 0:real^3,exp((L + inv(&2 * eps)) / sqrt(&2))) DIFF
                ball(vec 0,exp(--inv(&2 * eps) / sqrt(&2)))` THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    X_GEN_TAC `b:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `p2bt_conf:A topology->(real^3->A)->real->A->bool`))
          (concl th))) THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [USE_THEN "bc" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `(x:int->A)(&0)`; `(x:int->A)(&n)`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "bc" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `(x:int->A)(&n)`; `(x:int->A)(&0)`] THEN
      ASM_SIMP_TAC[APX_REV_NECK] THEN
      ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM; REAL_ADD_SYM]]]);;

(* A minimizing radial geodesic on [0,1] is a constant-speed shortest curve *)
(* in the sense of apx_shortest.                                           *)

let P2BT_GEO_SHORTEST = prove
 (`!top atlas (g:A->real^3^3) x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\
     v IN mfd_exp_dom (top,atlas) g x /\
     mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v
     ==> apx_shortest (top,atlas) g (mfd_geo (top,atlas) g x v) (&0) (&1) /\
         mfd_geo (top,atlas) g x v (&0) = x /\
         mfd_geo (top,atlas) g x v (&1) = mfd_exp (top,atlas) g x v /\
         mfd_length atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) = mfd_tnorm g x v /\
         (!t. t IN real_interval[&0,&1]
              ==> mfd_speed atlas g (mfd_geo (top,atlas) g x v) (&0) (&1) t =
                  mfd_tnorm g x v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `v:real^3`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `beta = mfd_geo (top,atlas) (g:A->real^3^3) x v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^3^3) x v` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ex") (LABEL_TAC "sp")))))) THEN
  SUBGOAL_THEN
   `!s t. &0 <= s /\ s <= t /\ t <= &1
          ==> mfd_c1_curve (top,atlas) (beta:real->A) s t /\
              mfd_length atlas (g:A->real^3^3) beta s t = (t - s) * mfd_tnorm g x v /\
              (s < t ==> !r. r IN real_interval[s,t]
                             ==> mfd_velocity atlas beta s t r = mfd_vel atlas beta r)`
  (LABEL_TAC "len") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `beta:real->A`; `J:real->bool`; `s:real`; `t:real`]
      MFD_GEODESIC_C1_CURVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    USE_THEN "sp" MATCH_MP_TAC THEN
    UNDISCH_TAC `real_interval[&0,&1] SUBSET J` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(beta:real->A)(&1) = mfd_exp (top,atlas) (g:A->real^3^3) x (v:real^3)`
  ASSUME_TAC THENL
   [USE_THEN "ex" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[VECTOR_MUL_LID; REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_POS] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[apx_shortest] THEN CONJ_TAC THENL
     [USE_THEN "len" (MP_TAC o SPECL [`&0`; `&1`]) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "len" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `v:real^3`; `s:real`; `t:real`] CMPS_RAY_DIST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ex" (MP_TAC o SPEC `s:real`) THEN
    USE_THEN "ex" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    USE_THEN "len" (MP_TAC o SPECL [`&0`; `&1`]) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[REAL_SUB_RZERO; REAL_MUL_LID]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "len" (MP_TAC o SPECL [`&0`; `&1`]) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o (fun th -> MP th (REAL_ARITH `&0 < &1`)) o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[mfd_speed] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM mfd_tnorm] THEN USE_THEN "sp" MATCH_MP_TAC THEN
    UNDISCH_TAC `real_interval[&0,&1] SUBSET J` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The points of a minimizing radial geodesic lie between its ends.       *)

let P2BT_GEO_BETWEEN = prove
 (`!top atlas (g:A->real^3^3) x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\
     v IN mfd_exp_dom (top,atlas) g x /\
     mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v) = mfd_tnorm g x v
     ==> !t. t IN real_interval[&0,&1]
             ==> mfd_joinable (top,atlas) x (mfd_geo (top,atlas) g x v t) /\
                 mfd_joinable (top,atlas) (mfd_geo (top,atlas) g x v t)
                                          (mfd_exp (top,atlas) g x v) /\
                 mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x v t) +
                 mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x v t)
                          (mfd_exp (top,atlas) g x v) =
                 mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `v:real^3`] CMPS_RAY_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
             CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `v:real^3`; `t:real`] CMPS_RAY_DIST0) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `v:real^3`; `t:real`; `&1`] CMPS_RAY_DIST) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* If every point between x and y lies in a compact set K, a constant-speed *)
(* shortest curve on [0,1] inside K joins x to y.                          *)

let P2BT_MIN_FROM_COMPACT = prove
 (`!top atlas (g:A->real^3^3) x y K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_joinable (top,atlas) x y /\ compact_in top K /\
     (!b. mfd_joinable (top,atlas) x b /\ mfd_joinable (top,atlas) b y /\
          mfd_dist (top,atlas) g x b + mfd_dist (top,atlas) g b y =
          mfd_dist (top,atlas) g x y
          ==> b IN K)
     ==> ?gamma. apx_shortest (top,atlas) g gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y /\
                 mfd_length atlas g gamma (&0) (&1) = mfd_dist (top,atlas) g x y /\
                 (!t. t IN real_interval[&0,&1]
                      ==> mfd_speed atlas g gamma (&0) (&1) t =
                          mfd_dist (top,atlas) g x y) /\
                 (!t. t IN real_interval[&0,&1] ==> gamma t IN K)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `y:A`; `K:A->bool`] P2BT_HR_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `v:real^3`] P2BT_GEO_BETWEEN) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `v:real^3`] P2BT_GEO_SHORTEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^3^3) x v` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]);;

(* Any two centres of a chain: the points between them lie in a compact   *)
(* part of the chain union.                                                 *)

let P2BT_CHAIN_PAIR_BETWEEN = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas (g:A->real^3^3) eps Ix x e i j.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              apx_chain (top,atlas) g eps Ix x e /\ i IN Ix /\ j IN Ix
              ==> ?K. compact_in top K /\ K SUBSET apx_chain_union eps Ix e /\
                      !b. mfd_joinable (top,atlas) (x i) b /\
                          mfd_joinable (top,atlas) b (x j) /\
                          mfd_dist (top,atlas) g (x i) b +
                          mfd_dist (top,atlas) g b (x j) =
                          mfd_dist (top,atlas) g (x i) (x j)
                          ==> b IN K`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BT_CHAIN_BETWEEN) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `Ix:int->bool`; `x:int->A`;
                       `e:int->real^3->A`; `i:int`; `j:int`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a c. a IN Ix /\ c IN Ix /\ a <= c
          ==> ?K. compact_in top K /\ K SUBSET apx_chain_union eps Ix (e:int->real^3->A) /\
                  !b. mfd_joinable (top,atlas) ((x:int->A) a) b /\
                      mfd_joinable (top,atlas) b (x c) /\
                      mfd_dist (top,atlas) (g:A->real^3^3) (x a) b +
                      mfd_dist (top,atlas) g b (x c) =
                      mfd_dist (top,atlas) g (x a) (x c)
                      ==> b IN K`
  (LABEL_TAC "le") THENL
   [MAP_EVERY X_GEN_TAC [`a:int`; `c:int`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {k:int | a <= k /\ k <= c} x e`
    ASSUME_TAC THENL
     [MATCH_MP_TAC APX21_SUBCHAIN THEN EXISTS_TAC `Ix:int->bool` THEN
      ASM_REWRITE_TAC[APX_INT_INTERVAL_SEGMENT] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `a:int` THEN
        ASM_REWRITE_TAC[INT_LE_REFL];
        UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
        REWRITE_TAC[apx_chain; apx_int_interval] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?n. (c:int) = a + &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
     [EXISTS_TAC `num_of_int(c - a)` THEN
      MP_TAC(SPEC `c - a:int` INT_OF_NUM_OF_INT) THEN
      ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP APX_CHAIN_SHIFT) THEN STRIP_TAC THEN
    REMOVE_THEN "cb" (MP_TAC o SPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `n:num`; `\k:int. (x:int->A)(k + a)`;
       `\k:int. (e:int->real^3->A)(k + a)`]) THEN
    ASM_REWRITE_TAC[INT_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `K:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `apx_chain_union eps {k:int | a <= k /\ k <= a + &n} (e:int->real^3->A)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; APX21_IN_CHAIN_UNION; IN_ELIM_THM] THEN
      UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
      REWRITE_TAC[apx_chain; apx_int_interval] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_MESON_TAC[];
      ONCE_REWRITE_TAC[INT_ADD_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(INT_ARITH `i:int <= j \/ j <= i`) THENL
   [USE_THEN "le" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "le" (MP_TAC o SPECL [`j:int`; `i:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `K:A->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `b:A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM; REAL_ADD_SYM]]);;

(* MT Claim 10.3, chain case: two centres of a chain are joined by a       *)
(* constant-speed shortest curve inside the chain union.                    *)

let P2BT_CHAIN_MINIMIZER = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas (g:A->real^3^3) eps Ix x e i j.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              apx_chain (top,atlas) g eps Ix x e /\ i IN Ix /\ j IN Ix /\
              mfd_joinable (top,atlas) (x i) (x j)
              ==> ?gamma. apx_shortest (top,atlas) g gamma (&0) (&1) /\
                          gamma(&0) = x i /\ gamma(&1) = x j /\
                          mfd_length atlas g gamma (&0) (&1) =
                          mfd_dist (top,atlas) g (x i) (x j) /\
                          (!t. t IN real_interval[&0,&1]
                               ==> mfd_speed atlas g gamma (&0) (&1) t =
                                   mfd_dist (top,atlas) g (x i) (x j)) /\
                          (!t. t IN real_interval[&0,&1]
                               ==> gamma t IN apx_chain_union eps Ix e)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BT_CHAIN_PAIR_BETWEEN) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pb"))) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `eps:real`; `Ix:int->bool`; `x:int->A`;
                       `e:int->real^3->A`; `i:int`; `j:int`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "pb" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `eps:real`; `Ix:int->bool`; `x:int->A`; `e:int->real^3->A`; `i:int`; `j:int`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(x:int->A) i`; `(x:int->A) j`; `K:A->bool`] P2BT_MIN_FROM_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* MT Claim 10.3 at one time slice.  Curvature and distance of points of a   *)
(* neck relative to its centre, the end points of the path replaced by chain *)
(* centres, and the minimizer in the four cases of A.21.                     *)
(* ========================================================================= *)

(* The scalar curvature on an eps-neck is within a factor 3/2 of R at the  *)
(* centre (APX_NECK_CURV at alpha = 1/2).                                  *)

let P2BT_NECK_R = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) eps x e y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> mfd_scalar atlas g x / &2 <= mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &3 / &2 * mfd_scalar atlas g x`,
  MP_TAC(SPEC `&1 / &2`
    (REWRITE_RULE[APX_NECK_CURV_STATEMENT] (ISPEC `UNIV:A->bool` APX_NECK_CURV))) THEN
  REWRITE_TAC[REAL_ARITH `&0 < &1 / &2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nc"))) THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC APX_NECK_SCALAR_COMPARE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "nc" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                                 `y:real^3`]) THEN
  ASM_SIMP_TAC[]);;

(* inv(sqrt a) <= k inv(sqrt b) when b <= k a and k >= 1.                  *)

let P2BT_INV_SQRT_LE = prove
 (`!a b k. &0 < a /\ &0 < b /\ &1 <= k /\ b <= k * a
           ==> inv(sqrt a) <= k * inv(sqrt b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt a /\ &0 < sqrt b /\ sqrt k <= k /\ &0 < sqrt k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_ARITH `&1 <= k ==> &0 < k`] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b <= k * sqrt a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt k * sqrt a` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * inv(sqrt b) = k / sqrt b` SUBST1_TAC THENL
   [REWRITE_TAC[real_div]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `inv(sqrt a) * sqrt b = sqrt b / sqrt a` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ]);;

(* A point of an eps-neck is joinable to the centre, at distance at most   *)
(* (2 / eps) R(x)^(-1/2) (eps <= 1/100).                                    *)

let P2BT_NECK_CENTRE_DIST = prove
 (`!top atlas (g:A->real^3^3) eps x e y.
     &0 < eps /\ eps <= &1 / &100 /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
     ==> mfd_joinable (top,atlas) x (e y) /\
         mfd_dist (top,atlas) g x (e y) <= &2 / eps * inv(sqrt(mfd_scalar atlas g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?w. w IN sphere(vec 0,&1) /\ x = (e:real^3->A) w`
  (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
    REWRITE_TAC[rfs_neck; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom eps /\ apx_sval w = &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; APX_SLAB_NECK_DOM; APX_SLAB_SVAL; apx_sval] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO; GSYM NORM_EQ_0] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `w:real^3`; `y:real^3`]
    APX_NECK_DIST_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `x:A`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `a <= b ==> b <= c ==> a <= c`)) THEN
  ABBREV_TAC `r = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
    SIMP_TAC[rfs_neck; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 + eps) <= &101 / &100 /\ sqrt(&2) * pi <= &5 /\ &100 <= inv eps`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &13 / &4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          MP_TAC PI_POS THEN REAL_ARITH_TAC;
          MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
        CONV_TAC REAL_RAT_REDUCE_CONV];
      MP_TAC(SPECL [`eps:real`; `&1 / &100`] REAL_LE_INV2) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * (abs(apx_sval w - apx_sval y) + sqrt(&2) * pi) <=
                &2 / eps`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * (inv eps + &5)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[];
        MP_TAC PI_POS THEN MP_TAC(SPEC `&2` SQRT_POS_LE) THEN
        REWRITE_TAC[REAL_POS] THEN DISCH_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
        REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * r * (abs(&0 - apx_sval y) + sqrt(&2) * pi) =
                r * (sqrt(&1 + eps) * (abs(apx_sval w - apx_sval y) + sqrt(&2) * pi))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* A point of a neck and the centre: curvature within 2C and distance at   *)
(* most (5C / eps) R^(-1/2) at the point.                                  *)

let P2BT_NECK_ENDPOINT = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) C eps x e y.
        &1 < C /\ &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> mfd_joinable (top,atlas) x (e y) /\
            mfd_scalar atlas g x <= &2 * C * mfd_scalar atlas g (e y) /\
            mfd_scalar atlas g (e y) <= &2 * C * mfd_scalar atlas g x /\
            mfd_dist (top,atlas) g x (e y) <=
            &5 * C / eps * inv(sqrt(mfd_scalar atlas g (e y)))`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr")) P2BT_NECK_R THEN
  EXISTS_TAC `min eps1 (&1 / &100)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "nr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
                                 `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]
    P2BT_NECK_CENTRE_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ABBREV_TAC `rx = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `ry = mfd_scalar atlas (g:A->real^3^3) (e(y:real^3))` THEN
  SUBGOAL_THEN `&0 < ry` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * ry` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * rx` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`rx:real`; `ry:real`; `&3 / &2`] P2BT_INV_SQRT_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt ry) /\ &0 <= inv eps /\ &100 <= inv eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`eps:real`; `&1 / &100`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `a <= b ==> b <= c ==> a <= c`)) THEN
  REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * inv eps * &3 / &2 * inv(sqrt ry)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&3 * inv eps <= (&5 * C) * inv eps` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* A point z of a cap U whose end neck e a precedes e(a + 1) in a chain:   *)
(* the same comparison with the centre x(a + 1).                           *)

let P2BT_CAP_ENDPOINT = prove
 (`?eps1. &0 < eps1 /\
     !top atlas (g:A->real^3^3) C eps U Y Ix x e a z.
        &1 < C /\ &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_cap (top,atlas) g C eps U Y /\
        apx_chain (top,atlas) g eps Ix x e /\ a IN Ix /\ (a + &1) IN Ix /\
        IMAGE (e a) (rfs_neck_dom eps) SUBSET U /\ z IN U
        ==> mfd_joinable (top,atlas) (x(a + &1)) z /\
            mfd_scalar atlas g (x(a + &1)) <= &2 * C * mfd_scalar atlas g z /\
            mfd_scalar atlas g z <= &2 * C * mfd_scalar atlas g (x(a + &1)) /\
            mfd_dist (top,atlas) g (x(a + &1)) z <=
            &5 * C / eps * inv(sqrt(mfd_scalar atlas g z))`,
  X_CHOOSE_THEN `eps1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr")) P2BT_NECK_R THEN
  EXISTS_TAC `min eps1 (&1 / &100)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `v = exp((--(&3) / (&4 * eps)) / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `(v:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps)) /\
                v IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(v:real^3 = vec 0) /\ apx_sval v = --(&3) / (&4 * eps)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN
      SIMP_TAC[GSYM NORM_EQ_0; apx_sval; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH;
               REAL_ABS_EXP; REAL_MUL_RID; LOG_EXP; REAL_EXP_NZ] THEN
      MATCH_MP_TAC REAL_DIV_LMUL THEN SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH;
                                              REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps (x(a + &1)) (e(a + &1)) /\
                (e:int->real^3->A) (a + &1) v IN U`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(a + &1))
                    ((e:int->real^3->A)(a + &1))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
      REWRITE_TAC[apx_chain] THEN
      DISCH_THEN(MP_TAC o SPEC `a + &1:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `a:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `IMAGE ((e:int->real^3->A) a) (rfs_neck_dom eps) SUBSET U` THEN
    UNDISCH_TAC `(v:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p = (x:int->A)(a + &1)` THEN
  ABBREV_TAC `w = (e:int->real^3->A) (a + &1) v` THEN
  USE_THEN "nr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `g:A->real^3^3`; `eps:real`; `p:A`;
                                 `(e:int->real^3->A)(a + &1)`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `p:A`; `(e:int->real^3->A)(a + &1)`;
                 `v:real^3`] P2BT_NECK_CENTRE_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `z:A`; `w:A`]
    APX22_CAP_RATIO) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `w:A`; `z:A`]
    APX22_CAP_RATIO) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `z:A`; `w:A`]
    APX22_CAP_DIAM) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX22_CAP_SMOOTH]; ALL_TAC] THEN
  ABBREV_TAC `rp = mfd_scalar atlas (g:A->real^3^3) p` THEN
  ABBREV_TAC `rw = mfd_scalar atlas (g:A->real^3^3) w` THEN
  ABBREV_TAC `rz = mfd_scalar atlas (g:A->real^3^3) z` THEN
  SUBGOAL_THEN `&0 < rp` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rz <= &2 * C * rp` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * rw` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * &3 / &2 * rp` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `w:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * rw` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `p:A`; `w:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) w z = mfd_dist (top,atlas) g z w`
  SUBST1_TAC THENL [ASM_MESON_TAC[MFD_DIST_SYM]; ALL_TAC] THEN
  MP_TAC(SPECL [`rp:real`; `rz:real`; `&2 * C`] P2BT_INV_SQRT_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt rz) /\ &0 <= inv eps /\ &1 <= inv eps` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / eps * inv(sqrt rp) <= &4 * C / eps * inv(sqrt rz) /\
                C * inv(sqrt rz) <= C / eps * inv(sqrt rz)`
  MP_TAC THENL
   [REWRITE_TAC[real_div] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * inv eps * (&2 * C) * inv(sqrt rz)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `inv(sqrt rp) <= (&2 * C) * inv(sqrt rz)` THEN
        REWRITE_TAC[REAL_MUL_ASSOC];
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) z w < C * inv(sqrt rz)` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) p w <= &2 / eps * inv(sqrt rp)` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* MT Claim 10.3 at one time slice.  X is a compact connected set of       *)
(* points that are centres of NK-necks or lie in cap cores, z and y lie in *)
(* X, R(y) > 4 C^2 R(z).  Then a constant-speed shortest curve joins a     *)
(* point p with R(p) <= 4 C R(z) to a point q with R(y) <= 4 C R(q), of    *)
(* length at most d(z,y) + (10 C / eps) R(z)^(-1/2).  In the chain cases p *)
(* and q are chain centres (A.1 confinement and the A13 chart); in the     *)
(* compact-component case p = z and q = y; a single cap is excluded by its *)
(* curvature ratio.                                                         *)

let P2BT_CLAIM_10_3 = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u /\ P2BT_REQ_A21_CH_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps top atlas (g:A->real^3^3) NK X z y.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              compact_in top X /\ connected_in top X /\ z IN X /\ y IN X /\
              mfd_joinable (top,atlas) z y /\
              (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
              (!x. x IN X
                   ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y)) /\
              &0 < mfd_scalar atlas g z /\
              &4 * C * C * mfd_scalar atlas g z < mfd_scalar atlas g y
              ==> ?p q gamma.
                    apx_shortest (top,atlas) g gamma (&0) (&1) /\
                    gamma(&0) = p /\ gamma(&1) = q /\ &0 < mfd_scalar atlas g p /\
                    (!t. t IN real_interval[&0,&1]
                         ==> mfd_speed atlas g gamma (&0) (&1) t =
                             mfd_dist (top,atlas) g p q) /\
                    mfd_scalar atlas g p <= &4 * C * mfd_scalar atlas g z /\
                    mfd_scalar atlas g y <= &4 * C * mfd_scalar atlas g q /\
                    mfd_dist (top,atlas) g p q <=
                    mfd_dist (top,atlas) g z y +
                    &10 * C / eps * inv(sqrt(mfd_scalar atlas g z))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[P2BT_REQ_A21_CH_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `epsa:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a21"))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BT_CHAIN_MINIMIZER) THEN
  DISCH_THEN(X_CHOOSE_THEN `epsm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cm"))) THEN
  X_CHOOSE_THEN `epsn:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ne"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_ENDPOINT) THEN
  X_CHOOSE_THEN `epsc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce"))
    (INST_TYPE [`:A`,`:A`] P2BT_CAP_ENDPOINT) THEN
  EXISTS_TAC `min (min epsa epsm) (min (min epsn epsc) (&1 / &100))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `NK:A->(real^3->A)->bool`; `X:A->bool`; `z:A`; `y:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= epsa /\ eps <= epsm /\ eps <= epsn /\ eps <= epsc /\
                eps <= &1 / &100`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z <= mfd_scalar atlas g y` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= C * C` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&1`; `C:real`; `&1`; `C:real`] REAL_LE_MUL2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z <= (C * C) * mfd_scalar atlas g z`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (C * C) * mfd_scalar atlas (g:A->real^3^3) z` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&4 * C * C * mfd_scalar atlas (g:A->real^3^3) z < mfd_scalar atlas g y` THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* assembly from a chain and the two end comparisons *)
  SUBGOAL_THEN
   `!Ix x e i j.
      apx_chain (top,atlas) g eps Ix x (e:int->real^3->A) /\ i IN Ix /\ j IN Ix /\
      (mfd_joinable (top,atlas) (x i) z /\
       mfd_scalar atlas g (x i) <= &2 * C * mfd_scalar atlas g z /\
       mfd_scalar atlas g z <= &2 * C * mfd_scalar atlas g (x i) /\
       mfd_dist (top,atlas) g (x i) z <= &5 * C / eps * inv(sqrt(mfd_scalar atlas g z))) /\
      (mfd_joinable (top,atlas) (x j) y /\
       mfd_scalar atlas g (x j) <= &2 * C * mfd_scalar atlas g y /\
       mfd_scalar atlas g y <= &2 * C * mfd_scalar atlas g (x j) /\
       mfd_dist (top,atlas) g (x j) y <= &5 * C / eps * inv(sqrt(mfd_scalar atlas g y)))
      ==> ?p q gamma.
            apx_shortest (top,atlas) g gamma (&0) (&1) /\
            gamma(&0) = p /\ gamma(&1) = q /\ &0 < mfd_scalar atlas g p /\
            (!t. t IN real_interval[&0,&1]
                 ==> mfd_speed atlas g gamma (&0) (&1) t = mfd_dist (top,atlas) g p q) /\
            mfd_scalar atlas g p <= &4 * C * mfd_scalar atlas g z /\
            mfd_scalar atlas g y <= &4 * C * mfd_scalar atlas g q /\
            mfd_dist (top,atlas) g p q <=
            mfd_dist (top,atlas) g z y + &10 * C / eps * inv(sqrt(mfd_scalar atlas g z))`
  (LABEL_TAC "asm") THENL
   [MAP_EVERY X_GEN_TAC [`Ix:int->bool`; `x:int->A`; `e:int->real^3->A`; `i:int`; `j:int`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
      REWRITE_TAC[apx_chain] THEN
      DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) y ((x:int->A) j)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(x:int->A) j`; `y:A`] MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) z ((x:int->A) j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) ((x:int->A) i) (x j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "cm" (MP_TAC o SPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `Ix:int->bool`; `x:int->A`; `e:int->real^3->A`; `i:int`; `j:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i)` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
      REWRITE_TAC[apx_chain] THEN
      DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`(x:int->A) i`; `(x:int->A) j`; `gamma:real->A`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((x:int->A) j)` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
      REWRITE_TAC[apx_chain] THEN
      DISCH_THEN(MP_TAC o SPEC `j:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&0 <= C * mfd_scalar atlas (g:A->real^3^3) z` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= C * mfd_scalar atlas (g:A->real^3^3) ((x:int->A) j)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(x:int->A) i`; `z:A`; `(x:int->A) j`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `z:A`; `y:A`; `(x:int->A) j`] MFD_DIST_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) y ((x:int->A) j) =
                  mfd_dist (top,atlas) g (x j) y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `C / eps * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) y)) <=
                  C / eps * inv(sqrt(mfd_scalar atlas g z))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((x:int->A) j) y <=
                 &5 * C / eps * inv(sqrt(mfd_scalar atlas g y))` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((x:int->A) i) z <=
                 &5 * C / eps * inv(sqrt(mfd_scalar atlas g z))` THEN
    MAP_EVERY UNDISCH_TAC
     [`mfd_dist (top,atlas) (g:A->real^3^3) y ((x:int->A) j) =
       mfd_dist (top,atlas) g (x j) y`;
      `C / eps * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) y)) <=
       C / eps * inv(sqrt(mfd_scalar atlas g z))`;
      `mfd_dist (top,atlas) (g:A->real^3^3) z ((x:int->A) j) <=
       mfd_dist (top,atlas) g z y + mfd_dist (top,atlas) g y (x j)`;
      `mfd_dist (top,atlas) (g:A->real^3^3) ((x:int->A) i) (x j) <=
       mfd_dist (top,atlas) g (x i) z + mfd_dist (top,atlas) g z (x j)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `!x. x IN X
                     ==> (?e. (NK:A->(real^3->A)->bool) x e) \/
                         (?U Y. rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y /\ x IN Y)` THEN
    DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps z (e:real^3->A)` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[rfs_neck]];
      MATCH_MP_TAC APX22_CAP_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* end points in a chain union *)
  SUBGOAL_THEN
   `!Ix x e w.
      apx_chain (top,atlas) g eps Ix x (e:int->real^3->A) /\
      w IN apx_chain_union eps Ix e
      ==> ?i. i IN Ix /\ (mfd_joinable (top,atlas) (x i) w /\
          mfd_scalar atlas g (x i) <= &2 * C * mfd_scalar atlas g w /\
          mfd_scalar atlas g w <= &2 * C * mfd_scalar atlas g (x i) /\
          mfd_dist (top,atlas) g (x i) w <=
          &5 * C / eps * inv(sqrt(mfd_scalar atlas g w)))`
  (LABEL_TAC "cend") THENL
   [MAP_EVERY X_GEN_TAC [`Ix:int->bool`; `x:int->A`; `e:int->real^3->A`; `w:A`] THEN
    REWRITE_TAC[APX21_IN_CHAIN_UNION; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i:int`
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `i:int` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ne" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_chain (top,atlas) (g:A->real^3^3) eps Ix x e` THEN
    REWRITE_TAC[apx_chain] THEN
    DISCH_THEN(MP_TAC o SPEC `i:int` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `z:A`; `y:A`]
      MFD_JOINABLE_IN_TOPSPACE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C / eps * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) /\
                &0 <= C * mfd_scalar atlas g z /\ &0 <= C * mfd_scalar atlas g y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "a21" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `g:A->real^3^3`; `NK:A->(real^3->A)->bool`; `X:A->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [(* a compact component containing X *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `z:A`; `y:A`; `V:A->bool`] P2BT_MIN_FROM_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `connected_component_of top (z:A)`; `V:A->bool`]
        CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:A` THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `(X:A->bool) SUBSET V` THEN UNDISCH_TAC `(z:A) IN X` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `z:A`; `b:A`]
        MFD_JOINABLE_CONNECTED_COMPONENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `y:A`; `gamma:real->A`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z <= C * mfd_scalar atlas g z /\
                  mfd_scalar atlas g y <= C * mfd_scalar atlas g y`
    MP_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&0 <= C / eps * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))`;
      `&0 <= C * mfd_scalar atlas (g:A->real^3^3) z`;
      `&0 <= C * mfd_scalar atlas (g:A->real^3^3) y`] THEN
    REAL_ARITH_TAC;
    (* a single cap containing X: excluded by its curvature ratio *)
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `z:A`; `y:A`]
      APX22_CAP_RATIO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(X:A->bool) SUBSET U` THEN
      UNDISCH_TAC `(z:A) IN X` THEN UNDISCH_TAC `(y:A) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `C * mfd_scalar atlas (g:A->real^3^3) z <= &4 * C * C * mfd_scalar atlas g z`
    MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    (* a capped chain *)
    SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e`
    ASSUME_TAC THENL
     [UNDISCH_TAC `apx_balanced (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e` THEN
      SIMP_TAC[apx_balanced];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!w. w IN X ==> ?i. i IN {i:int | a <= i /\ i <= b} /\ (mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) ((x:int->A) i) w /\
          mfd_scalar atlas (g:A->real^3^3) ((x:int->A) i) <= &2 * C * mfd_scalar atlas g w /\
          mfd_scalar atlas g w <= &2 * C * mfd_scalar atlas g ((x:int->A) i) /\
          mfd_dist (top,atlas) g ((x:int->A) i) w <=
          &5 * C / eps * inv(sqrt(mfd_scalar atlas g w)))`
    (LABEL_TAC "wend") THENL
     [X_GEN_TAC `w:A` THEN DISCH_TAC THEN ASM_CASES_TAC `(w:A) IN U` THENL
       [EXISTS_TAC `a + &1:int` THEN REWRITE_TAC[IN_ELIM_THM] THEN
        CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "ce" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`U:A->bool`; `Y:A->bool`; `{i:int | a <= i /\ i <= b}`;
                              `e:int->real^3->A`] THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
        TRY ASM_INT_ARITH_TAC THEN SET_TAC[];
        USE_THEN "cend" MATCH_MP_TAC THEN EXISTS_TAC `e:int->real^3->A` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(X:A->bool) SUBSET
                     U UNION apx_chain_union eps {i:int | a <= i /\ i <= b} e` THEN
        UNDISCH_TAC `~((w:A) IN U)` THEN UNDISCH_TAC `(w:A) IN X` THEN SET_TAC[]];
      ALL_TAC] THEN
    USE_THEN "wend" (MP_TAC o SPEC `z:A`) THEN
    USE_THEN "wend" (MP_TAC o SPEC `y:A`) THEN
    REWRITE_TAC[ASSUME `(z:A) IN X`; ASSUME `(y:A) IN X`] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
    USE_THEN "asm" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`{i:int | a <= i /\ i <= b}`; `x:int->A`; `e:int->real^3->A`;
                          `i:int`; `j:int`] THEN
    ASM_REWRITE_TAC[];
    (* a chain covering X *)
    SUBGOAL_THEN `apx_chain (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e`
    ASSUME_TAC THENL
     [UNDISCH_TAC `apx_balanced (top,atlas) (g:A->real^3^3) eps {i:int | a <= i /\ i <= b} x e` THEN
      SIMP_TAC[apx_balanced];
      ALL_TAC] THEN
    USE_THEN "cend" (MP_TAC o SPECL [`{i:int | a <= i /\ i <= b}`; `x:int->A`;
                                     `e:int->real^3->A`; `z:A`]) THEN
    USE_THEN "cend" (MP_TAC o SPECL [`{i:int | a <= i /\ i <= b}`; `x:int->A`;
                                     `e:int->real^3->A`; `y:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(X:A->bool) SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e` THEN
      UNDISCH_TAC `(y:A) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:int` STRIP_ASSUME_TAC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(X:A->bool) SUBSET apx_chain_union eps {i:int | a <= i /\ i <= b} e` THEN
      UNDISCH_TAC `(z:A) IN X` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) THEN
    USE_THEN "asm" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`{i:int | a <= i /\ i <= b}`; `x:int->A`; `e:int->real^3->A`;
                          `i:int`; `j:int`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Exclusion of components and caps along a shortest curve, and the window   *)
(* of MT Claim 10.4.                                                         *)
(* ========================================================================= *)

(* Scalar curvature against sectional curvature bounds at a point (with an *)
(* orthonormal frame, R is the sum over i <> j of the sectional curvatures). *)
(* P2BT_FRAME_TERM_SECT, P2BT_DOUBLE_SUM_OFFDIAG, P2BT_LSCALAR_SECT and    *)
(* P2BT_MFD_SCALAR_SECT are renamed copies of P2BS_FRAME_TERM_SECT,        *)
(* P2BS_DOUBLE_SUM_OFFDIAG, P2BS_LSCALAR_SECT and P2BS_MFD_SCALAR_SECT of  *)
(* pc_p2b_slice (loading pc_p2b_slice would add 21 files to the load       *)
(* closure of this unit).                                                  *)

let P2BT_FRAME_TERM_SECT = prove
 (`!U (G:real^N->real^N^N) y (M:real^N^N) i j.
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (i = j
          ==> (matrix_inv M ** basis i) dot
              (G y ** lriemann G y (matrix_inv M ** basis i)
                                   (matrix_inv M ** basis j) (matrix_inv M ** basis j)) = &0) /\
         (~(i = j)
          ==> ~collinear {vec 0, matrix_inv M ** basis i, matrix_inv M ** basis j} /\
              (matrix_inv M ** basis i) dot
              (G y ** lriemann G y (matrix_inv M ** basis i)
                                   (matrix_inv M ** basis j) (matrix_inv M ** basis j)) =
              lsectional G y (matrix_inv M ** basis i) (matrix_inv M ** basis j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `fi = matrix_inv(M:real^N^N) ** basis i` THEN
  ABBREV_TAC `fj = matrix_inv(M:real^N^N) ** basis j` THEN
  SUBGOAL_THEN `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1 /\
                (fj:real^N) dot (G y ** fj) = &1 /\
                (fi:real^N) dot (G y ** fj) = (if (i:num) = j then &1 else &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `i:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `j:num`; `j:num`]
                    P2B_FRAME_ORTHO);
      MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`; `i:num`; `j:num`]
                    P2B_FRAME_ORTHO)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(G:real^N->real^N^N) y = transp(M:real^N^N) ** M` THEN DISCH_THEN(K ALL_TAC) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(fi:real^N) = fj` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["fi"; "fj"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `fj:real^N`;
                   `fj:real^N`; `fj:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x:real^N) = --x <=> x = vec 0`] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) =
               (if (i:num) = j then &1 else &0)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_LEMMA] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fj) = &0` THEN
      UNDISCH_TAC `(fj:real^N) dot ((G:real^N->real^N^N) y ** fj) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      UNDISCH_TAC `(fi:real^N) dot ((G:real^N->real^N^N) y ** fi) = &1` THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; DOT_LMUL] THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `c * c = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    REWRITE_TAC[lsectional] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_DIV_1]]);;

let P2BT_DOUBLE_SUM_OFFDIAG = prove
 (`!n (t:num->num->real) a.
     (!i. 1 <= i /\ i <= n ==> t i i = &0)
     ==> ((!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n /\ ~(i = j) ==> a <= t i j)
          ==> &(n * (n - 1)) * a <= sum(1..n) (\j. sum(1..n) (\i. t i j))) /\
         ((!i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n /\ ~(i = j) ==> t i j <= a)
          ==> sum(1..n) (\j. sum(1..n) (\i. t i j)) <= &(n * (n - 1)) * a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum(1..n) (\j. sum(1..n) (\i. if i = j then &0 else a)) = &(n * (n - 1)) * a`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..n) (\j. &(n - 1) * a)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `jj:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\i. if (i:num) = jj then &0 else a) =
                    (\i. a - (if (i:num) = jj then a else &0))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUM_DELTA; IN_NUMSEG] THEN
      ASM_REWRITE_TAC[ADD_SUB] THEN
      SUBGOAL_THEN `1 <= n` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

let P2BT_LSCALAR_SECT = prove
 (`!U (G:real^N->real^N^N) y a.
     metric_field U G /\ y IN U
     ==> ((!u v. ~collinear {vec 0,u,v} ==> a <= lsectional G y u v)
          ==> &(dimindex(:N) * (dimindex(:N) - 1)) * a <= lscalar G y) /\
         ((!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v <= a)
          ==> lscalar G y <= &(dimindex(:N) * (dimindex(:N) - 1)) * a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `M:real^N^N`]
                P2B_LSCALAR_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `Tm = \i j. (matrix_inv(M:real^N^N) ** basis i) dot
                         ((G:real^N->real^N^N) y ** lriemann G y (matrix_inv M ** basis i)
                              (matrix_inv M ** basis j) (matrix_inv M ** basis j))` THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\j. lricci (G:real^N->real^N^N) y (matrix_inv(M:real^N^N) ** basis j)
                  (matrix_inv M ** basis j)) =
    sum(1..dimindex(:N)) (\j. sum(1..dimindex(:N)) (\i. (Tm:num->num->real) i j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN EXPAND_TAC "Tm" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_LRICCI_FRAME THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> (i = j ==> (Tm:num->num->real) i j = &0) /\
              (~(i = j)
               ==> ~collinear {vec 0, matrix_inv(M:real^N^N) ** basis i,
                               matrix_inv M ** basis j} /\
                   Tm i j = lsectional (G:real^N->real^N^N) y (matrix_inv M ** basis i)
                                       (matrix_inv M ** basis j))`
  (LABEL_TAC "term") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "Tm" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BT_FRAME_TERM_SECT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `Tm:num->num->real`; `a:real`] P2BT_DOUBLE_SUM_OFFDIAG) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "term" (MP_TAC o SPECL [`i:num`; `i:num`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN USE_THEN "term" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BT_MFD_SCALAR_SECT = prove
 (`!top atlas (g:A->real^3^3) x a.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> ((!u v. ~collinear {vec 0,u,v} ==> a <= mfd_sectional atlas g x u v)
          ==> &6 * a <= mfd_scalar atlas g x) /\
         ((!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g x u v <= a)
          ==> mfd_scalar atlas g x <= &6 * a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_scalar; mfd_sectional] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `a:real`] P2BT_LSCALAR_SECT) THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* P2BT_ROUND_UNIFORM is APX_ROUND_SECTIONAL (pc_apx_neck) with one        *)
(* change: the scale q of the round metric is chosen before the point x    *)
(* (it is the q of rfs_round_component), so it is uniform over W.          *)

let P2BT_ROUND_UNIFORM = prove
 (`!top atlas (g:A->real^3^3) eps W.
        &0 < eps /\ eps <= &1 / &40 /\ riemannian_metric atlas g /\
        rfs_round_component (top,atlas) g eps W
        ==> ?q. &0 < q /\
                !x. x IN W
                    ==> !u v. ~collinear {vec 0,u,v}
                              ==> abs(mfd_sectional atlas g x u v / q - &1) <= &24 * eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_round_component; rfs_mclose] THEN STRIP_TAC THEN
  EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lck_dist2")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `yc = SND (c:(A->bool)#(A->real^3)) x` THEN
  ABBREV_TAC `S = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN `(yc:real^3) IN S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["yc"; "S"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local atlas c (g1:A->real^3^3)) /\
                metric_field S (metric_local atlas c (g:A->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g1:A->real^3^3)`;
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)`] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas c (\x. q %% (g:A->real^3^3) x) =
                (\z. q %% metric_local atlas c g z)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[metric_local; FUN_EQ_THM; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]; ALL_TAC] THEN
  ABBREV_TAC `G1 = metric_local atlas c (g1:A->real^3^3)` THEN
  ABBREV_TAC `Gg = metric_local atlas c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field S (\z. q %% (Gg:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v} ==> lsectional (G1:real^3->real^3^3) yc u v = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_sectional"))
          (concl th))) THEN
    ASM_REWRITE_TAC[mfd_sectional];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`; `&1`]
                APX_CONST_CURV_RIEMANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `yc:real^3`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G1:real^3->real^3^3`; `yc:real^3`; `M:real^3^3`]
                APX_CONST1_FRAME_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt d` THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MONO_LE_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 (rfs_kreg eps) (G1:real^3->real^3^3) (\z. q %% Gg z) yc` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LCK_DIST_MONO THEN
      EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC APX_KREG_TWO THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eps pow 2)` THEN
      ASM_SIMP_TAC[SQRT_MONO_LT_EQ; POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G1:real^3->real^3^3`; `\z. q %% (Gg:real^3->real^3^3) z`;
                 `yc:real^3`; `M:real^3^3`; `&2`] APX_SECTIONAL_STABILITY_LIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `u:real^3` THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "lsectional")) (concl th) &&
    can (find_term (fun t -> t = `&8`)) (concl th))) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `Gg:real^3->real^3^3`; `q:real`; `yc:real^3`;
                 `u:real^3`; `v:real^3`] APX_LSECTIONAL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `lsectional (Gg:real^3->real^3^3) yc u v =
                mfd_sectional (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (x:A) u v`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Gg"; "yc"; "c"] THEN REWRITE_TAC[mfd_sectional]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt(lck_dist2 2 (G1:real^3->real^3^3) (\z. q %% Gg z) yc) < eps` THEN
  REAL_ARITH_TAC);;

(* On an eps-round component the scalar curvature varies by a factor at   *)
(* most 2 (eps <= 1/100).                                                   *)

let P2BT_ROUND_RATIO = prove
 (`!top atlas (g:A->real^3^3) eps W x y.
     &0 < eps /\ eps <= &1 / &100 /\ riemannian_metric atlas g /\
     rfs_round_component (top,atlas) g eps W /\ x IN W /\ y IN W
     ==> mfd_scalar atlas g y <= &2 * mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `W:A->bool`] P2BT_ROUND_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "un"))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                (x:A) IN topspace top /\ (y:A) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps W` THEN
    REWRITE_TAC[rfs_round_component] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(x:A) IN W`; `(y:A) IN W`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w u v. w IN W /\ ~collinear {vec 0,u,v}
            ==> q * (&1 - &24 * eps) <= mfd_sectional atlas (g:A->real^3^3) w u v /\
                mfd_sectional atlas g w u v <= q * (&1 + &24 * eps)`
  (LABEL_TAC "bd") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "un" (MP_TAC o SPECL [`u:real^3`; `v:real^3`] o
                   C MATCH_MP (ASSUME `(w:A) IN W`) o SPEC `w:A`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
      (REAL_ARITH `abs(a - &1) <= b ==> a <= &1 + b /\ &1 - b <= a`)) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `q * (&1 - &24 * eps)`] P2BT_MFD_SCALAR_SECT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `y:A`; `q * (&1 + &24 * eps)`] P2BT_MFD_SCALAR_SECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ANTS_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "bd" (MP_TAC o SPECL [`y:A`; `u:real^3`; `v:real^3`]) THEN
                  ASM_SIMP_TAC[]; DISCH_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "bd" (MP_TAC o SPECL [`x:A`; `u:real^3`; `v:real^3`]) THEN
                  ASM_SIMP_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `q * eps <= q * (&1 / &100)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&6 * q * (&1 - &24 * eps) <= mfd_scalar atlas (g:A->real^3^3) x`;
    `mfd_scalar atlas (g:A->real^3^3) y <= &6 * q * (&1 + &24 * eps)`;
    `&0 < q`] THEN
  REAL_ARITH_TAC);;

(* On a C-component, 6 R(y) < C R(x) for all points x, y (MT Def 9.75:    *)
(* sectional curvature above sup R / C, and R >= 6 min sec).               *)

let P2BT_C_COMPONENT_RATIO = prove
 (`!top atlas (g:A->real^3^3) C W x y.
     &0 < C /\ riemannian_metric atlas g /\
     rfs_c_component (top,atlas) g C W /\ x IN W /\ y IN W
     ==> &6 * mfd_scalar atlas g y < C * mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C W` THEN
  REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (y:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(x:A) IN W`; `(y:A) IN W`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b. !r. r IN IMAGE (mfd_scalar atlas (g:A->real^3^3)) W ==> r <= b`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `euclideanreal`;
                   `mfd_scalar atlas (g:A->real^3^3)`; `W:A->bool`] IMAGE_COMPACT_IN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded] THEN
    MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) y <= sup(IMAGE (mfd_scalar atlas g) W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_inf_gt")) (concl th))) THEN
  REWRITE_TAC[rfs_inf_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lb"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `d0:real`] P2BT_MFD_SCALAR_SECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "lb" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:A`; `u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `inv C * mfd_scalar atlas (g:A->real^3^3) y <=
                inv C * sup(IMAGE (mfd_scalar atlas g) W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 * mfd_scalar atlas (g:A->real^3^3) y =
                C * (&6 * (inv C * mfd_scalar atlas g y))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC);;

(* The end neck of a cap, oriented with its negative half next to the      *)
(* closed core (the hypothesis form of APX_A8_CS): from APX21_CAP_ENDS; if  *)
(* the closure of the negative half missed the closed core K, K would be    *)
(* open and closed in the connected cap U, though K and U - K are nonempty. *)

let P2BT_CAP_ORIENTED = prove
 (`?eps0. &0 < eps0 /\
     !top atlas (g:A->real^3^3) C eps U Y.
        &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        rfs_cap (top,atlas) g C eps U Y
        ==> top closure_of Y SUBSET U /\
            ?x e. rfs_neck (top,atlas) g eps x e /\
                  IMAGE e (rfs_neck_dom eps) = U DIFF top closure_of Y /\
                  ~(top closure_of (IMAGE e (apx_slab (--inv eps) (&0))) INTER
                    top closure_of Y = {})`,
  X_CHOOSE_THEN `ec:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `en:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r"))
    (INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  EXISTS_TAC `min ec (min en (&1 / &11))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CAP_ENDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                      `g:A->real^3^3`; `eps:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "n4r" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `z0:A` (X_CHOOSE_THEN `K:A->bool`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `K = top closure_of (Y:A->bool)` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`z0:A`; `e0:real^3->A`] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Kc = top closure_of (Y:A->bool)` THEN
  ABBREV_TAC `Ah = IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))` THEN
  SUBGOAL_THEN `open_in top ((Kc:A->bool) UNION Ah)` ASSUME_TAC THENL
   [EXPAND_TAC "Ah" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_slab")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "compact_in")) (concl th))) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `&11 <= inv eps` MP_TAC THENL
       [MP_TAC(SPECL [`eps:real`; `&1 / &11`] REAL_LE_INV2) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
        REAL_ARITH_TAC];
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `open_in top (Kc:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `Kc:A->bool = (Kc UNION Ah) INTER (topspace top DIFF top closure_of Ah)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `Ah:A->bool`] CLOSURE_OF_SUBSET_INTER) THEN
      MP_TAC(ISPECL [`top:A topology`; `Kc:A->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `top closure_of Ah INTER (Kc:A->bool) = {}` THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN
      REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_CLOSURE_OF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `Kc:A->bool`] CONNECTED_IN_CLOPEN_CASES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX21_CAP_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                            `C:real`; `eps:real`; `Y:A->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (e0:real^3->A) (rfs_neck_dom eps) = {})` MP_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `basis 1:real^3` THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`~(Y:A->bool = {})`; `(Y:A->bool) SUBSET Kc`; `(Kc:A->bool) SUBSET U`] THEN
  SET_TAC[]);;

(* MT Claim 10.4, the observation from Cor A.8: if a constant-speed        *)
(* shortest curve on [0,1] meets the core of a (C,eps)-cap U, then every   *)
(* point w of U satisfies R(w) < C R(gamma 0) or R(gamma 1) < C R(w).      *)

let P2BT_SHORTEST_CAP = prove
 (`!u:A->bool.
     APX_A8_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C top atlas (g:A->real^3^3) eps U Y gamma t0.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              rfs_cap (top,atlas) g C eps U Y /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 <= t0 /\ t0 <= &1 /\ gamma t0 IN Y
              ==> !w. w IN U
                      ==> mfd_scalar atlas g w < C * mfd_scalar atlas g (gamma(&0)) \/
                          mfd_scalar atlas g (gamma(&1)) < C * mfd_scalar atlas g w`,
  GEN_TAC THEN REWRITE_TAC[APX_A8_CS_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e8:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a8"))) THEN
  X_CHOOSE_THEN `eo:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "or"))
    (INST_TYPE [`:A`,`:A`] P2BT_CAP_ORIENTED) THEN
  EXISTS_TAC `min e8 eo` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "or" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                 `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`;
                                 `Y:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "a8" (MP_TAC o SPECL
    [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `eps:real`; `U:A->bool`; `Y:A->bool`; `x:A`; `e:real^3->A`; `gamma:real->A`;
     `&0`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`] o CONJUNCT2) THEN
      REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN SIMP_TAC[];
      EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iv"))))))) THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET U /\ U SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX22_CAP_DATA) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K:A->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= t0 /\ t0 <= d` STRIP_ASSUME_TAC THENL
   [USE_THEN "iv" (MP_TAC o SPEC `t0:real`) THEN
    REWRITE_TAC[ASSUME `&0 <= t0`; ASSUME `t0 <= &1`; IN_UNION] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISJ1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `Y:A->bool`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(Y:A->bool) SUBSET U`; `(U:A->bool) SUBSET topspace top`] THEN
      SET_TAC[];
      UNDISCH_TAC `(gamma:real->A) t0 IN Y` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (Y:A->bool) UNION
                IMAGE (e:real^3->A) {y | y IN rfs_neck_dom eps /\ norm y <= &1} SUBSET U`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [DISJ1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `(gamma:real->A)(&0)`; `w:A`]
      APX22_CAP_RATIO) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "iv" (MP_TAC o SPEC `&0`) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `&0` && is_var(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    UNDISCH_TAC `top closure_of (Y:A->bool) UNION
                 IMAGE (e:real^3->A) {y | y IN rfs_neck_dom eps /\ norm y <= &1} SUBSET U` THEN
    SET_TAC[];
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `w:A`; `(gamma:real->A)(&1)`]
      APX22_CAP_RATIO) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "iv" (MP_TAC o SPEC `&1`) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `&1` && is_var(lhs(concl th)))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    UNDISCH_TAC `top closure_of (Y:A->bool) UNION
                 IMAGE (e:real^3->A) {y | y IN rfs_neck_dom eps /\ norm y <= &1} SUBSET U` THEN
    SET_TAC[]]);;

(* Preimages of closed sets under a continuous function on a compact       *)
(* interval are compact.                                                    *)

let P2BT_PREIMAGE_COMPACT = prove
 (`!f a b t.
     continuous_map (subtopology euclideanreal (real_interval[a,b]),euclideanreal) f /\
     real_closed t
     ==> real_compact {s | s IN real_interval[a,b] /\ f s IN t}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_compact_def] THEN
  SUBGOAL_THEN
   `compact_in (subtopology euclideanreal (real_interval[a,b]))
               {s | s IN real_interval[a,b] /\ (f:real->real) s IN t}`
  MP_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
      MP_TAC(ISPECL [`f:real->real`; `subtopology euclideanreal (real_interval[a,b])`;
                     `euclideanreal`; `t:real->bool`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[GSYM REAL_CLOSED_IN; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]];
    SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]]);;

(* The window of MT Claim 10.4: for f continuous on [0,1] with f(0) < lo <  *)
(* hi < f(1), the last time s0 at level lo and the first later time s1 at  *)
(* level hi; lo <= f <= hi on [s0,s1] and f > lo after s0.                 *)

let P2BT_REAL_WINDOW = prove
 (`!f lo hi.
     continuous_map (subtopology euclideanreal (real_interval[&0,&1]),euclideanreal) f /\
     f(&0) < lo /\ lo < hi /\ hi < f(&1)
     ==> ?s0 s1. &0 < s0 /\ s0 < s1 /\ s1 < &1 /\ f s0 = lo /\ f s1 = hi /\
                 (!s. s0 <= s /\ s <= s1 ==> lo <= f s /\ f s <= hi) /\
                 (!s. s0 < s /\ s <= &1 ==> lo < f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. &0 <= a /\ b <= &1
                      ==> (f:real->real) real_continuous_on real_interval[a,b] /\
                          continuous_map (subtopology euclideanreal (real_interval[a,b]),
                                          euclideanreal) f`
  (LABEL_TAC "cont") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[a,b]),
                                  euclideanreal) (f:real->real)`
    (fun th -> REWRITE_TAC[th; GSYM GRGD_CONTINUOUS_MAP_REAL]) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* s0: the last time with f <= lo *)
  MP_TAC(SPECL [`f:real->real`; `&0`; `&1`; `{y:real | y <= lo}`] P2BT_PREIMAGE_COMPACT) THEN
  ASM_REWRITE_TAC[REAL_CLOSED_HALFSPACE_LE; IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{s | s IN real_interval[&0,&1] /\ (f:real->real) s <= lo}`
    REAL_COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `&0` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "s0max"))) THEN
  SUBGOAL_THEN `!s. s0 < s /\ s <= &1 ==> lo < (f:real->real) s` (LABEL_TAC "after") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "s0max" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 < &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) s0 = lo` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a /\ ~(x < a) ==> x = a`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    USE_THEN "cont" (MP_TAC o SPECL [`s0:real`; `&1`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`f:real->real`; `s0:real`; `&1`; `lo:real`] REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `s:real = s0` THENL
     [UNDISCH_TAC `(f:real->real) s = lo` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "after" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* s1: the first time after s0 with f >= hi *)
  USE_THEN "cont" (MP_TAC o SPECL [`s0:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`f:real->real`; `s0:real`; `&1`; `{y:real | y >= hi}`] P2BT_PREIMAGE_COMPACT) THEN
  ASM_REWRITE_TAC[REAL_CLOSED_HALFSPACE_GE; IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{s | s IN real_interval[s0,&1] /\ (f:real->real) s >= hi}`
    REAL_COMPACT_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `&1` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "s1min"))) THEN
  SUBGOAL_THEN `!s. s0 <= s /\ s < s1 ==> (f:real->real) s < hi` (LABEL_TAC "before") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "s1min" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 < s1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) s1 = hi` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x >= a /\ ~(a < x) ==> x = a`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    USE_THEN "cont" (MP_TAC o SPECL [`s0:real`; `s1:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`f:real->real`; `s0:real`; `s1:real`; `hi:real`] REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `s:real = s1` THENL
     [UNDISCH_TAC `(f:real->real) s = hi` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "before" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s0:real`; `s1:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_CASES_TAC `s:real = s0` THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL];
        USE_THEN "after" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC];
      ASM_CASES_TAC `s:real = s1` THENL
       [ASM_REWRITE_TAC[REAL_LE_REFL];
        USE_THEN "before" (MP_TAC o SPEC `s:real`) THEN ASM_REAL_ARITH_TAC]]]);;

(* The window along a C^1 curve on [0,1], for the scalar curvature.        *)

let P2BT_GAMMA_WINDOW = prove
 (`!top atlas (g:A->real^3^3) gamma lo hi.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     mfd_scalar atlas g (gamma(&0)) < lo /\ lo < hi /\
     hi < mfd_scalar atlas g (gamma(&1))
     ==> ?s0 s1. &0 < s0 /\ s0 < s1 /\ s1 < &1 /\
                 mfd_scalar atlas g (gamma s0) = lo /\ mfd_scalar atlas g (gamma s1) = hi /\
                 (!s. s0 <= s /\ s <= s1
                      ==> lo <= mfd_scalar atlas g (gamma s) /\
                          mfd_scalar atlas g (gamma s) <= hi) /\
                 (!s. s0 < s /\ s <= &1 ==> lo < mfd_scalar atlas g (gamma s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\s. mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s)`;
                `lo:real`; `hi:real`] P2BT_REAL_WINDOW) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\s. mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s)) =
                mfd_scalar atlas g o gamma`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A)
                              (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]]);;

(* Exclusions along a constant-speed shortest curve on [0,1] whose end     *)
(* curvatures straddle R(w) by the factor C: w is not in a cap core that    *)
(* meets the curve, nor in a C-component or eps-round component that meets  *)
(* the curve.                                                               *)

let P2BT_ALONG_EXCLUDE = prove
 (`!u:A->bool.
     APX_A8_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C top atlas (g:A->real^3^3) eps gamma w.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 < mfd_scalar atlas g (gamma(&0)) /\
              &2 * mfd_scalar atlas g (gamma(&0)) < mfd_scalar atlas g (gamma(&1)) /\
              C * mfd_scalar atlas g (gamma(&0)) <= mfd_scalar atlas g w /\
              C * mfd_scalar atlas g w <= mfd_scalar atlas g (gamma(&1))
              ==> (!U Y t0. rfs_cap (top,atlas) g C eps U Y /\ w IN Y /\
                            &0 <= t0 /\ t0 <= &1 /\ gamma t0 IN Y ==> F) /\
                  (!U t0. w IN U /\
                          (rfs_c_component (top,atlas) g C U \/
                           rfs_round_component (top,atlas) g eps U) /\
                          &0 <= t0 /\ t0 <= &1 /\ gamma t0 IN U ==> F)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BT_SHORTEST_CAP) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))) THEN
  EXISTS_TAC `min es (&1 / &100)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w /\
                mfd_scalar atlas g w <= C * mfd_scalar atlas g w /\
                mfd_scalar atlas g (gamma(&0)) <= C * mfd_scalar atlas g ((gamma:real->A) (&0))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) w` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `C * mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) (&0))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:A->bool`; `Y:A->bool`; `t0:real`] THEN STRIP_TAC THEN
    REMOVE_THEN "sc" (MP_TAC o SPECL
      [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `U:A->bool`; `Y:A->bool`; `gamma:real->A`; `t0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `w:A`) THEN
    SUBGOAL_THEN `(w:A) IN U` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX22_CAP_DATA) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `(K:A->bool) SUBSET U` THEN UNDISCH_TAC `(Y:A->bool) SUBSET K` THEN
      UNDISCH_TAC `(w:A) IN Y` THEN SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `t0:real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `U IN connected_components_of top /\
                IMAGE (gamma:real->A) (real_interval[&0,&1]) SUBSET U`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `U IN connected_components_of (top:A topology)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t &&
          (fst(dest_const t) = "rfs_c_component" ||
           fst(dest_const t) = "rfs_round_component"))) (concl th))) THEN
      SIMP_TAC[rfs_c_component; rfs_round_component];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
      UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      SIMP_TAC[apx_shortest; mfd_c1_curve];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
      EXISTS_TAC `(gamma:real->A) t0` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) (&0) IN U /\ (gamma:real->A) (&1) IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (gamma:real->A) (real_interval[&0,&1]) SUBSET U` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `U:A->bool`; `(gamma:real->A)(&0)`; `(gamma:real->A)(&1)`]
      P2BT_C_COMPONENT_RATIO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`C * mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) (&0)) <= mfd_scalar atlas g w`;
      `C * mfd_scalar atlas (g:A->real^3^3) w <= mfd_scalar atlas g ((gamma:real->A) (&1))`;
      `mfd_scalar atlas (g:A->real^3^3) w <= C * mfd_scalar atlas g w`;
      `&0 < mfd_scalar atlas (g:A->real^3^3) w`] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `U:A->bool`; `(gamma:real->A)(&0)`; `(gamma:real->A)(&1)`]
      P2BT_ROUND_RATIO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* MT Claim 10.4: every point of the window is the centre of an NK-neck    *)
(* (given strong canonical neighbourhoods above lo; caps and components    *)
(* are excluded by P2BT_ALONG_EXCLUDE).                                     *)

let P2BT_WINDOW_NECKS = prove
 (`!u:A->bool.
     APX_A8_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C top atlas (g:A->real^3^3) eps (NK:A->(real^3->A)->bool) gamma lo hi s0 s1.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 < mfd_scalar atlas g (gamma(&0)) /\
              &2 * mfd_scalar atlas g (gamma(&0)) < mfd_scalar atlas g (gamma(&1)) /\
              C * mfd_scalar atlas g (gamma(&0)) <= lo /\
              C * hi <= mfd_scalar atlas g (gamma(&1)) /\
              (!w. w IN topspace top /\ lo <= mfd_scalar atlas g w
                   ==> (?e. NK w e) \/
                       (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y) \/
                       (?U. w IN U /\ rfs_c_component (top,atlas) g C U) \/
                       (?U. w IN U /\ rfs_round_component (top,atlas) g eps U)) /\
              &0 <= s0 /\ s1 <= &1 /\
              (!s. s0 <= s /\ s <= s1
                   ==> lo <= mfd_scalar atlas g (gamma s) /\
                       mfd_scalar atlas g (gamma s) <= hi)
              ==> !s. s0 <= s /\ s <= s1 ==> ?e. NK (gamma s) e`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BT_ALONG_EXCLUDE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ea:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ex"))) THEN
  EXISTS_TAC `ea:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
    is_forall(concl th) && is_imp(snd(strip_forall(concl th))) &&
    can (find_term (fun t -> t = `s0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ex" (MP_TAC o SPECL
    [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `eps:real`; `gamma:real->A`; `(gamma:real->A) s`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * hi` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "xcap") (LABEL_TAC "xcomp")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(gamma:real->A) s` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_round_component"))
        (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `gamma:real->A`; `&0`; `&1`; `s:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      SIMP_TAC[apx_shortest];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[];
    USE_THEN "xcap" (MP_TAC o SPECL [`U:A->bool`; `Y:A->bool`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    USE_THEN "xcomp" (MP_TAC o SPECL [`U:A->bool`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    USE_THEN "xcomp" (MP_TAC o SPECL [`U:A->bool`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* A constant-speed shortest curve through the centre of an eps-neck, with   *)
(* both end points outside the neck, traverses it: it meets both end slabs   *)
(* (A.6 for constant-speed curves excludes a U-turn).                        *)
(* ========================================================================= *)

let P2BT_NORM_CONTINUOUS = prove
 (`continuous_map (euclidean,euclideanreal) (norm:real^N->real)`,
  MP_TAC(ISPECL [`lift o (norm:real^N->real)`; `(:real^N)`] CONTINUOUS_MAP_EUCLIDEAN) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; CONTINUOUS_ON_LIFT_NORM; GSYM CONTINUOUS_MAP_EQ_LIFT]);;

(* A constant-speed shortest curve on [0,1] restricted to [p,q].            *)

let P2BT_CS_SUB = prove
 (`!top atlas (g:A->real^3^3) gamma p q.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     apx_shortest (top,atlas) g gamma (&0) (&1) /\
     (!t. t IN real_interval[&0,&1]
          ==> mfd_speed atlas g gamma (&0) (&1) t =
              mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
     &0 <= p /\ p < q /\ q <= &1
     ==> apx_shortest (top,atlas) g gamma p q /\
         mfd_length atlas g gamma p q =
         (q - p) * mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1)) /\
         (!t. t IN real_interval[p,q]
              ==> mfd_speed atlas g gamma p q t = mfd_length atlas g gamma p q / (q - p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) (&0) (&1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) (gamma(&0)) (gamma(&1))` THEN
  SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma p q = (q - p) * L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `gamma:real->A`; `&0`; `&1`; `p:real`; `q:real`]
      GRGD_LENGTH_SUBINTERVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS `real_integral (real_interval[p,q]) (\t:real. L)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
    REWRITE_TAC[apx_shortest] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `((q - p) * L) / (q - p) = L` SUBST1_TAC THENL
   [UNDISCH_TAC `p < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&0`; `&1`; `\t:real. t`;
                 `\t:real. &1`; `p:real`; `q:real`; `t:real`] GRGD_SPEED_REPARAM) THEN
  SUBGOAL_THEN `(gamma:real->A) o (\t. t) = gamma` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
    UNDISCH_TAC `(t:real) IN real_interval[p,q]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(t:real) IN real_interval[p,q]` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* Preimages of closed sets under a continuous curve on a compact interval  *)
(* are compact.                                                             *)

let P2BT_CURVE_PREIMAGE_COMPACT = prove
 (`!top (gamma:real->A) a b C.
     continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
     closed_in top C
     ==> real_compact {t | t IN real_interval[a,b] /\ gamma t IN C}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_compact_def] THEN
  SUBGOAL_THEN
   `compact_in (subtopology euclideanreal (real_interval[a,b]))
               {t | t IN real_interval[a,b] /\ (gamma:real->A) t IN C}`
  MP_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
      MP_TAC(ISPECL [`gamma:real->A`; `subtopology euclideanreal (real_interval[a,b])`;
                     `top:A topology`; `C:A->bool`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]];
    SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]]);;

(* The maximal excursion of a curve through s in an open set N, when both  *)
(* end points lie outside N.                                                *)

let P2BT_EXCURSION = prove
 (`!top (gamma:real->A) N s.
     continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) gamma /\
     open_in top N /\ &0 <= s /\ s <= &1 /\ gamma s IN N /\
     ~(gamma(&0) IN N) /\ ~(gamma(&1) IN N)
     ==> ?c d. &0 <= c /\ c < s /\ s < d /\ d <= &1 /\
               ~(gamma c IN N) /\ ~(gamma d IN N) /\
               (!t. c < t /\ t < d ==> gamma t IN N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. &0 <= a /\ b <= &1
                      ==> real_compact {t | t IN real_interval[a,b] /\
                                            (gamma:real->A) t IN topspace top DIFF N}`
  (LABEL_TAC "cpt") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BT_CURVE_PREIMAGE_COMPACT THEN
    EXISTS_TAC `top:A topology` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> (gamma:real->A) t IN topspace top`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                                (gamma:real->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "cpt" (MP_TAC o SPECL [`&0`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `{t | t IN real_interval[&0,s] /\ (gamma:real->A) t IN topspace top DIFF N}`
    REAL_COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL; IN_DIFF] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "cmax"))) THEN
  USE_THEN "cpt" (MP_TAC o SPECL [`s:real`; `&1`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `{t | t IN real_interval[s,&1] /\ (gamma:real->A) t IN topspace top DIFF N}`
    REAL_COMPACT_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL; IN_DIFF] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "dmin"))) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `t <= s` THENL
     [USE_THEN "cmax" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      USE_THEN "dmin" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]]);;

(* The s-value and the radius: |s| <= a iff the radius lies between the    *)
(* radii of the levels -a and a.                                            *)

let P2BT_SVAL_NORM = prove
 (`!y:real^3 a.
     ~(y = vec 0)
     ==> (abs(apx_sval y) <= a <=>
          exp(--a / sqrt(&2)) <= norm y /\ norm y <= exp(a / sqrt(&2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LT; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  MP_TAC(SPECL [`--a / sqrt(&2)`; `log(norm(y:real^3))`] REAL_EXP_MONO_LE) THEN
  MP_TAC(SPECL [`log(norm(y:real^3))`; `a / sqrt(&2)`] REAL_EXP_MONO_LE) THEN
  ASM_SIMP_TAC[EXP_LOG] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* MT Claim 10.4(5), traversal: a constant-speed shortest curve on [0,1]    *)
(* through the central sphere of an eps-neck whose ends lie outside the     *)
(* neck meets both end slabs beyond the level a >= 1/(2 eps) (otherwise it  *)
(* would meet the level sphere a or -a twice inside the neck, against A.6). *)

let P2BT_TRAVERSE = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas (g:A->real^3^3) eps x e gamma s a.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 <= s /\ s <= &1 /\ gamma s IN IMAGE (e:real^3->A) (sphere(vec 0,&1)) /\
              ~(gamma(&0) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
              ~(gamma(&1) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
              inv(&2 * eps) <= a /\ a < inv eps
              ==> (?t. &0 <= t /\ t <= &1 /\
                       gamma t IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (--a))) /\
                  (?t. &0 <= t /\ t <= &1 /\
                       gamma t IN IMAGE (e:real^3->A) (apx_slab a (inv eps)))`,
  GEN_TAC THEN REWRITE_TAC[P2B_APX_A6_CS_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e6:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "a6"))) THEN
  EXISTS_TAC `min e6 (&1 / &1024)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N = IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                               (gamma:real->A)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
    SIMP_TAC[apx_shortest; mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `N:A->bool`; `s:real`] P2BT_EXCURSION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  (* the radii *)
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&2 * eps)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rlo = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `rhi = exp(inv eps / sqrt(&2))` THEN
  ABBREV_TAC `ra = exp(a / sqrt(&2))` THEN
  ABBREV_TAC `ra' = exp(--a / sqrt(&2))` THEN
  SUBGOAL_THEN `rlo < ra' /\ ra' < &1 /\ &1 < ra /\ ra < rhi /\ &0 < rlo`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rlo"; "rhi"; "ra"; "ra'"] THEN
    REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus rlo rhi` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the middle region K and its last and first visits *)
  ABBREV_TAC `K = IMAGE (e:real^3->A) {y | ra' <= norm y /\ norm y <= ra}` THEN
  SUBGOAL_THEN `compact_in top (K:A->bool) /\ closed_in top K /\ K SUBSET N` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | ra' <= norm y /\ norm y <= ra} SUBSET rfs_neck_dom eps`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `compact_in top (K:A->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{y:real^3 | ra' <= norm y /\ norm y <= ra} =
                    cball(vec 0,ra) DIFF ball(vec 0,ra')` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN EXPAND_TAC "K" THEN EXPAND_TAC "N" THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p q. &0 <= p /\ q <= &1
                      ==> real_compact {t | t IN real_interval[p,q] /\
                                            (gamma:real->A) t IN K}`
  (LABEL_TAC "kc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BT_CURVE_PREIMAGE_COMPACT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "kc" (MP_TAC o SPECL [`s:real`; `d:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `{t | t IN real_interval[s,d] /\ (gamma:real->A) t IN K}`
    REAL_COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "mmax"))) THEN
  USE_THEN "kc" (MP_TAC o SPECL [`c:real`; `s:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPEC `{t | t IN real_interval[c,s] /\ (gamma:real->A) t IN K}`
    REAL_COMPACT_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "mmin"))) THEN
  SUBGOAL_THEN `m < d /\ c < m'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(K:A->bool) SUBSET N`; `~((gamma:real->A) d IN N)`;
                             `(gamma:real->A) d IN K`] THEN SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC [`(K:A->bool) SUBSET N`; `~((gamma:real->A) m' IN N)`;
                             `(gamma:real->A) m' IN K`] THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c2 = (c + m') / &2` THEN ABBREV_TAC `d2 = (m + d) / &2` THEN
  SUBGOAL_THEN `c < c2 /\ c2 < m' /\ m < d2 /\ d2 < d /\ c2 < s /\ s < d2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c2"; "d2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* points of the excursion in chart coordinates *)
  SUBGOAL_THEN `!t. c < t /\ t < d
                    ==> (e':A->real^3) ((gamma:real->A) t) IN annulus rlo rhi /\
                        e(e'(gamma t)) = gamma t`
  (LABEL_TAC "chart") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) t IN N` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e':A->real^3) N = rfs_neck_dom eps` THEN
    UNDISCH_TAC `!y. y IN N ==> (e:real^3->A)((e':A->real^3) y) = y` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(gamma:real->A) t IN N` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. c < t /\ t < d /\ ~((gamma:real->A) t IN K)
        ==> norm((e':A->real^3) (gamma t)) < ra' \/ ra < norm(e'(gamma t))`
  (LABEL_TAC "off") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `~((gamma:real->A) t IN K)` THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `(e':A->real^3) ((gamma:real->A) t)`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gamma:real->A) c2 IN K) /\ ~((gamma:real->A) d2 IN K)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "mmin" (MP_TAC o SPEC `c2:real`); USE_THEN "mmax" (MP_TAC o SPEC `d2:real`)] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  (* the U-turn is impossible *)
  SUBGOAL_THEN `inv(&100 * eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) <
                mfd_length atlas g gamma c2 d2 /\
                &0 < mfd_dist (top,atlas) g ((gamma:real->A)(&0)) (gamma(&1))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?w:real^3. w IN sphere(vec 0,&1) /\ (gamma:real->A) s = (e:real^3->A) w`
    (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "chart" (MP_TAC o SPEC `d2:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ABBREV_TAC `yd = (e':A->real^3) ((gamma:real->A) d2)` THEN
    SUBGOAL_THEN `(yd:real^3) IN rfs_neck_dom eps /\ (w:real^3) IN rfs_neck_dom eps /\
                  apx_sval w = &0`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
        SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
      ALL_TAC] THEN
    SUBGOAL_THEN `a < abs(apx_sval yd) /\ abs(apx_sval yd) < inv eps` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `yd:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
      ASM_SIMP_TAC[P2BT_SVAL_NORM] THEN
      USE_THEN "off" (MP_TAC o SPEC `d2:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `w:real^3`; `yd:real^3`]
      APX_NECK_DIST_LOWER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `(gamma:real->A) s`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `s:real`; `d2:real`] P2BT_CS_SUB) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `c2:real`; `d2:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A) s) (gamma d2) =
                  mfd_length atlas g gamma s d2`
    ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN
      UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A)(&0)) (gamma(&1))` THEN
    ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
    SUBGOAL_THEN `&0 < h /\ &1 / &2 <= sqrt(&1 - eps) /\ &0 <= L` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
        MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "L" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN
        UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
        SIMP_TAC[apx_shortest]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `mn = min (abs(apx_sval(yd:real^3))) (&2 * inv eps - abs(apx_sval yd))` THEN
    SUBGOAL_THEN `a <= mn` ASSUME_TAC THENL [EXPAND_TAC "mn" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&1 / &2 * h * a <= (d2 - s) * L` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&1 - eps) * h * mn` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH `&0 <= &1 / &2`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(d2 - s) * L <= (d2 - c2) * L /\ h * inv(&2 * eps) <= h * a`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&100 * eps) * h < &1 / &2 * h * inv(&2 * eps)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < h * a` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (d2 - s) * L` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r t1 t2. sphere(vec 0,r) SUBSET rfs_neck_dom eps /\
              c2 <= t1 /\ t1 < s /\ s < t2 /\ t2 <= d2 /\
              (gamma:real->A) t1 IN IMAGE (e:real^3->A) (sphere(vec 0,r)) /\
              gamma t2 IN IMAGE (e:real^3->A) (sphere(vec 0,r))
              ==> F`
  (LABEL_TAC "uturn") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `c2:real`; `d2:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "a6" (MP_TAC o SPECL
      [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `x:A`; `e:real^3->A`; `gamma:real->A`; `c2:real`; `d2:real`; `r:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(gamma:real->A) t IN N` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "N" THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `t1:real`; `t2:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_length atlas (g:A->real^3^3) gamma t1 t2 = &0` MP_TAC THENL
     [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      REWRITE_TAC[apx_shortest] THEN
      DISCH_THEN(MP_TAC o SPECL [`t1:real`; `t2:real`] o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `(gamma:real->A) t1`)) THEN
      MATCH_MP_TAC MFD_DIST_REFL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(N:A->bool) SUBSET topspace top` THEN EXPAND_TAC "N" THEN
      UNDISCH_TAC `sphere(vec 0,r) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `(gamma:real->A) t1 IN IMAGE (e:real^3->A) (sphere(vec 0,r))` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (t2 - t1) * mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A)(&0)) (gamma(&1))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the level function along the excursion *)
  SUBGOAL_THEN `(\t. norm((e':A->real^3) ((gamma:real->A) t))) real_continuous_on
                real_interval[c2,d2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
    SUBGOAL_THEN `(\t. norm((e':A->real^3) ((gamma:real->A) t))) = norm o e' o gamma`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
    REWRITE_TAC[P2BT_NORM_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `subtopology top (N:A->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE;
                    IN_REAL_INTERVAL] THEN
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `continuous_map (subtopology top (N:A->bool),euclidean) (e':A->real^3)` THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((e':A->real^3) ((gamma:real->A) s)) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `(e':A->real^3) ((e:real^3->A) w) = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. c2 <= t /\ t <= d2 /\ norm((e':A->real^3) ((gamma:real->A) t)) = ra
                    ==> gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,ra))` (LABEL_TAC "onra") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. c2 <= t /\ t <= d2 /\ norm((e':A->real^3) ((gamma:real->A) t)) = ra'
                    ==> gamma t IN IMAGE (e:real^3->A) (sphere(vec 0,ra'))` (LABEL_TAC "onra'") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0,ra) SUBSET rfs_neck_dom eps /\
                sphere(vec 0,ra') SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. c < t /\ t < d /\ norm((e':A->real^3) ((gamma:real->A) t)) < ra'
        ==> gamma t IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (--a))` (LABEL_TAC "neg") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[apx_slab; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e':A->real^3) ((gamma:real->A) t) IN annulus rlo rhi` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. c < t /\ t < d /\ ra < norm((e':A->real^3) ((gamma:real->A) t))
        ==> gamma t IN IMAGE (e:real^3->A) (apx_slab a (inv eps))` (LABEL_TAC "pos") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "chart" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[apx_slab; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(e':A->real^3) ((gamma:real->A) t)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e':A->real^3) ((gamma:real->A) t) IN annulus rlo rhi` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "off" (MP_TAC o SPEC `c2:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "off" (MP_TAC o SPEC `d2:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `rc = norm((e':A->real^3) ((gamma:real->A) c2))` THEN
  ABBREV_TAC `rd = norm((e':A->real^3) ((gamma:real->A) d2))` THEN
  ABBREV_TAC `rho = \t. norm((e':A->real^3) ((gamma:real->A) t))` THEN
  SUBGOAL_THEN `rho real_continuous_on real_interval[c2,s] /\
                rho real_continuous_on real_interval[s,d2]` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[c2,d2]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(rho:real->real) c2 = rc /\ rho d2 = rd /\ rho s = &1 /\
                (!t. rho t = norm((e':A->real^3) ((gamma:real->A) t)))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [(* rd < ra' and rc < ra': U-turn at ra' *)
    MP_TAC(SPECL [`rho:real->real`; `c2:real`; `s:real`; `ra':real`] REAL_IVT_INCREASING) THEN
    MP_TAC(SPECL [`rho:real->real`; `s:real`; `d2:real`; `ra':real`] REAL_IVT_DECREASING) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~(t1:real = s) /\ ~(t2:real = s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "uturn" (MP_TAC o SPECL [`ra':real`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      USE_THEN "onra'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]];
    (* rd < ra', rc > ra *)
    CONJ_TAC THENL
     [EXISTS_TAC `d2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "neg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `c2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* rd > ra, rc < ra': traverses from the negative to the positive end *)
    CONJ_TAC THENL
     [EXISTS_TAC `c2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "neg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `d2:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* both > ra: U-turn at ra *)
    MP_TAC(SPECL [`rho:real->real`; `c2:real`; `s:real`; `ra:real`] REAL_IVT_DECREASING) THEN
    MP_TAC(SPECL [`rho:real->real`; `s:real`; `d2:real`; `ra:real`] REAL_IVT_INCREASING) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC)] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~(t1:real = s) /\ ~(t2:real = s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "uturn" (MP_TAC o SPECL [`ra:real`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      USE_THEN "onra" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]]]);;

(* Two eps-necks, the second of comparable scale with a central-sphere point *)
(* at level at most 1/(2 eps) in the first: every point of the second       *)
(* central sphere lies at level below 3/(4 eps) in the first.               *)

let P2BT_SPHERE_LEVELS = prove
 (`!top atlas (g:A->real^3^3) eps x e z' (e':real^3->A) wm ym w yw.
     &0 < eps /\ eps <= &1 / &1024 /\ hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps z' e' /\
     inv(sqrt(mfd_scalar atlas g z')) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g x)) /\
     wm IN sphere(vec 0,&1) /\ w IN sphere(vec 0,&1) /\
     ym IN rfs_neck_dom eps /\ yw IN rfs_neck_dom eps /\
     abs(apx_sval ym) <= inv(&2 * eps) /\ e' wm = e ym /\ e' w = e yw
     ==> abs(apx_sval yw) < &3 / &4 * inv eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`] P2BT_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(wm:real^3) IN rfs_neck_dom eps /\ (w:real^3) IN rfs_neck_dom eps /\
                apx_sval wm = &0 /\ apx_sval w = &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(wm:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
      UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
      UNDISCH_TAC `(wm:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO];
      UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `wm:real^3`; `w:real^3`]
    APX_NECK_DIST_UPPER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `ym:real^3`; `yw:real^3`]
    APX_NECK_DIST_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`eps:real`; `yw:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `h' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z'))` THEN
  ABBREV_TAC `ie = inv eps` THEN
  SUBGOAL_THEN `&0 < h /\ &0 <= h' /\ &1024 <= ie /\ inv(&2 * eps) = ie / &2 /\
                sqrt(&1 + eps) <= &101 / &100 /\ &1 / &2 <= sqrt(&1 - eps) /\
                sqrt(&2) * pi <= &5`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
      EXPAND_TAC "h'" THEN MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' e'` THEN
      SIMP_TAC[rfs_neck; REAL_LT_IMP_LE];
      EXPAND_TAC "ie" THEN MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      EXPAND_TAC "ie" THEN REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &13 / &4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          MP_TAC PI_POS THEN REAL_ARITH_TAC;
          MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
        CONV_TAC REAL_RAT_REDUCE_CONV]];
    ALL_TAC] THEN
  ABBREV_TAC `mn = min (abs(apx_sval(ym:real^3) - apx_sval(yw:real^3)))
                       (&2 * ie - abs(apx_sval ym) - abs(apx_sval yw))` THEN
  SUBGOAL_THEN `ie / &4 <= mn` ASSUME_TAC THENL
   [EXPAND_TAC "mn" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 * h * ie / &4 <= sqrt(&1 - eps) * h * mn` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= &1 / &2`] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h' * sqrt(&2) * pi <= &101 / &100 * (&3 / &2 * h) * &5`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      MP_TAC PI_POS THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      MP_TAC PI_POS THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LT_IMP_LE; REAL_LE_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h * ie` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1024 * h <= ie * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* A connected set meeting an open set Y and missing its frontier lies in Y. *)

let P2BT_CONNECTED_IN_OPEN = prove
 (`!top (H:A->bool) Y.
     connected_in top H /\ open_in top Y /\ ~(H INTER Y = {}) /\
     H INTER (top closure_of Y DIFF Y) = {}
     ==> H SUBSET Y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE `!H Y:A->bool. H SUBSET Y <=> H DIFF Y = {}`] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `H:A->bool`; `Y:A->bool`] CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_SIMP_TAC[FRONTIER_OF_OPEN_IN]);;

(* The central sphere of the end neck of a cap misses the core: points just *)
(* outside it lie outside the closed core K, while the core is open.        *)

let P2BT_CAP_SPHERE_NOT_CORE = prove
 (`!top atlas (g:A->real^3^3) eps z (e':real^3->A) U K Y.
     rfs_neck (top,atlas) g eps z e' /\ eps <= &1 / &1024 /\ hausdorff_space top /\
     IMAGE e' (annulus (&1) (&2)) SUBSET U DIFF K /\ Y SUBSET K /\ open_in top Y
     ==> DISJOINT (IMAGE e' (sphere(vec 0,&1))) Y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e':real^3->A`] P2BT_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`] MFD_PARAM_MAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  MP_TAC(ISPECL [`e':real^3->A`; `subtopology euclidean (rfs_neck_dom eps)`; `top:A topology`;
                 `Y:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {y | y IN rfs_neck_dom eps /\ (e':real^3->A) y IN Y}` MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `p:A`)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = &1 + min (r / &2) (&1 / &2)` THEN
  SUBGOAL_THEN `t % (w:real^3) IN ball(w,r) /\ t % w IN annulus (&1) (&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; annulus; IN_ELIM_THM; dist; NORM_MUL] THEN
    REWRITE_TAC[VECTOR_ARITH `w - t % w:real^3 = (&1 - t) % w`; NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID] THEN EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e':real^3->A) (t % w) IN Y` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(w:real^3,r) SUBSET {y | y IN rfs_neck_dom eps /\ (e':real^3->A) y IN Y}` THEN
    UNDISCH_TAC `t % (w:real^3) IN ball(w,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`IMAGE (e':real^3->A) (annulus (&1) (&2)) SUBSET U DIFF K`; `(Y:A->bool) SUBSET K`;
    `(e':real^3->A) (t % w) IN Y`; `t % (w:real^3) IN annulus (&1) (&2)`] THEN
  SET_TAC[]);;


(* MT Claim 10.4(5), the cap case: if a point v of the middle half of an   *)
(* eps-neck centred on a constant-speed shortest curve (with ends outside   *)
(* the neck) lies in the core Y of a cap, then the curve meets Y.  Either   *)
(* the middle half lies in Y, or the boundary sphere of Y (the central      *)
(* sphere of the cap's end neck) lies in the neck as a section, the part of *)
(* the neck on the side of v lies in Y, and the curve traverses the neck.   *)

let P2BT_P1_CAP = prove
 (`!u:A->bool.
     P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C top atlas (g:A->real^3^3) eps x e gamma s U Y v.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 <= s /\ s <= &1 /\ gamma s IN IMAGE (e:real^3->A) (sphere(vec 0,&1)) /\
              ~(gamma(&0) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
              ~(gamma(&1) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
              rfs_cap (top,atlas) g C eps U Y /\ v IN Y /\
              v IN IMAGE (e:real^3->A) (apx_slab (--inv(&2 * eps)) (inv(&2 * eps)))
              ==> ?t. &0 <= t /\ t <= &1 /\ gamma t IN Y`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2BT_TRAVERSE) THEN
  DISCH_THEN(X_CHOOSE_THEN `et:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  X_CHOOSE_THEN `ec:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `en:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4r"))
    (INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  EXISTS_TAC `min (min et ec) (min en (&1 / &1024))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= et /\ eps <= ec /\ eps <= en /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX21_CAP_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (X_CHOOSE_THEN `e1:real^3->A` (X_CHOOSE_THEN `z1:A`
    (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `z':A` (X_CHOOSE_THEN `K:A->bool`
      STRIP_ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `top closure_of (Y:A->bool) = K` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `H = IMAGE (e:real^3->A) (apx_slab (--inv(&2 * eps)) (inv(&2 * eps)))` THEN
  SUBGOAL_THEN `apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps /\
                sphere(vec 0,&1) SUBSET apx_slab (--inv(&2 * eps)) (inv(&2 * eps))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&2 * eps) /\ inv(&2 * eps) < inv eps` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; SUBSET; APX_SLAB_SVAL; IN_SPHERE_0] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^3` THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NORM_EQ_0; apx_sval; LOG_1; REAL_MUL_RZERO] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN H /\ connected_in top (H:A->bool) /\
                H SUBSET IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(gamma:real->A) s IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `sphere(vec 0,&1) SUBSET apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      SET_TAC[];
      MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(H:A->bool) SUBSET Y` THENL
   [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. m IN H /\ m IN K DIFF (Y:A->bool)` (X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC)
  THENL
   [MP_TAC(ISPECL [`top:A topology`; `H:A->bool`; `Y:A->bool`] P2BT_CONNECTED_IN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:A) IN H` THEN UNDISCH_TAC `(v:A) IN Y` THEN SET_TAC[];
    ALL_TAC] THEN
  (* m lies on the boundary sphere S' = e'(S^2) and in the middle half of e *)
  SUBGOAL_THEN `?wm. wm IN sphere(vec 0,&1) /\ m = (e':real^3->A) wm`
  (X_CHOOSE_THEN `wm:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `K DIFF (Y:A->bool) SUBSET IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `(m:A) IN K DIFF Y` THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ym. ym IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\ m = (e:real^3->A) ym`
  (X_CHOOSE_THEN `ym:real^3` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(m:A) IN H` THEN EXPAND_TAC "H" THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`] P2BT_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(wm:real^3) IN rfs_neck_dom eps /\ (ym:real^3) IN rfs_neck_dom eps /\
                apx_sval wm = &0 /\ abs(apx_sval ym) <= inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `(wm:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
      UNDISCH_TAC `apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `(ym:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN SET_TAC[];
      UNDISCH_TAC `(wm:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO];
      UNDISCH_TAC `(ym:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* scales: h' <= 3/2 h *)
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z')) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas g x))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `apx_ch_ctx top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) eps` THEN
    REWRITE_TAC[apx_ch_ctx] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `wm:real^3`] o
               CONJUNCT1 o funpow 7 CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `m:A` && rand(rhs(concl th)) = `wm:real^3`)) THEN
    UNDISCH_TAC `(m:A) IN H` THEN UNDISCH_TAC `(H:A->bool) SUBSET IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* S' inside the neck e (APX_DEEP_LEVELS) *)
  SUBGOAL_THEN `!w. w IN sphere(vec 0,&1) ==> (e':real^3->A) w IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  (LABEL_TAC "sin") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC APX_DEEP_LEVELS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`; `z':A`; `ym:real^3`;
                          `wm:real^3`; `inv(&2 * eps)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom eps /\ apx_sval w = &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN SET_TAC[];
        UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
        SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_ADD_LID] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `apx_ch_ctx top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) eps` THEN
      SIMP_TAC[apx_ch_ctx];
      UNDISCH_TAC `(m:A) = (e':real^3->A) wm` THEN UNDISCH_TAC `(m:A) = (e:real^3->A) ym` THEN
      MESON_TAC[];
      REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN `&1024 <= inv eps` MP_TAC THENL
       [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* S' lies at levels below 3/(4 eps) of e *)
  SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET
                IMAGE (e:real^3->A) (apx_slab (--(&3 / &4 * inv eps)) (&3 / &4 * inv eps))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "sin" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
                    SPEC `w:real^3`) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `yw:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `yw:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    MP_TAC(SPECL [`eps:real`; `yw:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `x:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `wm:real^3`;
                   `ym:real^3`; `w:real^3`; `yw:real^3`] P2BT_SPHERE_LEVELS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(m:A) = (e':real^3->A) wm` THEN UNDISCH_TAC `(m:A) = (e:real^3->A) ym` THEN
      MESON_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* S' is a section of e *)
  USE_THEN "n4r" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[apx_ch_n4r] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z':A`; `e':real^3->A`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    USE_THEN "sin" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP APX_SECTION_DATA) THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:real^3->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `e':real^3->A`; `uu:real^3->real`; `eps:real`; `--(&3 / &4 * inv eps)`;
                 `&3 / &4 * inv eps`] APX_SECTION_LEVELS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; SUBSET; APX_SLAB_SVAL] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  ABBREV_TAC `r1 = exp(--inv eps / sqrt(&2))` THEN
  ABBREV_TAC `r2 = exp(inv eps / sqrt(&2))` THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus r1 r2 /\ &0 < r1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "r1" THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `r1:real`; `r2:real`; `uu:real^3->real`] APX_SECTION_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps)
                           (e:real^3->A)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bl = IMAGE (e:real^3->A)
                     {z | ~(z = vec 0) /\ r1 < norm z /\ norm z < uu(inv(norm z) % z)}` THEN
  ABBREV_TAC `Ab = IMAGE (e:real^3->A)
                     {z | ~(z = vec 0) /\ uu(inv(norm z) % z) < norm z /\ norm z < r2}` THEN
  STRIP_TAC THEN
  ABBREV_TAC `S2 = IMAGE (\x. (e:real^3->A)(uu x % x)) (sphere(vec 0,&1))` THEN
  (* v is off S' and lies in one of the two parts, which lies in Y *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z':A`; `e':real^3->A`; `U:A->bool`; `K:A->bool`; `Y:A->bool`]
    P2BT_CAP_SPHERE_NOT_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(v:A) IN Bl \/ v IN Ab` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:A) IN IMAGE (e:real^3->A) (annulus r1 r2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(H:A->bool) SUBSET IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:A) IN H` THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (IMAGE (e':real^3->A) (sphere(vec 0,&1))) Y`;
      `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = S2`;
      `IMAGE (e:real^3->A) (annulus r1 r2) = S2 UNION Bl UNION Ab`;
      `(v:A) IN IMAGE (e:real^3->A) (annulus r1 r2)`; `(v:A) IN Y`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!P. P = Bl \/ P = Ab ==> (v:A) IN P ==> P SUBSET Y` (LABEL_TAC "inY") THENL
   [GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BT_CONNECTED_IN_OPEN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `P = (Bl:A->bool) \/ P = Ab` THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(v:A) IN P` THEN UNDISCH_TAC `(v:A) IN Y` THEN SET_TAC[];
      UNDISCH_TAC `P = (Bl:A->bool) \/ P = Ab` THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
       [MAP_EVERY UNDISCH_TAC
         [`K DIFF (Y:A->bool) SUBSET IMAGE (e':real^3->A) (sphere(vec 0,&1))`;
          `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = S2`; `DISJOINT (S2:A->bool) Bl`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`K DIFF (Y:A->bool) SUBSET IMAGE (e':real^3->A) (sphere(vec 0,&1))`;
          `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = S2`; `DISJOINT (S2:A->bool) Ab`] THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  (* the end slabs of e lie in the two parts *)
  SUBGOAL_THEN `IMAGE (e:real^3->A) (apx_slab (--inv eps) (--(&3 / &4 * inv eps))) SUBSET Bl /\
                IMAGE (e:real^3->A) (apx_slab (&3 / &4 * inv eps) (inv eps)) SUBSET Ab`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1)
                             ==> exp(--(&3 / &4 * inv eps) / sqrt(&2)) < uu y /\
                                 uu y < exp((&3 / &4 * inv eps) / sqrt(&2))`
    (LABEL_TAC "ub") THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_sval")) (concl th) &&
        can (find_term (fun t -> t = `uu:real^3->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < (uu:real^3->real) y` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = `r1:real`)) (concl th) &&
          can (find_term (fun t -> t = `uu:real^3->real`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`uu:real^3->real`; `y:real^3`] APX_SECTION_EXP_LEVEL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN sphere(vec 0,&1)` THEN
        REWRITE_TAC[IN_SPHERE_0];
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Bl" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; apx_slab; annulus; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(z:real^3 = vec 0) /\ norm(inv(norm z) % z:real^3) = &1`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[GSYM NORM_POS_LT; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
                     REAL_LT_IMP_NZ];
        ALL_TAC] THEN
      USE_THEN "ub" (MP_TAC o SPEC `inv(norm z) % z:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Ab" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; apx_slab; annulus; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_TRANS THEN
        EXISTS_TAC `exp((&3 / &4 * inv eps) / sqrt(&2))` THEN
        ASM_REWRITE_TAC[REAL_EXP_POS_LT];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(z:real^3 = vec 0) /\ norm(inv(norm z) % z:real^3) = &1`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[GSYM NORM_POS_LT; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV;
                     REAL_LT_IMP_NZ];
        ALL_TAC] THEN
      USE_THEN "ub" (MP_TAC o SPEC `inv(norm z) % z:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "tr" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`;
     `x:A`; `e:real^3->A`; `gamma:real->A`; `s:real`; `&3 / &4 * inv eps`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tn:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `tp:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term (fun t -> t = `v:A`)) (concl th))) THENL
   [EXISTS_TAC `tn:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Bl:A->bool) SUBSET Y` MP_TAC THENL
     [USE_THEN "inY" (MP_TAC o SPEC `Bl:A->bool`) THEN REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (apx_slab (--inv eps) (--(&3 / &4 * inv eps))) SUBSET Bl` THEN
    UNDISCH_TAC `(gamma:real->A) tn IN IMAGE (e:real^3->A) (apx_slab (--inv eps) (--(&3 / &4 * inv eps)))` THEN
    SET_TAC[];
    EXISTS_TAC `tp:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Ab:A->bool) SUBSET Y` MP_TAC THENL
     [USE_THEN "inY" (MP_TAC o SPEC `Ab:A->bool`) THEN REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (apx_slab (&3 / &4 * inv eps) (inv eps)) SUBSET Ab` THEN
    UNDISCH_TAC `(gamma:real->A) tp IN IMAGE (e:real^3->A) (apx_slab (&3 / &4 * inv eps) (inv eps))` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* MT Claim 10.4(5) (P1): every point of the middle half of an eps-neck      *)
(* centred at a window point of the shortest curve is the centre of an       *)
(* NK-neck (given strong canonical neighbourhoods above lo/2).               *)
(* ========================================================================= *)

let P2BT_P1 = prove
 (`!u:A->bool.
     APX_A8_CS_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C top atlas (g:A->real^3^3) eps (NK:A->(real^3->A)->bool) gamma lo hi s e v.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              apx_shortest (top,atlas) g gamma (&0) (&1) /\
              (!t. t IN real_interval[&0,&1]
                   ==> mfd_speed atlas g gamma (&0) (&1) t =
                       mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
              &0 < mfd_scalar atlas g (gamma(&0)) /\
              &2 * mfd_scalar atlas g (gamma(&0)) < mfd_scalar atlas g (gamma(&1)) /\
              &2 * C * mfd_scalar atlas g (gamma(&0)) <= lo /\
              &2 * C * hi <= mfd_scalar atlas g (gamma(&1)) /\
              (!w. w IN topspace top /\ lo / &2 <= mfd_scalar atlas g w
                   ==> (?e. NK w e) \/
                       (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y) \/
                       (?U. w IN U /\ rfs_c_component (top,atlas) g C U) \/
                       (?U. w IN U /\ rfs_round_component (top,atlas) g eps U)) /\
              &0 <= s /\ s <= &1 /\
              lo <= mfd_scalar atlas g (gamma s) /\ mfd_scalar atlas g (gamma s) <= hi /\
              rfs_neck (top,atlas) g eps (gamma s) e /\
              v IN IMAGE e (apx_slab (--inv(&2 * eps)) (inv(&2 * eps)))
              ==> ?e'. NK v e'`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ALONG_EXCLUDE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ea:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ae"))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_P1_CAP o check (fun th ->
    can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "P2B_APX_A6_CS_STATEMENT")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ep:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1c"))) THEN
  X_CHOOSE_THEN `er:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_R) THEN
  EXISTS_TAC `min (min ea ep) (min er (&1 / &1024))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= ea /\ eps <= ep /\ eps <= er /\ eps <= &1 / &1024` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) s`; `e:real^3->A`] P2BT_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&2 * eps) < inv eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; SUBSET; APX_SLAB_SVAL] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the curvature of the neck points *)
  SUBGOAL_THEN
   `!p. p IN IMAGE (e:real^3->A) (rfs_neck_dom eps)
        ==> mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s) / &2 <= mfd_scalar atlas g p /\
            mfd_scalar atlas g p <= &3 / &2 * mfd_scalar atlas g (gamma s)`
  (LABEL_TAC "rr") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "nr" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`top:A topology`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `(v:A) IN IMAGE (e:real^3->A) (apx_slab (--inv(&2 * eps)) (inv(&2 * eps)))` THEN
    UNDISCH_TAC `apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "rr" (MP_TAC o SPEC `v:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the ends of gamma lie outside the neck *)
  SUBGOAL_THEN `~((gamma:real->A) (&0) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) /\
                ~((gamma:real->A) (&1) IN IMAGE (e:real^3->A) (rfs_neck_dom eps))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "rr" (MP_TAC o SPEC `(gamma:real->A) (&0)`);
      USE_THEN "rr" (MP_TAC o SPEC `(gamma:real->A) (&1)`)] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    (SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) (&0)) <
                   C * mfd_scalar atlas g (gamma(&0)) /\ hi <= C * hi`
     MP_TAC THENL
      [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THENL
        [MATCH_MP_TAC REAL_LT_RMUL; MATCH_MP_TAC REAL_LE_RMUL] THEN ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the exclusions for v *)
  SUBGOAL_THEN
   `C * mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A)(&0)) <= mfd_scalar atlas g v /\
    C * mfd_scalar atlas g v <= mfd_scalar atlas g (gamma(&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * &3 / &2 * hi` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "ae" (MP_TAC o SPECL
    [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `eps:real`; `gamma:real->A`; `v:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "xcap") (LABEL_TAC "xcomp")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:A` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_round_component"))
        (concl th))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
      UNDISCH_TAC `(v:A) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `e':real^3->A` THEN ASM_REWRITE_TAC[];
    (* a cap core containing v meets gamma *)
    USE_THEN "p1c" (MP_TAC o SPECL
      [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `eps:real`; `(gamma:real->A) s`; `e:real^3->A`; `gamma:real->A`; `s:real`;
       `U:A->bool`; `Y:A->bool`; `v:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((gamma:real->A) s) e` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "xcap" (MP_TAC o SPECL [`U:A->bool`; `Y:A->bool`; `t0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    (* components: the neck lies in the component, hence gamma s *)
    ALL_TAC;
    ALL_TAC] THEN
  (SUBGOAL_THEN `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET U` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `IMAGE (e:real^3->A) (rfs_neck_dom eps)`; `U:A->bool`]
      CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t &&
            (fst(dest_const t) = "rfs_c_component" ||
             fst(dest_const t) = "rfs_round_component"))) (concl th))) THEN
        SIMP_TAC[rfs_c_component; rfs_round_component];
        MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[rfs_neck_dom; APX_CONNECTED_ANNULUS3];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[]];
    ALL_TAC]) THEN
  USE_THEN "xcomp" (MP_TAC o SPECL [`U:A->bool`; `s:real`]) THEN
  (ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
    UNDISCH_TAC `sphere(vec 0,&1) SUBSET rfs_neck_dom eps` THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((gamma:real->A) s) e` THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[]]));;

