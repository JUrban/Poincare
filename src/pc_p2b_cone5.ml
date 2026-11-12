(* ========================================================================= *)
(* Unit pc_p2b_cone5: P2BK_CONE_REGULAR at every carrier type (in particular *)
(* (:real^3)).  On an open set O of a Riemannian manifold, a positive        *)
(* 1-Lipschitz rho with ray points and the exact angle triangle inequality   *)
(* is smooth and rho^2/2 has the Hessian g in every chart.  Proof: a planar  *)
(* Stewart lemma makes rho^2/2 quadratic along radial geodesics of uniformly *)
(* normal balls (MFD_UNIFORMLY_NORMAL); for a ray point z of x the triangle  *)
(* inequality gives equal comparison angles cang(x,y) = cang(z,y), so the    *)
(* linear part of rho^2/2 at x is the derivative of the smooth d(z,.)^2,     *)
(* hence linear; then rho^2/2 = f(x) + <w,b> + |w|^2/2 in the exp chart,     *)
(* which gives smoothness and the Hessian along geodesics.                   *)
(* ========================================================================= *)

needs "src/pc_p2b_conestmts.ml";;
needs "src/pc_geo_hr.ml";;
needs "src/pc_cmp_affine.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The planar Stewart lemma.  If the comparison angles of (p,m) and (m,q)    *)
(* add up to at least that of (p,q), and d(p,q) = d(p,m) + d(m,q), then the  *)
(* planar comparison point of m is on the segment, so (d1 + d2) rho(m)^2 =   *)
(* d2 rho(p)^2 + d1 rho(q)^2 - d1 d2 (d1 + d2).                              *)
(* ========================================================================= *)

let P2BK_STEWART = prove
 (`!A M C d1 d2.
     &0 < A /\ &0 < M /\ &0 < C /\ &0 <= d1 /\ &0 <= d2 /\ &0 < d1 + d2 /\
     abs((A pow 2 + M pow 2 - d1 pow 2) / (&2 * A * M)) <= &1 /\
     abs((M pow 2 + C pow 2 - d2 pow 2) / (&2 * M * C)) <= &1 /\
     abs((A pow 2 + C pow 2 - (d1 + d2) pow 2) / (&2 * A * C)) <= &1 /\
     p2bk_cang A C (d1 + d2) <= p2bk_cang A M d1 + p2bk_cang M C d2 /\
     p2bk_cang A M d1 + p2bk_cang M C d2 <= pi
     ==> (d1 + d2) * M pow 2 = d2 * A pow 2 + d1 * C pow 2 - d1 * d2 * (d1 + d2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_cang] THEN STRIP_TAC THEN
  ABBREV_TAC `al = acs((A pow 2 + M pow 2 - d1 pow 2) / (&2 * A * M))` THEN
  ABBREV_TAC `be = acs((M pow 2 + C pow 2 - d2 pow 2) / (&2 * M * C))` THEN
  ABBREV_TAC `ga = acs((A pow 2 + C pow 2 - (d1 + d2) pow 2) / (&2 * A * C))` THEN
  SUBGOAL_THEN
   `cos al = (A pow 2 + M pow 2 - d1 pow 2) / (&2 * A * M) /\
    cos be = (M pow 2 + C pow 2 - d2 pow 2) / (&2 * M * C) /\
    cos ga = (A pow 2 + C pow 2 - (d1 + d2) pow 2) / (&2 * A * C)`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["al"; "be"; "ga"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC COS_ACS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= al /\ &0 <= be /\ &0 <= ga` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["al"; "be"; "ga"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= pi ==> &0 <= x`) THEN
    MATCH_MP_TAC ACS_BOUNDS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * A * M /\ &0 < &2 * M * C /\ &0 < &2 * A * C` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * A * M * cos al = A pow 2 + M pow 2 - d1 pow 2 /\
                &2 * M * C * cos be = M pow 2 + C pow 2 - d2 pow 2 /\
                &2 * A * C * cos ga = A pow 2 + C pow 2 - (d1 + d2) pow 2`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < M` THEN UNDISCH_TAC `&0 < C` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `cos(al + be) <= cos ga` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `P = vector[A; &0]:real^2` THEN
  ABBREV_TAC `Mv = vector[M * cos al; M * sin al]:real^2` THEN
  ABBREV_TAC `Q = vector[C * cos(al + be); C * sin(al + be)]:real^2` THEN
  SUBGOAL_THEN `norm(P - Mv:real^2) = d1 /\ norm(Mv - Q:real^2) = d2 /\
                norm(P:real^2) = A /\ norm(Mv:real^2) = M /\ norm(Q:real^2) = C`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_EQ_SQUARE] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MAP_EVERY EXPAND_TAC ["P"; "Mv"; "Q"] THEN
    REWRITE_TAC[DOT_2; VECTOR_2; VECTOR_SUB_COMPONENT; COS_ADD; SIN_ADD] THEN
    MP_TAC(SPEC `al:real` SIN_CIRCLE) THEN MP_TAC(SPEC `be:real` SIN_CIRCLE) THEN
    UNDISCH_TAC `&2 * A * M * cos al = A pow 2 + M pow 2 - d1 pow 2` THEN
    UNDISCH_TAC `&2 * M * C * cos be = M pow 2 + C pow 2 - d2 pow 2` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(P - Q:real^2) pow 2 = A pow 2 + C pow 2 - &2 * A * C * cos(al + be)`
    ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2] THEN MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN
    REWRITE_TAC[DOT_2; VECTOR_2; VECTOR_SUB_COMPONENT] THEN
    MP_TAC(SPEC `al + be:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(P - Q:real^2) = d1 + d2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y /\ y <= x ==> x = y`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `norm(P - Mv:real^2) = d1` THEN UNDISCH_TAC `norm(Mv - Q:real^2) = d2` THEN
      MP_TAC(ISPECL [`P - Mv:real^2`; `Mv - Q:real^2`] NORM_TRIANGLE) THEN
      REWRITE_TAC[VECTOR_ARITH `(P - Mv) + (Mv - Q) = P - Q:real^2`] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= A * C * (cos ga - cos(al + be))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < A` THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `cos(al + be) <= cos ga` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `&2 * A * C * cos ga = A pow 2 + C pow 2 - (d1 + d2) pow 2` THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* equality in the triangle inequality puts Mv on the segment *)
  MP_TAC(ISPECL [`P - Mv:real^2`; `Mv - Q:real^2`] NORM_TRIANGLE_EQ) THEN
  REWRITE_TAC[VECTOR_ARITH `(P - Mv) + (Mv - Q) = P - Q:real^2`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(d1 + d2) % Mv = d2 % P + d1 % (Q:real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `d1 % (Mv - Q) = d2 % (P - Mv:real^2)` THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((d1 + d2) % Mv:real^2) dot ((d1 + d2) % Mv) =
                (d2 % P + d1 % Q:real^2) dot (d2 % P + d1 % Q)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `(Mv:real^2) dot Mv = M pow 2 /\ (P:real^2) dot P = A pow 2 /\
                (Q:real^2) dot Q = C pow 2 /\
                (P:real^2) dot Q = (A pow 2 + C pow 2 - (d1 + d2) pow 2) / &2 /\
                (Q:real^2) dot P = (A pow 2 + C pow 2 - (d1 + d2) pow 2) / &2`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN
    UNDISCH_TAC `norm(P - Q:real^2) = d1 + d2` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
    REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB] THEN
    REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < d1 + d2` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* Radial geodesics in injectivity balls are minimizing.                     *)
(* ========================================================================= *)

let P2BK_GEO_SEG_LE = prove
 (`!top atlas (g:B->real^3^3) x w a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ real_interval[a,b] SUBSET mfd_geo_maxint (top,atlas) g x w /\ a <= b
     ==> mfd_geo (top,atlas) g x w a IN topspace top /\
         mfd_geo (top,atlas) g x w b IN topspace top /\
         mfd_joinable (top,atlas) (mfd_geo (top,atlas) g x w a) (mfd_geo (top,atlas) g x w b) /\
         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x w a) (mfd_geo (top,atlas) g x w b)
         <= (b - a) * mfd_tnorm g x w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x w`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x w`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) x w /\
                b IN mfd_geo_maxint (top,atlas) g x w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `real_interval[a,b]`)) (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN UNDISCH_TAC `a <= b:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm g (mfd_geo (top,atlas) (g:B->real^3^3) x w a)
                  (mfd_vel atlas (mfd_geo (top,atlas) g x w) a) = mfd_tnorm g x w`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `mfd_geo (top,atlas) (g:B->real^3^3) x w`;
                   `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x w`; `a:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x w`; `a:real`; `b:real`]
    MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x w`; `a:real`; `b:real`]
    MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN
  ASM_REWRITE_TAC[]);;

let P2BK_INJ_DIST = prove
 (`!top atlas (g:B->real^3^3) x r w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ mfd_inj_ball (top,atlas) g x r /\ mfd_tnorm g x w < r
     ==> w IN mfd_exp_dom (top,atlas) g x /\
         mfd_joinable (top,atlas) x (mfd_exp (top,atlas) g x w) /\
         mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x w) = mfd_tnorm g x w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN mfd_exp_dom (top,atlas) (g:B->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:B->real^3^3) x r` THEN
    REWRITE_TAC[mfd_inj_ball; SUBSET; mfd_tball; IN_ELIM_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`; `&0`; `&1`] P2BK_GEO_SEG_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN
    UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:B->real^3^3) x w)` THEN
    UNDISCH_TAC `(w:real^3) IN mfd_exp_dom (top,atlas) (g:B->real^3^3) x` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM; is_realinterval; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[GSYM mfd_exp; REAL_SUB_RZERO; REAL_MUL_LID] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `r:real`; `mfd_exp (top,atlas) (g:B->real^3^3) x w`] MFD_LOCAL_HOPF_RINOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_inj_ball (top,atlas) (g:B->real^3^3) x r` THEN SIMP_TAC[mfd_inj_ball];
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x (mfd_exp (top,atlas) g x w) <=
                   mfd_tnorm g x w` THEN
      UNDISCH_TAC `mfd_tnorm (g:B->real^3^3) x w < r` THEN REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `v:real^3 = w` (fun th -> ASM_MESON_TAC[th]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `r:real`; `v:real^3`; `w:real^3`] CMPS_INJ_BALL_INJ) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x (mfd_exp (top,atlas) g x w) <=
               mfd_tnorm g x w` THEN
  UNDISCH_TAC `mfd_tnorm (g:B->real^3^3) x w < r` THEN REAL_ARITH_TAC);;

let P2BK_INJ_SEG = prove
 (`!top atlas (g:B->real^3^3) x r w s t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ mfd_inj_ball (top,atlas) g x r /\ mfd_tnorm g x w < r /\
     &0 <= s /\ s <= t /\ t <= &1
     ==> mfd_geo (top,atlas) g x w t = mfd_exp (top,atlas) g x (t % w) /\
         mfd_geo (top,atlas) g x w t IN topspace top /\
         mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x w t) = t * mfd_tnorm g x w /\
         mfd_joinable (top,atlas) (mfd_geo (top,atlas) g x w s) (mfd_geo (top,atlas) g x w t) /\
         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x w s) (mfd_geo (top,atlas) g x w t) =
         (t - s) * mfd_tnorm g x w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `r:real`; `w:real^3`] P2BK_INJ_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_interval[&0,&1] SUBSET mfd_geo_maxint (top,atlas) (g:B->real^3^3) x w`
    ASSUME_TAC THENL
   [UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:B->real^3^3) x w)` THEN
    UNDISCH_TAC `(w:real^3) IN mfd_exp_dom (top,atlas) (g:B->real^3^3) x` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM; is_realinterval; SUBSET; IN_REAL_INTERVAL] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a. &0 <= a /\ a <= &1
        ==> mfd_geo (top,atlas) (g:B->real^3^3) x w a = mfd_exp (top,atlas) g x (a % w) /\
            mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x w a) = a * mfd_tnorm g x w`
    (LABEL_TAC "rad") THENL
   [X_GEN_TAC `a:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) x w a = mfd_exp (top,atlas) g x (a % w)`
      ASSUME_TAC THENL
     [REWRITE_TAC[mfd_exp] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `x:B`; `w:real^3`; `a:real`] MFD_GEO_RESCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT2) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term ((=) `real_interval[&0,&1]`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL];
        SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `r:real`; `a % w:real^3`] P2BK_INJ_DIST) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs a * mfd_tnorm (g:B->real^3^3) x w = a * mfd_tnorm g x w`
      (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`]; ALL_TAC] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `mfd_tnorm (g:B->real^3^3) x w` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s <= t:real` THEN UNDISCH_TAC `t <= &1` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s <= t:real` THEN UNDISCH_TAC `t <= &1` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`; `s:real`; `t:real`] P2BK_GEO_SEG_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`; `&0`; `s:real`] P2BK_GEO_SEG_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    UNDISCH_TAC `s <= t:real` THEN UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `mfd_geo (top,atlas) (g:B->real^3^3) x w (&0) = x` (fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `mfd_geo (top,atlas) (g:B->real^3^3) x w s`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x w t`] MFD_DIST_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) (mfd_geo (top,atlas) g x w s)
                 (mfd_geo (top,atlas) g x w t) <= (t - s) * mfd_tnorm g x w` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x (mfd_geo (top,atlas) g x w t) =
               t * mfd_tnorm g x w` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x (mfd_geo (top,atlas) g x w s) =
               s * mfd_tnorm g x w` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The hypotheses of CONE_REGULAR as a predicate, comparison cosines of      *)
(* nearby points, Stewart for points of O, and the local setup.              *)
(* ========================================================================= *)

let p2bk_crhyp = new_definition
 `p2bk_crhyp (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
             (O:B->bool) (rho:B->real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ open_in top O /\
    (!x. x IN O ==> &0 < rho x) /\
    (!x y. x IN O /\ y IN O
           ==> mfd_joinable (top,atlas) x y /\
               abs(rho x - rho y) <= mfd_dist (top,atlas) g x y) /\
    (!x. x IN O
         ==> ?r. &0 < r /\
                 !t. &0 < t /\ t < r
                     ==> ?y. y IN O /\ mfd_dist (top,atlas) g x y = t /\
                             rho y = rho x - t) /\
    (!x y z. x IN O /\ y IN O /\ z IN O
             ==> p2bk_cang (rho x) (rho z) (mfd_dist (top,atlas) g x z) <=
                 p2bk_cang (rho x) (rho y) (mfd_dist (top,atlas) g x y) +
                 p2bk_cang (rho y) (rho z) (mfd_dist (top,atlas) g y z))`;;

let P2BK_CR_COS = prove
 (`!top atlas (g:B->real^3^3) O rho x y.
     p2bk_crhyp (top,atlas) g O rho /\ x IN O /\ y IN O /\
     mfd_dist (top,atlas) g x y <= rho y
     ==> &0 <= mfd_dist (top,atlas) g x y /\
         &0 <= (rho x pow 2 + rho y pow 2 - mfd_dist (top,atlas) g x y pow 2) /
               (&2 * rho x * rho y) /\
         (rho x pow 2 + rho y pow 2 - mfd_dist (top,atlas) g x y pow 2) /
         (&2 * rho x * rho y) <= &1 /\
         cos(p2bk_cang (rho x) (rho y) (mfd_dist (top,atlas) g x y)) =
         (rho x pow 2 + rho y pow 2 - mfd_dist (top,atlas) g x y pow 2) /
         (&2 * rho x * rho y) /\
         &0 <= p2bk_cang (rho x) (rho y) (mfd_dist (top,atlas) g x y) /\
         p2bk_cang (rho x) (rho y) (mfd_dist (top,atlas) g x y) <= pi / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_crhyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (rho:B->real) x /\ &0 < rho y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((rho:B->real) x - rho y) <= mfd_dist (top,atlas) (g:B->real^3^3) x y`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A = (rho:B->real) x` THEN ABBREV_TAC `C = (rho:B->real) y` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:B->real^3^3) x y` THEN
  SUBGOAL_THEN `&0 < &2 * A * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(A - C) <= D` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(A - C) pow 2 <= D pow 2 /\ D pow 2 <= C pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    UNDISCH_TAC `abs(A - C) <= D` THEN UNDISCH_TAC `D <= C` THEN
    UNDISCH_TAC `&0 <= D` THEN UNDISCH_TAC `&0 < C` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (A pow 2 + C pow 2 - D pow 2) / (&2 * A * C) /\
                (A pow 2 + C pow 2 - D pow 2) / (&2 * A * C) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MP_TAC(SPEC `A:real` REAL_LE_POW_2) THEN
        UNDISCH_TAC `D pow 2 <= C pow 2` THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      UNDISCH_TAC `(A - C) pow 2 <= D pow 2` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2bk_cang] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COS_ACS THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= pi ==> &0 <= x`) THEN
    MATCH_MP_TAC ACS_BOUNDS THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM ACS_0] THEN
    MATCH_MP_TAC(MESON[ACS_MONO_LE_EQ]
      `!x y. abs x <= &1 /\ abs y <= &1 /\ y <= x ==> acs x <= acs y`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Stewart for three points of O on a minimizing configuration. *)

let P2BK_CR_STEWART_SEG = prove
 (`!top atlas (g:B->real^3^3) O rho a m b.
     p2bk_crhyp (top,atlas) g O rho /\ a IN O /\ m IN O /\ b IN O /\
     mfd_dist (top,atlas) g a b = mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b /\
     &0 < mfd_dist (top,atlas) g a b /\
     mfd_dist (top,atlas) g a m <= rho m /\ mfd_dist (top,atlas) g m b <= rho b /\
     mfd_dist (top,atlas) g a b <= rho b
     ==> mfd_dist (top,atlas) g a b * rho m pow 2 =
         mfd_dist (top,atlas) g m b * rho a pow 2 + mfd_dist (top,atlas) g a m * rho b pow 2 -
         mfd_dist (top,atlas) g a m * mfd_dist (top,atlas) g m b * mfd_dist (top,atlas) g a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `a:B`; `m:B`] P2BK_CR_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `m:B`; `b:B`] P2BK_CR_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `a:B`; `b:B`] P2BK_CR_COS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `&0 < (rho:B->real) a /\ &0 < rho m /\ &0 < rho b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bk_cang ((rho:B->real) a) (rho b) (mfd_dist (top,atlas) (g:B->real^3^3) a b) <=
    p2bk_cang (rho a) (rho m) (mfd_dist (top,atlas) g a m) +
    p2bk_cang (rho m) (rho b) (mfd_dist (top,atlas) g m b)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "p2bk_cang" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) a b =
               mfd_dist (top,atlas) g a m + mfd_dist (top,atlas) g m b` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  MATCH_MP_TAC P2BK_STEWART THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;

(* The local setup at x0: a uniformly normal open set W of points near x0,  *)
(* inside a ball of radius 4e in O, with e small against r and rho(x0).     *)

let P2BK_CR_SETUP = prove
 (`!top atlas (g:B->real^3^3) O rho x0.
     p2bk_crhyp (top,atlas) g O rho /\ x0 IN O
     ==> ?W r e. open_in top W /\ x0 IN W /\ &0 < r /\ &0 < e /\ &2 * e <= r /\
                 &10 * e <= rho x0 /\
                 W SUBSET mfd_ball (top,atlas) g x0 e /\
                 mfd_ball (top,atlas) g x0 (&4 * e) SUBSET O /\
                 !y. y IN W
                     ==> mfd_inj_ball (top,atlas) g y r /\
                         W SUBSET IMAGE (mfd_exp (top,atlas) g y) (mfd_tball g y r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `(x0:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x0:B`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:B->bool` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `x0:B`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rO:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (rho:B->real) x0` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `e = min (r / &2) (min (rO / &4) ((rho:B->real) x0 / &10))` THEN
  SUBGOAL_THEN `&0 < e /\ &2 * e <= r /\ &4 * e <= rO /\ &10 * e <= (rho:B->real) x0`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < rO` THEN
    UNDISCH_TAC `&0 < (rho:B->real) x0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W0 INTER mfd_ball (top,atlas) (g:B->real^3^3) x0 e`; `r:real`; `e:real`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_BALL_OPEN THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x0:B`] MFD_DIST_REFL) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_ball (top,atlas) (g:B->real^3^3) x0 rO` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
    UNDISCH_TAC `&4 * e <= rO` THEN MESON_TAC[REAL_LTE_TRANS];
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W0:B->bool` THEN
    ASM_SIMP_TAC[INTER_SUBSET]]);;

(* ========================================================================= *)
(* Unit radial geodesics in injectivity balls, and rho^2 quadratic along     *)
(* them (Stewart).                                                           *)
(* ========================================================================= *)

let P2BK_RAY_GEO_DIST = prove
 (`!top atlas (g:B->real^3^3) p r u a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p IN topspace top /\ mfd_inj_ball (top,atlas) g p r /\ mfd_tnorm g p u = &1 /\
     &0 <= a /\ a <= b /\ b < r
     ==> b IN mfd_geo_maxint (top,atlas) g p u /\
         mfd_geo (top,atlas) g p u b IN topspace top /\
         mfd_dist (top,atlas) g p (mfd_geo (top,atlas) g p u b) = b /\
         mfd_joinable (top,atlas) (mfd_geo (top,atlas) g p u a) (mfd_geo (top,atlas) g p u b) /\
         mfd_dist (top,atlas) g (mfd_geo (top,atlas) g p u a) (mfd_geo (top,atlas) g p u b) =
         b - a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `b = &0` THENL
   [SUBGOAL_THEN `a = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&0 <= a` THEN UNDISCH_TAC `a <= b` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    ASM_SIMP_TAC[MFD_DIST_REFL; MFD_JOINABLE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [UNDISCH_TAC `~(b = &0)` THEN UNDISCH_TAC `&0 <= a` THEN UNDISCH_TAC `a <= b` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tnorm (g:B->real^3^3) p (b % u) = b` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID] THEN UNDISCH_TAC `&0 < b` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `r:real`; `b % u:real^3`] P2BK_INJ_DIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `u:real^3`; `b:real`] MFD_GEO_RESCALE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dom") (LABEL_TAC "eq")) THEN
  SUBGOAL_THEN `b IN mfd_geo_maxint (top,atlas) (g:B->real^3^3) p u` ASSUME_TAC THENL
   [UNDISCH_TAC `b % u IN mfd_exp_dom (top,atlas) (g:B->real^3^3) p` THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN USE_THEN "dom" SUBST1_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_MUL_RID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `r:real`; `b % u:real^3`; `a / b`; `&1`] P2BK_INJ_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= &1
                    ==> mfd_geo (top,atlas) (g:B->real^3^3) p (b % u) s = mfd_geo (top,atlas) g p u (b * s)`
    (LABEL_TAC "resc") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN
    UNDISCH_TAC `is_realinterval(mfd_geo_maxint (top,atlas) (g:B->real^3^3) p u)` THEN
    REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN(MATCH_MP_TAC o SPECL [`&0`; `b:real`; `b * s:real`]) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) p (b % u) (a / b) = mfd_geo (top,atlas) g p u a /\
                mfd_geo (top,atlas) g p (b % u) (&1) = mfd_geo (top,atlas) g p u b`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [USE_THEN "resc" (MP_TAC o SPEC `a / b`) THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID];
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < b` THEN
        CONV_TAC REAL_FIELD];
      USE_THEN "resc" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
      REWRITE_TAC[REAL_MUL_RID]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD);;

let p2bk_crsetup = new_definition
 `p2bk_crsetup (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
               (O:B->bool) (rho:B->real) (x0:B) (W:B->bool) (r:real) (e:real) <=>
    p2bk_crhyp (top,atlas) g O rho /\ x0 IN O /\
    open_in top W /\ x0 IN W /\ &0 < r /\ &0 < e /\ &2 * e <= r /\ &10 * e <= rho x0 /\
    W SUBSET mfd_ball (top,atlas) g x0 e /\ mfd_ball (top,atlas) g x0 (&4 * e) SUBSET O /\
    !y. y IN W
        ==> mfd_inj_ball (top,atlas) g y r /\
            W SUBSET IMAGE (mfd_exp (top,atlas) g y) (mfd_tball g y r)`;;

let P2BK_CRSETUP_EXISTS = prove
 (`!top atlas (g:B->real^3^3) O rho x0.
     p2bk_crhyp (top,atlas) g O rho /\ x0 IN O
     ==> ?W r e. p2bk_crsetup (top,atlas) g O rho x0 W r e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bk_crsetup] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BK_CR_SETUP THEN ASM_REWRITE_TAC[]);;

(* Points near x0 are in O with rho >= 6e. *)

let P2BK_CRSETUP_NEAR = prove
 (`!top atlas (g:B->real^3^3) O rho x0 W r e p q.
     p2bk_crsetup (top,atlas) g O rho x0 W r e /\ p IN W /\
     mfd_joinable (top,atlas) p q /\ mfd_dist (top,atlas) g p q < &3 * e
     ==> p IN topspace top /\ q IN O /\ q IN topspace top /\
         mfd_dist (top,atlas) g x0 p < e /\ mfd_dist (top,atlas) g x0 q < &4 * e /\
         &6 * e <= rho q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_crsetup; p2bk_crhyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas) (x0:B) p /\ mfd_dist (top,atlas) (g:B->real^3^3) x0 p < e`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(W:B->bool) SUBSET mfd_ball (top,atlas) (g:B->real^3^3) x0 e` THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (x0:B) q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:B` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) x0 q < &4 * e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x0:B`; `p:B`; `q:B`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x0 p < e` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) p q < &3 * e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:B) IN O` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_ball (top,atlas) (g:B->real^3^3) x0 (&4 * e) SUBSET O` THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE o
    check (fun th -> concl th = `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) p q`)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs((rho:B->real) x0 - rho q) <= mfd_dist (top,atlas) (g:B->real^3^3) x0 q`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&10 * e <= (rho:B->real) x0` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x0 q < &4 * e` THEN REAL_ARITH_TAC);;

(* Stewart along a unit radial geodesic from a point of W. *)

let P2BK_CR_RAD3 = prove
 (`!top atlas (g:B->real^3^3) O rho x0 W r e p u s1 s2.
     p2bk_crsetup (top,atlas) g O rho x0 W r e /\ p IN W /\ mfd_tnorm g p u = &1 /\
     &0 <= s1 /\ s1 < s2 /\ s2 < e
     ==> s2 * rho(mfd_geo (top,atlas) g p u s1) pow 2 =
         (s2 - s1) * rho p pow 2 + s1 * rho(mfd_geo (top,atlas) g p u s2) pow 2 -
         s1 * (s2 - s1) * s2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crsetup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `(p:B) IN topspace top /\ mfd_inj_ball (top,atlas) (g:B->real^3^3) p r`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `r:real`; `u:real^3`; `&0`; `s1:real`] P2BK_RAY_GEO_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `&0 <= s1` THEN UNDISCH_TAC `s1 < s2` THEN
    UNDISCH_TAC `s2 < e` THEN UNDISCH_TAC `&2 * e <= r` THEN UNDISCH_TAC `&0 < e` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `r:real`; `u:real^3`; `s1:real`; `s2:real`] P2BK_RAY_GEO_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= s1` THEN UNDISCH_TAC `s1 < s2` THEN
    UNDISCH_TAC `s2 < e` THEN UNDISCH_TAC `&2 * e <= r` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_THEN `mfd_geo (top,atlas) (g:B->real^3^3) p u (&0) = p`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x0:B`; `W:B->bool`; `r:real`; `e:real`; `p:B`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) p u s1`] P2BK_CRSETUP_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `s1 < s2` THEN UNDISCH_TAC `s2 < e` THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x0:B`; `W:B->bool`; `r:real`; `e:real`; `p:B`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) p u s2`] P2BK_CRSETUP_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
      EXISTS_TAC `mfd_geo (top,atlas) (g:B->real^3^3) p u s1` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `s2 < e` THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC];
    STRIP_TAC] THEN
  SUBGOAL_THEN `(p:B) IN O` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `O:B->bool`; `rho:B->real`; `x0:B`; `W:B->bool`; `r:real`; `e:real`; `p:B`;
                   `p:B`] P2BK_CRSETUP_NEAR) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
    ANTS_TAC THENL [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s1 = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `p:B`; `mfd_geo (top,atlas) (g:B->real^3^3) p u s1`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) p u s2`] P2BK_CR_STEWART_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&6 * e <= (rho:B->real) (mfd_geo (top,atlas) (g:B->real^3^3) p u s1)` THEN
    UNDISCH_TAC `&6 * e <= (rho:B->real) (mfd_geo (top,atlas) (g:B->real^3^3) p u s2)` THEN
    UNDISCH_TAC `&0 <= s1` THEN UNDISCH_TAC `~(s1 = &0)` THEN UNDISCH_TAC `s1 < s2` THEN
    UNDISCH_TAC `s2 < e` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* rho^2 is quadratic with leading coefficient 1 along unit radial          *)
(* geodesics from points of W, on [0,e).                                     *)

let P2BK_CR_RADIAL = prove
 (`!top atlas (g:B->real^3^3) O rho x0 W r e p u.
     p2bk_crsetup (top,atlas) g O rho x0 W r e /\ p IN W /\ mfd_tnorm g p u = &1
     ==> ?c. !s. &0 <= s /\ s < e
                 ==> rho(mfd_geo (top,atlas) g p u s) pow 2 =
                     rho p pow 2 + &2 * c * s + s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crsetup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `(p:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t0 = e / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `((rho:B->real)(mfd_geo (top,atlas) (g:B->real^3^3) p u t0) pow 2 -
               rho p pow 2) / (&2 * t0) - t0 / &2` THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `s <= t0 \/ t0 < s`) THENL
   [ASM_CASES_TAC `s:real = t0` THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < t0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `O:B->bool`; `rho:B->real`; `x0:B`; `W:B->bool`; `r:real`; `e:real`;
                   `p:B`; `u:real^3`; `s:real`; `t0:real`] P2BK_CR_RAD3) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `s <= t0` THEN UNDISCH_TAC `~(s:real = t0)` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < t0` THEN CONV_TAC REAL_FIELD];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `O:B->bool`; `rho:B->real`; `x0:B`; `W:B->bool`; `r:real`; `e:real`;
                   `p:B`; `u:real^3`; `t0:real`; `s:real`] P2BK_CR_RAD3) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < t0` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < t0` THEN UNDISCH_TAC `t0 < s` THEN CONV_TAC REAL_FIELD]]);;

(* ========================================================================= *)
(* Equal comparison angles along a ray.  If z is a ray point of p            *)
(* (rho z = rho p - d(p,z)), the exact triangle inequality gives             *)
(* cang(p,y) = cang(z,y), hence near p                                       *)
(* rho(y)^2 = rho p rho z + (rho p / tau) d(z,y)^2 - (rho z / tau) d(p,y)^2. *)
(* ========================================================================= *)

let P2BK_CR_EQANGLE = prove
 (`!top atlas (g:B->real^3^3) O rho p z y.
     p2bk_crhyp (top,atlas) g O rho /\ p IN O /\ z IN O /\ y IN O /\
     &0 < mfd_dist (top,atlas) g p z /\
     rho z = rho p - mfd_dist (top,atlas) g p z /\
     mfd_dist (top,atlas) g p y <= rho y /\ mfd_dist (top,atlas) g z y <= rho y
     ==> rho y pow 2 =
         rho p * rho z +
         rho p / mfd_dist (top,atlas) g p z * mfd_dist (top,atlas) g z y pow 2 -
         rho z / mfd_dist (top,atlas) g p z * mfd_dist (top,atlas) g p y pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `&0 < (rho:B->real) p /\ &0 < rho z /\ &0 < rho y` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) z p = mfd_dist (top,atlas) g p z`
    ASSUME_TAC THENL [ASM_MESON_TAC[MFD_DIST_SYM]; ALL_TAC] THEN
  (* the comparison angle of p and z is 0 *)
  SUBGOAL_THEN `p2bk_cang ((rho:B->real) p) (rho z) (mfd_dist (top,atlas) (g:B->real^3^3) p z) = &0 /\
                p2bk_cang (rho z) (rho p) (mfd_dist (top,atlas) g z p) = &0`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2bk_cang] THEN
    ONCE_REWRITE_TAC[ASSUME `mfd_dist (top,atlas) (g:B->real^3^3) z p = mfd_dist (top,atlas) g p z`] THEN
    SUBGOAL_THEN `((rho:B->real) p pow 2 + rho z pow 2 -
                   mfd_dist (top,atlas) (g:B->real^3^3) p z pow 2) / (&2 * rho p * rho z) = &1 /\
                  (rho z pow 2 + rho p pow 2 - mfd_dist (top,atlas) g p z pow 2) /
                  (&2 * rho z * rho p) = &1`
      (fun th -> REWRITE_TAC[th; ACS_1]) THEN
    UNDISCH_TAC `(rho:B->real) z = rho p - mfd_dist (top,atlas) (g:B->real^3^3) p z` THEN
    UNDISCH_TAC `&0 < (rho:B->real) p` THEN UNDISCH_TAC `&0 < (rho:B->real) z` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* equal comparison angles by the exact triangle inequality *)
  SUBGOAL_THEN
   `p2bk_cang ((rho:B->real) p) (rho y) (mfd_dist (top,atlas) (g:B->real^3^3) p y) <=
    p2bk_cang (rho p) (rho z) (mfd_dist (top,atlas) g p z) +
    p2bk_cang (rho z) (rho y) (mfd_dist (top,atlas) g z y) /\
    p2bk_cang (rho z) (rho y) (mfd_dist (top,atlas) g z y) <=
    p2bk_cang (rho z) (rho p) (mfd_dist (top,atlas) g z p) +
    p2bk_cang (rho p) (rho y) (mfd_dist (top,atlas) g p y)`
    MP_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "p2bk_cang" with Failure _ -> false))
          (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `p2bk_cang ((rho:B->real) p) (rho z)
                         (mfd_dist (top,atlas) (g:B->real^3^3) p z) = &0`;
              ASSUME `p2bk_cang ((rho:B->real) z) (rho p)
                         (mfd_dist (top,atlas) (g:B->real^3^3) z p) = &0`; REAL_ADD_LID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `p2bk_cang ((rho:B->real) p) (rho y) (mfd_dist (top,atlas) (g:B->real^3^3) p y) =
    p2bk_cang (rho z) (rho y) (mfd_dist (top,atlas) g z y)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_conj(concl th))) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* hence equal cosines *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `p:B`; `y:B`] P2BK_CR_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `z:B`; `y:B`] P2BK_CR_COS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = (rho:B->real) p` THEN ABBREV_TAC `C = (rho:B->real) z` THEN
  ABBREV_TAC `Y = (rho:B->real) y` THEN
  ABBREV_TAC `t = mfd_dist (top,atlas) (g:B->real^3^3) p z` THEN
  ABBREV_TAC `d1 = mfd_dist (top,atlas) (g:B->real^3^3) p y` THEN
  ABBREV_TAC `d2 = mfd_dist (top,atlas) (g:B->real^3^3) z y` THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    can (find_term ((=) `d1:real`)) (concl th) && can (find_term ((=) `d2:real`)) (concl th))) THEN
  UNDISCH_TAC `C = A - t` THEN
  UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < C` THEN UNDISCH_TAC `&0 < Y` THEN
  UNDISCH_TAC `&0 < t` THEN
  CONV_TAC REAL_FIELD);;

(* The squared distance from z is smooth on the image of an injectivity     *)
(* ball of z.                                                                *)

let P2BK_SQDIST_SMOOTH = prove
 (`!top atlas (g:B->real^3^3) z r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     z IN topspace top /\ mfd_inj_ball (top,atlas) g z r
     ==> open_in top (IMAGE (mfd_exp (top,atlas) g z) (mfd_tball g z r)) /\
         (!y. y IN IMAGE (mfd_exp (top,atlas) g z) (mfd_tball g z r)
              ==> mfd_joinable (top,atlas) z y /\ mfd_dist (top,atlas) g z y < r) /\
         mfd_smooth_on atlas (IMAGE (mfd_exp (top,atlas) g z) (mfd_tball g z r))
                       (\y. lift(mfd_dist (top,atlas) g z y pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_inj_ball]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `ei:B->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `U = IMAGE (mfd_exp (top,atlas) (g:B->real^3^3) z) (mfd_tball g z r)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `z:B`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> (ei:B->real^3) y IN mfd_tball (g:B->real^3^3) z r /\
            mfd_joinable (top,atlas) z y /\
            mfd_dist (top,atlas) g z y = mfd_tnorm g z (ei y) /\
            mfd_dist (top,atlas) g z y < r`
    (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ei:B->real^3) y IN mfd_tball (g:B->real^3^3) z r` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (ei:B->real^3) U = mfd_tball (g:B->real^3^3) z r` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `z:B`; `r:real`; `(ei:B->real^3) y`] P2BK_INJ_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(ei:B->real^3) y IN mfd_tball (g:B->real^3^3) z r` THEN
      REWRITE_TAC[mfd_tball; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_exp (top,atlas) (g:B->real^3^3) z ((ei:B->real^3) y) = y` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(ei:B->real^3) y IN mfd_tball (g:B->real^3^3) z r` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "pt" (MP_TAC o SPEC `y:B`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_on] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER U))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER U))
                  ((ei:B->real^3) o chart_inv c)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo euclidean (open_set_atlas (:real^3)) (mfd_tball (g:B->real^3^3) z r)
                   top atlas U (mfd_exp (top,atlas) g z) (ei:B->real^3)` THEN
    REWRITE_TAC[mfd_diffeo; mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(B->bool)#(B->real^3)`; `(:real^3),(\x:real^3. x)`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; IN_UNIV] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN SET_TAC[]; REWRITE_TAC[FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\Y:real^3. lift(((ei:B->real^3) o chart_inv (c:(B->bool)#(B->real^3))) Y dot
                              (\Y. (g:B->real^3^3) z ** ((ei:B->real^3) o chart_inv c) Y) Y)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `Y:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[] THEN
    USE_THEN "pt" (MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\Y. (g:B->real^3^3) z ** ((ei:B->real^3) o chart_inv (c:(B->bool)#(B->real^3))) Y) =
                (\v. g z ** v) o (ei o chart_inv c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]]);;

(* Local smoothness of rho near each point of O. *)

let P2BK_CR_LOCAL_SMOOTH = prove
 (`!top atlas (g:B->real^3^3) O rho x0.
     p2bk_crhyp (top,atlas) g O rho /\ x0 IN O
     ==> ?N. open_in top N /\ x0 IN N /\ N SUBSET O /\
             mfd_smooth_on atlas N (\y. lift(rho y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x0:B`] P2BK_CRSETUP_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:B->bool` (X_CHOOSE_THEN `r:real` (X_CHOOSE_TAC `e:real`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crsetup]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x0:B` o el 6 o CONJUNCTS o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ray"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `(x0:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `W:B->bool`; `x0:B`] MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bW:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tau = min (rr / &2) (min (bW / &2) (e / &2))` THEN
  SUBGOAL_THEN `&0 < tau /\ tau < rr /\ tau < bW /\ tau < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN UNDISCH_TAC `&0 < rr` THEN UNDISCH_TAC `&0 < bW` THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "ray" (MP_TAC o SPEC `tau:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(W:B->bool) SUBSET O` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:B->real^3^3) x0 (&4 * e)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:B->real^3^3) x0 e` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN UNDISCH_TAC `&0 < e` THEN
    MESON_TAC[REAL_ARITH `&0 < e /\ d < e ==> d < &4 * e`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:B. y IN W ==> &0 < (rho:B->real) y` (LABEL_TAC "rpos") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    UNDISCH_TAC `!x:B. x IN O ==> &0 < (rho:B->real) x` THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(W:B->bool) SUBSET O` THEN UNDISCH_TAC `(y:B) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) (x0:B) z`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN W` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_ball (top,atlas) (g:B->real^3^3) x0 bW SUBSET W` THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  (* the squared distances from z and from x0 are smooth on W *)
  SUBGOAL_THEN
   `mfd_smooth_on atlas (W:B->bool)
      (\y. lift(mfd_dist (top,atlas) (g:B->real^3^3) z y pow 2)) /\
    mfd_smooth_on atlas W (\y. lift(mfd_dist (top,atlas) g x0 y pow 2))`
    (CONJUNCTS_THEN2 (LABEL_TAC "smz") (LABEL_TAC "smx")) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_SMOOTH_ON_SUBSET THENL
     [EXISTS_TAC `IMAGE (mfd_exp (top,atlas) (g:B->real^3^3) z) (mfd_tball g z r)`;
      EXISTS_TAC `IMAGE (mfd_exp (top,atlas) (g:B->real^3^3) x0) (mfd_tball g x0 r)`] THEN
    ASM_SIMP_TAC[P2BK_SQDIST_SMOOTH];
    ALL_TAC] THEN
  (* the identity for rho squared on W *)
  SUBGOAL_THEN
   `!y. y IN W
        ==> (rho:B->real) y pow 2 =
            rho x0 * rho z +
            rho x0 / tau * mfd_dist (top,atlas) (g:B->real^3^3) z y pow 2 -
            rho z / tau * mfd_dist (top,atlas) g x0 y pow 2`
    (LABEL_TAC "id") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas) (x0:B) y /\
                  mfd_dist (top,atlas) (g:B->real^3^3) x0 y < e` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(W:B->bool) SUBSET mfd_ball (top,atlas) (g:B->real^3^3) x0 e` THEN
      REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `O:B->bool`; `rho:B->real`; `x0:B`; `W:B->bool`; `r:real`; `e:real`;
                   `x0:B`; `y:B`] P2BK_CRSETUP_NEAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x0 y < e` THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:B->real^3^3) z y <= tau + mfd_dist (top,atlas) g x0 y`
      ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `z:B`; `x0:B`; `y:B`] MFD_DIST_TRIANGLE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `z:B`; `x0:B`] MFD_DIST_SYM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x0 z = tau` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `O:B->bool`; `rho:B->real`; `x0:B`; `z:B`; `y:B`] P2BK_CR_EQANGLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) z y <= tau + mfd_dist (top,atlas) g x0 y` THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x0 y < e` THEN
      UNDISCH_TAC `&6 * e <= (rho:B->real) y` THEN UNDISCH_TAC `tau < e` THEN
      UNDISCH_TAC `&0 < tau` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `W:B->bool` THEN ASM_REWRITE_TAC[] THEN
  (* chartwise smoothness *)
  REWRITE_TAC[mfd_smooth_on] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "smz" (MP_TAC o C MATCH_MP (ASSUME `(c:(B->bool)#(B->real^3)) IN atlas`) o
                  SPEC `c:(B->bool)#(B->real^3)` o REWRITE_RULE[mfd_smooth_on]) THEN
  DISCH_TAC THEN
  USE_THEN "smx" (MP_TAC o C MATCH_MP (ASSUME `(c:(B->bool)#(B->real^3)) IN atlas`) o
                  SPEC `c:(B->bool)#(B->real^3)` o REWRITE_RULE[mfd_smooth_on]) THEN
  DISCH_TAC THEN
  ABBREV_TAC `S = IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER W)` THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\Y:real^3. lift(sqrt(drop(lift((rho:B->real) x0 * rho z) +
       ((rho x0 / tau) %
          ((\y. lift(mfd_dist (top,atlas) (g:B->real^3^3) z y pow 2)) o
           chart_inv (c:(B->bool)#(B->real^3))) Y -
        (rho z / tau) % ((\y. lift(mfd_dist (top,atlas) g x0 y pow 2)) o chart_inv c) Y))))` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (SND c y) = y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_CMUL; LIFT_DROP] THEN
    USE_THEN "id" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(y:B) IN W`))]) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SQRT THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `y:B` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (SND c y) = y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_CMUL; LIFT_DROP] THEN
    USE_THEN "id" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(y:B) IN W`))]) THEN
    MATCH_MP_TAC REAL_POW_LT THEN USE_THEN "rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Smoothness of rho on O, local geodesic chart curves (no completeness),    *)
(* the quadratic profile of rho^2 along geodesics, and the one-dimensional   *)
(* calculus behind the Hessian identity.                                     *)
(* ========================================================================= *)

let P2BK_CR_SMOOTH = prove
 (`!top atlas (g:B->real^3^3) O rho.
     p2bk_crhyp (top,atlas) g O rho
     ==> mfd_smooth_on atlas O (\y. lift(rho y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  REWRITE_TAC[mfd_smooth_on] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x:B`] P2BK_CR_LOCAL_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `mfd_smooth_on (atlas:((B->bool)#(B->real^3))->bool) N
                   (\y:B. lift((rho:B->real) y))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)`) THEN
    ASM_REWRITE_TAC[]]);;

(* rho^2/2 is smooth in every chart over O. *)

let P2BK_CR_CHART_SQ = prove
 (`!top atlas (g:B->real^3^3) O rho c.
     p2bk_crhyp (top,atlas) g O rho /\ c IN atlas
     ==> open (IMAGE (SND c) (FST c INTER O)) /\
         smooth_map_on (IMAGE (SND c) (FST c INTER O))
           (\y. lift(rho(chart_inv c y) pow 2 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER O))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`] P2BK_CR_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `c:(B->bool)#(B->real^3)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y:real^3. inv(&2) %
     lift(drop(((\y:B. lift((rho:B->real) y)) o chart_inv (c:(B->bool)#(B->real^3))) y) *
          drop(((\y:B. lift(rho y)) o chart_inv c) y))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_THM; LIFT_DROP; GSYM LIFT_CMUL] THEN GEN_TAC THEN DISCH_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* Local geodesic chart curves (the local form of CMPAF_GEO_CHART): the     *)
(* geodesic from P with chart velocity z stays in the chart for small t,    *)
(* and its chart curve satisfies sigma' = v, v' = -Gamma(v,v), v(0) = z.     *)

let P2BK_GEO_CHART = prove
 (`!top atlas (g:B->real^N^N) c (P:B) z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas /\ P IN FST c
        ==> ?v d. &0 < d /\ v(&0) = z /\
                  !t. abs t < d
                      ==> t IN mfd_geo_maxint (top,atlas) g P
                                 (chart_jac c (chart_at atlas P) P z) /\
                          mfd_geo (top,atlas) g P (chart_jac c (chart_at atlas P) P z) t
                            IN FST c /\
                          ((\s. SND c (mfd_geo (top,atlas) g P
                                         (chart_jac c (chart_at atlas P) P z) (drop s)))
                           has_vector_derivative v t) (at (lift t)) /\
                          ((\s. v(drop s)) has_vector_derivative
                           --(christoffel (metric_local atlas c g)
                                (SND c (mfd_geo (top,atlas) g P
                                          (chart_jac c (chart_at atlas P) P z) t))
                                (v t) (v t))) (at (lift t))`,
  INTRO_TAC "!top atlas g c P z; haus smooth riem cat Pc" THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `g:B->real^N^N`; `P:B`;
                 `chart_jac (c:(B->bool)#(B->real^N)) (chart_at atlas (P:B)) P z`]
    MFD_GEO_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = chart_jac (c:(B->bool)#(B->real^N)) (chart_at atlas (P:B)) P z` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:B->real^N^N) P w` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:B->real^N^N) P w` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `g:B->real^N^N`; `gam:real->B`; `J:real->bool`; `c:(B->bool)#(B->real^N)`]
    GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (LABEL_TAC "vv")) THEN
  MP_TAC(ISPECL [`top:B topology`; `gam:real->B`; `J:real->bool`;
                 `FST(c:(B->bool)#(B->real^N))`; `&0`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GEOL_GEODESIC_BASIC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_geodesic"
      with Failure _ -> false)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:real->real^N`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `g:B->real^N^N`; `gam:real->B`; `J:real->bool`; `c:(B->bool)#(B->real^N)`;
                   `(v:real->real^N)(&0)`; `&0`] GEOL_CHART_VEL_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "vv" (MP_TAC o SPEC `&0`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `chart_jac (c:(B->bool)#(B->real^N)) (chart_at atlas (P:B)) P z = w`)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`;
                   `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (P:B))`;
                   `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (P:B))`; `P:B`]
      CHART_JAC_INVERSE) THEN
    REWRITE_TAC[PAIR] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `P:B`] CHART_AT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C AP_THM `z:real^N`) THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `t IN J /\ (gam:real->B) t IN FST (c:(B->bool)#(B->real^N))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "vv" (fun th -> ACCEPT_TAC(MATCH_MP th
    (CONJ (ASSUME `(t:real) IN (J:real->bool)`) (ASSUME `(gam:real->B) t IN FST (c:(B->bool)#(B->real^N))`)))));;

(* A function agreeing with a quadratic on [0,d) has, at a point s of        *)
(* [0,d), the derivative of the quadratic (one-sided at s = 0).              *)

let P2BK_QUAD_DERIV = prove
 (`!(f:real^1->real^1) f' a b q d s.
     &0 < d /\ &0 <= s /\ s < d /\
     (!t. &0 <= t /\ t < d ==> f(lift t) = lift(a + b * t + q * t pow 2)) /\
     (f has_vector_derivative f') (at (lift s))
     ==> f' = lift(b + &2 * q * s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((lift o (\t. a + b * t + q * t pow 2) o drop) has_vector_derivative
     lift(b + &2 * q * s)) (at (lift s))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
    MP_TAC(REAL_DIFF_CONV
      `((\t. a + b * t + q * t pow 2) has_real_derivative f0) (atreal s)`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
  MAP_EVERY EXISTS_TAC [`f:real^1->real^1`; `lift s`; `lift((s + d) / &2)`; `lift s`] THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `s < d` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `s < d` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`lift o (\t. a + b * t + q * t pow 2) o drop`; `&1`] THEN
    REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `s < d` THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      MP_TAC(SPEC `drop y` (ASSUME `!t. &0 <= t /\ t < d
                 ==> (f:real^1->real^1)(lift t) = lift(a + b * t + q * t pow 2)`)) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
       [UNDISCH_TAC `s <= drop y` THEN UNDISCH_TAC `drop y <= (s + d) / &2` THEN
        UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s < d` THEN REAL_ARITH_TAC;
        DISCH_THEN(fun th -> REWRITE_TAC[th])];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[]]]);;

(* Along a geodesic from x in O with nonzero initial vector w, rho^2 is a   *)
(* quadratic in t for small t >= 0 with leading coefficient |w|^2.          *)

let P2BK_CR_GEO_QUAD = prove
 (`!top atlas (g:B->real^3^3) O rho x w.
     p2bk_crhyp (top,atlas) g O rho /\ x IN O /\ ~(w = vec 0)
     ==> ?d b. &0 < d /\
               !t. &0 <= t /\ t < d
                   ==> t IN mfd_geo_maxint (top,atlas) g x w /\
                       mfd_geo (top,atlas) g x w t IN O /\
                       rho(mfd_geo (top,atlas) g x w t) pow 2 =
                       rho x pow 2 + b * t + mfd_tnorm g x w pow 2 * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x:B`] P2BK_CRSETUP_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:B->bool` (X_CHOOSE_THEN `r:real` (X_CHOOSE_TAC `e:real`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crsetup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`] GEOD_TNORM_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`] GEOD_TNORM_EQ_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_tnorm (g:B->real^3^3) x w` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = mfd_tnorm (g:B->real^3^3) x w` THEN
  ABBREV_TAC `u1 = inv L % (w:real^3)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:B->real^3^3) x u1 = &1 /\ L % u1 = w` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u1" THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; REAL_ABS_INV;
                 REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x:B`; `W:B->bool`; `r:real`; `e:real`;
                 `x:B`; `u1:real^3`] P2BK_CR_RADIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real` (LABEL_TAC "rad")) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u1:real^3`] MFD_GEO_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u1:real^3`; `L:real`] MFD_GEO_RESCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `L % u1:real^3 = w`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "resc")) THEN
  MAP_EVERY EXISTS_TAC [`e / L`; `&2 * cc * L`] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L * t /\ L * t < e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `t < e / L` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `r:real`; `u1:real^3`; `&0`; `L * t`] P2BK_RAY_GEO_DIST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `L * t < e` THEN UNDISCH_TAC `&2 * e <= r` THEN UNDISCH_TAC `&0 < e` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:B->real^3^3) x u1 (&0) = x`; REAL_SUB_RZERO] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:B->real^3^3) x w t = mfd_geo (top,atlas) g x u1 (L * t)`
    SUBST1_TAC THENL
   [USE_THEN "resc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM];
    UNDISCH_TAC `mfd_ball (top,atlas) (g:B->real^3^3) x (&4 * e) SUBSET O` THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `L * t < e` THEN UNDISCH_TAC `&0 < e` THEN
    REAL_ARITH_TAC;
    USE_THEN "rad" (MP_TAC o SPEC `L * t`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC REAL_RING]);;

(* The local metric in a chart is the pullback of g by the chart Jacobian. *)

let P2BK_METRIC_LOCAL_TNORM = prove
 (`!top atlas (g:B->real^N^N) c x z.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ x IN FST c
        ==> z dot (metric_local atlas c g (SND c x) ** z) =
            mfd_tnorm g x (chart_jac c (chart_at atlas x) x z) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `x:B`] GEOD_TNORM_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[metric_local] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (chart_jac (c:(B->bool)#(B->real^N)) (chart_at atlas (x:B)) x)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`;
                   `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B))`;
                   `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B))`; `x:B`]
      CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

(* The chart Jacobian into the preferred chart is injective. *)

let P2BK_CHART_JAC_NZ = prove
 (`!top atlas c (x:B) (z:real^N).
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c /\ ~(z = vec 0)
        ==> ~(chart_jac c (chart_at atlas x) x z = vec 0)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `~(z:real^N = vec 0)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`;
                 `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B))`; `x:B`]
    CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
  DISCH_THEN(MP_TAC o C AP_THM `z:real^N`) THEN REWRITE_TAC[o_THM] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPEC `chart_jac (chart_at atlas (x:B)) (c:(B->bool)#(B->real^N)) x` LINEAR_0) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `FST(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^N))->bool) (x:B))`;
                 `FST(c:(B->bool)#(B->real^N))`; `SND(c:(B->bool)#(B->real^N))`; `x:B`]
    CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER]);;

(* Chart calculus along a curve: if F o sigma is quadratic on [0,d) and     *)
(* v' = -G at 0, then D2F(z,z) - DF(G) = 2q at sigma(0) (z = v(0)).         *)

let P2BK_ALONG_DERIV = prove
 (`!U (Fc:real^N->real^1) (sig:real->real^N) (v:real->real^N) Y z G d a b q.
        open U /\ smooth_map_on U Fc /\ &0 < d /\ sig(&0) = Y /\ v(&0) = z /\
        (!t. &0 <= t /\ t < d
             ==> sig t IN U /\ Fc(sig t) = lift(a + b * t + q * t pow 2)) /\
        (!t. &0 <= t /\ t < d
             ==> ((\s. sig(drop s)) has_vector_derivative v t) (at (lift t))) /\
        ((\s. v(drop s)) has_vector_derivative --G) (at (lift(&0)))
        ==> frechet_derivative (\y'. frechet_derivative Fc (at y') z) (at Y) z -
            frechet_derivative Fc (at Y) G = lift(&2 * q)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "oU smF d0 s0 v0 quad dsig dv" THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t < d
                    ==> frechet_derivative (Fc:real^N->real^1) (at ((sig:real->real^N) t))
                          ((v:real->real^N) t) = lift(b + &2 * q * t)`
    (LABEL_TAC "dF") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BK_QUAD_DERIV THEN
    MAP_EVERY EXISTS_TAC [`\s:real^1. (Fc:real^N->real^1)((sig:real->real^N)(drop s))`;
                          `a:real`; `d:real`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "quad" (MP_TAC o SPEC `s:real`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Fc:real^N->real^1`;
                   `frechet_derivative (Fc:real^N->real^1) (at ((sig:real->real^N) t))`;
                   `\s:real^1. (sig:real->real^N)(drop s)`; `(v:real->real^N) t`; `lift t`]
      CMPAF_VCHAIN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [USE_THEN "dsig" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `Fc:real^N->real^1`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "quad" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N) IN U` ASSUME_TAC THENL
   [USE_THEN "s0" (SUBST1_TAC o SYM) THEN USE_THEN "quad" (MP_TAC o SPEC `&0`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fc:real^N->real^1) (at Y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\s. (sig:real->real^N)(drop s)) has_vector_derivative z) (at (lift(&0)))`
    ASSUME_TAC THENL
   [USE_THEN "v0" (SUBST1_TAC o SYM) THEN USE_THEN "dsig" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Fc:real^N->real^1`; `\s:real^1. (sig:real->real^N)(drop s)`;
                 `\s:real^1. (v:real->real^N)(drop s)`; `z:real^N`; `--(G:real^N)`; `lift(&0)`]
    GEOL_FRECHET_ALONG) THEN
  REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r:real^1. frechet_derivative (Fc:real^N->real^1) (at ((sig:real->real^N)(drop r)))
                               ((v:real->real^N)(drop r))`;
                 `frechet_derivative (\y'. frechet_derivative (Fc:real^N->real^1) (at y') z)
                    (at (Y:real^N)) z + --(frechet_derivative Fc (at Y) G)`;
                 `b:real`; `&2 * q`; `&0`; `d:real`; `&0`] P2BK_QUAD_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; LIFT_DROP] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "dF" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The Hessian identity Hess(rho^2/2) = g in every chart, by the diagonal    *)
(* identity along geodesics and polarization (CMPAF_POLAR), and the main     *)
(* theorem P2BK_CONE_REGULAR.                                                *)
(* ========================================================================= *)

let P2BK_BILINEAR_SUB = prove
 (`!(f:real^M->real^N->real^P) g.
     bilinear f /\ bilinear g ==> bilinear (\x y. f x y - g x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bilinear; linear] THEN
  ASM_SIMP_TAC[BILINEAR_LADD; BILINEAR_RADD; BILINEAR_LMUL; BILINEAR_RMUL] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let P2BK_BILINEAR_COMPOSE = prove
 (`!(L:real^N->real^M) (h:real^P->real^Q->real^N).
     linear L /\ bilinear h ==> bilinear (\x y. L(h x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bilinear; linear] THEN
  ASM_SIMP_TAC[BILINEAR_LADD; BILINEAR_RADD; BILINEAR_LMUL; BILINEAR_RMUL;
               LINEAR_ADD; LINEAR_CMUL]);;

let P2BK_BILINEAR_QFORM = prove
 (`!A:real^N^N. bilinear (\x y. lift(x dot (A ** y)))`,
  REWRITE_TAC[bilinear; linear; MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; LIFT_ADD; LIFT_CMUL]);;

(* The diagonal identity: D2F(z,z) - DF(Gamma(z,z)) = <z, G z> in a chart,  *)
(* for F = rho^2/2 o chart_inv c, from the quadratic profile along the      *)
(* geodesic with chart velocity z.                                           *)

let P2BK_CR_HESS_DIAG = prove
 (`!top atlas (g:B->real^3^3) O rho c x z.
     p2bk_crhyp (top,atlas) g O rho /\ c IN atlas /\ x IN FST c /\ x IN O /\
     ~(z = vec 0)
     ==> frechet_derivative
           (\y'. frechet_derivative (\y. lift(rho(chart_inv c y) pow 2 / &2)) (at y') z)
           (at (SND c x)) z -
         frechet_derivative (\y. lift(rho(chart_inv c y) pow 2 / &2)) (at (SND c x))
           (christoffel (metric_local atlas c g) (SND c x) z z) =
         lift(z dot (metric_local atlas c g (SND c x) ** z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2")))) THEN
  SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `c:(B->bool)#(B->real^3)`; `x:B`; `z:real^3`] P2BK_METRIC_LOCAL_TNORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`; `x:B`; `z:real^3`] P2BK_CHART_JAC_NZ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `c:(B->bool)#(B->real^3)`; `x:B`; `z:real^3`] P2BK_GEO_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w = chart_jac (c:(B->bool)#(B->real^3)) (chart_at atlas (x:B)) x z` THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^3` (X_CHOOSE_THEN `d0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "v0") (LABEL_TAC "loc"))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `x:B`; `w:real^3`] P2BK_CR_GEO_QUAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `b:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "quad")))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `w:real^3`] MFD_GEO_MAXIMAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `c:(B->bool)#(B->real^3)`] P2BK_CR_CHART_SQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER O)`;
    `\y:real^3. lift((rho:B->real)(chart_inv (c:(B->bool)#(B->real^3)) y) pow 2 / &2)`;
    `\t:real. SND (c:(B->bool)#(B->real^3)) (mfd_geo (top,atlas) (g:B->real^3^3) x w t)`;
    `v:real->real^3`; `SND (c:(B->bool)#(B->real^3)) x`; `z:real^3`;
    `christoffel (metric_local atlas (c:(B->bool)#(B->real^3)) (g:B->real^3^3)) (SND c x) z z`;
    `min d0 d1`; `(rho:B->real) x pow 2 / &2`; `b / &2`;
    `mfd_tnorm (g:B->real^3^3) x w pow 2 / &2`] P2BK_ALONG_DERIV) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_LT_MIN];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `&0 <= t` THEN UNDISCH_TAC `t < d0` THEN REAL_ARITH_TAC;
        STRIP_TAC] THEN
      USE_THEN "quad" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3))
                      (SND c (mfd_geo (top,atlas) (g:B->real^3^3) x w t)) =
                    mfd_geo (top,atlas) g x w t` SUBST1_TAC THENL
       [USE_THEN "inv1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
        ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `&0 <= t` THEN UNDISCH_TAC `t < d0` THEN REAL_ARITH_TAC;
        SIMP_TAC[]];
      USE_THEN "loc" (MP_TAC o SPEC `&0`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_0]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

(* The full Hessian identity in every chart over O, by polarization. *)

let P2BK_CR_HESS = prove
 (`!top atlas (g:B->real^3^3) O rho c x u v.
     p2bk_crhyp (top,atlas) g O rho /\ c IN atlas /\ x IN FST c /\ x IN O
     ==> p2bk_chart_hess atlas c g (\y. rho y pow 2 / &2) x u v =
         u dot (metric_local atlas c g (SND c x) ** v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2bk_chart_hess; lnabla; SUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_crhyp]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `O:B->bool`; `rho:B->real`; `c:(B->bool)#(B->real^3)`] P2BK_CR_CHART_SQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!a:real^3. ~(a = vec 0)
       ==> frechet_derivative
             (\z. frechet_derivative
                    (\y. lift((rho:B->real)(chart_inv (c:(B->bool)#(B->real^3)) y) pow 2 / &2))
                    (at z) a) (at (SND c x)) a -
           frechet_derivative (\y. lift(rho(chart_inv c y) pow 2 / &2)) (at (SND c x))
             (christoffel (metric_local atlas c (g:B->real^3^3)) (SND c x) a a) =
           lift(a dot (metric_local atlas c g (SND c x) ** a))`
    (LABEL_TAC "diag") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_CR_HESS_DIAG THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `O:B->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Fc = \y:real^3. lift((rho:B->real)(chart_inv (c:(B->bool)#(B->real^3)) y) pow 2 / &2)` THEN
  ABBREV_TAC `U = IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER O)` THEN
  ABBREV_TAC `Y = SND (c:(B->bool)#(B->real^3)) x` THEN
  ABBREV_TAC `G = metric_local atlas (c:(B->bool)#(B->real^3)) (g:B->real^3^3)` THEN
  SUBGOAL_THEN `(Y:real^3) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN EXPAND_TAC "Y" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c))
                  (G:real^3->real^3^3) /\
                (Y:real^3) IN IMAGE (SND c) (FST c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "G" THEN
      UNDISCH_TAC `riemannian_metric (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Y" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^3->real^3^3) Y) = G Y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fc:real^3->real^1) (at Y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `BB = \a b:real^3. frechet_derivative (\z. frechet_derivative (Fc:real^3->real^1) (at z) b)
                        (at (Y:real^3)) a -
                      frechet_derivative Fc (at Y) (christoffel (G:real^3->real^3^3) Y a b) -
                      lift(a dot (G Y ** b))` THEN
  SUBGOAL_THEN `bilinear (BB:real^3->real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN
    MATCH_MP_TAC P2BK_BILINEAR_SUB THEN REWRITE_TAC[P2BK_BILINEAR_QFORM] THEN
    MATCH_MP_TAC P2BK_BILINEAR_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPAF_D2_BILINEAR THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BK_BILINEAR_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
      EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^3. (BB:real^3->real^3->real^1) a b = BB b a` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "BB" THEN
    SUBGOAL_THEN
     `frechet_derivative (\z. frechet_derivative (Fc:real^3->real^1) (at z) b) (at (Y:real^3)) a =
      frechet_derivative (\z. frechet_derivative Fc (at z) a) (at Y) b`
      SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `christoffel (G:real^3->real^3^3) Y a b = christoffel G Y b a`
      SUBST1_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_SYM THEN
      EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^3) dot ((G:real^3->real^3^3) Y ** b) = b dot (G Y ** a)`
      SUBST1_TAC THENL
     [MP_TAC(ISPECL [`(G:real^3->real^3^3) Y`; `a:real^3`; `b:real^3`] DOT_MATRIX_TRANSP_LMUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC DOT_SYM;
      ALL_TAC] THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^3. (BB:real^3->real^3->real^1) a a = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3` THEN ASM_CASES_TAC `a:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`BB:real^3->real^3->real^1`; `vec 0:real^3`] BILINEAR_LZERO) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "BB" THEN USE_THEN "diag" (MP_TAC o SPEC `a:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`BB:real^3->real^3->real^1`; `\x:real^3. (vec 0:real^1)`;
                 `\a:real^3 b:real^3. (vec 0:real^3)`] CMPAF_POLAR) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LINEAR_ZERO] THEN REWRITE_TAC[bilinear; LINEAR_ZERO];
    DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `u:real^3`])] THEN
  EXPAND_TAC "BB" THEN
  SUBGOAL_THEN `(v:real^3) dot ((G:real^3->real^3^3) Y ** u) = u dot (G Y ** v)`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`(G:real^3->real^3^3) Y`; `v:real^3`; `u:real^3`] DOT_MATRIX_TRANSP_LMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[DROP_SUB; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC);;

(* The main theorem P2BK_CONE_REGULAR (P2BK_CONE_REGULAR_STATEMENT). *)

let P2BK_CONE_REGULAR = prove
 (`!w:B->bool. P2BK_CONE_REGULAR_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2BK_CONE_REGULAR_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bk_crhyp (top,atlas) (g:B->real^3^3) O rho` ASSUME_TAC THENL
   [REWRITE_TAC[p2bk_crhyp] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BK_CR_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `g:B->real^3^3`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BK_CR_HESS THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `O:B->bool`] THEN ASM_REWRITE_TAC[]]);;

