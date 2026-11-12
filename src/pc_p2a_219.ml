(* ========================================================================= *)
(* pc_p2a_219: MT Prop 2.19 in the route form P2_PROP_2_19_SEP_STATEMENT of  *)
(* pc_p3_iface: on a complete connected 3-manifold with sec >= 0 in which    *)
(* every neck-chart sphere separates, the eps-necks have R bounded at their  *)
(* centres.  A neck of large R is small and far from a base point p; its     *)
(* central sphere S separates off a side F not containing p.  (a) F          *)
(* unbounded: Toponogov at a far point y of F (CMP_R1_TOPONOGOV) with two    *)
(* points q1, q2 near p equidistant from y gives d(w1,w2) >= (2/3) d(q1,q2)  *)
(* for the crossing points w1, w2 on S, against diam S -> 0.  (b) F bounded: *)
(* d_p has an interior maximum on the closure of F beyond the critical       *)
(* radius of Gromov's lemma (CMP_R2_CRITICAL), against the first variation   *)
(* along a regular field (CMP_R6_REGULAR_FIELD, CMP_R7_FIRST_VARIATION).     *)
(* ========================================================================= *)

needs "src/pc_p3_iface.ml";;
needs "src/pc_cmp_tpg.ml";;
needs "src/pc_cmp_busemann.ml";;
needs "src/pc_cmp_crit.ml";;
needs "src/pc_cmp_regf.ml";;
needs "src/pc_cmp_fvar.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_apx_sep.ml";;
needs "src/pc_grg_distcont.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The sides of a closed set S.  A continuous curve from the component F of  *)
(* a point c in M \ S to a point outside F meets S; the components are open  *)
(* in M (manifolds are locally connected) and F union S is closed.           *)
(* ========================================================================= *)

let P2AS_CROSS = prove
 (`!top S (c:A) (gamma:real->A) a b.
     a <= b /\
     continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
     connected_component_of (subtopology top (topspace top DIFF S)) c (gamma a) /\
     gamma b IN topspace top /\
     ~(connected_component_of (subtopology top (topspace top DIFF S)) c (gamma b))
     ==> ?t. a <= t /\ t <= b /\ gamma t IN S`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?t. a <= t /\ t <= b /\ (gamma:real->A) t IN S` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `connected_in (subtopology top (topspace top DIFF S))
                 (IMAGE (gamma:real->A) (real_interval[a,b]))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                      CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
        REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE;
                    IN_REAL_INTERVAL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top (topspace top DIFF S))
                           ((gamma:real->A) a) (gamma b)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`;
                   `IMAGE (gamma:real->A) (real_interval[a,b])`; `(gamma:real->A) a`]
                  CONNECTED_COMPONENT_OF_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `(gamma:real->A) b`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN]];
    ALL_TAC] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS]);;

let P2AS_COMPONENT_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) S (c:A).
     smooth_manifold_atlas top atlas /\ closed_in top S
     ==> open_in top (connected_component_of (subtopology top (topspace top DIFF S)) c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF S:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology top (topspace top DIFF S))
      (connected_component_of (subtopology top (topspace top DIFF S)) (c:A))`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE THEN
    MATCH_MP_TAC LOCALLY_CONNECTED_SPACE_OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE THEN
    MATCH_MP_TAC GEO_MANIFOLD_LOCALLY_PATH_CONNECTED THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[OPEN_IN_TRANS_FULL]]);;

let P2AS_COMPONENT_SUBSET = prove
 (`!top S (c:A).
     connected_component_of (subtopology top (topspace top DIFF S)) c SUBSET
     topspace top DIFF S`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`; `c:A`]
                CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let P2AS_COMPONENT_UNION_CLOSED = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) S (c:A).
     smooth_manifold_atlas top atlas /\ closed_in top S
     ==> closed_in top
           (connected_component_of (subtopology top (topspace top DIFF S)) c UNION S)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Fs = connected_component_of (subtopology top (topspace top DIFF S)) (c:A)` THEN
  SUBGOAL_THEN `(Fs:A->bool) SUBSET topspace top DIFF S` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN REWRITE_TAC[P2AS_COMPONENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF S:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology top (topspace top DIFF S))
            ((topspace top DIFF S) DIFF (Fs:A->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (topspace top DIFF S):A topology`; `c:A`]
                  CLOSED_IN_CONNECTED_COMPONENT_OF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_DIFF o CONJ
      (ISPEC `subtopology top (topspace top DIFF S):A topology` OPEN_IN_TOPSPACE)) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `topspace top INTER (topspace top DIFF S) = topspace top DIFF S:A->bool`
    SUBST1_TAC THENL [SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top ((topspace top DIFF S) DIFF (Fs:A->bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_TRANS_FULL]; ALL_TAC] THEN
  REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
   [UNDISCH_TAC `closed_in top (S:A->bool)` THEN
    REWRITE_TAC[closed_in] THEN ASM SET_TAC[];
    SUBGOAL_THEN
     `topspace top DIFF (Fs UNION S) = (topspace top DIFF S) DIFF (Fs:A->bool)`
    SUBST1_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]]]);;


(* ========================================================================= *)
(* Minimizing segments on a complete manifold and the splitting of a        *)
(* distance at a crossing point of S.  P2AS_SEGMENT is CMPSO_SEGMENT of     *)
(* pc_cmp_soul with the same proof (the load closure of pc_cmp_soul is      *)
(* avoided here).                                                           *)
(* ========================================================================= *)

let P2AS_SEGMENT = prove
 (`!top atlas (g:A->real^N^N) (p0:A) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        p0 IN topspace top /\ mfd_joinable (top,atlas) p0 x /\ ~(x = p0)
        ==> &0 < mfd_dist (top,atlas) g p0 x /\
            ?u. mfd_tnorm g p0 u = &1 /\
                mfd_geo (top,atlas) g p0 u (mfd_dist (top,atlas) g p0 x) = x /\
                !s. &0 <= s /\ s <= mfd_dist (top,atlas) g p0 x
                    ==> mfd_dist (top,atlas) g p0 (mfd_geo (top,atlas) g p0 u s) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `l = mfd_dist (top,atlas) (g:A->real^N^N) p0 x` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `x:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `inv l % (v:real^N)` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p0 (inv l % v) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `inv l % (v:real^N)`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l = x` ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l =
                  mfd_exp (top,atlas) g p0 (l % inv l % v)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  ABBREV_TAC `y = mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) s` THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p0 y /\
                mfd_dist (top,atlas) (g:A->real^N^N) p0 y <= s /\
                mfd_joinable (top,atlas) y x /\ mfd_dist (top,atlas) g y x <= l - s`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `s:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s:real`; `l:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) (&0) = p0`;
                ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) s = y`;
                ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l = x`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `y:A`; `x:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Geodesics of a complete manifold are continuous on every interval. *)

let P2AS_GEO_CONT = prove
 (`!top atlas (g:A->real^N^N) (x:A) u a b.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ x IN topspace top
     ==> continuous_map (subtopology euclideanreal (real_interval[a,b]),top)
                        (mfd_geo (top,atlas) g x u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[mfd_geodesic] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `u:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `continuous_map
      (subtopology euclideanreal (mfd_geo_maxint (top,atlas) g x u),top)
      (mfd_geo (top,atlas) (g:A->real^N^N) x u)` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEANREAL; SUBTOPOLOGY_TOPSPACE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL] THEN SIMP_TAC[]);;

(* A minimizing segment from y in the component F of c in M \ S to a point  *)
(* z outside F crosses S at a point w splitting the distance.               *)

let P2AS_CROSS_DIST = prove
 (`!top atlas (g:A->real^N^N) S (c:A) y z.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     connected_component_of (subtopology top (topspace top DIFF S)) c y /\
     z IN topspace top /\
     ~(connected_component_of (subtopology top (topspace top DIFF S)) c z) /\
     mfd_joinable (top,atlas) y z
     ==> ?w. w IN S /\ mfd_joinable (top,atlas) y w /\ mfd_joinable (top,atlas) w z /\
             mfd_dist (top,atlas) g y z =
             mfd_dist (top,atlas) g y w + mfd_dist (top,atlas) g w z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z:A = y)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `z:A`] P2AS_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^N^N) y z` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `u:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `c:A`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) y u`; `&0`; `L:real`] P2AS_CROSS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; P2AS_GEO_CONT] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) y u t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y
       (mfd_geo (top,atlas) (g:A->real^N^N) y u t) /\
    mfd_joinable (top,atlas) (mfd_geo (top,atlas) g y u t) z /\
    mfd_dist (top,atlas) g (mfd_geo (top,atlas) g y u t) z <= L - t`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `t:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`t:real`; `L:real`] o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) y u (&0) = y`;
                ASSUME `mfd_geo (top,atlas) (g:A->real^N^N) y u L = z`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) y (mfd_geo (top,atlas) g y u t) = t`
  ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `mfd_geo (top,atlas) (g:A->real^N^N) y u t`;
                 `z:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The geometry and topology of one eps-neck (x,e) at scale h = R(x)^(-1/2), *)
(* from APX_NECK_DIST with alpha = 1/2: the central sphere S = e(S^2) is     *)
(* compact with diameter <= 7 h, the neck lies within 2 h / eps of x, the    *)
(* axis points zp, zm at s-values +-1/(2 eps) are at distance >= h / (4 eps) *)
(* from S; S separates e(3/4 e1) from e(4/3 e1) (apx_sphere_sep) and the     *)
(* axis joins e(4/3 e1) to zp, e(3/4 e1) to zm in M \ S.                     *)
(* ========================================================================= *)

let P2AS_SQRT2_PI = prove
 (`sqrt(&2) * pi <= &14 / &3`,
  SUBGOAL_THEN `sqrt(&2) <= &71 / &50` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC PI_APPROX_32 THEN MP_TAC(SPEC `&2` SQRT_POS_LE) THEN
  REWRITE_TAC[REAL_POS] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(x - a) <= e <=> a - e <= x /\ x <= a + e`] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&71 / &50 * pi` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2AS_SVAL_SPHERE = prove
 (`!y:real^3. y IN sphere(vec 0,&1) ==> apx_sval y = &0`,
  SIMP_TAC[IN_SPHERE_0; apx_sval; LOG_1; REAL_MUL_RZERO]);;

let P2AS_AXIS = prove
 (`!t. norm(exp t % basis 1:real^3) = exp t /\ apx_sval(exp t % basis 1:real^3) = sqrt(&2) * t`,
  GEN_TAC THEN
  SUBGOAL_THEN `norm(exp t % basis 1:real^3) = exp t` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    REWRITE_TAC[real_abs; REAL_EXP_POS_LE];
    ASM_REWRITE_TAC[apx_sval; LOG_EXP]]);;

let P2AS_NECK_METRIC = prove
 (`?eps2. &0 < eps2 /\
     !eps top atlas (g:A->real^3^3) x e.
        &0 < eps /\ eps <= eps2 /\ hausdorff_space top /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e
        ==> (!w1 w2. w1 IN IMAGE e (sphere(vec 0,&1)) /\ w2 IN IMAGE e (sphere(vec 0,&1))
                     ==> mfd_joinable (top,atlas) w1 w2 /\
                         mfd_dist (top,atlas) g w1 w2 <=
                         &7 * inv(sqrt(mfd_scalar atlas g x))) /\
            (!y. y IN rfs_neck_dom eps
                 ==> mfd_joinable (top,atlas) x (e y) /\
                     mfd_dist (top,atlas) g x (e y) <=
                     &2 * inv eps * inv(sqrt(mfd_scalar atlas g x))) /\
            (!w s. w IN IMAGE e (sphere(vec 0,&1)) /\
                   (s = inv(&2 * sqrt(&2) * eps) \/ s = --inv(&2 * sqrt(&2) * eps))
                   ==> inv(&4 * eps) * inv(sqrt(mfd_scalar atlas g x)) <=
                       mfd_dist (top,atlas) g w (e(exp s % basis 1)))`,
  MP_TAC(SPEC `(:A)` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `epsa:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N"))) THEN
  EXISTS_TAC `min epsa (&1 / &100)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `x:A`; `e:real^3->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s = inv(&2 * sqrt(&2) * eps) \/ s = --inv(&2 * sqrt(&2) * eps)
        ==> (exp s % basis 1:real^3) IN rfs_neck_dom eps /\
            abs(apx_sval(exp s % basis 1:real^3)) = inv(&2 * eps)`
  (LABEL_TAC "AX") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&2) * inv(&2 * sqrt(&2) * eps) = inv(&2 * eps)` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2 * sqrt(&2) * eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2 * eps) /\
                  inv(&2 * sqrt(&2) * eps) < inv(sqrt(&2) * eps)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `&0 < sqrt(&2) * eps` MP_TAC THENL
           [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[P2AS_AXIS; rfs_neck_dom; annulus; IN_ELIM_THM; REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_ABS_NEG] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w1:A`; `w2:A`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "N" (MP_TAC o SPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
      `y1:real^3`; `y2:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2AS_SVAL_SPHERE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * h * sqrt(&2) * pi` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&3 / &2 * h * sqrt(&2) * pi = h * (&3 / &2 * (sqrt(&2) * pi)) /\
                  &7 * h = h * &7` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC P2AS_SQRT2_PI THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `x IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "N" (MP_TAC o SPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
      `y0:real^3`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2AS_SVAL_SPHERE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `y0:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(apx_sval(y:real^3)) < inv eps` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN rfs_neck_dom eps` THEN
      REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; apx_sval] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
       [MP_TAC(SPEC `--inv(sqrt(&2) * eps)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `abs(log(norm(y:real^3))) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_BOUNDS_LT] THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[EXP_LOG];
          ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[EXP_LOG]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(&2) * inv(sqrt(&2) * eps)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < sqrt(&2)` THEN
        UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `&100 <= inv eps` ASSUME_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &100`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * h * (abs(&0 - apx_sval(y:real^3)) + sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
    SUBGOAL_THEN `&3 / &2 * h * (abs(apx_sval(y:real^3)) + sqrt(&2) * pi) =
                  h * (&3 / &2 * (abs(apx_sval y) + sqrt(&2) * pi)) /\
                  &2 * inv eps * h = h * (&2 * inv eps)` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC P2AS_SQRT2_PI THEN
    UNDISCH_TAC `&100 <= inv eps` THEN UNDISCH_TAC `abs(apx_sval(y:real^3)) < inv eps` THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`w:A`; `s:real`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    USE_THEN "AX" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "N" (MP_TAC o SPECL [`top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`;
      `y1:real^3`; `exp s % basis 1:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2AS_SVAL_SPHERE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
       try fst(dest_const t) = "real_min" with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_0; REAL_SUB_RZERO] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `min (inv(&2 * eps)) (&2 * inv eps - inv(&2 * eps)) = inv(&2 * eps)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* The topology of a neck: e is a continuous injective map of its domain     *)
(* into M, S = e(S^2) is compact, S separates e(3/4 e1) from e(4/3 e1)       *)
(* (apx_sphere_sep on the restriction to annulus(1/2,2)), and the axis arcs  *)
(* join e(4/3 e1) to the far point zp and e(3/4 e1) to zm in M \ S.          *)
(* ========================================================================= *)

let P2AS_AXIS_CURVE = prove
 (`!a b. continuous_map (subtopology euclideanreal (real_interval[a,b]),euclidean)
                        (\t. t % basis 1:real^3)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN REWRITE_TAC[CONTINUOUS_MAP_ID]);;

let P2AS_NECK_BASICS = prove
 (`!eps top atlas (g:A->real^3^3) x e.
     rfs_neck (top,atlas) g eps x e
     ==> smooth_manifold_atlas top atlas /\ &0 < eps /\
         &0 < mfd_scalar atlas g x /\ open(rfs_neck_dom eps) /\
         continuous_map (subtopology euclidean (rfs_neck_dom eps),top) e /\
         (!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps /\ e y = e z ==> y = z) /\
         IMAGE e (rfs_neck_dom eps) SUBSET topspace top /\
         sphere(vec 0,&1) SUBSET rfs_neck_dom eps /\
         compact_in top (IMAGE e (sphere(vec 0,&1))) /\
         x IN IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE]]);;

(* An axis arc avoiding the unit sphere joins its ends in M \ S.          *)

let P2AS_AXIS_ARC = prove
 (`!eps top atlas (g:A->real^3^3) x e a b.
     rfs_neck (top,atlas) g eps x e /\ a <= b /\
     (!t. a <= t /\ t <= b ==> t % basis 1 IN rfs_neck_dom eps /\ ~(abs t = &1))
     ==> connected_component_of
           (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
           (e(a % basis 1)) (e(b % basis 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AS_NECK_BASICS) THEN
  REWRITE_TAC[connected_component_of] THEN
  EXISTS_TAC `IMAGE (\t. (e:real^3->A)(t % basis 1)) (real_interval[a,b])` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                  CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
      SUBGOAL_THEN `(\t. (e:real^3->A)(t % basis 1)) = e o (\t. t % basis 1)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps:real^3->bool)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; P2AS_AXIS_CURVE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
        UNDISCH_TAC `t % basis 1:real^3 IN rfs_neck_dom eps` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `t % basis 1:real^3 = y` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom eps` THEN
        UNDISCH_TAC `norm(y:real^3) = &1` THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN MESON_TAC[];
        DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
        ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID]]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `b:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

let P2AS_NECK_SEP = prove
 (`!eps top atlas (g:A->real^3^3) x e.
     rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\ apx_sphere_sep top atlas
     ==> e(&3 / &4 % basis 1) IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
         e(&4 / &3 % basis 1) IN topspace top DIFF IMAGE e (sphere(vec 0,&1)) /\
         ~(connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
            (e(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))) /\
         connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
            (e(&4 / &3 % basis 1)) (e(exp(inv(&2 * sqrt(&2) * eps)) % basis 1)) /\
         connected_component_of
            (subtopology top (topspace top DIFF IMAGE e (sphere(vec 0,&1))))
            (e(&3 / &4 % basis 1)) (e(exp(--inv(&2 * sqrt(&2) * eps)) % basis 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AS_NECK_BASICS) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2) * eps) = &2 * inv(&2 * sqrt(&2) * eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `T1 = inv(&2 * sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&1 <= T1` ASSUME_TAC THENL
   [EXPAND_TAC "T1" THEN MATCH_MP_TAC REAL_INV_1_LE THEN
    SUBGOAL_THEN `sqrt(&2) <= &3 / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * (&3 / &2 * &1 / &100)` THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp T1` ASSUME_TAC THENL
   [MP_TAC(SPEC `T1:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--T1) <= &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN
    MP_TAC(SPECL [`&2`; `exp T1`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp T1 < exp(&2 * T1) /\ exp(--(&2 * T1)) < exp(--T1) /\
                &0 < exp(--(&2 * T1))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT; REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. exp(--(&2 * T1)) < abs t /\ abs t < exp(&2 * T1)
        ==> t % basis 1:real^3 IN rfs_neck_dom eps`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas (e:real^3->A)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET; rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `apx_sphere_sep top (atlas:((A->bool)#(A->real^3))->bool)` THEN
  REWRITE_TAC[apx_sphere_sep] THEN DISCH_THEN(MP_TAC o SPEC `e:real^3->A`) THEN
  ASM_REWRITE_TAC[apx_separates] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AS_AXIS_ARC THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(MESON[CONNECTED_COMPONENT_OF_SYM]
      `connected_component_of (top:A topology) (b:A) a ==> connected_component_of top a b`) THEN
    MATCH_MP_TAC P2AS_AXIS_ARC THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(SPEC `--T1` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;


(* ========================================================================= *)
(* Two points near p at equal distance from any given y.  On the            *)
(* g(p)-circle V(t) = E (rho (cos t e1 + sin t e2)) (E an orthonormal frame *)
(* at p, rho below the injectivity radius) the antipodal pairs exp(V t),    *)
(* exp(-V t) are distinct, so their distances are bounded below by d0 > 0   *)
(* (compactness), and t -> d(y,exp V t) - d(y,exp(-V t)) changes sign on    *)
(* [0,pi] (connectedness).                                                  *)
(* ========================================================================= *)

let P2AS_REAL_CMAP = prove
 (`!f. f real_continuous_on (:real) ==> continuous_map (euclideanreal,euclideanreal) f`,
  GEN_TAC THEN REWRITE_TAC[real_continuous_on; IN_UNIV] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; METRIC_CONTINUOUS_MAP;
              REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `e:real`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real`; `e:real`]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MESON_TAC[REAL_ABS_SUB]);;

let P2AS_TRIG_CURVE = prove
 (`!a b:real^N. continuous_map (euclideanreal,euclidean) (\t. cos t % a + sin t % b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2AS_REAL_CMAP THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_COS; REAL_CONTINUOUS_ON_SIN]);;

let P2AS_ONB_TNORM = prove
 (`!(g:A->real^N^N) p (E:real^N^N) (w:real^N).
     transp E ** g p ** E = mat 1 ==> mfd_tnorm g p (E ** w) = norm w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tnorm; vector_norm] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

let P2AS_CIRCLE_NORM = prove
 (`!t. norm(cos t % basis 1 + sin t % basis 2:real^3) = &1`,
  GEN_TAC THEN REWRITE_TAC[vector_norm] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `cos t * (cos t * &1 + sin t * &0) + sin t * (cos t * &0 + sin t * &1) = &1`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN REAL_ARITH_TAC; REWRITE_TAC[SQRT_1]]);;

let P2AS_CIRCLE = prove
 (`!top atlas (g:A->real^3^3) p r1.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p IN topspace top /\ &0 < r1
     ==> ?d0. &0 < d0 /\
              !y. y IN topspace top
                  ==> ?v1 v2. mfd_tnorm g p v1 <= r1 /\ mfd_tnorm g p v2 <= r1 /\
                              d0 <= mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p v1)
                                                         (mfd_exp (top,atlas) g p v2) /\
                              mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v1) =
                              mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `mfd_inj_ball (top,atlas) (g:A->real^3^3) p r` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^3^3`) THEN
  ABBREV_TAC `rho = min (r / &2) r1` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < r /\ rho <= r1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `V = \t. cos t % (rho % ((E:real^3^3) ** basis 1)) +
                     sin t % (rho % (E ** basis 2))` THEN
  SUBGOAL_THEN
   `!t. (V:real->real^3) t = (E:real^3^3) ** (rho % (cos t % basis 1 + sin t % basis 2))`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN GEN_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. mfd_tnorm (g:A->real^3^3) p ((V:real->real^3) t) = rho`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g:A->real^3^3`; `p:A`; `E:real^3^3`;
                   `rho % (cos t % basis 1 + sin t % basis 2):real^3`] P2AS_ONB_TNORM) THEN
    ASM_REWRITE_TAC[NORM_MUL; P2AS_CIRCLE_NORM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `E:real^3^3`)) (concl th))) THEN
  SUBGOAL_THEN `!t. (V:real->real^3)(t + pi) = --(V t)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[SIN_PERIODIC_PI; COS_PERIODIC_PI] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^3^3) p = (:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`] MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[mfd_exp_dom; EXTENSION; IN_UNIV; IN_ELIM_THM] THEN ASM_SIMP_TAC[IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `q = \t. mfd_exp (top,atlas) (g:A->real^3^3) p ((V:real->real^3) t)` THEN
  SUBGOAL_THEN `continuous_map (euclideanreal,top) (q:real->A)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    SUBGOAL_THEN
     `(\t. mfd_exp (top,atlas) (g:A->real^3^3) p ((V:real->real^3) t)) =
      mfd_exp (top,atlas) g p o V`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[P2AS_TRIG_CURVE];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `p:A`] MFD_EXP_SMOOTH) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) p ((q:real->A) t) /\
        mfd_dist (top,atlas) (g:A->real^3^3) p (q t) = rho`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `r:real`; `(V:real->real^3) t`] MFD_EXP_DIST) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ~((q:real->A) t = q(t + pi))` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^3^3) p (--((V:real->real^3) t)) = rho`
    ASSUME_TAC THENL
     [MP_TAC(SPEC `t:real`
        (ASSUME `!t. mfd_tnorm (g:A->real^3^3) p ((V:real->real^3) t) = rho`)) THEN
      MP_TAC(SPECL [`-- &1`; `(V:real->real^3) t`]
        (ASSUME `!t v. mfd_tnorm (g:A->real^3^3) p (t % v) = abs t * mfd_tnorm g p v`)) THEN
      REWRITE_TAC[GSYM VECTOR_NEG_MINUS1] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `mfd_exp (top,atlas) (g:A->real^3^3) p`; `mfd_tball (g:A->real^3^3) p r`]
                  GEOJR_PARAM_FACTS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[mfd_inj_ball]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`(V:real->real^3) t`; `--((V:real->real^3) t)`] o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_ARITH `(v:real^3) = --v <=> v = vec 0`] THEN DISCH_TAC THEN
    UNDISCH_TAC `!t. mfd_tnorm (g:A->real^3^3) p ((V:real->real^3) t) = rho` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclideanreal,top) (\t. (q:real->A)(t + pi))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\t. (q:real->A)(t + pi)) = q o (\t. t + pi)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`] MFD_DIST_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b:real->A. continuous_map (euclideanreal,top) a /\ continuous_map (euclideanreal,top) b
                  ==> continuous_map (euclideanreal,euclideanreal)
                        (\t. mfd_dist (top,atlas) (g:A->real^3^3) (a t) (b t))`
  (LABEL_TAC "DC") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\t. mfd_dist (top,atlas) (g:A->real^3^3) ((a:real->A) t) (b t)) =
      (\(x,y). mfd_dist (top,atlas) g x y) o (\t. a t,b t)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `prod_topology top top:(A#A)topology` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (q:real->A)((t + pi) + pi) = q t` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[VECTOR_NEG_NEG]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\t. mfd_dist (top,atlas) (g:A->real^3^3) ((q:real->A) t) (q(t + pi)))
                      (real_interval[&0,pi])` REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_compact_def; IMAGE_EQ_EMPTY; REAL_INTERVAL_EQ_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,pi])` THEN
      REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL; COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      USE_THEN "DC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) ((q:real->A) t0) (q(t0 + pi))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool)
                    ((q:real->A) t0) (q(t0 + pi))` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `p:A` THEN
      ASM_MESON_TAC[MFD_JOINABLE_SYM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MFD_DIST_POS_LE; MFD_DIST_EQ_0];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `connected_in euclideanreal
      (IMAGE (\t. mfd_dist (top,atlas) (g:A->real^3^3) y ((q:real->A) t) -
                  mfd_dist (top,atlas) g y (q(t + pi))) (real_interval[&0,pi]))`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,pi])` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL; CONNECTED_IN_EUCLIDEANREAL_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN
    USE_THEN "DC" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL; is_realinterval] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`min (mfd_dist (top,atlas) (g:A->real^3^3) y ((q:real->A) (&0)) -
          mfd_dist (top,atlas) g y (q(&0 + pi)))
         (mfd_dist (top,atlas) g y (q pi) - mfd_dist (top,atlas) g y (q(pi + pi)))`;
    `max (mfd_dist (top,atlas) (g:A->real^3^3) y ((q:real->A) (&0)) -
          mfd_dist (top,atlas) g y (q(&0 + pi)))
         (mfd_dist (top,atlas) g y (q pi) - mfd_dist (top,atlas) g y (q(pi + pi)))`;
    `&0`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    SUBGOAL_THEN `(q:real->A)(pi + pi) = q(&0)` ASSUME_TAC THENL
     [MP_TAC(SPEC `&0` (ASSUME `!t. (q:real->A)((t + pi) + pi) = q t`)) THEN
      REWRITE_TAC[REAL_ADD_LID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[real_min] THEN COND_CASES_TAC THENL
       [EXISTS_TAC `&0` THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_ADD_LID] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC;
        EXISTS_TAC `pi` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC];
      REWRITE_TAC[real_max] THEN COND_CASES_TAC THENL
       [EXISTS_TAC `pi` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
        EXISTS_TAC `&0` THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_ADD_LID] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(V:real->real^3) t`; `(V:real->real^3)(t + pi)`] THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^3^3) p ((V:real->real^3) t) = q t /\
                mfd_exp (top,atlas) g p (V(t + pi)) = q(t + pi)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `t0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* An interior local maximum of d_p is not a regular point.  At a regular    *)
(* point x0 the regular direction v0, kept constant in the chart at x0       *)
(* (CMPRF_LOCAL of pc_cmp_regf), makes a uniformly obtuse angle with every   *)
(* minimizing direction to p near x0; along the chart segment in direction   *)
(* v0 the first variation CMP_R7_FIRST_VARIATION makes d_p increase          *)
(* strictly.                                                                 *)
(* ========================================================================= *)

(* Chart segments y0 + t v (0 <= t <= 1): C^1 curves whose velocity in the  *)
(* preferred chart is the chart vector v carried by the transition.          *)

let P2AS_CHART_LINE = prove
 (`!top atlas (c0:(A->bool)#(A->real^N)) y0 v (gamma:real->A).
     smooth_manifold_atlas top atlas /\ c0 IN atlas /\
     segment[y0,y0 + v] SUBSET IMAGE (SND c0) (FST c0) /\
     (!t. gamma t = chart_inv c0 (y0 + t % v))
     ==> mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
         (!t. t IN real_interval[&0,&1]
              ==> gamma t IN FST c0 /\ SND c0 (gamma t) = y0 + t % v) /\
         (!t. t IN real_interval[&0,&1]
              ==> mfd_velocity atlas gamma (&0) (&1) t =
                  chart_jac c0 (chart_at atlas (gamma t)) (gamma t) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `gamma = (\t. chart_inv (c0:(A->bool)#(A->real^N)) (y0 + t % v))`
  SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `y0:real^N`; `y0 + v:real^N`] GRGD_CHART_SEGMENT) THEN
  ASM_REWRITE_TAC[PAIR; VECTOR_ARITH `(y0 + v) - y0:real^N = v`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) (y0 + t % v) IN topspace top`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_inv (c0:(A->bool)#(A->real^N)) (y0 + t % v)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t. chart_inv (c0:(A->bool)#(A->real^N)) (y0 + t % v)`;
                 `&0`; `&1`; `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                        (chart_inv (c0:(A->bool)#(A->real^N)) (y0 + t % v)))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                        (chart_inv (c0:(A->bool)#(A->real^N)) (y0 + t % v)))`;
                 `t:real`] GRGD_VELOCITY_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; REAL_LT_01; IN_INTER] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[mfd_velocity]);;

(* The local maximum lemma.                                                   *)

let P2AS_LOCAL_MAX_NOT_REGULAR = prove
 (`!top atlas (g:A->real^3^3) (p:A) W x.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     open_in top W /\ x IN W /\ mfd_joinable (top,atlas) p x /\
     (!y. y IN W /\ mfd_joinable (top,atlas) p y
          ==> mfd_dist (top,atlas) g p y <= mfd_dist (top,atlas) g p x)
     ==> ~p2b_dist_regular (top,atlas) g p x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2b_dist_regular] THEN
  DISCH_THEN(X_CHOOSE_TAC `v0:real^3`) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v0:real^3 = vec 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`; `p:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_SYM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[IN_UNIV] THEN
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `vec 0 dot ((g:A->real^3^3) x ** w) < &0` THEN
    REWRITE_TAC[DOT_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `x:A`; `v0:real^3`] CMPRF_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `c:real`
    (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c0:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y0 = SND(c0:(A->bool)#(A->real^3)) x` THEN
  SUBGOAL_THEN `open(IMAGE (SND(c0:(A->bool)#(A->real^3))) (U INTER W))` MP_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y0:real^3`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(v0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `?tau. &0 < tau /\ norm(tau % v0:real^3) < r`
  (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `r / (&2 * norm(v0:real^3))` THEN REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `&0 < r / (&2 * norm(v0:real^3))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
    SUBGOAL_THEN `r / (&2 * norm(v0:real^3)) * norm v0 = r / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(v0:real^3)` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[y0,y0 + tau % v0] SUBSET IMAGE (SND(c0:(A->bool)#(A->real^3))) (U INTER W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y0:real^3,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_BALL; IN_BALL; DIST_REFL] THEN
    ASM_REWRITE_TAC[NORM_ARITH `dist(y0:real^3,y0 + v) = norm v`];
    ALL_TAC] THEN
  ABBREV_TAC `gam = \t. chart_inv (c0:(A->bool)#(A->real^3)) (y0 + t % tau % v0)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c0:(A->bool)#(A->real^3)`; `y0:real^3`; `tau % v0:real^3`;
                 `gam:real->A`] P2AS_CHART_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (SND(c0:(A->bool)#(A->real^3))) (U INTER W)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXPAND_TAC "gam" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1] ==> (gam:real->A) t IN U INTER W`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `y0 + t % tau % v0 IN IMAGE (SND(c0:(A->bool)#(A->real^3))) (U INTER W)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `segment[y0:real^3,y0 + tau % v0]`)) (concl th) &&
        can (find_term ((=) `W:A->bool`)) (concl th))) THEN
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
      UNDISCH_TAC `t IN real_interval[&0,&1]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(gam:real->A) t = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    EXPAND_TAC "gam" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gam:real->A)(&0) = x` ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    EXPAND_TAC "y0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((gam:real->A)(&1) = x)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `SND(c0:(A->bool)#(A->real^3))`)) (concl th) &&
      can (find_term ((=) `gam:real->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL; VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `y0 = y0 + v:real^3 <=> v = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x ((gam:real->A)(&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `gam:real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_tnorm (g:A->real^3^3) x
                  (chart_jac (c0:(A->bool)#(A->real^3)) (chart_at atlas x) x v0)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`] GEOD_TNORM_BASIC) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:A)` CMP_R7_FIRST_VARIATION) THEN
  REWRITE_TAC[CMP_R7_FIRST_VARIATION_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `p:A`; `gam:real->A`; `&0`; `&1`; `c / (M + &1)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `v:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM))))) THEN
    SUBGOAL_THEN `t IN real_interval[&0,&1]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    SUBGOAL_THEN `(gam:real->A) t IN U INTER W` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gam:real->A) t IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `(gam:real->A) t IN FST(c0:(A->bool)#(A->real^3))` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `c0:(A->bool)#(A->real^3)`; `(gam:real->A) t`] CMPRF_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `Zc = chart_jac (c0:(A->bool)#(A->real^3))
                       (chart_at atlas ((gam:real->A) t)) (gam t) v0` THEN
    SUBGOAL_THEN `mfd_velocity atlas (gam:real->A) (&0) (&1) t = tau % (Zc:real^3)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN EXPAND_TAC "Zc" THEN
      MATCH_MP_TAC LINEAR_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_speed] THEN
    REWRITE_TAC[ASSUME `mfd_velocity atlas (gam:real->A) (&0) (&1) t = tau % (Zc:real^3)`] THEN
    REWRITE_TAC[GSYM mfd_tnorm] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `(gam:real->A) t`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[DOT_LMUL] THEN
    SUBGOAL_THEN `(Zc:real^3) dot ((g:A->real^3^3) ((gam:real->A) t) ** v) <=
                  --c * mfd_tnorm g (gam t) v`
    ASSUME_TAC THENL
     [EXPAND_TAC "Zc" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `c:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^3^3) ((gam:real->A) t) Zc <= M` ASSUME_TAC THENL
     [EXPAND_TAC "Zc" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `M:real`)) (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `A0 = (Zc:real^3) dot ((g:A->real^3^3) ((gam:real->A) t) ** v)` THEN
    ABBREV_TAC `N0 = mfd_tnorm (g:A->real^3^3) ((gam:real->A) t) Zc` THEN
    ABBREV_TAC `T0 = mfd_tnorm (g:A->real^3^3) ((gam:real->A) t) v` THEN
    SUBGOAL_THEN `&0 <= N0 /\ &0 <= T0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "N0" THEN EXPAND_TAC "T0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `c / (M + &1) * N0 <= c` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `c / m * n = c * (n / m)`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= M ==> &0 < M + &1`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(c / (M + &1) * N0) * (tau * T0) <= c * (tau * T0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `tau * A0 <= tau * (--c * T0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < tau ==> abs tau = tau`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`]) THEN
  REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gam:real->A`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^3^3) x ((gam:real->A)(&1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(x:A = (gam:real->A)(&1))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `(gam:real->A)(&1)`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x:A`; `(gam:real->A)(&1)`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) p ((gam:real->A)(&1)) <=
                mfd_dist (top,atlas) g p x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `W:A->bool`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_dist" with Failure _ -> false))
          (concl th))) THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `&1` (ASSUME
        `!t. t IN real_interval[&0,&1] ==> (gam:real->A) t IN U INTER W`)) THEN
      REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN SET_TAC[];
      MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c / (M + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 < c / (M + &1) * mfd_length atlas (g:A->real^3^3) (gam:real->A) (&0) (&1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Case (b) of the proof.  Points near p lie on the side of p when S stays  *)
(* away from p; a far point z of the far side F beats every point of S in   *)
(* distance from p (P2AS_CROSS_DIST); if F is bounded, d_p attains its      *)
(* maximum over the compact set F union S at a point of the open set F,     *)
(* beyond the critical radius D, which is impossible                        *)
(* (P2AS_LOCAL_MAX_NOT_REGULAR against CMP_R2_CRITICAL).                    *)
(* ========================================================================= *)

let P2AS_EXP_DOM_UNIV = prove
 (`!top atlas (g:A->real^N^N) (x:A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ x IN topspace top
     ==> mfd_exp_dom (top,atlas) g x = (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[mfd_exp_dom; EXTENSION; IN_UNIV; IN_ELIM_THM] THEN ASM_SIMP_TAC[IN_UNIV]);;

let P2AS_RAY_CURVE = prove
 (`!v:real^N. continuous_map (euclideanreal,euclidean) (\t. t % v)`,
  GEN_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN REWRITE_TAC[CONTINUOUS_MAP_ID]);;

(* The ray from p to exp_p v stays within |v| of p. *)

let P2AS_NEAR_P_COMPONENT = prove
 (`!top atlas (g:A->real^N^N) (p:A) S v r1.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     mfd_tnorm g p v <= r1 /\
     (!z. mfd_joinable (top,atlas) p z /\ mfd_dist (top,atlas) g p z <= r1 ==> ~(z IN S))
     ==> connected_component_of (subtopology top (topspace top DIFF S)) p
                                (mfd_exp (top,atlas) g p v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) p = (:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[P2AS_EXP_DOM_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v. &0 <= mfd_tnorm (g:A->real^N^N) p v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &0 <= s /\ s <= &1
        ==> mfd_joinable (top,atlas) p (mfd_exp (top,atlas) (g:A->real^N^N) p (s % v)) /\
            mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p (s % v)) <= r1`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `s % v:real^N`] CMPH_EXP_DIST_LE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `n <= r ==> d <= n ==> d <= r`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * mfd_tnorm (g:A->real^N^N) p v` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:A) IN S)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `S:A->bool`)) (concl th))) THEN
    ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `mfd_tnorm (g:A->real^N^N) p v` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `connected_component_of (subtopology top (topspace top DIFF S)) (p:A)
                           (mfd_exp (top,atlas) (g:A->real^N^N) p v)` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `p:A`;
                 `\s. mfd_exp (top,atlas) (g:A->real^N^N) p (s % v)`; `&0`; `&1`]
                P2AS_CROSS) THEN
  REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO; VECTOR_MUL_LID] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      SUBGOAL_THEN
       `(\s. mfd_exp (top,atlas) (g:A->real^N^N) p (s % v)) =
        mfd_exp (top,atlas) g p o (\s. s % v)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
      REWRITE_TAC[P2AS_RAY_CURVE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`] MFD_EXP_SMOOTH) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN SIMP_TAC[];
      REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN
      ASM SET_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `p:A`; `v:real^N`] CMPH_EXP_DIST_LE) THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `r1:real`)) (concl th) &&
    not(can (find_term ((=) `S:A->bool`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `mfd_exp (top,atlas) (g:A->real^N^N) p (t % v)` o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `S:A->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* A far point z of the side F beats every point of S. *)

let P2AS_FAR_BEATS_S = prove
 (`!top atlas (g:A->real^N^N) (p:A) S c z dS dF.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     S SUBSET topspace top /\
     connected_component_of (subtopology top (topspace top DIFF S)) c z /\
     ~(connected_component_of (subtopology top (topspace top DIFF S)) c p) /\
     (!w w'. w IN S /\ w' IN S ==> mfd_dist (top,atlas) g w w' <= dS) /\
     (!w. w IN S ==> dF <= mfd_dist (top,atlas) g w z) /\ dS < dF
     ==> !w. w IN S ==> mfd_dist (top,atlas) g p w < mfd_dist (top,atlas) g p z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `c:A`] P2AS_COMPONENT_SUBSET) THEN
    UNDISCH_TAC `connected_component_of (subtopology top (topspace top DIFF S)) (c:A) z` THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN REWRITE_TAC[IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) a b`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `S:A->bool`; `c:A`; `z:A`; `p:A`] P2AS_CROSS_DIST) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w0:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w0:A) IN topspace top /\ (w:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `w0:A`; `w:A`] MFD_DIST_TRIANGLE) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) w0 w <= dS /\
    dF <= mfd_dist (top,atlas) g w0 z`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^N^N) p z =
    mfd_dist (top,atlas) g p w0 + mfd_dist (top,atlas) g w0 z`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `z:A`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `w0:A`] MFD_DIST_SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `w0:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Case (b): a bounded far side is impossible beyond the critical radius. *)

let P2AS_CASE_B = prove
 (`!top atlas (g:A->real^3^3) (p:A) S c z D R0.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     compact_in top S /\
     (!x. x IN topspace top /\ D < mfd_dist (top,atlas) g p x
          ==> p2b_dist_regular (top,atlas) g p x) /\
     connected_component_of (subtopology top (topspace top DIFF S)) c z /\
     D < mfd_dist (top,atlas) g p z /\
     (!w. w IN S ==> mfd_dist (top,atlas) g p w < mfd_dist (top,atlas) g p z) /\
     (!y. connected_component_of (subtopology top (topspace top DIFF S)) c y
          ==> mfd_dist (top,atlas) g p y <= R0)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Fs = connected_component_of (subtopology top (topspace top DIFF S)) (c:A)` THEN
  SUBGOAL_THEN `closed_in top (S:A->bool) /\ S SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fs:A->bool) SUBSET topspace top DIFF S` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN REWRITE_TAC[P2AS_COMPONENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN Fs` ASSUME_TAC THENL
   [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN Fs ==> mfd_dist (top,atlas) (g:A->real^3^3) p y <= R0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) a b`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top ((Fs:A->bool) UNION S)` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `S:A->bool`; `c:A`] P2AS_COMPONENT_UNION_CLOSED) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (Fs:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `S:A->bool`; `c:A`] P2AS_COMPONENT_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top ((Fs:A->bool) UNION S)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) p
                  (max R0 (mfd_dist (top,atlas) g p z))` THEN
    ASM_SIMP_TAC[REWRITE_RULE[mfd_complete] (ASSUME `mfd_complete (top,atlas) (g:A->real^3^3)`)] THEN
    REWRITE_TAC[SUBSET; IN_UNION; mfd_cball; IN_ELIM_THM] THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x < b ==> x <= max a b`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (top,euclideanreal) (\y. mfd_dist (top,atlas) (g:A->real^3^3) p y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. mfd_dist (top,atlas) (g:A->real^3^3) p y) =
      (\(a,b). mfd_dist (top,atlas) g a b) o (\y:A. p,y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `prod_topology top top:(A#A)topology` THEN
    ASM_SIMP_TAC[MFD_DIST_CONTINUOUS; CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_CONST;
                 CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\y. mfd_dist (top,atlas) (g:A->real^3^3) p y) ((Fs:A->bool) UNION S)`
               REAL_COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_compact_def; IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) p z <= mfd_dist (top,atlas) g p ys`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ys:A`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((ys:A) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ys:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `S:A->bool`)) (concl th) &&
      can (find_term ((=) `z:A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ys:A) IN Fs` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ys:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~p2b_dist_regular (top,atlas) (g:A->real^3^3) p ys` MP_TAC THENL
   [MATCH_MP_TAC P2AS_LOCAL_MAX_NOT_REGULAR THEN EXISTS_TAC `Fs:A->bool` THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ys:A`)) (concl th))) THEN
    ASM SET_TAC[];
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;


(* ========================================================================= *)
(* Case (a) of the proof.  For y on the far side F, far from the neck, and  *)
(* q1, q2 near p with d(y,q1) = d(y,q2) = L and d(q1,q2) >= d0, the         *)
(* minimizing segments from y to q1, q2 cross S at w1, w2 at distances t1,  *)
(* t2 >= 2L/3 from y; Toponogov's comparison (CMP_R1_TOPONOGOV) at y gives  *)
(* d(w1,w2) >= (2/3) d(q1,q2), which the diameter of S forbids.             *)
(* ========================================================================= *)

let P2AS_HINGE_ALG = prove
 (`!L t1 t2 dl d12.
     &0 < L /\ &2 * L <= &3 * t1 /\ t1 <= L /\ &2 * L <= &3 * t2 /\ t2 <= L /\
     &0 <= dl /\ &0 <= d12 /\
     (t1 pow 2 + t2 pow 2 - dl pow 2) / (&2 * t1 * t2) <=
     (L pow 2 + L pow 2 - d12 pow 2) / (&2 * L * L)
     ==> &2 * d12 <= &3 * dl`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t1 /\ &0 < t2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * t1 * t2 /\ &0 < &2 * L * L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    (CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(t1 pow 2 + t2 pow 2 - dl pow 2) * (&2 * L * L) <=
    (L pow 2 + L pow 2 - d12 pow 2) * (&2 * t1 * t2)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `(t1 pow 2 + t2 pow 2 - dl pow 2) / (&2 * t1 * t2) <=
      (L pow 2 + L pow 2 - d12 pow 2) / (&2 * L * L)` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `c / d * b = (c * b) / d`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 * t2 * d12 pow 2 <= L pow 2 * dl pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &2 * L pow 2 * (t1 - t2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2];
      UNDISCH_TAC
       `(t1 pow 2 + t2 pow 2 - dl pow 2) * (&2 * L * L) <=
        (L pow 2 + L pow 2 - d12 pow 2) * (&2 * t1 * t2)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * L pow 2 <= &9 * (t1 * t2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&2 * L) * (&2 * L) <= (&3 * t1) * (&3 * t2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `L pow 2 * (&4 * d12 pow 2) <= L pow 2 * (&9 * dl pow 2)` MP_TAC THENL
   [SUBGOAL_THEN `(&4 * L pow 2) * d12 pow 2 <= (&9 * (t1 * t2)) * d12 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    UNDISCH_TAC `t1 * t2 * d12 pow 2 <= L pow 2 * dl pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&2 * d12`; `&3 * dl`] REAL_LE_SQUARE_ABS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs(&2 * x) = &2 * x`;
               REAL_ARITH `&0 <= x ==> abs(&3 * x) = &3 * x`] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

(* Case (a). *)

let P2AS_CASE_A = prove
 (`!top atlas (g:A->real^3^3) (p:A) S c y v1 v2 r1 Lam dS.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     p IN topspace top /\ S SUBSET topspace top /\
     connected_component_of (subtopology top (topspace top DIFF S)) c y /\
     ~(connected_component_of (subtopology top (topspace top DIFF S)) c p) /\
     (!z. mfd_joinable (top,atlas) p z /\ mfd_dist (top,atlas) g p z <= r1 ==> ~(z IN S)) /\
     mfd_tnorm g p v1 <= r1 /\ mfd_tnorm g p v2 <= r1 /\
     mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v1) =
     mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v2) /\
     (!w w'. w IN S /\ w' IN S ==> mfd_dist (top,atlas) g w w' <= dS) /\
     (!w. w IN S ==> mfd_dist (top,atlas) g w (mfd_exp (top,atlas) g p v1) <= Lam /\
                     mfd_dist (top,atlas) g w (mfd_exp (top,atlas) g p v2) <= Lam) /\
     &3 * Lam < mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v1) /\
     &3 * dS < &2 * mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p v1)
                                          (mfd_exp (top,atlas) g p v2)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) a b`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component_of (subtopology top (topspace top DIFF S)) p
       (mfd_exp (top,atlas) (g:A->real^3^3) p v1) /\
    connected_component_of (subtopology top (topspace top DIFF S)) p
       (mfd_exp (top,atlas) g p v2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2AS_NEAR_P_COMPONENT THEN
    EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q1 = mfd_exp (top,atlas) (g:A->real^3^3) p v1` THEN
  ABBREV_TAC `q2 = mfd_exp (top,atlas) (g:A->real^3^3) p v2` THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) y q1` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `L:real`)) THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (q1:A) IN topspace top /\ (q2:A) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `c:A`] P2AS_COMPONENT_SUBSET) THEN
    MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `p:A`] P2AS_COMPONENT_SUBSET) THEN
    UNDISCH_TAC `connected_component_of (subtopology top (topspace top DIFF S)) (c:A) y` THEN
    UNDISCH_TAC `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) q1` THEN
    UNDISCH_TAC `connected_component_of (subtopology top (topspace top DIFF S)) (p:A) q2` THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN REWRITE_TAC[IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Ts = topspace top DIFF (S:A->bool)` THEN
  SUBGOAL_THEN
   `~(connected_component_of (subtopology top Ts) (c:A) q1) /\
    ~(connected_component_of (subtopology top Ts) c q2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(connected_component_of (subtopology top Ts) (c:A) p)` THEN
    REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q1:A = y) /\ ~(q2:A = y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* the two minimizing segments from y *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`; `q1:A`] P2AS_SEGMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u1:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`; `q2:A`] P2AS_SEGMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`; `u1:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`; `u2:real^3`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* each crosses S *)
  SUBGOAL_THEN
   `?t1. &0 <= t1 /\ t1 <= L /\ mfd_geo (top,atlas) (g:A->real^3^3) y u1 t1 IN S`
  (X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC P2AS_CROSS THEN MAP_EVERY EXISTS_TAC [`top:A topology`; `c:A`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[P2AS_GEO_CONT; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "Ts" THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(connected_component_of (subtopology top Ts) (c:A) q1)` THEN
    EXPAND_TAC "Ts" THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t2. &0 <= t2 /\ t2 <= L /\ mfd_geo (top,atlas) (g:A->real^3^3) y u2 t2 IN S`
  (X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC P2AS_CROSS THEN MAP_EVERY EXISTS_TAC [`top:A topology`; `c:A`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[P2AS_GEO_CONT; REAL_LT_IMP_LE] THEN
    EXPAND_TAC "Ts" THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(connected_component_of (subtopology top Ts) (c:A) q2)` THEN
    EXPAND_TAC "Ts" THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^3^3) y (mfd_geo (top,atlas) g y u1 t1) = t1 /\
    mfd_dist (top,atlas) g y (mfd_geo (top,atlas) g y u2 t2) = t2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `w1 = mfd_geo (top,atlas) (g:A->real^3^3) y u1 t1` THEN
  ABBREV_TAC `w2 = mfd_geo (top,atlas) (g:A->real^3^3) y u2 t2` THEN
  SUBGOAL_THEN `(w1:A) IN topspace top /\ (w2:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  (* the crossing times are at least 2L/3 *)
  SUBGOAL_THEN `&2 * L < &3 * t1 /\ &2 * L < &3 * t2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `y:A`; `w1:A`; `q1:A`] MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `y:A`; `w2:A`; `q2:A`] MFD_DIST_TRIANGLE) THEN
    ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o (fun th -> MATCH_MP th (ASSUME `(w1:A) IN S`)) o SPEC `w1:A` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Lam:real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o (fun th -> MATCH_MP th (ASSUME `(w2:A) IN S`)) o SPEC `w2:A` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `Lam:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Toponogov at y *)
  MP_TAC(ISPEC `(:A)` CMP_R1_TOPONOGOV) THEN REWRITE_TAC[CMP_R1_TOPONOGOV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `y:A`; `u1:real^3`; `u2:real^3`; `L:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t1:real`; `L:real`; `t2:real`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`L:real`; `t1:real`; `t2:real`;
                `mfd_dist (top,atlas) (g:A->real^3^3) w1 w2`;
                `mfd_dist (top,atlas) (g:A->real^3^3) q1 q2`] P2AS_HINGE_ALG) THEN
  ASM_SIMP_TAC[MFD_DIST_POS_LE; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) w1 w2 <= dS` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The main theorem P2AS_PROP_2_19_SEP (MT Prop 2.19 in the separating      *)
(* form).  Fix p.  CMP_R2_CRITICAL gives the critical radius D, the circle  *)
(* lemma P2AS_CIRCLE gives d0; R is bounded by B1 on the ball of radius |D| *)
(* + 3 about p.  A neck (x,e) with R(x) > max B1 (h0^-2), where h0 = min    *)
(* (d0/11) (eps/2), lies beyond that ball at scale h < h0; its far side is  *)
(* then excluded by case (b) if bounded, by case (a) otherwise              *)
(* (P2AS_NECK_CONTRA).                                                      *)
(* ========================================================================= *)

let P2AS_SCALE_BOUND = prove
 (`!top atlas (g:A->real^N^N) (p:A) r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top
     ==> ?B1. !y. mfd_joinable (top,atlas) p y /\ mfd_dist (top,atlas) g p y <= r
                  ==> mfd_scalar atlas g y <= B1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact_in top (mfd_cball (top,atlas) (g:A->real^N^N) p r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_complete]; ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (mfd_scalar atlas (g:A->real^N^N)) (mfd_cball (top,atlas) g p r)`
               REAL_COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[MFD_SCALAR_CONTINUOUS];
    ALL_TAC] THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; mfd_cball; IN_ELIM_THM] THEN
  MESON_TAC[REAL_ARITH `abs x <= B ==> x <= B`]);;

let P2AS_H_SMALL = prove
 (`!R h0. &0 < h0 /\ inv(h0 pow 2) < R ==> inv(sqrt R) < h0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv h0 < sqrt R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[REAL_POW_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv h0` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(SPECL [`inv h0`; `sqrt R`] REAL_LT_INV2) THEN
  ASM_SIMP_TAC[REAL_INV_INV]);;

(* The core contradiction: a neck far from p at a small scale. *)

let P2AS_NECK_CONTRA = prove
 (`?eps3. &0 < eps3 /\
     !eps top atlas (g:A->real^3^3) (p:A) D d0 x e.
       &0 < eps /\ eps <= eps3 /\
       hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ apx_sphere_sep top atlas /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top /\
       (!y. y IN topspace top /\ D < mfd_dist (top,atlas) g p y
            ==> p2b_dist_regular (top,atlas) g p y) /\
       &0 < d0 /\
       (!y. y IN topspace top
            ==> ?v1 v2. mfd_tnorm g p v1 <= &1 /\ mfd_tnorm g p v2 <= &1 /\
                        d0 <= mfd_dist (top,atlas) g (mfd_exp (top,atlas) g p v1)
                                                   (mfd_exp (top,atlas) g p v2) /\
                        mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v1) =
                        mfd_dist (top,atlas) g y (mfd_exp (top,atlas) g p v2)) /\
       rfs_neck (top,atlas) g eps x e /\
       &11 * inv(sqrt(mfd_scalar atlas g x)) < d0 /\
       &2 * inv(sqrt(mfd_scalar atlas g x)) < eps /\
       abs D + &3 < mfd_dist (top,atlas) g p x
       ==> F`,
  X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NM"))
    (INST_TYPE [`:A`,`:A`] P2AS_NECK_METRIC) THEN
  EXISTS_TAC `min eps2 (&1 / &100)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `p:A`; `D:real`; `d0:real`; `x:A`; `e:real^3->A`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AS_NECK_BASICS) THEN
  REMOVE_THEN "NM" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`; `e:real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "DIAM") (CONJUNCTS_THEN2 (LABEL_TAC "NBR")
    (LABEL_TAC "FAR"))) THEN
  MP_TAC(ISPECL [`eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `e:real^3->A`] P2AS_NECK_SEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `S = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `S SUBSET topspace top /\ (x:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `S:A->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. a IN topspace top /\ b IN topspace top
                        ==> mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) a b`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:A. mfd_dist (top,atlas) (g:A->real^3^3) a b = mfd_dist (top,atlas) g b a`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_DIST_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `!w w'. w IN S /\ w' IN S
                       ==> mfd_dist (top,atlas) (g:A->real^3^3) w w' <= &7 * h`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "DIAM" (MP_TAC o SPECL [`w:A`; `w':A`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the neck sphere is far from p *)
  SUBGOAL_THEN `!w. w IN S ==> abs D + &2 < mfd_dist (top,atlas) (g:A->real^3^3) p w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `w:A`; `x:A`] MFD_DIST_TRIANGLE) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) w x <= &7 * h` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&7 * h`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the far side and its far point *)
  ABBREV_TAC `T1 = inv(&2 * sqrt(&2) * eps)` THEN
  SUBGOAL_THEN
   `?c z. connected_component_of (subtopology top (topspace top DIFF S)) (c:A) z /\
          ~(connected_component_of (subtopology top (topspace top DIFF S)) c p) /\
          !w. w IN S ==> inv(&4 * eps) * h <= mfd_dist (top,atlas) (g:A->real^3^3) w z`
  (X_CHOOSE_THEN `c:A` (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THENL
   [ASM_CASES_TAC
     `connected_component_of (subtopology top (topspace top DIFF S))
                             ((e:real^3->A)(&3 / &4 % basis 1)) p` THENL
     [MAP_EVERY EXISTS_TAC [`(e:real^3->A)(&4 / &3 % basis 1)`;
                            `(e:real^3->A)(exp T1 % basis 1)`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN
        UNDISCH_TAC
         `~(connected_component_of (subtopology top (topspace top DIFF S))
                ((e:real^3->A)(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1)))` THEN
        REWRITE_TAC[] THEN
        ASM_MESON_TAC[CONNECTED_COMPONENT_OF_TRANS; CONNECTED_COMPONENT_OF_SYM];
        X_GEN_TAC `w:A` THEN DISCH_TAC THEN
        REMOVE_THEN "FAR" (MP_TAC o SPECL [`w:A`; `T1:real`]) THEN ASM_REWRITE_TAC[]];
      MAP_EVERY EXISTS_TAC [`(e:real^3->A)(&3 / &4 % basis 1)`;
                            `(e:real^3->A)(exp(--T1) % basis 1)`] THEN
      ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      REMOVE_THEN "FAR" (MP_TAC o SPECL [`w:A`; `--T1:real`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 * h < inv(&4 * eps) * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&25` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&4 * eps`; `&4 / &100`] REAL_LE_INV2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `S:A->bool`; `c:A`; `z:A`; `&7 * h`;
                 `inv(&4 * eps) * h`] P2AS_FAR_BEATS_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `D < mfd_dist (top,atlas) (g:A->real^3^3) p z` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `z:A`)) (concl th) &&
      not(can (find_term ((=) `h:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?R0. !y. connected_component_of (subtopology top (topspace top DIFF S)) (c:A) y
             ==> mfd_dist (top,atlas) (g:A->real^3^3) p y <= R0` THENL
   [(* case (b) *)
    FIRST_X_ASSUM(X_CHOOSE_TAC `R0:real`) THEN
    MATCH_MP_TAC P2AS_CASE_B THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `p:A`; `S:A->bool`; `c:A`; `z:A`; `D:real`;
                          `R0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* case (a) *)
  ABBREV_TAC `Lam = &7 * h + mfd_dist (top,atlas) (g:A->real^3^3) p x + &1` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&3 * Lam + &1` o
    REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `S:A->bool`; `c:A`] P2AS_COMPONENT_SUBSET) THEN
    UNDISCH_TAC `connected_component_of (subtopology top (topspace top DIFF S)) (c:A) y` THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN REWRITE_TAC[IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^3` (X_CHOOSE_THEN `v2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) (g:A->real^3^3) p (mfd_exp (top,atlas) g p v1) <= &1 /\
    mfd_dist (top,atlas) g p (mfd_exp (top,atlas) g p v2) <= &1 /\
    mfd_exp (top,atlas) g p v1 IN topspace top /\ mfd_exp (top,atlas) g p v2 IN topspace top`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`] P2AS_EXP_DOM_UNIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `v1:real^3`] CMPH_EXP_DIST_LE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `v2:real^3`] CMPH_EXP_DIST_LE) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN REPEAT STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AS_CASE_A THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `p:A`; `S:A->bool`; `c:A`; `y:A`; `v1:real^3`;
                        `v2:real^3`; `&1`; `Lam:real`; `&7 * h`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `w:A` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `abs D + &2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) w x <= &7 * h` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&7 * h`)) (concl th) &&
        not(can (find_term ((=) `p:A`)) (concl th)))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN EXPAND_TAC "Lam" THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `w:A`; `x:A`;
                     `mfd_exp (top,atlas) (g:A->real^3^3) p v1`] MFD_DIST_TRIANGLE) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`; `p:A`;
                     `mfd_exp (top,atlas) (g:A->real^3^3) p v1`] MFD_DIST_TRIANGLE) THEN
      ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[SPECL [`x:A`; `p:A`] th]) THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `w:A`; `x:A`;
                     `mfd_exp (top,atlas) (g:A->real^3^3) p v2`] MFD_DIST_TRIANGLE) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `x:A`; `p:A`;
                     `mfd_exp (top,atlas) (g:A->real^3^3) p v2`] MFD_DIST_TRIANGLE) THEN
      ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[SPECL [`x:A`; `p:A`] th]) THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `p:A`; `mfd_exp (top,atlas) (g:A->real^3^3) p v1`;
                   `y:A`] MFD_DIST_TRIANGLE) THEN
    ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[SPECL
      [`mfd_exp (top,atlas) (g:A->real^3^3) p v1`; `y:A`] th]) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The main theorem. *)

let P2AS_PROP_2_19_SEP = prove
 (`!u:A->bool. P2_PROP_2_19_SEP_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_PROP_2_19_SEP_STATEMENT] THEN
  X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NC"))
    (INST_TYPE [`:A`,`:A`] P2AS_NECK_CONTRA) THEN
  EXISTS_TAC `eps3:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `&0` THEN MAP_EVERY X_GEN_TAC [`x:A`; `e:real^3->A`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP P2AS_NECK_BASICS) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPEC `(:A)` CMP_R2_CRITICAL) THEN REWRITE_TAC[CMP_R2_CRITICAL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `p:A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `D:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `&1`] P2AS_CIRCLE) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `p:A`; `abs D + &3`] P2AS_SCALE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
  ABBREV_TAC `h0 = min (d0 / &11) (eps / &2)` THEN
  SUBGOAL_THEN `&0 < h0` ASSUME_TAC THENL [EXPAND_TAC "h0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `max B1 (inv(h0 pow 2))` THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `e:real^3->A`] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AS_NECK_BASICS) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) < h0` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AS_H_SMALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "NC" (MP_TAC o SPECL [`eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `p:A`; `D:real`; `d0:real`;
    `x:A`; `e:real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) < h0` THEN
    EXPAND_TAC "h0" THEN REAL_ARITH_TAC;
    UNDISCH_TAC `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) < h0` THEN
    EXPAND_TAC "h0" THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) x <= B1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MFD_JOINABLE_CONNECTED];
      ASM_REAL_ARITH_TAC]]);;

