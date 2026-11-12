(* ========================================================================= *)
(* pc_p2b_tube2: MT Thm 10.2, the bad-tube half, Part I continued: parabolic *)
(* rescaling of the failure data, the approximating tubes along the window   *)
(* of the minimizer of MT Claim 10.3, the cut A1 with a blow-up subsequence, *)
(* MT Claims 10.5 and 10.6, and the hypotheses of the local-compactness      *)
(* statement P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT (pc_p2b_lcreqg).          *)
(* ========================================================================= *)

needs "src/pc_p2b_tube.ml";;
needs "src/pc_p2b_cscale.ml";;
needs "src/pc_p2b_vscale.ml";;
needs "src/pc_p2b_979.ml";;
needs "src/pc_grg_dist2.ml";;
needs "src/pc_rfs_evmono.ml";;
needs "src/pc_p2b_neckbd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Parabolic rescaling at the base time.  For Q > 0 the view                 *)
(* p2b_rescale_view V t Q has at time 0 the slice of V at t with the metric  *)
(* Q g.  Evolving necks at (x,t) are evolving necks at (x,0) with the same   *)
(* parametrization, and strong canonical neighbourhoods at (x,t) are strong  *)
(* canonical neighbourhoods at (x,0) (caps and components by the P2BCS       *)
(* lemmas).                                                                  *)
(* ========================================================================= *)

let P2BT_RESCALE_ZERO = prove
 (`!t Q. t + &0 / Q = t`,
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID]);;

let P2BT_RESCALE_SLICE0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t Q.
     rfs_vtop (p2b_rescale_view V t Q) (&0) = rfs_vtop V t /\
     rfs_vatlas (p2b_rescale_view V t Q) (&0) = rfs_vatlas V t /\
     rfs_vmetric (p2b_rescale_view V t Q) (&0) = (\y. Q %% rfs_vmetric V t y)`,
  REWRITE_TAC[P2BK_VS_PARTS; P2BT_RESCALE_ZERO]);;

(* The neck centre facts are P2BN_NECK_CENTRE_FACTS of pc_p2b_neckbd.         *)

let P2BT_EVOLVING_NECK_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t len e Q.
     &0 < Q /\ riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
     rfs_evolving_neck V eps x t len e
     ==> rfs_evolving_neck (p2b_rescale_view V t Q) eps x (&0) len e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2B9_EVOLVING_NECK_ALT; P2B9_RFS_VSCALAR; P2BK_VS_PARTS; P2BT_RESCALE_ZERO;
              REAL_ADD_LID] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "per") (LABEL_TAC "fam")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS) THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t`;
                 `Q:real`; `x:A`] P2BCS_SCALAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t`;
                 `eps:real`; `x:A`; `e:real^3->A`; `Q:real`] P2BCS_NECK_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                     (rfs_vmetric V t) x` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "per" MATCH_MP_TAC THEN
    SUBGOAL_THEN `--(len / R) < s / Q /\ s / Q <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
      UNDISCH_TAC `&0 - len / (R / Q) < s` THEN
      SUBGOAL_THEN `&0 - len / (R / Q) = --(len / R) * Q` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Q` THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
        REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s y. R / Q %%
           rfs_pullback (rfs_vatlas (V:(real->A topology)#
                                      (real->((A->bool)#(A->real^3))->bool)#
                                      (real->A->real^3^3)) (t + s / (R / Q) / Q)) e
             (\y. Q %% rfs_vmetric V (t + s / (R / Q) / Q) y) y) =
    (\s y. R %% rfs_pullback (rfs_vatlas V (t + s / R)) e (rfs_vmetric V (t + s / R)) y)`
  (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[FUN_EQ_THM; P2B9_RFS_PULLBACK_CMUL] THEN BETA_TAC THEN
  REWRITE_TAC[MATRIX_CMUL_ASSOC; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN
  SUBGOAL_THEN `t + s / (R / Q) / Q = t + s / R /\ R / Q * Q = R`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < Q` THEN UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[]]);;

let P2BT_STRONG_CANONICAL_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U.
     rfs_strong_canonical V C eps x t U <=>
     (?e. rfs_strong_neck V eps x t e /\ U = IMAGE e (rfs_neck_dom eps)) \/
     (?Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
     (x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) \/
     (x IN U /\ rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_strong_canonical; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2BT_CANON_RESCALE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t Q.
     &0 < Q /\ hausdorff_space (rfs_vtop V t) /\
     riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
     p3_canon_at V C eps x t
     ==> p3_canon_at (p2b_rescale_view V t Q) C eps x (&0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3_canon_at; P2BT_STRONG_CANONICAL_ALT; P2BT_RESCALE_SLICE0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `U:A->bool`)))) THEN
  EXISTS_TAC `U:A->bool` THEN
  SUBGOAL_THEN
   `(!Y. rfs_cap (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t,rfs_vatlas V t)
                 (\y. Q %% rfs_vmetric V t y) C eps U Y <=>
         rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps (U:A->bool) Y) /\
    (rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (\y. Q %% rfs_vmetric V t y) C U <=>
     rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) /\
    (rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (\y. Q %% rfs_vmetric V t y) eps U <=>
     rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC P2BCS_CAP_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BCS_CCOMP_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BCS_ROUND_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) THEN DISJ1_TAC THEN
    EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[rfs_strong_neck] THEN
    MATCH_MP_TAC P2BT_EVOLVING_NECK_RESCALE THEN
    ASM_REWRITE_TAC[GSYM rfs_strong_neck];
    DISCH_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* One failure in a normalized slice (R(x) = 1).  A C^1 curve from x to y    *)
(* shorter than A, its last point z with R = 4 and the compact connected     *)
(* tail X (MT p. 247); the points of X are neck centres or lie in cap cores  *)
(* (components are excluded by their curvature ratios).                      *)
(* ========================================================================= *)

let P2BT_DIST_LT_CURVE = prove
 (`!top atlas (g:A->real^3^3) x y r.
     mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y < r
     ==> ?c. mfd_c1_curve (top,atlas) c (&0) (&1) /\ c(&0) = x /\ c(&1) = y /\
             mfd_length atlas g c (&0) (&1) < r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `r <= mfd_dist (top,atlas) (g:A->real^3^3) x y` MP_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) x y` THEN
    REWRITE_TAC[mfd_joinable; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `c0:real->A`) THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) c0 (&0) (&1)` THEN
    EXISTS_TAC `c0:real->A` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `c:real->A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real->A`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let P2BT_CURVE_TAIL = prove
 (`!top atlas (g:A->real^3^3) c lo hi.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) c (&0) (&1) /\
     mfd_scalar atlas g (c(&0)) < lo /\ lo < hi /\ hi < mfd_scalar atlas g (c(&1))
     ==> ?T0. &0 < T0 /\ T0 < &1 /\ mfd_scalar atlas g (c T0) = lo /\
              compact_in top (IMAGE c (real_interval[T0,&1])) /\
              connected_in top (IMAGE c (real_interval[T0,&1])) /\
              c T0 IN IMAGE c (real_interval[T0,&1]) /\
              c(&1) IN IMAGE c (real_interval[T0,&1]) /\
              (!w. w IN IMAGE c (real_interval[T0,&1]) ==> lo <= mfd_scalar atlas g w) /\
              mfd_joinable (top,atlas) (c T0) (c(&1)) /\
              mfd_dist (top,atlas) g (c T0) (c(&1)) <= mfd_length atlas g c (&0) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:real->A`; `lo:real`; `hi:real`] P2BT_GAMMA_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` (X_CHOOSE_THEN `T1:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `T0:real` THEN
  SUBGOAL_THEN `T0 < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) (c:real->A)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) c (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[T0,&1] SUBSET real_interval[&0,&1]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL];
    MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN ASM_CASES_TAC `s:real = T0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN
    MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:real->A`; `&0`; `T0:real`; `&1`]
    MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:real->A`; `T0:real`; `&1`] MFD_DIST_LE_LENGTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:real->A`; `&0`; `T0:real`] MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Components containing a point of a connected set contain the set. *)

let P2BT_COMPONENT_CONTAINS = prove
 (`!top (U:A->bool) X w.
     U IN connected_components_of top /\ connected_in top X /\ w IN X /\ w IN U
     ==> X SUBSET U`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[]);;

(* Points of the tail X: neck centres or in cap cores.  A C-component or a  *)
(* round component containing a point of X contains X, hence z and y, and   *)
(* its curvature ratio is too small for R(y) > D R(z) / 4 with D large.     *)

let P2BT_TAIL_POINTS = prove
 (`!C top atlas (g:A->real^3^3) eps (NK:A->(real^3->A)->bool) X z y.
     &1 < C /\ &0 < eps /\ eps <= &1 / &100 /\ riemannian_metric atlas g /\
     connected_in top X /\ z IN X /\ y IN X /\ &0 < mfd_scalar atlas g z /\
     C * mfd_scalar atlas g z < mfd_scalar atlas g y /\
     &2 * mfd_scalar atlas g z < mfd_scalar atlas g y /\
     (!w. w IN X
          ==> (?e. NK w e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y) \/
              (?U. w IN U /\ rfs_c_component (top,atlas) g C U) \/
              (?U. w IN U /\ rfs_round_component (top,atlas) g eps U))
     ==> !w. w IN X
             ==> (?e. NK w e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~c /\ ~d ==> (a \/ b \/ c \/ d ==> a \/ b)`) THEN CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(X:A->bool) SUBSET U` ASSUME_TAC THENL
     [MATCH_MP_TAC P2BT_COMPONENT_CONTAINS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `w:A`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
      SIMP_TAC[rfs_c_component];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `C:real`; `U:A->bool`; `z:A`; `y:A`]
      P2BT_C_COMPONENT_RATIO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= C * mfd_scalar atlas (g:A->real^3^3) z` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(X:A->bool) SUBSET U` ASSUME_TAC THENL
     [MATCH_MP_TAC P2BT_COMPONENT_CONTAINS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `w:A`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
      SIMP_TAC[rfs_round_component];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `eps:real`; `U:A->bool`; `z:A`; `y:A`]
      P2BT_ROUND_RATIO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* One failure gives a window of a minimizer (MT Claims 10.3, 10.4).  In a   *)
(* slice normalized by R(x) = 1 with strong canonical neighbourhoods above R *)
(* = 4, a point y within A of x with R(y) > D: the minimizer gamma of Claim  *)
(* 10.3 from the tail of a curve x -> y, and a window [s0,s1] with R(gamma   *)
(* s0) = lo = 32 C^2 and R(gamma s1) = R(q)/2C, whose points and the middle  *)
(* halves of their necks are NK-neck centres.                                *)
(* ========================================================================= *)

let P2BT_C_POWERS = prove
 (`!C. &1 < C
       ==> &0 < C /\ &1 <= C pow 2 /\ C <= C pow 2 /\ C pow 2 <= C pow 3 /\
           C pow 3 <= C pow 4`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_LE_1] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let P2BT_SQRT4 = prove
 (`sqrt(&4) = &2`,
  MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Claim 10.3 for one failure, normalized. *)

let P2BT_TAIL_CLAIM = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u /\ P2BT_REQ_A21_CH_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps A top atlas (g:A->real^3^3) (NK:A->(real^3->A)->bool) x y D.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < A /\
              hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              (!w e. NK w e ==> rfs_neck (top,atlas) g eps w e) /\
              (!w. w IN topspace top /\ &4 <= mfd_scalar atlas g w
                   ==> (?e. NK w e) \/
                       (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y) \/
                       (?U. w IN U /\ rfs_c_component (top,atlas) g C U) \/
                       (?U. w IN U /\ rfs_round_component (top,atlas) g eps U)) /\
              x IN topspace top /\ mfd_scalar atlas g x = &1 /\
              y IN mfd_ball (top,atlas) g x A /\
              &2048 * C pow 4 <= D /\ D < mfd_scalar atlas g y
              ==> ?gamma.
                    apx_shortest (top,atlas) g gamma (&0) (&1) /\
                    (!t. t IN real_interval[&0,&1]
                         ==> mfd_speed atlas g gamma (&0) (&1) t =
                             mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
                    &0 < mfd_scalar atlas g (gamma(&0)) /\
                    mfd_scalar atlas g (gamma(&0)) <= &16 * C /\
                    D <= &4 * C * mfd_scalar atlas g (gamma(&1)) /\
                    mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1)) <= A + &5 * C / eps`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BT_CLAIM_10_3) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c103"))) THEN
  EXISTS_TAC `min e1 (&1 / &100)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `A:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `NK:A->(real^3->A)->bool`; `x:A`; `y:A`; `D:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= &1 / &100` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BT_C_POWERS) THEN
  SUBGOAL_THEN `&1 <= C pow 4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^3^3) x A` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`; `y:A`; `A:real`] P2BT_DIST_LT_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `c:real->A`; `&4`; `&5`] P2BT_CURVE_TAIL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `X = IMAGE (c:real->A) (real_interval[T0,&1])` THEN
  ABBREV_TAC `z = (c:real->A) T0` THEN
  SUBGOAL_THEN `(X:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `eps:real`; `NK:A->(real^3->A)->bool`; `X:A->bool`;
                 `z:A`; `y:A`] P2BT_TAIL_POINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    DISCH_TAC] THEN
  USE_THEN "c103" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `g:A->real^3^3`; `NK:A->(real^3->A)->bool`; `X:A->bool`; `z:A`; `y:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` (X_CHOOSE_THEN `q:A`
    (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `mfd_scalar atlas (g:A->real^3^3) z = &4`;
                              P2BT_SQRT4]) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) z y + &10 * C / eps * inv(&2)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&10 * C / eps * inv(&2) = &5 * C / eps` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* The window and its necks (P2BT_WINDOW_NECKS, P2BT_P1). *)

let P2BT_TUBE_ONE = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u /\ P2BT_REQ_A21_CH_STATEMENT u /\
     APX_A8_CS_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !C eps A top atlas (g:A->real^3^3) (NK:A->(real^3->A)->bool) x y D.
              &1 < C /\ &0 < eps /\ eps <= eps0 /\ &0 < A /\
              hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              (!w e. NK w e ==> rfs_neck (top,atlas) g eps w e) /\
              (!w. w IN topspace top /\ &4 <= mfd_scalar atlas g w
                   ==> (?e. NK w e) \/
                       (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y) \/
                       (?U. w IN U /\ rfs_c_component (top,atlas) g C U) \/
                       (?U. w IN U /\ rfs_round_component (top,atlas) g eps U)) /\
              x IN topspace top /\ mfd_scalar atlas g x = &1 /\
              y IN mfd_ball (top,atlas) g x A /\
              &2048 * C pow 4 <= D /\ D < mfd_scalar atlas g y
              ==> ?gamma s0 s1.
                    apx_shortest (top,atlas) g gamma (&0) (&1) /\
                    (!t. t IN real_interval[&0,&1]
                         ==> mfd_speed atlas g gamma (&0) (&1) t =
                             mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))) /\
                    &0 < mfd_scalar atlas g (gamma(&0)) /\
                    mfd_scalar atlas g (gamma(&0)) <= &16 * C /\
                    D <= &4 * C * mfd_scalar atlas g (gamma(&1)) /\
                    mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1)) <= A + &5 * C / eps /\
                    &0 < s0 /\ s0 < s1 /\ s1 < &1 /\
                    mfd_scalar atlas g (gamma s0) = &32 * C pow 2 /\
                    mfd_scalar atlas g (gamma s1) =
                    mfd_scalar atlas g (gamma(&1)) / (&2 * C) /\
                    (!s. s0 <= s /\ s <= s1
                         ==> &32 * C pow 2 <= mfd_scalar atlas g (gamma s) /\
                             mfd_scalar atlas g (gamma s) <=
                             mfd_scalar atlas g (gamma(&1)) / (&2 * C)) /\
                    (!s. s0 < s /\ s <= &1
                         ==> &32 * C pow 2 < mfd_scalar atlas g (gamma s)) /\
                    (!s. s0 <= s /\ s <= s1 ==> ?e. NK (gamma s) e) /\
                    (!s e v. s0 <= s /\ s <= s1 /\ rfs_neck (top,atlas) g eps (gamma s) e /\
                             v IN IMAGE e (apx_slab (--inv(&2 * eps)) (inv(&2 * eps)))
                             ==> ?e'. NK v e')`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2BT_TAIL_CLAIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tc"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BT_WINDOW_NECKS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wn"))) THEN
  MP_TAC(SPEC `u:A->bool` P2BT_P1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "p1"))) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `A:real`; `top:A topology`;
                       `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `NK:A->(real^3->A)->bool`; `x:A`; `y:A`; `D:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BT_C_POWERS) THEN
  USE_THEN "tc" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `A:real`; `top:A topology`;
     `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
     `NK:A->(real^3->A)->bool`; `x:A`; `y:A`; `D:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `rp = mfd_scalar atlas (g:A->real^3^3) (gamma(&0))` THEN
  ABBREV_TAC `rq = mfd_scalar atlas (g:A->real^3^3) (gamma(&1))` THEN
  SUBGOAL_THEN `&512 * C pow 3 <= rq` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &4 * C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ th)]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C pow 3 /\ &0 < rq /\ rq <= C * rq /\ C * rp <= &16 * C pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `C * rp <= C * &16 * C` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * rq / (&2 * C) = rq / &2 /\ &2 * C * rq / (&2 * C) = rq`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&32 * C pow 2 < rq / (&2 * C) /\ rq / (&2 * C) < rq` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `gamma:real->A`; `&32 * C pow 2`; `rq / (&2 * C)`]
    P2BT_GAMMA_WINDOW) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
      SIMP_TAC[apx_shortest];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`s0:real`; `s1:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w. w IN topspace top /\ &4 <= mfd_scalar atlas (g:A->real^3^3) w
        ==> (?e. (NK:A->(real^3->A)->bool) w e) \/
            (?U Y. rfs_cap (top,atlas) g C eps U Y /\ w IN Y) \/
            (?U. w IN U /\ rfs_c_component (top,atlas) g C U) \/
            (?U. w IN U /\ rfs_round_component (top,atlas) g eps U)`
  (LABEL_TAC "can") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "wn" (MP_TAC o SPECL
      [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
       `g:A->real^3^3`; `eps:real`; `NK:A->(real^3->A)->bool`; `gamma:real->A`;
       `&32 * C pow 2`; `rq / (&2 * C)`; `s0:real`; `s1:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      X_GEN_TAC `w:A` THEN STRIP_TAC THEN USE_THEN "can" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `e:real^3->A`; `v:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&32 * C pow 2 <= mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s) /\
                mfd_scalar atlas g (gamma s) <= rq / (&2 * C)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `!s. s0 <= s /\ s <= s1
                     ==> &32 * C pow 2 <= mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s) /\
                         mfd_scalar atlas g (gamma s) <= rq / (&2 * C)` THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "p1" (MP_TAC o SPECL
    [`C:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
     `g:A->real^3^3`; `eps:real`; `NK:A->(real^3->A)->bool`; `gamma:real->A`;
     `&32 * C pow 2`; `rq / (&2 * C)`; `s:real`; `e:real^3->A`; `v:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `w:A` THEN STRIP_TAC THEN USE_THEN "can" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The approximating sequence.  The failure hypothesis of                    *)
(* P2B_BAD_TUBE_FROM_FAILURE_STATEMENT (p2bt_fail, verbatim) with D0 = n+1   *)
(* and D = 2048 C^4 + n + 1 gives views V0 n, times t n and points x n, y n; *)
(* V n is V0 n rescaled at t n by Q n = R(x n) (so R(x n) = 1 at time 0),    *)
(* and P2BT_TUBE_ONE in the time-0 slice of V n, with NK = strong eps-necks  *)
(* of V n at time 0, gives the minimizer gamma n, the window [s0 n,s1 n] and *)
(* the window necks EN n s (p2bt_approx).                                    *)
(* ========================================================================= *)

let p2bt_fail = new_definition
 `p2bt_fail (u:A->bool) (eps:real) (C:real) (A:real) <=>
    (!D0 D. &0 < D0 /\ &0 < D
            ==> ?V x t y.
                   p2c_regular_view (V:(real->A topology)#
                                       (real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) /\
                   rfs_pinched V /\ (!s. s < &0 ==> rfs_vtop V s = discrete_topology {}) /\
                   (!s. apx_sphere_sep (rfs_vtop V s) (rfs_vatlas V s)) /\
                   x IN topspace(rfs_vtop V t) /\
                   (!y' s. s <= t /\ y' IN topspace(rfs_vtop V s) /\
                           &4 * rfs_vscalar V t x <= rfs_vscalar V s y'
                           ==> p3_canon_at V C eps y' s) /\
                   D0 <= rfs_vscalar V t x /\
                   y IN rfs_vball V t x (A * inv(sqrt(rfs_vscalar V t x))) /\
                   D * rfs_vscalar V t x < rfs_vscalar V t y)`;;

let P2BT_VBALL_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    t x r.
     rfs_vball V t x r = mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vball; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2BT_STRONG_NECK_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t e.
     rfs_strong_neck V eps x t e
     ==> rfs_neck (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps x e`,
  SIMP_TAC[rfs_strong_neck; P2B9_EVOLVING_NECK_ALT]);;

(* One failure, rescaled to R(x) = 1 at time 0. *)

let P2BT_NORMALIZE = prove
 (`!(V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps A x t y D Q V.
     p2c_regular_view V0 /\
     (!s. apx_sphere_sep (rfs_vtop V0 s) (rfs_vatlas V0 s)) /\
     x IN topspace(rfs_vtop V0 t) /\
     (!y' s. s <= t /\ y' IN topspace(rfs_vtop V0 s) /\
             &4 * rfs_vscalar V0 t x <= rfs_vscalar V0 s y'
             ==> p3_canon_at V0 C eps y' s) /\
     &0 < rfs_vscalar V0 t x /\
     y IN rfs_vball V0 t x (A * inv(sqrt(rfs_vscalar V0 t x))) /\
     D * rfs_vscalar V0 t x < rfs_vscalar V0 t y /\
     Q = rfs_vscalar V0 t x /\ V = p2b_rescale_view V0 t Q
     ==> p2c_regular_view V /\
         hausdorff_space (rfs_vtop V (&0)) /\
         smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
         riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
         apx_sphere_sep (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
         x IN topspace (rfs_vtop V (&0)) /\
         mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x = &1 /\
         (!w. w IN topspace (rfs_vtop V (&0)) /\
              &4 <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w
              ==> p3_canon_at V C eps w (&0)) /\
         y IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) x A /\
         D < mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[P2BT_RESCALE_SLICE0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[P2B9_RFS_VSCALAR; P2BT_VBALL_ALT]) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2c_regular_view]) THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V0:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                    (rfs_vmetric V0 t) x` THEN
  UNDISCH_THEN `Q:real = R` SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[P2BK_REGULAR_VIEW_RESCALE; RIEMANNIAN_METRIC_CMUL] THEN
  SUBGOAL_THEN
   `!w. w IN topspace (rfs_vtop (V0:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
        ==> mfd_scalar (rfs_vatlas V0 t) (\y. R %% rfs_vmetric V0 t y) w =
            mfd_scalar (rfs_vatlas V0 t) (rfs_vmetric V0 t) w / R`
  (LABEL_TAC "sc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BCS_SCALAR_CMUL THEN
    EXISTS_TAC `rfs_vtop (V0:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace (rfs_vtop (V0:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN mfd_ball (rfs_vtop V0 t,rfs_vatlas V0 t)
                   (rfs_vmetric (V0:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) x
                   (A * inv(sqrt R))` THEN
    REWRITE_TAC[mfd_ball; mfd_joinable; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real->A` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V0:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t`;
                          `&0`; `&1`] THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_LT_RDIV_EQ] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `w:A` THEN STRIP_TAC THEN MATCH_MP_TAC P2BT_CANON_RESCALE THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `&4 <= mfd_scalar (rfs_vatlas (V0:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                   (\y. R %% rfs_vmetric V0 t y) (w:A)` THEN
    USE_THEN "sc" (fun th -> ASM_SIMP_TAC[th; REAL_LE_RDIV_EQ]);
    ASM_SIMP_TAC[MFD_BALL_SCALE; ETA_AX] THEN
    UNDISCH_TAC `(y:A) IN mfd_ball (rfs_vtop V0 t,rfs_vatlas V0 t)
                   (rfs_vmetric (V0:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) x
                   (A * inv(sqrt R))` THEN
    REWRITE_TAC[real_div]]);;

(* The data of one approximant (index n) and of the sequence. *)

let p2bt_one = new_definition
 `p2bt_one (eps:real) (C:real) (A:real) (n:num)
    (V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (t:real) (Q:real)
    (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (gamma:real->A) (s0:real) (s1:real) (EN:real->real^3->A) <=>
    V = p2b_rescale_view V0 t Q /\
    p2c_regular_view V0 /\ rfs_pinched V0 /\
    (!s. s < &0 ==> rfs_vtop V0 s = discrete_topology {}) /\
    &0 <= t /\ &n + &1 <= Q /\
    p2c_regular_view V /\
    hausdorff_space (rfs_vtop V (&0)) /\
    smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
    riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
    apx_sphere_sep (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
    apx_shortest (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) gamma (&0) (&1) /\
    (!s. s IN real_interval[&0,&1]
         ==> mfd_speed (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) gamma (&0) (&1) s =
             mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                      (gamma(&0)) (gamma(&1))) /\
    &0 < mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) /\
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) <= &16 * C /\
    &2048 * C pow 4 + &n + &1 <=
    &4 * C * mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&1)) /\
    mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
             (gamma(&0)) (gamma(&1)) <= A + &5 * C / eps /\
    &0 < s0 /\ s0 < s1 /\ s1 < &1 /\
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s0) = &32 * C pow 2 /\
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s1) =
    mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&1)) / (&2 * C) /\
    (!s. s0 <= s /\ s <= s1
         ==> &32 * C pow 2 <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) /\
             mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) <=
             mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&1)) / (&2 * C)) /\
    (!s. s0 < s /\ s <= &1
         ==> &32 * C pow 2 < mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s)) /\
    (!s. s0 <= s /\ s <= s1 ==> rfs_strong_neck V eps (gamma s) (&0) (EN s)) /\
    (!s e v. s0 <= s /\ s <= s1 /\
             rfs_neck (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) eps
                      (gamma s) e /\
             v IN IMAGE e (apx_slab (--inv(&2 * eps)) (inv(&2 * eps)))
             ==> ?e'. rfs_strong_neck V eps v (&0) e')`;;

let p2bt_approx = new_definition
 `p2bt_approx (eps:real) (C:real) (A:real)
    (V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (t:num->real) (Q:num->real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (gamma:num->real->A) (s0:num->real) (s1:num->real) (EN:num->real->real^3->A) <=>
    !n. p2bt_one eps C A n (V0 n) (t n) (Q n) (V n) (gamma n) (s0 n) (s1 n) (EN n)`;;

(* One approximant from one failure. *)

let P2BT_APPROX_ONE = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u /\ P2BT_REQ_A21_CH_STATEMENT u /\
     APX_A8_CS_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A n V0 x t y.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\
              p2c_regular_view (V0:(real->A topology)#
                                   (real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) /\
              rfs_pinched V0 /\ (!s. s < &0 ==> rfs_vtop V0 s = discrete_topology {}) /\
              (!s. apx_sphere_sep (rfs_vtop V0 s) (rfs_vatlas V0 s)) /\
              x IN topspace(rfs_vtop V0 t) /\
              (!y' s. s <= t /\ y' IN topspace(rfs_vtop V0 s) /\
                      &4 * rfs_vscalar V0 t x <= rfs_vscalar V0 s y'
                      ==> p3_canon_at V0 C eps y' s) /\
              &n + &1 <= rfs_vscalar V0 t x /\
              y IN rfs_vball V0 t x (A * inv(sqrt(rfs_vscalar V0 t x))) /\
              (&2048 * C pow 4 + &n + &1) * rfs_vscalar V0 t x < rfs_vscalar V0 t y
              ==> ?gamma s0 s1 EN.
                    p2bt_one eps C A n V0 t (rfs_vscalar V0 t x)
                             (p2b_rescale_view V0 t (rfs_vscalar V0 t x))
                             gamma s0 s1 EN`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_TUBE_ONE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "one"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `x:A`; `t:real`; `y:A`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Q = rfs_vscalar (V0:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x` THEN
  ABBREV_TAC `V = p2b_rescale_view (V0:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t Q` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(t < &0) ==> &0 <= t`) THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:A) IN topspace(rfs_vtop (V0:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)` THEN
    ASM_SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)`;
                 `C:real`; `eps:real`; `A:real`; `x:A`; `t:real`; `y:A`;
                 `&2048 * C pow 4 + &n + &1`; `Q:real`;
                 `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`] P2BT_NORMALIZE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "one" (MP_TAC o SPECL
    [`C:real`; `eps:real`; `A:real`; `rfs_vtop (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vatlas (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `rfs_vmetric (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
     `\w e. rfs_strong_neck (V:(real->A topology)#
       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) eps w (&0) e`;
     `x:A`; `y:A`; `&2048 * C pow 4 + &n + &1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[P2BT_STRONG_NECK_SLICE];
      X_GEN_TAC `w:A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:A` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[p3_canon_at; P2BT_STRONG_CANONICAL_ALT] THEN
      MESON_TAC[];
      SUBGOAL_THEN `&1 <= C pow 4` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` (X_CHOOSE_THEN `s0:real`
    (X_CHOOSE_THEN `s1:real` (STRIP_ASSUME_TAC o REWRITE_RULE[])))) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM] o
    check (fun th -> can (find_term ((=) `s0:real`)) (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck"))
                         (concl th) && is_forall (concl th) &&
                     not (can (find_term ((=) `apx_slab`)) (concl th)))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `EN:real->real^3->A`) THEN
  MAP_EVERY EXISTS_TAC [`gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] THEN
  REWRITE_TAC[p2bt_one] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The approximating sequence from the failure hypothesis. *)

let P2BT_SEQ_EXISTS = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u /\ P2BT_REQ_A21_CH_STATEMENT u /\
     APX_A8_CS_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\ p2bt_fail u eps C A
                     ==> ?V0 t Q V (gamma:num->real->A) s0 s1 EN.
                           p2bt_approx eps C A V0 t Q V gamma s0 s1 EN`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BT_APPROX_ONE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "one"))) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2bt_fail (u:A->bool) eps C A` THEN REWRITE_TAC[p2bt_fail] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPECL [`&n + &1`; `&2048 * C pow 4 + &n + &1`]) THEN
  SUBGOAL_THEN `!n. &0 < &n + &1 /\ &0 < &2048 * C pow 4 + &n + &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN SUBGOAL_THEN `&0 <= C pow 4` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`
    (X_CHOOSE_THEN `x:num->A` (X_CHOOSE_THEN `t:num->real`
      (X_CHOOSE_THEN `y:num->A` (LABEL_TAC "f"))))) THEN
  SUBGOAL_THEN
   `!n. ?gamma s0 s1 EN.
          p2bt_one eps C A n
            ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) n) (t n)
            (rfs_vscalar (V0 n) (t n) ((x:num->A) n))
            (p2b_rescale_view (V0 n) (t n) (rfs_vscalar (V0 n) (t n) (x n)))
            gamma s0 s1 EN`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "one" MATCH_MP_TAC THEN EXISTS_TAC `(y:num->A) n` THEN
    USE_THEN "f" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:num->real->A` (X_CHOOSE_THEN `s0:num->real`
    (X_CHOOSE_THEN `s1:num->real` (X_CHOOSE_TAC `EN:num->real->real^3->A`)))) THEN
  MAP_EVERY EXISTS_TAC
   [`V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `t:num->real`;
    `\n. rfs_vscalar ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) n) (t n) ((x:num->A) n)`;
    `\n. p2b_rescale_view ((V0:num->(real->A topology)#
                                  (real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) n) (t n)
                          (rfs_vscalar (V0 n) (t n) ((x:num->A) n))`;
    `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`] THEN
  ASM_REWRITE_TAC[p2bt_approx]);;

(* ========================================================================= *)
(* The cut A1 of MT p. 251 with a blow-up subsequence, for abstract          *)
(* profiles.  rho n a is the curvature at arc length a along the window of   *)
(* the n-th minimizer (0 <= a <= len n).  A1 is the supremum of the A for    *)
(* which rho is bounded on [0,A] uniformly in n; along a subsequence, the    *)
(* maximum of rho on [0, A1 + 1/(j+1)] tends to infinity for every j        *)
(* (needed for: moderate necks do not reach the cut, in the limit).          *)
(* ========================================================================= *)

let P2BT_FINITE_MAX = prove
 (`!(B:num->real) N. ?K. !n. n < N ==> B n <= K`,
  GEN_TAC THEN INDUCT_TAC THENL
   [EXISTS_TAC `&0` THEN REWRITE_TAC[LT];
    FIRST_X_ASSUM(X_CHOOSE_TAC `K:real`) THEN EXISTS_TAC `max K ((B:num->real) N)` THEN
    REWRITE_TAC[LT] THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

let P2BT_CUT_ABSTRACT = prove
 (`!(rho:num->real->real) len a0 K0 Lmax.
     &0 < a0 /\
     (!n. &0 <= len n /\ len n <= Lmax) /\
     (!n. ?B. !a. &0 <= a /\ a <= len n ==> rho n a <= B) /\
     (!M. ?n. M < rho n (len n)) /\
     (!n a. &0 <= a /\ a <= a0 /\ a <= len n ==> rho n a <= K0)
     ==> ?sub A1. p3_subseq sub /\ a0 <= A1 /\ A1 <= Lmax /\
                  (!A. A < A1 ==> ?K. !k a. &0 <= a /\ a <= A /\ a <= len (sub k)
                                            ==> rho (sub k) a <= K) /\
                  (!j M. ?N. !k. N <= k
                                 ==> ?a. &0 <= a /\ a <= len (sub k) /\
                                         a <= A1 + inv(&j + &1) /\ M < rho (sub k) a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "len")
    (CONJUNCTS_THEN2 (LABEL_TAC "bd") (CONJUNCTS_THEN2 (LABEL_TAC "unb") (LABEL_TAC "low"))))) THEN
  ABBREV_TAC `Fs = {A | &0 <= A /\
                        ?K. !n a. &0 <= a /\ a <= A /\ a <= len n
                                  ==> (rho:num->real->real) n a <= K}` THEN
  SUBGOAL_THEN `(a0:real) IN Fs` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; EXISTS_TAC `K0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A. A IN Fs ==> A < Lmax` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `A:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `K:real`)) THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "unb" (X_CHOOSE_TAC `n:num` o SPEC `K:real`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `(len:num->real) n`]) THEN
    USE_THEN "len" (MP_TAC o SPEC `n:num`) THEN
    UNDISCH_TAC `K < (rho:num->real->real) n (len n)` THEN UNDISCH_TAC `Lmax <= A` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Fs:real->bool = {}) /\ (?b. !x. x IN Fs ==> x <= b)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `Lmax:real` THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUP o CONJ (ASSUME `~(Fs:real->bool = {})`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  ABBREV_TAC `A1 = sup(Fs:real->bool)` THEN
  SUBGOAL_THEN `a0 <= A1 /\ A1 <= Lmax` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!A. A < A1 ==> ?K. !n a. &0 <= a /\ a <= A /\ a <= len n
                             ==> (rho:num->real->real) n a <= K`
  (LABEL_TAC "prof") THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`Fs:real->bool`; `A:real`] SUP_APPROACH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `A':real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(A':real) IN Fs` THEN EXPAND_TAC "Fs" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `K:real` o CONJUNCT2) THEN EXISTS_TAC `K:real` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "bd" (MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num->real` (LABEL_TAC "B")) THEN
  SUBGOAL_THEN
   `!k N. ?n. N <= n /\
              ?a. &0 <= a /\ a <= A1 + inv(&k + &1) /\ a <= len n /\
                  &k < (rho:num->real->real) n a`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `N:num`] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!n a. N <= n /\ &0 <= a /\ a <= A1 + inv(&k + &1) /\ a <= (len:num->real) n
            ==> (rho:num->real->real) n a <= &k`
    (LABEL_TAC "nb") THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC
       `~(?n. N <= n /\
              ?a. &0 <= a /\ a <= A1 + inv(&k + &1) /\ a <= (len:num->real) n /\
                  &k < (rho:num->real->real) n a)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`B:num->real`; `N:num`] P2BT_FINITE_MAX) THEN
    DISCH_THEN(X_CHOOSE_TAC `K1:real`) THEN
    SUBGOAL_THEN `A1 + inv(&k + &1) IN Fs` MP_TAC THENL
     [EXPAND_TAC "Fs" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_INV THEN MP_TAC(SPEC `k:num` REAL_POS) THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      EXISTS_TAC `max K1 (&k)` THEN MAP_EVERY X_GEN_TAC [`n:num`; `a:real`] THEN
      STRIP_TAC THEN ASM_CASES_TAC `n:num < N` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B:num->real) n` THEN CONJ_TAC THENL
         [USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k` THEN CONJ_TAC THENL
         [USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          REAL_ARITH_TAC]];
      DISCH_TAC THEN
      SUBGOAL_THEN `A1 + inv(&k + &1) <= A1` MP_TAC THENL
       [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `&k + &1` REAL_LT_INV) THEN MP_TAC(SPEC `k:num` REAL_POS) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `G:num->num->num` (LABEL_TAC "G")) THEN
  MP_TAC(ISPECL [`(G:num->num->num) 0 0`; `\x n. (G:num->num->num) (SUC n) (x + 1)`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k. ?a. &0 <= a /\ a <= A1 + inv(&k + &1) /\ a <= len((sub:num->num) k) /\
            &k < (rho:num->real->real) (sub k) a`
  (LABEL_TAC "sp") THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "G" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `p3_subseq (sub:num->num)` ASSUME_TAC THENL
   [REWRITE_TAC[p3_subseq] THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    CONJ_TAC THENL [MESON_TAC[LT_TRANS]; ALL_TAC] THEN GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "G" (MP_TAC o CONJUNCT1 o SPECL [`SUC n`; `(sub:num->num) n + 1`]) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `A1:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "prof" (X_CHOOSE_TAC `K:real` o C MATCH_MP (ASSUME `A:real < A1`)) THEN
    EXISTS_TAC `K:real` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `M:real`] THEN
  X_CHOOSE_TAC `m:num` (SPEC `M:real` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `j + m:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "sp" (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `A1 + inv(&k + &1)` THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&k` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&m` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* Facts about one approximant (the minimizer has constant speed L > 0, so   *)
(* d(gamma a, gamma b) = (b - a) L, and R is bounded along it), the first    *)
(* window neck (R <= 3/2 lo up to arc length 9/10 h/eps from the window      *)
(* start), and the cut for the approximating sequence.                       *)
(* ========================================================================= *)

let P2BT_SCALAR_CURVE_CONT = prove
 (`!top atlas (g:A->real^3^3) gamma.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1)
     ==> continuous_map (subtopology euclideanreal (real_interval[&0,&1]),euclideanreal)
                        (\s. mfd_scalar atlas g (gamma s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s)) =
                mfd_scalar atlas g o gamma`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A)
                              (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]]);;

let P2BT_SCALAR_CURVE_BOUNDED = prove
 (`!top atlas (g:A->real^3^3) gamma.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1)
     ==> ?B. !s. s IN real_interval[&0,&1] ==> abs(mfd_scalar atlas g (gamma s)) <= B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_SCALAR_CURVE_CONT o
    CONJ (ASSUME `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`) o
    CONJ (ASSUME `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\s. mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s))
                                    (real_interval[&0,&1]))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL; SUBSET_REFL];
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE]]);;

(* Unfolding p2bt_one puts V = p2b_rescale_view V0 t Q among the           *)
(* assumptions, where ASM_REWRITE_TAC would rewrite V; this tactic drops it. *)

let p2bt_drop_rescale_eq_tac : tactic =
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_rescale_view")) (concl th)));;

(* The minimizer of an approximant: constant speed L > 0. *)

let P2BT_ONE_DIST = prove
 (`!eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) gamma s0 s1 EN.
     &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN
     ==> &0 < mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                       (gamma(&0)) (gamma(&1)) /\
         mfd_c1_curve (rfs_vtop V (&0),rfs_vatlas V (&0)) gamma (&0) (&1) /\
         (!a b. &0 <= a /\ a <= b /\ b <= &1
                ==> mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (gamma a) (gamma b) /\
                    mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                             (gamma a) (gamma b) =
                    (b - a) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                       (gamma(&0)) (gamma(&1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  SUBGOAL_THEN `mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                              (gamma:real->A) (&0) (&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
    SIMP_TAC[apx_shortest];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a b. &0 <= a /\ a <= b /\ b <= &1
          ==> mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                           ((gamma:real->A) a) (gamma b) /\
              mfd_dist (top,atlas) (g:A->real^3^3) (gamma a) (gamma b) =
              (b - a) * mfd_dist (top,atlas) g (gamma(&0)) (gamma(&1))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `a:real = b` THENL
     [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] MFD_C1_CURVE_IN_TOPSPACE) THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `&0`; `&1`] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `gamma:real->A`; `a:real`; `b:real`] P2BT_CS_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    UNDISCH_TAC `apx_shortest (top,atlas) (g:A->real^3^3) gamma (&0) (&1)` THEN
    REWRITE_TAC[apx_shortest] THEN DISCH_THEN(MP_TAC o SPECL [`a:real`; `b:real`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((gamma:real->A)(&0) = gamma(&1))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                   ((gamma:real->A)(&0)) <= &16 * C` THEN
    UNDISCH_TAC `&2048 * C pow 4 + &n + &1 <=
                 &4 * C * mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                                     ((gamma:real->A)(&1))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BT_C_POWERS) THEN
    ABBREV_TAC `r = mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
                      ((gamma:real->A)(&1))` THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `C * r <= C * &16 * C` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `&1`]) THEN
  REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(gamma:real->A)(&0)`; `(gamma:real->A)(&1)`] MFD_DIST_EQ_0) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(gamma:real->A)(&0)`; `(gamma:real->A)(&1)`] MFD_DIST_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The first window neck: points of the minimizer within arc length         *)
(* 9/10 h/eps of the window start gamma(s0) (h = lo^(-1/2), lo = 32 C^2)    *)
(* lie in the neck EN s0, so R is there between lo/2 and 3 lo/2.            *)

let P2BT_FIRST_NECK = prove
 (`?eps1. &0 < eps1 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) gamma s0 s1 EN s.
        &0 < eps /\ eps <= eps1 /\ &1 < C /\
        p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= s /\ s <= &1 /\
        (s - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                            (gamma(&0)) (gamma(&1))
        < &9 / &10 * inv(sqrt(&32 * C pow 2)) * inv eps
        ==> gamma s IN IMAGE (EN s0) (rfs_neck_dom eps) /\
            &32 * C pow 2 / &2 <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) /\
            mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) <=
            &3 / &2 * &32 * C pow 2`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_R) THEN
  EXISTS_TAC `min e0 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((gamma:real->A) s0) ((EN:real->real^3->A) s0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`;
                   `eps:real`; `(gamma:real->A) s0`; `&0`; `(EN:real->real^3->A) s0`]
      P2BT_STRONG_NECK_SLICE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th) &&
      not (can (find_term ((=) `v:A`)) (concl th)))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  UNDISCH_TAC `(gamma:real->A) s0 IN IMAGE ((EN:real->real^3->A) s0) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps /\ apx_sval z = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s IN IMAGE ((EN:real->real^3->A) s0) (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_NECK_EXIT_BALL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `(gamma:real->A) s0`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps <= e0 /\ eps <= e2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                    `g:A->real^3^3`; `eps:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    REWRITE_TAC[apx_ch_ctx] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "dist" (MP_TAC o SPECL [`s0:real`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&32 * C pow 2)) * inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(gamma:real->A) s IN IMAGE ((EN:real->real^3->A) s0) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "nr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(gamma:real->A) s0`; `(EN:real->real^3->A) s0`;
    `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  TRY(EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REAL_ARITH_TAC);;

(* The cut in window-parameter form: f n s is the curvature at gamma n s,  *)
(* the arc length from the window start is (s - s0 n) L n.                  *)

let P2BT_CUT_S = prove
 (`!(f:num->real->real) s0 s1 L a0 K0 Lmax.
     &0 < a0 /\
     (!n. &0 < L n /\ s0 n <= s1 n /\ (s1 n - s0 n) * L n <= Lmax) /\
     (!n. ?B. !s. s0 n <= s /\ s <= s1 n ==> f n s <= B) /\
     (!M. ?n. M < f n (s1 n)) /\
     (!n s. s0 n <= s /\ s <= s1 n /\ (s - s0 n) * L n <= a0 ==> f n s <= K0)
     ==> ?sub A1.
           p3_subseq sub /\ a0 <= A1 /\ A1 <= Lmax /\
           (!A. A < A1
                ==> ?K. !k s. s0 (sub k) <= s /\ s <= s1 (sub k) /\
                              (s - s0 (sub k)) * L (sub k) <= A
                              ==> f (sub k) s <= K) /\
           (!j M. ?N. !k. N <= k
                          ==> ?s. s0 (sub k) <= s /\ s <= s1 (sub k) /\
                                  (s - s0 (sub k)) * L (sub k) <= A1 + inv(&j + &1) /\
                                  M < f (sub k) s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "w")
    (CONJUNCTS_THEN2 (LABEL_TAC "bd") (CONJUNCTS_THEN2 (LABEL_TAC "unb") (LABEL_TAC "low"))))) THEN
  SUBGOAL_THEN `!n a. &0 <= a /\ a <= ((s1:num->real) n - s0 n) * (L:num->real) n
                      ==> s0 n <= s0 n + a / L n /\ s0 n + a / L n <= s1 n /\
                          ((s0 n + a / L n) - s0 n) * L n = a`
  (LABEL_TAC "par") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "w" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `s0 + x <= s1 <=> x <= s1 - s0`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
      UNDISCH_TAC `&0 < (L:num->real) n` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n s. s0 n <= s /\ s <= (s1:num->real) n
                      ==> &0 <= (s - s0 n) * (L:num->real) n /\
                          (s - s0 n) * L n <= (s1 n - s0 n) * L n /\
                          s0 n + ((s - s0 n) * L n) / L n = s`
  (LABEL_TAC "pos") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "w" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < (L:num->real) n` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n a. (f:num->real->real) n ((s0:num->real) n + a / (L:num->real) n)`;
    `\n. ((s1:num->real) n - (s0:num->real) n) * (L:num->real) n`;
    `a0:real`; `K0:real`; `Lmax:real`] P2BT_CUT_ABSTRACT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "w" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN USE_THEN "bd" (X_CHOOSE_TAC `B:real` o SPEC `n:num`) THEN
      EXISTS_TAC `B:real` THEN X_GEN_TAC `a:real` THEN DISCH_TAC THEN
      USE_THEN "par" (MP_TAC o SPECL [`n:num`; `a:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `M:real` THEN USE_THEN "unb" (X_CHOOSE_TAC `n:num` o SPEC `M:real`) THEN
      EXISTS_TAC `n:num` THEN
      USE_THEN "w" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      SUBGOAL_THEN `(s0:num->real) n + (((s1:num->real) n - s0 n) * (L:num->real) n) / L n =
                    s1 n` (fun th -> ASM_REWRITE_TAC[th]) THEN
      UNDISCH_TAC `&0 < (L:num->real) n` THEN CONV_TAC REAL_FIELD;
      MAP_EVERY X_GEN_TAC [`n:num`; `a:real`] THEN STRIP_TAC THEN
      USE_THEN "par" (MP_TAC o SPECL [`n:num`; `a:real`]) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "low" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `A1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "prof") (LABEL_TAC "blow"))))))) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `A1:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `A:real` THEN DISCH_TAC THEN
    USE_THEN "prof" (X_CHOOSE_TAC `K:real` o C MATCH_MP (ASSUME `A:real < A1`)) THEN
    EXISTS_TAC `K:real` THEN MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "pos" (MP_TAC o SPECL [`(sub:num->num) k`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`;
      `(s - (s0:num->real) ((sub:num->num) k)) * (L:num->real) (sub k)`]) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`j:num`; `M:real`] THEN
    USE_THEN "blow" (X_CHOOSE_TAC `N:num` o SPECL [`j:num`; `M:real`]) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "par" (MP_TAC o SPECL [`(sub:num->num) k`; `a:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    EXISTS_TAC `(s0:num->real) ((sub:num->num) k) + a / (L:num->real) (sub k)` THEN
    ASM_REWRITE_TAC[]]);;

(* The cut for the approximating sequence (MT p. 251): A1 is at least      *)
(* 4/5 h/eps (the first window neck) and at most A + 5C/eps (the length of *)
(* the minimizers); below A1 the curvature along the windows is bounded     *)
(* uniformly in n, and along a subsequence it blows up within A1 + 1/(j+1). *)

let P2BT_CUT = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) gamma s0 s1 EN.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN
        ==> ?sub A1.
              p3_subseq sub /\
              &4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps <= A1 /\
              A1 <= A + &5 * C / eps /\
              (!A'. A' < A1
                    ==> ?K. !k s. s0 (sub k) <= s /\ s <= s1 (sub k) /\
                                  (s - s0 (sub k)) *
                                  mfd_dist (rfs_vtop (V (sub k)) (&0),rfs_vatlas (V (sub k)) (&0))
                                           (rfs_vmetric (V (sub k)) (&0))
                                           (gamma (sub k) (&0)) (gamma (sub k) (&1)) <= A'
                                  ==> mfd_scalar (rfs_vatlas (V (sub k)) (&0))
                                                 (rfs_vmetric (V (sub k)) (&0))
                                                 (gamma (sub k) s) <= K) /\
              (!j M. ?N. !k. N <= k
                             ==> ?s. s0 (sub k) <= s /\ s <= s1 (sub k) /\
                                     (s - s0 (sub k)) *
                                     mfd_dist (rfs_vtop (V (sub k)) (&0),
                                               rfs_vatlas (V (sub k)) (&0))
                                              (rfs_vmetric (V (sub k)) (&0))
                                              (gamma (sub k) (&0)) (gamma (sub k) (&1))
                                     <= A1 + inv(&j + &1) /\
                                     M < mfd_scalar (rfs_vatlas (V (sub k)) (&0))
                                                    (rfs_vmetric (V (sub k)) (&0))
                                                    (gamma (sub k) s))`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fn"))
    (INST_TYPE [`:A`,`:A`] P2BT_FIRST_NECK) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. p2bt_one eps C A n ((V0:num->(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                  ((t:num->real) n) ((Q:num->real) n)
                  ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) n)
                  ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
                  ((EN:num->real->real^3->A) n)`
  (LABEL_TAC "one") THENL [ASM_MESON_TAC[p2bt_approx]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BT_C_POWERS) THEN
  MP_TAC(ISPECL
   [`\n s. mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0))
             (rfs_vmetric (V n) (&0)) ((gamma:num->real->A) n s)`;
    `s0:num->real`; `s1:num->real`;
    `\n. mfd_dist (rfs_vtop ((V:num->(real->A topology)#
           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0),
           rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))
           ((gamma:num->real->A) n (&0)) (gamma n (&1))`;
    `&4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps`; `&3 / &2 * &32 * C pow 2`;
    `A + &5 * C / eps`] P2BT_CUT_S) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&32 * C pow 2)) * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    GEN_TAC THEN USE_THEN "one" (fun th ->
      MP_TAC(MATCH_MP P2BT_ONE_DIST (CONJ (ASSUME `&1 < C`) (SPEC `n:num` th))) THEN
      MP_TAC(SPEC `n:num` th)) THEN
    REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist (rfs_vtop ((V:num->(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0),
                  rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))
                  ((gamma:num->real->A) n (&0)) (gamma n (&1))` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN USE_THEN "one" (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
    MP_TAC(ISPECL [`rfs_vtop ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)`;
                   `rfs_vatlas ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)`;
                   `rfs_vmetric ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)`;
                   `(gamma:num->real->A) n`] P2BT_SCALAR_CURVE_BOUNDED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `apx_shortest (rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0),
                     rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))
                     ((gamma:num->real->A) n) (&0) (&1)` THEN
      SIMP_TAC[apx_shortest];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= B ==> x <= B`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `M:real` THEN
    X_CHOOSE_TAC `m:num` (SPEC `&8 * C pow 2 * M` REAL_ARCH_SIMPLE) THEN
    EXISTS_TAC `m:num` THEN USE_THEN "one" (MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `r = mfd_scalar (rfs_vatlas ((V:num->(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) m) (&0))
                      (rfs_vmetric (V m) (&0)) ((gamma:num->real->A) m (&1))` THEN
    SUBGOAL_THEN `&0 < &2 * C /\ &0 < &4 * C` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LT_LMUL_EQ (ASSUME `&0 < &4 * C`))] THEN
    MP_TAC(SPEC `m:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real`] THEN STRIP_TAC THEN
    USE_THEN "fn" (MP_TAC o SPECL
      [`eps:real`; `C:real`; `A:real`; `n:num`;
       `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) n`;
       `(t:num->real) n`; `(Q:num->real) n`;
       `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) n`;
       `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
       `(EN:num->real->real^3->A) n`; `s:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "one" (MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Subsequences of the approximating sequence, and Part I up to the cut: the *)
(* failure hypothesis gives an approximating sequence with a cut A1 and a    *)
(* blow-up along the whole (sub)sequence.                                    *)
(* ========================================================================= *)

let P2BT_ONE_MONO = prove
 (`!eps C A m n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) gamma s0 s1 EN.
     p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\ m <= n
     ==> p2bt_one eps C A m V0 t Q V gamma s0 s1 EN`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && is_var(lhand(concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_rescale_view")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&m <= &n` MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BT_APPROX_SUBSEQ = prove
 (`!eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) gamma s0 s1 EN sub.
     p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p3_subseq sub
     ==> p2bt_approx eps C A (\k. V0 (sub k)) (\k. t (sub k)) (\k. Q (sub k))
                     (\k. V (sub k)) (\k. gamma (sub k)) (\k. s0 (sub k)) (\k. s1 (sub k))
                     (\k. EN (sub k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bt_approx; p3_subseq] THEN STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN MATCH_MP_TAC P2BT_ONE_MONO THEN
  EXISTS_TAC `(sub:num->num) k` THEN ASM_REWRITE_TAC[] THEN
  ACCEPT_TAC(SPEC `k:num` (MATCH_MP MONOTONE_BIGGER
    (ASSUME `!m n. m < n ==> (sub:num->num) m < sub n`))));;

let p2bt_cut = new_definition
 `p2bt_cut (eps:real) (C:real) (A:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (gamma:num->real->A) (s0:num->real) (s1:num->real) (A1:real) <=>
    &4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps <= A1 /\
    A1 <= A + &5 * C / eps /\
    (!A'. A' < A1
          ==> ?K. !k s. s0 k <= s /\ s <= s1 k /\
                        (s - s0 k) *
                        mfd_dist (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                 (rfs_vmetric (V k) (&0)) (gamma k (&0)) (gamma k (&1)) <= A'
                        ==> mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                                       (gamma k s) <= K) /\
    (!j M. ?N. !k. N <= k
                   ==> ?s. s0 k <= s /\ s <= s1 k /\
                           (s - s0 k) *
                           mfd_dist (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0))
                                    (rfs_vmetric (V k) (&0)) (gamma k (&0)) (gamma k (&1))
                           <= A1 + inv(&j + &1) /\
                           M < mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                                          (gamma k s))`;;

(* Part I up to the cut. *)

let P2BT_PART1_CUT = prove
 (`!u:A->bool.
     APX_A1_STATEMENT u /\ P2BT_REQ_A21_CH_STATEMENT u /\
     APX_A8_CS_STATEMENT u /\ P2B_APX_A6_CS_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !eps C A. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\ p2bt_fail u eps C A
                     ==> ?V0 t Q V (gamma:num->real->A) s0 s1 EN A1.
                           p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\
                           p2bt_cut eps C A V gamma s0 s1 A1`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP P2BT_SEQ_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "seq"))) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cut"))
    (INST_TYPE [`:A`,`:A`] P2BT_CUT) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `C:real`; `A:real`] THEN STRIP_TAC THEN
  USE_THEN "seq" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`
    (X_CHOOSE_THEN `t:num->real` (X_CHOOSE_THEN `Q:num->real`
      (X_CHOOSE_THEN
        `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`
        (X_CHOOSE_THEN `gamma:num->real->A` (X_CHOOSE_THEN `s0:num->real`
          (X_CHOOSE_THEN `s1:num->real` (X_CHOOSE_TAC `EN:num->real->real^3->A`)))))))) THEN
  USE_THEN "cut" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `A1:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`\k. (V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) ((sub:num->num) k)`;
    `\k. (t:num->real) ((sub:num->num) k)`; `\k. (Q:num->real) ((sub:num->num) k)`;
    `\k. (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) ((sub:num->num) k)`;
    `\k. (gamma:num->real->A) ((sub:num->num) k)`;
    `\k. (s0:num->real) ((sub:num->num) k)`; `\k. (s1:num->real) ((sub:num->num) k)`;
    `\k. (EN:num->real->real^3->A) ((sub:num->num) k)`; `A1:real`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BT_APPROX_SUBSEQ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2bt_cut] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The tube and its cut (MT p. 251).  T is the union of the middle halves of *)
(* the window necks EN s, s0 <= s <= s1; U is T cut by the ball of radius A1 *)
(* about the window start gamma(s0).  Both are open, and every point of U is *)
(* the centre of a strong eps-neck at time 0 (P1).                           *)
(* ========================================================================= *)

let p2bt_tube = new_definition
 `p2bt_tube (eps:real) (EN:real->real^3->A) (s0:real) (s1:real) =
    UNIONS {IMAGE (EN s) (apx_slab (--inv(&2 * eps)) (inv(&2 * eps))) | s | s0 <= s /\ s <= s1}`;;

let p2bt_cutset = new_definition
 `p2bt_cutset (eps:real)
    (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (gamma:real->A) (EN:real->real^3->A) (s0:real) (s1:real) (A1:real) =
    p2bt_tube eps EN s0 s1 INTER
    mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s0) A1`;;

let P2BT_MIDDLE_IN_DOM = prove
 (`!eps. &0 < eps
         ==> apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) SUBSET rfs_neck_dom eps /\
             open(apx_slab (--inv(&2 * eps)) (inv(&2 * eps))) /\
             sphere(vec 0,&1) SUBSET apx_slab (--inv(&2 * eps)) (inv(&2 * eps))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; OPEN_ANNULUS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM apx_slab] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
    REWRITE_TAC[REAL_LE_NEG2] THEN
    SUBGOAL_THEN `inv(&2 * eps) <= inv eps` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < inv(&2 * eps) / sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--inv(&2 * eps) / sqrt(&2) = --(inv(&2 * eps) / sqrt(&2))` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LNEG]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
  ASM_REAL_ARITH_TAC);;

(* Facts about the tube of one approximant. *)

let P2BT_TUBE_FACTS = prove
 (`!eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) gamma s0 s1 EN.
     &0 < eps /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN
     ==> open_in (rfs_vtop V (&0)) (p2bt_tube eps EN s0 s1) /\
         (!s. s0 <= s /\ s <= s1
              ==> rfs_neck (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) eps
                           (gamma s) (EN s) /\
                  gamma s IN IMAGE (EN s) (sphere(vec 0,&1)) /\
                  gamma s IN p2bt_tube eps EN s0 s1) /\
         (!w. w IN p2bt_tube eps EN s0 s1
              ==> ?s y. s0 <= s /\ s <= s1 /\
                        y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\ w = EN s y) /\
         (!w. w IN p2bt_tube eps EN s0 s1 ==> ?e. rfs_strong_neck V eps w (&0) e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BT_MIDDLE_IN_DOM) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  SUBGOAL_THEN
   `!s. s0 <= s /\ s <= s1
        ==> rfs_neck (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) (&0),rfs_vatlas V (&0))
                     (rfs_vmetric V (&0)) eps ((gamma:real->A) s) ((EN:real->real^3->A) s)`
  (LABEL_TAC "nk") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BT_STRONG_NECK_SLICE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_strong_neck")) (concl th) &&
      not (can (find_term ((=) `v:A`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[p2bt_tube] THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`rfs_vatlas (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
                          `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(gamma:real->A) s IN IMAGE ((EN:real->real^3->A) s) (sphere(vec 0,&1))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                     rfs_vatlas V (&0)) (rfs_vmetric V (&0)) eps ((gamma:real->A) s)
                     ((EN:real->real^3->A) s)` THEN
      SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p2bt_tube; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[p2bt_tube; IN_UNIONS; EXISTS_IN_GSPEC; IN_IMAGE] THEN MESON_TAC[];
    REWRITE_TAC[p2bt_tube; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `w:A` THEN DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `v:A`)) (concl th) && is_forall(concl th))) THEN
    EXISTS_TAC `s:real` THEN EXISTS_TAC `(EN:real->real^3->A) s` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Deep points of the cut tube (MT Def 5.1 in the form p2b_lc_deep).  A      *)
(* point EN sig y of a window neck at level |s(y)| <= lam is delta-deep in U *)
(* = T cut at A1 when the closed slab of level lam + delta/h' (h' = 99/100   *)
(* R(gamma sig)^(-1/2)) lies in the middle half of the neck and within       *)
(* distance A1 of the window start (P2BN_BALL_LEVELS).                       *)
(* ========================================================================= *)

let P2BT_WINDOW_DEEP = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) gamma s0 s1 EN A1 sig y lam delta.
        &0 < eps /\ eps <= eps0 /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= sig /\ sig <= s1 /\ y IN rfs_neck_dom eps /\ abs(apx_sval y) <= lam /\
        &0 < delta /\
        lam + delta / (&99 / &100 *
                       inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                           (gamma sig)))) < inv(&2 * eps) /\
        mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (gamma s0) (EN sig y) /\
        mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                 (gamma s0) (EN sig y) +
        &101 / &100 * inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                          (gamma sig))) *
        (&2 * lam + delta / (&99 / &100 *
                             inv(sqrt(mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                                 (gamma sig)))) + sqrt(&2) * pi) < A1
        ==> p2b_lc_deep V (p2bt_cutset eps V gamma EN s0 s1 A1) (EN sig y) delta`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  EXISTS_TAC `min e0 (&1 / &4)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `t:real`; `Q:real`;
    `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (MP_TAC o SPEC `sig:real`)
    (CONJUNCTS_THEN2 (K ALL_TAC) (K ALL_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) sig)))` THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) sig`; `(EN:real->real^3->A) sig`; `y:real^3`;
                 `lam:real`; `delta:real`] P2BN_BALL_LEVELS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&2 * eps) <= inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Lam = lam + delta / (&99 / &100 * h)` THEN
  STRIP_TAC THEN REWRITE_TAC[p2b_lc_deep; P2BT_VBALL_ALT] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE ((EN:real->real^3->A) sig) {z | ~(z = vec 0) /\ abs(apx_sval z) <= Lam}` THEN
  ASM_REWRITE_TAC[p2bt_cutset; SUBSET_INTER] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2bt_tube; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN EXISTS_TAC `sig:real` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; mfd_ball] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&2 * eps) <= inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_eng_n2 top atlas (g:A->real^3^3) eps (&1 / &100)` THEN
  REWRITE_TAC[apx_eng_n2] THEN
  DISCH_THEN(MP_TAC o SPECL [`(gamma:real->A) sig`; `(EN:real->real^3->A) sig`;
                             `y:real^3`; `z:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
    EXISTS_TAC `(EN:real->real^3->A) sig y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `(gamma:real->A) s0`; `(EN:real->real^3->A) sig y`;
                 `(EN:real->real^3->A) sig z`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs(apx_sval y - apx_sval z) <= &2 * lam + delta / (&99 / &100 * h)`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps ((gamma:real->A) sig)
                   ((EN:real->real^3->A) sig)` THEN
    SIMP_TAC[rfs_neck; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + &1 / &100) * h * (abs(apx_sval y - apx_sval z) + sqrt(&2) * pi) <=
                &101 / &100 * h * (&2 * lam + delta / (&99 / &100 * h) + sqrt(&2) * pi)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(&1 + &1 / &100) * h * a = &101 / &100 * h * a`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The base points and the sets of the local-compactness statement           *)
(* (hypotheses R0, R3 of P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT,              *)
(* pc_p2b_lcreqg).  The base point of the n-th approximant is z n = gamma n  *)
(* (s0 + Db / L) at arc length Db = 2/5 h/eps past the window start (h =     *)
(* lo^(-1/2), lo = 32 C^2), in the first window neck; U n is the tube cut at *)
(* A1.  U n is open, contains z n, and z n is h-deep in U n.                 *)
(* ========================================================================= *)

let p2bt_zbase = new_definition
 `p2bt_zbase (eps:real) (C:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (gamma:num->real->A) (s0:num->real) (n:num) =
    gamma n (s0 n + (&2 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps) /
                    mfd_dist (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))
                             (gamma n (&0)) (gamma n (&1)))`;;

(* The base point in one approximant. *)

let P2BT_ZBASE_FACTS = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) gamma s0 s1 EN.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN
        ==> let L = mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                             (gamma(&0)) (gamma(&1)) in
            let Db = &2 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps in
            s0 < s0 + Db / L /\ s0 + Db / L <= s1 /\
            ((s0 + Db / L) - s0) * L = Db /\
            mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (gamma s0) (gamma(s0 + Db / L)) /\
            mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                     (gamma s0) (gamma(s0 + Db / L)) = Db /\
            &32 * C pow 2 / &2 <=
            mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(s0 + Db / L)) /\
            mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(s0 + Db / L)) <=
            &3 / &2 * &32 * C pow 2 /\
            &9 / &10 * inv(sqrt(&32 * C pow 2)) * inv eps <= (s1 - s0) * L`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fn"))
    (INST_TYPE [`:A`,`:A`] P2BT_FIRST_NECK) THEN
  EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  SUBGOAL_THEN
   `!s. s0 <= s /\ s <= &1 /\
        (s - s0) * mfd_dist (rfs_vtop (V:(real->A topology)#
                              (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                              rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                              ((gamma:real->A)(&0)) (gamma(&1))
        < &9 / &10 * inv(sqrt(&32 * C pow 2)) * inv eps
        ==> &32 * C pow 2 / &2 <= mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) /\
            mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) <=
            &3 / &2 * &32 * C pow 2`
  (LABEL_TAC "first") THENL
   [GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    USE_THEN "fn" (MP_TAC o SPECL
      [`eps:real`; `C:real`; `A:real`; `n:num`;
       `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `t:real`; `Q:real`;
       `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
       `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V (&0))` THEN
  ABBREV_TAC `h = inv(sqrt(&32 * C pow 2))` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BT_C_POWERS) THEN
  SUBGOAL_THEN `&0 < h /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &10 * h * inv eps <= (s1 - s0) * L` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "first" (MP_TAC o SPEC `s1:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(R:A->real) ((gamma:real->A)(&1)) <= &96 * C pow 3` ASSUME_TAC THENL
     [SUBGOAL_THEN `&2 * C * (R:A->real) ((gamma:real->A) s1) = R (gamma(&1))`
      (SUBST1_TAC o SYM) THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `C * (R:A->real) ((gamma:real->A) s1) <= C * (&3 / &2 * &32 * C pow 2)`
      MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `C * (R:A->real) ((gamma:real->A)(&1)) <= C * (&96 * C pow 3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Db = &2 / &5 * h * inv eps` THEN
  SUBGOAL_THEN `&0 < Db /\ Db / L <= s1 - s0 /\ &0 < Db / L /\ ((s0 + Db / L) - s0) * L = Db`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < Db` ASSUME_TAC THENL
     [EXPAND_TAC "Db" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_DIV] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&9 / &10 * h * inv eps <= (s1 - s0) * L`;
                             `&2 / &5 * h * inv eps = Db`] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
    USE_THEN "dist" (MP_TAC o SPECL [`s0:real`; `s0 + Db / L`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    USE_THEN "dist" (MP_TAC o SPECL [`s0:real`; `s0 + Db / L`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    USE_THEN "first" (MP_TAC o SPEC `s0 + Db / L`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&2 / &5 * h * inv eps = Db`; `s1 < &1`] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    USE_THEN "first" (MP_TAC o SPEC `s0 + Db / L`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`&2 / &5 * h * inv eps = Db`; `s1 < &1`] THEN
      SUBGOAL_THEN `&0 < h * inv eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      SIMP_TAC[]];
    ASM_REWRITE_TAC[]]);;

let P2BT_SQRT2_PI = prove
 (`sqrt(&2) * pi <= &24 / &5`,
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ pi <= &16 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &16 / &5` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
    REAL_ARITH_TAC]);;

(* Hypotheses R0 and R3 of the local-compactness statement for the cut tubes. *)

let P2BT_REQ_R0R3 = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) gamma s0 s1 EN A1.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1
        ==> (!n. p2c_regular_view (V n) /\
                 open_in (rfs_vtop (V n) (&0))
                         (p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) /\
                 p2bt_zbase eps C V gamma s0 n IN
                 p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) /\
            (!n. p2b_lc_deep (V n) (p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1)
                             (p2bt_zbase eps C V gamma s0 n) (inv(sqrt(&32 * C pow 2))))`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "zb"))
    (INST_TYPE [`:A`,`:A`] P2BT_ZBASE_FACTS) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "deep"))
    (INST_TYPE [`:A`,`:A`] P2BT_WINDOW_DEEP) THEN
  EXISTS_TAC `min (min e1 e2) (&1 / &50)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= &1 / &50` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `p2bt_one eps C A n ((V0:num->(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
              ((t:num->real) n) ((Q:num->real) n)
              ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) n)
              ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
              ((EN:num->real->real^3->A) n)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2bt_approx]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &5 * inv(sqrt(&32 * C pow 2)) * inv eps <= A1` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bt_cut]; ALL_TAC] THEN
  USE_THEN "zb" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
           (real->A->real^3^3)) n`;
     `(t:num->real) n`; `(Q:num->real) n`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
          (real->A->real^3^3)) n`;
     `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
     `(EN:num->real->real^3->A) n`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
           (real->A->real^3^3)) n`;
     `(t:num->real) n`; `(Q:num->real) n`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
          (real->A->real^3^3)) n`;
     `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
     `(EN:num->real->real^3->A) n`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wn") (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_const(fst(strip_comb(concl th))) &&
    fst(dest_const(fst(strip_comb(concl th)))) = "p2bt_one")) THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `top = rfs_vtop ((V:num->(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas ((V:num->(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric ((V:num->(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)` THEN
  ABBREV_TAC `L = mfd_dist (top,atlas) (g:A->real^3^3) ((gamma:num->real->A) n (&0))
                           (gamma n (&1))` THEN
  ABBREV_TAC `h = inv(sqrt(&32 * C pow 2))` THEN
  ABBREV_TAC `Db = &2 / &5 * h * inv eps` THEN
  ABBREV_TAC `sig = (s0:num->real) n + Db / L` THEN
  SUBGOAL_THEN `p2bt_zbase eps C V gamma s0 n = (gamma:num->real->A) n sig` SUBST1_TAC THENL
   [REWRITE_TAC[p2bt_zbase] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h /\ &50 <= inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`eps:real`; `&1 / &50`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * &50 <= h * inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Db < A1` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&4 / &5 * h * inv eps <= A1`; `&2 / &5 * h * inv eps = Db`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "wn" (MP_TAC o SPEC `sig:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[p2bt_cutset; IN_INTER] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MFD_BALL_OPEN];
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y0) <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO; REAL_ABS_0; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `hs = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((gamma:num->real->A) n sig)))` THEN
  SUBGOAL_THEN `&0 < hs /\ h <= &2 * hs /\ hs <= &2 * h` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) ((gamma:num->real->A) n sig) /\
                  &0 < &32 * C pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]) THEN
      SUBGOAL_THEN `&0 < C pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "hs" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "h" THEN EXPAND_TAC "hs" THEN MATCH_MP_TAC P2BT_INV_SQRT_LE THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN EXPAND_TAC "hs" THEN MATCH_MP_TAC P2BT_INV_SQRT_LE THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `h / (&99 / &100 * hs) <= &200 / &99 /\
                hs * (h / (&99 / &100 * hs)) = &100 / &99 * h /\
                hs * (sqrt(&2) * pi) <= (&2 * h) * (&24 / &5)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < &99 / &100 * hs` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < hs` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; P2BT_SQRT2_PI] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(EN:num->real->real^3->A) n sig y0 = (gamma:num->real->A) n sig`
  (SUBST1_TAC o SYM) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "deep" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
           (real->A->real^3^3)) n`;
     `(t:num->real) n`; `(Q:num->real) n`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
          (real->A->real^3^3)) n`;
     `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
     `(EN:num->real->real^3->A) n`; `A1:real`; `sig:real`; `y0:real^3`; `&0`; `h:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&25 <= inv(&2 * eps)` MP_TAC THENL
     [MP_TAC(SPECL [`&2 * eps`; `&2 * (&1 / &50)`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&2 * &0 + a + b = a + b`; REAL_ADD_LDISTRIB] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[p2bt_cutset] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* MT Claim 10.6 without Lemma A.9.  A delta-deep point w of the cut tube U  *)
(* lies in the middle half of a window neck at gamma(s).  Either R(w) is     *)
(* below a constant depending on delta and eps, or the neck is small: then   *)
(* gamma(s + 3 delta / 4L) lies in the delta-ball of w, hence in U, hence    *)
(* within A1 of gamma(s0), and the arc length (s - s0) L is below A1 - 3     *)
(* delta / 4, where the cut bounds R. (The far end gamma(1) cannot lie in U: *)
(* its curvature is too large.)                                              *)
(* ========================================================================= *)

(* Points of the middle half of a window neck of small scale are close to   *)
(* the centre: d(gamma s, EN s y) < delta / 4 when R(gamma s) > (3/(delta eps))^2. *)

let P2BT_TUBE_NEAR = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) gamma s0 s1 EN s y delta.
        &0 < eps /\ eps <= eps0 /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= s /\ s <= s1 /\ y IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
        &0 < delta
        ==> mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) / &2 <=
            mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN s y) /\
            mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (EN s y) <=
            &3 / &2 * mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) /\
            mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (gamma s) (EN s y) /\
            ((&3 / (delta * eps)) pow 2 <
             mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s)
             ==> mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                          (gamma s) (EN s y) < delta / &4)`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_R) THEN
  EXISTS_TAC `min (min e0 e1) (&1 / &50)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1 /\ eps <= &1 / &50` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `t:real`; `Q:real`;
    `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `yc:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps /\ (yc:real^3) IN rfs_neck_dom eps /\
                apx_sval yc = &0 /\ abs(apx_sval y) < inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` P2BT_MIDDLE_IN_DOM) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO];
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "nr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(gamma:real->A) s`; `(EN:real->real^3->A) s`; `y:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  UNDISCH_TAC `apx_eng_n2 top atlas (g:A->real^3^3) eps (&1 / &100)` THEN
  REWRITE_TAC[apx_eng_n2] THEN
  DISCH_THEN(MP_TAC o SPECL [`(gamma:real->A) s`; `(EN:real->real^3->A) s`;
                             `yc:real^3`; `y:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `hs = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s)))` THEN
  SUBGOAL_THEN `&0 < delta * eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= hs /\ hs < (delta * eps) / &3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hs" THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(&3 / (delta * eps)) pow 2` THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `(delta * eps) / &3 = inv(sqrt((&3 / (delta * eps)) pow 2))` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 <= &3 / (delta * eps)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[POW_2_SQRT] THEN REWRITE_TAC[REAL_INV_DIV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_POW_LT THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs * (abs(&0 - apx_sval y) + sqrt(&2) * pi) <=
                ((delta * eps) / &3) * (inv(&2 * eps) + &24 / &5)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      MP_TAC P2BT_SQRT2_PI THEN REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((delta * eps) / &3) * (inv(&2 * eps) + &24 / &5) =
                delta / &6 + &8 / &5 * (delta * eps)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `delta * eps <= delta * (&1 / &50)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BT_DEEP_BOUND_ONE = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) gamma s0 s1 EN A1 delta Kc w.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        &0 < delta /\
        (!s. s0 <= s /\ s <= s1 /\
             (s - s0) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0))
                                 (gamma(&0)) (gamma(&1)) <= A1 - &3 / &4 * delta
             ==> mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) <= Kc) /\
        w IN p2bt_cutset eps V gamma EN s0 s1 A1 /\
        p2b_lc_deep V (p2bt_cutset eps V gamma EN s0 s1 A1) w delta
        ==> mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w <=
            max (&3 / &2 * Kc) (&3 / &2 * (&3 / (delta * eps)) pow 2)`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))
    (INST_TYPE [`:A`,`:A`] P2BT_TUBE_NEAR) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "prof")
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `t:real`; `Q:real`;
    `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "mem") (K ALL_TAC)))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  SUBGOAL_THEN
   `!q. mfd_joinable (rfs_vtop V (&0),rfs_vatlas V (&0)) (w:A) q /\
        mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w q < delta
        ==> q IN p2bt_cutset eps (V:(real->A topology)#
                                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                 gamma EN s0 s1 A1`
  (LABEL_TAC "ball") THENL
   [X_GEN_TAC `q:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `p2b_lc_deep (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (p2bt_cutset eps V gamma EN s0 s1 A1) w delta` THEN
    REWRITE_TAC[p2b_lc_deep; P2BT_VBALL_ALT] THEN
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o CONJUNCT2) THEN
    SUBGOAL_THEN
     `mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (w:A) delta SUBSET
      rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (&0) closure_of
      mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) w delta`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN
      UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
      SIMP_TAC[p2bt_one];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN p2bt_tube eps EN s0 s1` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:A) IN p2bt_cutset eps V gamma EN s0 s1 A1` THEN
    SIMP_TAC[p2bt_cutset; IN_INTER];
    ALL_TAC] THEN
  USE_THEN "mem" (MP_TAC o C MATCH_MP (ASSUME `(w:A) IN p2bt_tube eps EN s0 s1`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  USE_THEN "near" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:real`; `Q:real`;
     `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s:real`; `y:real^3`;
     `delta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `w:A`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nd")))) THEN
  ABBREV_TAC `M = (&3 / (delta * eps)) pow 2` THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0))
                    (rfs_vmetric V (&0))` THEN
  ASM_CASES_TAC `(R:A->real) ((EN:real->real^3->A) s y) <= &3 / &2 * M` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M < (R:A->real) ((gamma:real->A) s)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "nd" (MP_TAC o C MATCH_MP (ASSUME `M < (R:A->real) ((gamma:real->A) s)`)) THEN
  DISCH_TAC THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (&0)` THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    (let c,_ = strip_comb(concl th) in is_const c && fst(dest_const c) = "p2bt_one"))) THEN
  REWRITE_TAC[p2bt_one] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  SUBGOAL_THEN
   `!u. s <= u /\ u <= &1 /\ (u - s) * L <= &3 / &4 * delta
        ==> (gamma:real->A) u IN p2bt_cutset eps V gamma EN s0 s1 A1`
  (LABEL_TAC "close") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN USE_THEN "ball" MATCH_MP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`s:real`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                    ((EN:real->real^3->A) s y) ((gamma:real->A) s)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(gamma:real->A) s`; `(EN:real->real^3->A) s y`] MFD_JOINABLE_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `(gamma:real->A) s` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(EN:real->real^3->A) s y`; `(gamma:real->A) s`; `(gamma:real->A) u`]
      MFD_DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(EN:real->real^3->A) s y`; `(gamma:real->A) s`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s + (&3 / &4 * delta) / L <= &1` THENL
   [(* the point at arc length 3 delta / 4 past gamma(s) lies in U *)
    ABBREV_TAC `u = s + (&3 / &4 * delta) / L` THEN
    SUBGOAL_THEN `(u - s) * L = &3 / &4 * delta /\ s <= u` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD;
        SUBGOAL_THEN `&0 <= (&3 / &4 * delta) / L` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    USE_THEN "close" (MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[p2bt_cutset; IN_INTER; mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    USE_THEN "dist" (MP_TAC o SPECL [`s0:real`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(R:A->real) ((gamma:real->A) s) <= Kc` ASSUME_TAC THENL
     [USE_THEN "prof" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_MAX] THEN DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* otherwise the far end gamma(1) lies in U, which its curvature forbids *)
  SUBGOAL_THEN `(&1 - s) * L <= &3 / &4 * delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    SUBGOAL_THEN `&1 - s < (&3 / &4 * delta) / L` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ]];
    ALL_TAC] THEN
  USE_THEN "close" (MP_TAC o SPEC `&1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2bt_cutset; IN_INTER] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> USE_THEN "mem" (MP_TAC o C MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `(gamma:real->A)(&1)`)) THEN
  USE_THEN "near" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `n:num`;
     `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:real`; `Q:real`;
     `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`; `s':real`; `y':real^3`;
     `delta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s':real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&2 * C`)) (concl th) &&
    can (find_term ((=) `&32 * C pow 2`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < (R:A->real) ((gamma:real->A) s')` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->real) ((gamma:real->A) s') * (&2 * C) <= R (gamma(&1))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->real) ((gamma:real->A) s') * &1 < R (gamma s') * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* MT Claim 10.6 for the sequence of cut tubes and the hypotheses R1         *)
(* (backward neighbourhoods) and R2 (volume) of the local-compactness        *)
(* statement (pc_p2b_lcreqg).  For a delta-deep point y of U n, the points   *)
(* of B(y, delta/2) are delta/2-deep, so R <= K there uniformly in n         *)
(* (P2BT_DEEP_BOUND); being strong-neck centres, the half ball persists on   *)
(* (-1/K, 0] with |Rm| <= K1 K (P2BN_NECK_SET_BACKWARD), and its volume is   *)
(* at least pi/750 min(delta/2, (K1 K)^(-1/2))^3 (P2BN_NECK_BALL_VOLUME).    *)
(* ========================================================================= *)

(* The two clauses of p2c_regular_view used by P2BN_NECK_SET_BACKWARD,      *)
(* collected in one lemma.                                                   *)

let P2BT_REGULAR_VIEW_FACTS = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2c_regular_view V
     ==> (!s. ~(topspace(rfs_vtop V s) = {})
              ==> riemannian_metric (rfs_vatlas V s) (rfs_vmetric V s)) /\
         (!N a b s. a < s /\ s <= b /\ rfs_persists V N a b
                    ==> mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) N
                                   (rfs_vtop V b) (rfs_vatlas V b) N (\y:A. y) (\y. y))`,
  GEN_TAC THEN REWRITE_TAC[p2c_regular_view] THEN STRIP_TAC THEN
  CONJ_TAC THEN ASM_MESON_TAC[]);;

(* Points of the half ball about a deep point are half as deep.              *)

let P2BT_DEEP_HALF = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    U y w delta.
     smooth_manifold_atlas (rfs_vtop V (&0)) (rfs_vatlas V (&0)) /\
     riemannian_metric (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) /\
     p2b_lc_deep V U y delta /\ w IN rfs_vball V (&0) y (delta / &2)
     ==> rfs_vball V (&0) w (delta / &2) SUBSET rfs_vball V (&0) y delta /\
         p2b_lc_deep V U w (delta / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_lc_deep; P2BT_VBALL_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (w:A) (delta / &2) SUBSET
    mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) y delta`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(w:A) IN mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) y
                            (delta / &2)` THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `q:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)`;
                     `y:A`; `w:A`; `q:A`] MFD_DIST_TRIANGLE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `rfs_vtop V (&0) closure_of
    mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (w:A) (delta / &2) SUBSET
    rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) closure_of
    mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) y delta`
  ASSUME_TAC THENL [MATCH_MP_TAC CLOSURE_OF_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0) closure_of
                mfd_ball (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (y:A) delta` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ASM SET_TAC[]]);;

(* MT Claim 10.6 for the sequence: delta-deep points of the cut tubes have  *)
(* R bounded independently of n.                                              *)

let P2BT_DEEP_BOUND = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1 delta.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1 /\
        &0 < delta
        ==> ?K. &0 < K /\
                !n w. w IN p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1 /\
                      p2b_lc_deep (V n) (p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) w delta
                      ==> mfd_scalar (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) w <= K`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "one"))
    (INST_TYPE [`:A`,`:A`] P2BT_DEEP_BOUND_ONE) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `A1 - &3 / &4 * delta` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [p2bt_cut]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (LABEL_TAC "kc")) THEN
  EXISTS_TAC `max (&1) (max (&3 / &2 * Kc) (&3 / &2 * (&3 / (delta * eps)) pow 2))` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `w:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max (&1) b`) THEN
  SUBGOAL_THEN `p2bt_one eps C A n ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n)
              ((Q:num->real) n) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
              ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
              ((EN:num->real->real^3->A) n)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `n:num`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (s0:num->real) n <= s /\ s <= (s1:num->real) n /\
        (s - s0 n) *
        mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0),rfs_vatlas (V n) (&0))
                 (rfs_vmetric (V n) (&0)) ((gamma:num->real->A) n (&0)) (gamma n (&1))
        <= A1 - &3 / &4 * delta
        ==> mfd_scalar (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) (gamma n s) <= Kc`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "kc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "one" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`C:real`; `A:real`; `n:num`;
    `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
    `(t:num->real) n`; `(Q:num->real) n`;
    `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
    `(EN:num->real->real^3->A) n`; `A1:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The half ball about a deep point: persistence and the curvature bound.    *)

let P2BT_HALF_BALL_BACKWARD = prove
 (`?eps0 K1. &0 < eps0 /\ &0 < K1 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1 delta.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1 /\
        &0 < delta
        ==> ?K. &0 < K /\
                !n y. y IN p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1 /\
                      p2b_lc_deep (V n) (p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) y delta
                      ==> rfs_persists (V n) (rfs_vball (V n) (&0) y (delta / &2))
                                       (--inv K) (&0) /\
                          (!s y'. --inv K < s /\ s <= &0 /\
                                  y' IN rfs_vball (V n) (&0) y (delta / &2)
                                  ==> mfd_rm_norm (rfs_vatlas (V n) s) (rfs_vmetric (V n) s) y'
                                      <= K1 * K)`,
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "db"))
    (INST_TYPE [`:A`,`:A`] P2BT_DEEP_BOUND) THEN
  X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bw"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_SET_BACKWARD) THEN
  MAP_EVERY EXISTS_TAC [`min e1 (&1 / &4)`; `K1:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "db" (MP_TAC o SPECL ([`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
     `A1:real`; `delta / &2`])) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kb"))) THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bt_one eps C A n ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n)
              ((Q:num->real) n) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
              ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
              ((EN:num->real->real^3->A) n)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `n:num`);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
     `(t:num->real) n`; `(Q:num->real) n`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
     `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
     `(EN:num->real->real^3->A) n`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "sn")))) THEN
  SUBGOAL_THEN
   `p2c_regular_view ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) /\
    hausdorff_space (rfs_vtop (V n) (&0)) /\
    smooth_manifold_atlas (rfs_vtop (V n) (&0)) (rfs_vatlas (V n) (&0)) /\
    riemannian_metric (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_one eps C A n ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n)
              ((Q:num->real) n) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
              ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
              ((EN:num->real->real^3->A) n)` THEN
    SIMP_TAC[p2bt_one];
    ALL_TAC] THEN
  MP_TAC(SPEC `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n` P2BT_REGULAR_VIEW_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `U = p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
                    ((gamma:num->real->A) n) ((EN:num->real->real^3->A) n)
                    ((s0:num->real) n) ((s1:num->real) n) A1` THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (x:A). x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `p2bt_tube eps ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                          ((s1:num->real) n)` THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
    UNDISCH_TAC `(y:A) IN U` THEN EXPAND_TAC "U" THEN SIMP_TAC[p2bt_cutset; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0))
            (rfs_vball (V n) (&0) (y:A) (delta / &2)) /\
    (y:A) IN rfs_vball (V n) (&0) y (delta / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[P2BT_VBALL_ALT] THEN ASM_SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0) (y:A) (delta / &2) = {})`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:A. w IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0) y (delta / &2)
          ==> (?e. rfs_strong_neck (V n) eps w (&0) e) /\ rfs_vscalar (V n) (&0) w <= K`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `U:A->bool`; `y:A`; `w:A`;
                   `delta:real`] P2BT_DEEP_HALF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(w:A) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `p2b_lc_deep ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) U (y:A) delta` THEN
      REWRITE_TAC[p2b_lc_deep; P2BT_VBALL_ALT] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      MATCH_MP_TAC(SET_RULE `!a b c (x:A). x IN a /\ a SUBSET b ==> b SUBSET c ==> x IN c`) THEN
      EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0),
                            rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) (y:A) delta` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!a b (x:A). x IN a /\ a SUBSET b ==> x IN b`) THEN
        EXISTS_TAC `mfd_ball (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0),
                              rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) (y:A)
                             (delta / &2)` THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `(w:A) IN rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0) y (delta / &2)` THEN
          REWRITE_TAC[P2BT_VBALL_ALT];
          MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
        MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_SIMP_TAC[MFD_BALL_OPEN]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "sn" MATCH_MP_TAC THEN
      UNDISCH_TAC `(w:A) IN U` THEN EXPAND_TAC "U" THEN SIMP_TAC[p2bt_cutset; IN_INTER];
      REWRITE_TAC[P2BN_RFS_VSCALAR] THEN USE_THEN "kb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "bw" (MP_TAC o SPECL
    [`(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`; `eps:real`;
     `rfs_vball ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0) (y:A) (delta / &2)`; `K:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* Hypothesis R1 of the local-compactness statement for the cut tubes.       *)

let P2BT_REQ_R1 = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1
        ==> !delta. &0 < delta
                    ==> ?K tau N. &0 < tau /\
                          !n y. N <= n /\ y IN p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1 /\
                                p2b_lc_deep (V n) (p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) y delta
                                ==> rfs_persists (V n) (rfs_vball (V n) (&0) y (delta / &2))
                                                 (--tau) (&0) /\
                                    !s y'. --tau < s /\ s <= &0 /\
                                           y' IN rfs_vball (V n) (&0) y (delta / &2)
                                           ==> mfd_rm_norm (rfs_vatlas (V n) s)
                                                           (rfs_vmetric (V n) s) y' <= K`,
  X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hb"))))
    (INST_TYPE [`:A`,`:A`] P2BT_HALF_BALL_BACKWARD) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  USE_THEN "hb" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
     `A1:real`; `delta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`K1 * K`; `inv K`; `0`] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; LE_0]);;

(* Hypothesis R2 of the local-compactness statement for the cut tubes.       *)

let P2BT_REQ_R2 = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1
        ==> !delta. &0 < delta
                    ==> ?kappa N. &0 < kappa /\
                          !n y. N <= n /\ y IN p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1 /\
                                p2b_lc_deep (V n) (p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) y delta
                                ==> ?v. mfd_has_volume (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0))
                                          (rfs_vmetric (V n) (&0))
                                          (rfs_vball (V n) (&0) y (delta / &2)) v /\
                                        kappa * (delta / &2) pow 3 <= v`,
  X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `K1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hb"))))
    (INST_TYPE [`:A`,`:A`] P2BT_HALF_BALL_BACKWARD) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vol"))
    (INST_TYPE [`:A`,`:A`] P2BN_NECK_BALL_VOLUME) THEN
  EXISTS_TAC `min e0 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `delta:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "hb" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
     `A1:real`; `delta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kb"))) THEN
  SUBGOAL_THEN `&0 < K1 * K` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = min (delta / &2) (inv(sqrt(K1 * K)))` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`pi / &750 * (m / (delta / &2)) pow 3`; `0`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2bt_one eps C A n ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n)
              ((Q:num->real) n) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
              ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
              ((EN:num->real->real^3->A) n)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `n:num`);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
     `(t:num->real) n`; `(Q:num->real) n`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n`;
     `(gamma:num->real->A) n`; `(s0:num->real) n`; `(s1:num->real) n`;
     `(EN:num->real->real^3->A) n`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "sn")))) THEN
  SUBGOAL_THEN
   `hausdorff_space (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)) /\
    smooth_manifold_atlas (rfs_vtop (V n) (&0)) (rfs_vatlas (V n) (&0)) /\
    riemannian_metric (rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_one eps C A n ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((t:num->real) n)
              ((Q:num->real) n) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n)
              ((gamma:num->real->A) n) ((s0:num->real) n) ((s1:num->real) n)
              ((EN:num->real->real^3->A) n)` THEN
    SIMP_TAC[p2bt_one];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace(rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (x:A). x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `p2bt_tube eps ((EN:num->real->real^3->A) n) ((s0:num->real) n)
                          ((s1:num->real) n)` THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN
    UNDISCH_TAC `(y:A) IN p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((gamma:num->real->A) n)
                 ((EN:num->real->real^3->A) n) ((s0:num->real) n) ((s1:num->real) n) A1` THEN SIMP_TAC[p2bt_cutset; IN_INTER];
    ALL_TAC] THEN
  (* |Rm| at y at time 0 *)
  USE_THEN "kb" (MP_TAC o SPECL [`n:num`; `y:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `y:A`] o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL; REAL_NEG_LT0; REAL_LT_INV_EQ; P2BT_VBALL_ALT] THEN
    ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  (* the neck at y *)
  USE_THEN "sn" (MP_TAC o SPEC `y:A`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `(y:A) IN p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((gamma:num->real->A) n)
                 ((EN:num->real->real^3->A) n) ((s0:num->real) n) ((s1:num->real) n) A1` THEN SIMP_TAC[p2bt_cutset; IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_strong_neck; P2BN_EVOLVING_NECK_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->A` (ASSUME_TAC o CONJUNCT1)) THEN
  (* the closure of the half ball is compact *)
  SUBGOAL_THEN
   `compact_in (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0))
      (rfs_vtop (V n) (&0) closure_of
       mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0)) (y:A)
                (delta / &2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_lc_deep ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((gamma:num->real->A) n)
                 ((EN:num->real->real^3->A) n) ((s0:num->real) n) ((s1:num->real) n) A1) (y:A) delta` THEN
    REWRITE_TAC[p2b_lc_deep; P2BT_VBALL_ALT] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0) closure_of
                mfd_ball (rfs_vtop (V n) (&0),rfs_vatlas (V n) (&0)) (rfs_vmetric (V n) (&0))
                         (y:A) delta` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    MATCH_MP_TAC CLOSURE_OF_MONO THEN MATCH_MP_TAC P2BN_MFD_BALL_MONO THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "vol" (MP_TAC o SPECL
    [`rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)`;
     `rfs_vatlas ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)`;
     `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) (&0)`;
     `eps:real`; `y:A`; `e:real^3->A`; `delta / &2`; `K1 * K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM P2BT_VBALL_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(pi / &750 * (m / (delta / &2)) pow 3) * (delta / &2) pow 3 = pi / &750 * m pow 3`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < delta` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The far end of the profile.  Near a profile point gamma(s) with R <= K    *)
(* the profile stays in the window neck of gamma(s), where R is at most 3/2  *)
(* K (P2BT_PROFILE_NEAR_R).  Since along the subsequence R is unbounded on   *)
(* the profile up to A1 + 1/(j+1) for every j, but bounded up to any A' <    *)
(* A1, R is eventually above any K on the profile near arc length A1         *)
(* (P2BT_FAR_END).                                                           *)
(* ========================================================================= *)

let P2BT_PROFILE_NEAR_R = prove
 (`?eps0. &0 < eps0 /\
     !eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN s s' K.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\ p2bt_one eps C A n V0 t Q V gamma s0 s1 EN /\
        s0 <= s /\ s <= s1 /\ &0 <= s' /\ s' <= &1 /\ &0 < K /\
        mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s) <= K /\
        abs(s' - s) * mfd_dist (rfs_vtop V (&0),rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma(&0)) (gamma(&1))
        < &99 / &100 * inv(sqrt K) * inv eps
        ==> mfd_scalar (rfs_vatlas V (&0)) (rfs_vmetric V (&0)) (gamma s') <= &3 / &2 * K`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nr"))
    (INST_TYPE [`:A`,`:A`] P2BT_NECK_R) THEN
  EXISTS_TAC `min e0 e1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e0 /\ eps <= e1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `C:real`; `A:real`; `n:num`;
    `V0:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`; `t:real`; `Q:real`; `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `gamma:real->A`; `s0:real`; `s1:real`; `EN:real->real^3->A`] P2BT_TUBE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dist"))) THEN
  UNDISCH_TAC `p2bt_one eps C A n V0 t Q (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
  REWRITE_TAC[p2bt_one] THEN STRIP_TAC THEN p2bt_drop_rescale_eq_tac THEN
  ABBREV_TAC `L = mfd_dist (rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0),
                    rfs_vatlas V (&0)) (rfs_vmetric V (&0)) ((gamma:real->A)(&0)) (gamma(&1))` THEN
  ABBREV_TAC `top = rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `atlas = rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  ABBREV_TAC `g = rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (&0)` THEN
  USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN rfs_neck_dom eps /\ apx_sval y0 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[apx_sval; LOG_1; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BN_NECK_CENTRE_FACTS o check (fun th ->
    is_comb(concl th) && (let c,_ = strip_comb(concl th) in
      is_const c && fst(dest_const c) = "rfs_neck"))) THEN
  SUBGOAL_THEN
   `mfd_joinable (top,atlas) ((gamma:real->A) s) (gamma s') /\
    mfd_dist (top,atlas) (g:A->real^3^3) (gamma s) (gamma s') = abs(s' - s) * L`
  STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `s <= s' \/ s' < s`) THENL
     [USE_THEN "dist" (MP_TAC o SPECL [`s:real`; `s':real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(s' - s) = s' - s` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "dist" (MP_TAC o SPECL [`s':real`; `s:real`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `abs(s' - s) = s - s'` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `(gamma:real->A) s'`; `(gamma:real->A) s`] MFD_JOINABLE_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `(gamma:real->A) s`; `(gamma:real->A) s'`]
                      MFD_DIST_SYM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt K) <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) ((gamma:real->A) s)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(gamma:real->A) s`; `(EN:real->real^3->A) s`; `y0:real^3`;
                 `(gamma:real->A) s'`] APX_NECK_EXIT_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_0; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&99 / &100 * inv(sqrt K) * inv eps` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "nr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(gamma:real->A) s`; `(EN:real->real^3->A) s`; `y':real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* R is eventually above any K on the profile near arc length A1.           *)

let P2BT_FAR_END = prove
 (`?eps0. &0 < eps0 /\
     !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1.
        &0 < eps /\ eps <= eps0 /\ &1 < C /\
        p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1
        ==> !K. &0 < K
                ==> ?c N. &0 < c /\
                      !k s. N <= k /\ s0 k <= s /\ s <= s1 k /\
                            abs((s - s0 k) * mfd_dist (rfs_vtop (V k) (&0),rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0))
                                     (gamma k (&0)) (gamma k (&1)) - A1) <= c
                            ==> K < mfd_scalar (rfs_vatlas (V k) (&0)) (rfs_vmetric (V k) (&0)) (gamma k s)`,
  X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pn"))
    (INST_TYPE [`:A`,`:A`] P2BT_PROFILE_NEAR_R) THEN
  EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `K:real` THEN DISCH_TAC THEN
  ABBREV_TAC `r = &99 / &100 * inv(sqrt K) * inv eps` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_SIMP_TAC[SQRT_POS_LT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `A1 - r / &4` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [p2bt_cut]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K2:real` (LABEL_TAC "kb")) THEN
  MP_TAC(SPEC `r / &4` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_ARITH `&0 < r / &4 <=> &0 < r`] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `inv(&j + &1) < r / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&j)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_ARITH `x <= x + &1`] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `max K2 (&3 / &2 * K)`] o CONJUNCT2 o CONJUNCT2 o
    CONJUNCT2 o GEN_REWRITE_RULE I [p2bt_cut]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "bu")) THEN
  MAP_EVERY EXISTS_TAC [`r / &4`; `N:num`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `s:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  USE_THEN "bu" (MP_TAC o C MATCH_MP (ASSUME `N <= k:num`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2bt_one eps C A k ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k)
              ((Q:num->real) k) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
              ((gamma:num->real->A) k) ((s0:num->real) k) ((s1:num->real) k)
              ((EN:num->real->real^3->A) k)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_approx eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN` THEN
    REWRITE_TAC[p2bt_approx] THEN DISCH_THEN(ACCEPT_TAC o SPEC `k:num`);
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (s0:num->real) k /\ (s1:num->real) k < &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bt_one eps C A k ((V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) ((t:num->real) k)
              ((Q:num->real) k) ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k)
              ((gamma:num->real->A) k) ((s0:num->real) k) ((s1:num->real) k)
              ((EN:num->real->real^3->A) k)` THEN SIMP_TAC[p2bt_one];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2BT_ONE_DIST o CONJ (ASSUME `&1 < C`)) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `A1 - r / &4 < (s' - (s0:num->real) k) * mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0),rfs_vatlas (V k) (&0))
                   (rfs_vmetric (V k) (&0)) ((gamma:num->real->A) k (&0)) (gamma k (&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "kb" (MP_TAC o SPECL [`k:num`; `s':real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "pn" (MP_TAC o SPECL
    [`eps:real`; `C:real`; `A:real`; `k:num`;
     `(V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(t:num->real) k`; `(Q:num->real) k`;
     `(V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k`; `(gamma:num->real->A) k`;
     `(s0:num->real) k`; `(s1:num->real) k`; `(EN:num->real->real^3->A) k`;
     `s:real`; `s':real`; `K:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `L = mfd_dist (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) k) (&0),rfs_vatlas (V k) (&0))
                   (rfs_vmetric (V k) (&0)) ((gamma:num->real->A) k (&0)) (gamma k (&1))` THEN
    SUBGOAL_THEN `abs(s' - s) * L = abs((s' - (s0:num->real) k) * L - (s - s0 k) * L)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(a - c) * l - (b - c) * l = (a - b) * l`; REAL_ABS_MUL] THEN
      AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The limit.  p2bt_lim is the conclusion of the general local-limit         *)
(* statement (pc_p2b_lcreqg) for given V, U, z; the cut tubes with the base  *)
(* points satisfy its hypotheses (shown above), so the limit exists          *)
(* (P2BT_LIMIT_EXISTS).                                                      *)
(* ========================================================================= *)

let p2bt_lim = new_definition
 `p2bt_lim (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    (U:num->A->bool) (z:num->A) (sub:num->num) (top:B topology)
    (atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) (zl:B) (W:num->B->bool)
    (phi:num->B->A) (Vl:(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#(real->B->real^3^3)) <=>
    p3_subseq sub /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ zl IN topspace top /\
    (!k. open_in top (W k) /\ zl IN W k /\ compact_in top (top closure_of W k) /\
         top closure_of W k SUBSET W (SUC k)) /\
    UNIONS {W k | k IN (:num)} = topspace top /\
    (!k. phi k zl = z (sub k)) /\
    (!k. IMAGE (phi k) (W k) SUBSET U (sub k) /\
         ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V (sub k)) (&0))
                          (rfs_vatlas (V (sub k)) (&0))
                          (IMAGE (phi k) (W k)) (phi k) psi) /\
    (!K m eta. compact_in top K /\ &0 < eta
               ==> ?k0. !k. k0 <= k
                            ==> K SUBSET W k /\
                                !y. y IN K
                                    ==> lck_dist2 m
                                          (metric_local atlas (chart_at atlas y) g)
                                          (rfs_pullback (rfs_vatlas (V (sub k)) (&0))
                                             (phi k o chart_inv (chart_at atlas y))
                                             (rfs_vmetric (V (sub k)) (&0)))
                                          (SND(chart_at atlas y) y) < eta) /\
    (!delta A. &0 < delta /\ &0 < A
               ==> ?m k0. m <= k0 /\
                    !k gamma.
                      k0 <= k /\
                      mfd_c1_curve (rfs_vtop (V (sub k)) (&0),
                                    rfs_vatlas (V (sub k)) (&0)) gamma (&0) (&1) /\
                      gamma (&0) = z (sub k) /\
                      mfd_length (rfs_vatlas (V (sub k)) (&0))
                                 (rfs_vmetric (V (sub k)) (&0)) gamma (&0) (&1) <= A /\
                      (!s. &0 <= s /\ s <= &1
                           ==> p2b_lc_deep (V (sub k)) (U (sub k)) (gamma s) delta)
                      ==> !s. &0 <= s /\ s <= &1
                              ==> ?y'. y' IN W m /\ phi k y' = gamma s) /\
    p2c_regular_view Vl /\
    rfs_vtop Vl (&0) = top /\ rfs_vatlas Vl (&0) = atlas /\ rfs_vmetric Vl (&0) = g /\
    (!X a. open_in top X /\ compact_in top (top closure_of X) /\ a < &0 /\
           (?Kb N. !k. N <= k
                       ==> X SUBSET W k /\
                           rfs_persists (V (sub k)) (IMAGE (phi k) X) a (&0) /\
                           !s y. a < s /\ s <= &0 /\ y IN IMAGE (phi k) X
                                 ==> mfd_rm_norm (rfs_vatlas (V (sub k)) s)
                                                 (rfs_vmetric (V (sub k)) s) y <= Kb)
           ==> p2c_vflow Vl X a (&0) /\
               !K m eta b. compact_in top K /\ K SUBSET X /\ a < b /\ &0 < eta
                 ==> ?k0. !k s y. k0 <= k /\ b <= s /\ s <= &0 /\ y IN K
                                  ==> lck_dist2 m
                                        (metric_local (rfs_vatlas Vl s)
                                           (chart_at (rfs_vatlas Vl s) y)
                                           (rfs_vmetric Vl s))
                                        (rfs_pullback (rfs_vatlas (V (sub k)) s)
                                           (phi k o chart_inv
                                              (chart_at (rfs_vatlas Vl s) y))
                                           (rfs_vmetric (V (sub k)) s))
                                        (SND(chart_at (rfs_vatlas Vl s) y) y) < eta)`;;

let P2BT_LIMIT_EXISTS = prove
 (`!(u:A->bool) (w:B->bool).
     P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT u w
     ==> ?eps0. &0 < eps0 /\
           !eps C A V0 t Q (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0 s1 EN A1.
              &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A /\
              p2bt_approx eps C A V0 t Q V gamma s0 s1 EN /\ p2bt_cut eps C A V gamma s0 s1 A1
              ==> ?sub (top:B topology) atlas g zl W phi Vl.
                    p2bt_lim V (\n. p2bt_cutset eps (V n) (gamma n) (EN n) (s0 n) (s1 n) A1) (p2bt_zbase eps C V gamma s0)
                             sub top atlas g zl W phi Vl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_REQ_P2C_LOCAL_COMPACT_G_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "req") THEN
  X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r03"))
    (INST_TYPE [`:A`,`:A`] P2BT_REQ_R0R3) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1"))
    (INST_TYPE [`:A`,`:A`] P2BT_REQ_R1) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2"))
    (INST_TYPE [`:A`,`:A`] P2BT_REQ_R2) THEN
  EXISTS_TAC `min e1 (min e2 e3)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= e1 /\ eps <= e2 /\ eps <= e3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "r03" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
     `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "r1" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
     `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "r2" (MP_TAC o SPECL [`eps:real`; `C:real`; `A:real`;
     `V0:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `t:num->real`; `Q:num->real`;
     `V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `gamma:num->real->A`; `s0:num->real`; `s1:num->real`; `EN:num->real->real^3->A`;
     `A1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[p2bt_lim] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  USE_THEN "req" (MP_TAC o SPECL
    [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
     `(\n. p2bt_cutset eps ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) n) ((gamma:num->real->A) n)
             ((EN:num->real->real^3->A) n) ((s0:num->real) n) ((s1:num->real) n) A1)`;
     `p2bt_zbase eps C (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) gamma s0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `inv(sqrt(&32 * C pow 2))` THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN ACCEPT_TAC]);;

