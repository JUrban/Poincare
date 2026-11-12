(* ========================================================================= *)
(* pc_apx_twoends: the body of the statement                                 *)
(* P2C_REQ_TWO_ENDS_NO_CAP: a complete connected 3-manifold with sec >= 0    *)
(* and two ends (two different components of M minus a compact set K, both  *)
(* with noncompact closure) contains no (C,eps)-cap, for eps <= eps0 with    *)
(* eps0 independent of C.  The statement APXT_TWO_ENDS_NO_CAP_BODY is the    *)
(* right-hand side of the definition at type A; the thin unit                *)
(* pc_apx_twoendsreq proves P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT from it.       *)
(*                                                                           *)
(* Route:                                                                    *)
(*  (A) two ends give a line (no curvature): far points p_n, q_n in the two  *)
(*      ends, a point x_n of K on a minimizing geodesic from p_n to q_n, a   *)
(*      cluster point z of the x_n in K, and limit directions at z of the    *)
(*      segments from z to p_n and q_n (CMPB_DIR_SUBSEQ twice); the excess   *)
(*      of the broken path p_n, z, q_n is at most 2 d(x_n, z), so the two    *)
(*      limit rays glue to a line;                                           *)
(*  (B) with sec >= 0 the Busemann function f of the line is affine          *)
(*      (CMPSP_LINE_E_HYPS, then CMP_AFFINE_PARALLEL):                       *)
(*      f(exp_x w) = f x + <w, X x>_g with a unit field X;                   *)
(*  (C) no cap carries such an f: the cap's diameter clause (the fifth       *)
(*      conjunct of rfs_cap) bounds f on the cap, so the geodesics from a    *)
(*      point y at level -1/(2 eps) of the end neck in the directions X y    *)
(*      and -X y leave the core side Q of the neck through its central       *)
(*      sphere S; each exit time is at least sqrt(1 - eps) h/(2 eps), while  *)
(*      the two exit times add up to the oscillation of f on S, at most      *)
(*      sqrt(1 + eps) h sqrt(2) pi.                                          *)
(* ========================================================================= *)

needs "src/pc_apx_far.ml";;
needs "src/pc_cmp_split.ml";;
needs "src/pc_geo_hr.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* (A) two ends give a line.                                                 *)
(* ========================================================================= *)

(* (A) Two ends give a line.  A1: far points in an end. *)

let APXT_FAR_POINTS = prove
 (`!top atlas (g:A->real^N^N) U x0 R.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ x0 IN topspace top /\
     U SUBSET topspace top /\ ~compact_in top (top closure_of U)
     ==> ?p. p IN U /\ R <= mfd_dist (top,atlas) g x0 p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LE]) THEN
  UNDISCH_TAC `~compact_in top (top closure_of (U:A->bool))` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) x0 R` THEN
  REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `p:A`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A2: a minimizing geodesic between the two ends passes through K. *)

let APXT_SPLIT_POINT = prove
 (`!top atlas (g:A->real^N^N) K U1 U2 p q.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\
     U1 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
     U2 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
     ~(U1 = U2) /\ p IN U1 /\ q IN U2
     ==> ?x. x IN K /\ x IN topspace top /\
             mfd_dist (top,atlas) g p x + mfd_dist (top,atlas) g x q =
             mfd_dist (top,atlas) g p q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN topspace top /\ (q:A) IN topspace top` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `subtopology top (topspace top DIFF K:A->bool)`
                 CONNECTED_COMPONENTS_OF_SUBSET) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `U1:A->bool` th) THEN MP_TAC(SPEC `U2:A->bool` th)) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p q` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `q:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `v:real^N`] GEOD_RADIAL_GEODESIC) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `c = mfd_geo (top,atlas) (g:A->real^N^N) p v` THEN
  SUBGOAL_THEN `?tau. &0 <= tau /\ tau <= &1 /\ (c:real->A) tau IN K` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
    SUBGOAL_THEN `IMAGE (c:real->A) (real_interval[&0,&1]) SUBSET U1` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
      EXISTS_TAC `subtopology top (topspace top DIFF K:A->bool)` THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
        EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
        REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEANREAL_INTERVAL;
                    SUBSET_REFL] THEN
        UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (c:real->A) (&0) (&1)` THEN
        SIMP_TAC[mfd_c1_curve];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `c:real->A`; `&0`; `&1`] MFD_C1_CURVE_IN_TOPSPACE) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
        EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `&0` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`subtopology top (topspace top DIFF K:A->bool)`; `U1:A->bool`;
                     `U2:A->bool`] CONNECTED_COMPONENTS_OF_DISJOINT) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->A) tau IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:real->A`; `&0`; `&1`; `tau:real`] MFD_C1_CURVE_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  EXISTS_TAC `(c:real->A) tau` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:real->A`; `&0`; `tau:real`; `&1`] MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b d x y. a <= x /\ b <= y /\ x + y = d /\ d <= a + b ==> a + b = d`) THEN
  EXISTS_TAC `mfd_length atlas (g:A->real^N^N) c (&0) tau` THEN
  EXISTS_TAC `mfd_length atlas (g:A->real^N^N) c tau (&1)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `c:real->A`; `&0`; `tau:real`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `c:real->A`; `tau:real`; `&1`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`mfd_length atlas (g:A->real^N^N) c (&0) (&1) = mfd_dist (top,atlas) g p q`;
      `mfd_length atlas (g:A->real^N^N) c (&0) (&1) =
       mfd_length atlas g c (&0) tau + mfd_length atlas g c tau (&1)`] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]]);;

(* A4: a sequence in a compact set has a cluster point (for the manifold     *)
(* distance).                                                                 *)

let APXT_CLUSTER = prove
 (`!top atlas (g:A->real^N^N) K (xs:num->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     connected_space top /\ compact_in top K /\ (!n. xs n IN K)
     ==> ?x. x IN K /\
             !d N. &0 < d ==> ?n. N <= n /\ mfd_dist (top,atlas) g (xs n) x < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM;
                                       NOT_IMP; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `!x:A. x IN K ==> ?d N. &0 < d /\
                     !n. N <= n ==> d <= mfd_dist (top,atlas) (g:A->real^N^N) ((xs:num->A) n) x`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:A->real` (X_CHOOSE_THEN `NN:A->num` (LABEL_TAC "sep"))) THEN
  UNDISCH_TAC `compact_in top (K:A->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `{mfd_ball (top,atlas) (g:A->real^N^N) x (dd x) | x IN K}` o
             CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:A) IN topspace top /\ &0 < (dd:A->real) x` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]; ALL_TAC] THEN
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?Fs. FINITE Fs /\ Fs SUBSET K /\
                    V = IMAGE (\x. mfd_ball (top,atlas) (g:A->real^N^N) x (dd x)) Fs`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FINITE_SUBSET_IMAGE] THEN ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?N0. !x:A. x IN Fs ==> (NN:A->num) x <= N0` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (NN:A->num) Fs` num_FINITE) THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xs:num->A) N0 IN UNIONS V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(xs:num->A) N0 IN mfd_ball (top,atlas) (g:A->real^N^N) x (dd x)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "sep" (MP_TAC o SPEC `x:A`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `N0:num` o CONJUNCT2) THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `(xs:num->A) N0`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x ((xs:num->A) N0) < dd x` THEN
  REAL_ARITH_TAC);;

(* A3: a minimizing unit-speed geodesic segment from p0 to x.  This is the  *)
(* first half of CMPSO_SEGMENT (pc_cmp_soul), which is outside this load    *)
(* closure (it pulls in pc_cmp_shup and pc_rfa_secpres).                    *)

let APXT_SEGMENT = prove
 (`!top atlas (g:A->real^N^N) (p0:A) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        p0 IN topspace top /\ mfd_joinable (top,atlas) p0 x /\ ~(x = p0)
        ==> ?u. mfd_tnorm g p0 u = &1 /\
                mfd_geo (top,atlas) g p0 u (mfd_dist (top,atlas) g p0 x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `l = mfd_dist (top,atlas) (g:A->real^N^N) p0 x` THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x:A`] MFD_DIST_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p0:A`; `x:A`] MFD_DIST_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_LE];
    ALL_TAC] THEN
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
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p0:A`; `inv l % (v:real^N)`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p0 (inv l % v) l =
                mfd_exp (top,atlas) g p0 (l % inv l % v)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

(* A4: a compact set is bounded for the manifold distance. *)

let APXT_COMPACT_BOUNDED = prove
 (`!top atlas (g:A->real^N^N) K x0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ compact_in top K
     ==> ?D. !k. k IN K ==> mfd_dist (top,atlas) g x0 k <= D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`] MFD_DIST_CONTINUOUS_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`;
                 `\y:A. mfd_dist (top,atlas) (g:A->real^N^N) x0 y`; `K:A->bool`]
                IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL; MBOUNDED_REAL_EUCLIDEAN_METRIC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* A6: the cluster point as an "eventually" statement along an index map m *)
(* with k <= m k.                                                           *)

let APXT_CLUSTER_SEQ = prove
 (`!top atlas (g:A->real^N^N) K (xs:num->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     connected_space top /\ compact_in top K /\ (!n. xs n IN K)
     ==> ?x (m:num->num). x IN K /\ (!k. k <= m k) /\
             !e. &0 < e ==> ?N. !k. N <= k ==> mfd_dist (top,atlas) g (xs(m k)) x < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `K:A->bool`; `xs:num->A`] APXT_CLUSTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cl"))) THEN
  SUBGOAL_THEN `!k. ?n. k <= n /\
                        mfd_dist (top,atlas) (g:A->real^N^N) ((xs:num->A) n) x < inv(&k + &1)`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `m:num->num` (LABEL_TAC "m")) THEN
  MAP_EVERY EXISTS_TAC [`x:A`; `m:num->num`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "m" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  USE_THEN "m" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&k + &1)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* A7: two unit geodesics from x with d(r1 s, r2 t) = s + t glue to a line. *)

let APXT_LINE_GLUE = prove
 (`!top atlas (g:A->real^N^N) (x:A) u1 u2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ x IN topspace top /\
     mfd_tnorm g x u1 = &1 /\ mfd_tnorm g x u2 = &1 /\
     (!s t. &0 <= s /\ &0 <= t
            ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x u1 s)
                         (mfd_geo (top,atlas) g x u2 t) = s + t)
     ==> ?lam. !s t. lam s IN topspace top /\
                     mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus smooth riem comp x n1 n2 cross" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `u1:real^N`] CMPB_GEO_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `u2:real^N`] CMPB_GEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r1 = mfd_geo (top,atlas) (g:A->real^N^N) x u1` THEN
  ABBREV_TAC `r2 = mfd_geo (top,atlas) (g:A->real^N^N) x u2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r20") (CONJUNCTS_THEN2 (LABEL_TAC "r2top")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "r2lip")))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "r10") (CONJUNCTS_THEN2 (LABEL_TAC "r1top")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "r1lip")))) THEN
  SUBGOAL_THEN `!s. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) ((r1:real->A) s) x /\
                    mfd_joinable (top,atlas) x ((r2:real->A) s)`
  (LABEL_TAC "jx") THENL
   [GEN_TAC THEN
    USE_THEN "r1lip" (MP_TAC o CONJUNCT1 o SPECL [`s:real`; `&0`]) THEN
    USE_THEN "r2lip" (MP_TAC o CONJUNCT1 o SPECL [`&0`; `s:real`]) THEN
    USE_THEN "r10" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "r20" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s ==> mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A) s) x = s /\
                                mfd_dist (top,atlas) g x ((r2:real->A) s) = s`
  (LABEL_TAC "rad") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A) s) ((r2:real->A) (&0)) =
                    s + &0` MP_TAC THENL
       [USE_THEN "cross" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "r20" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A) (&0)) ((r2:real->A) s) =
                    &0 + s` MP_TAC THENL
       [USE_THEN "cross" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "r10" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ &0 <= t
                      ==> mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A) s) (r1 t) =
                          abs(t - s)`
  (LABEL_TAC "ray1") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A) t) x <=
      mfd_dist (top,atlas) g (r1 t) (r1 s) + mfd_dist (top,atlas) g (r1 s) x /\
      mfd_dist (top,atlas) g (r1 s) x <=
      mfd_dist (top,atlas) g (r1 s) (r1 t) + mfd_dist (top,atlas) g (r1 t) x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "rad" (MP_TAC o C MATCH_MP (ASSUME `&0 <= s`)) THEN
    USE_THEN "rad" (MP_TAC o C MATCH_MP (ASSUME `&0 <= t`)) THEN
    USE_THEN "r1lip" (MP_TAC o CONJUNCT2 o SPECL [`s:real`; `t:real`]) THEN
    USE_THEN "smooth" (fun th -> MP_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `(r1:real->A) s`; `(r1:real->A) t`] MFD_DIST_SYM) th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s t. &0 <= s /\ &0 <= t
                      ==> mfd_dist (top,atlas) (g:A->real^N^N) ((r2:real->A) s) (r2 t) =
                          abs(t - s)`
  (LABEL_TAC "ray2") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:A->real^N^N) x ((r2:real->A) t) <=
      mfd_dist (top,atlas) g x (r2 s) + mfd_dist (top,atlas) g (r2 s) (r2 t) /\
      mfd_dist (top,atlas) g x (r2 s) <=
      mfd_dist (top,atlas) g x (r2 t) + mfd_dist (top,atlas) g (r2 t) (r2 s)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "rad" (MP_TAC o C MATCH_MP (ASSUME `&0 <= s`)) THEN
    USE_THEN "rad" (MP_TAC o C MATCH_MP (ASSUME `&0 <= t`)) THEN
    USE_THEN "r2lip" (MP_TAC o CONJUNCT2 o SPECL [`s:real`; `t:real`]) THEN
    USE_THEN "smooth" (fun th -> MP_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `(r2:real->A) s`; `(r2:real->A) t`] MFD_DIST_SYM) th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `\s. if &0 <= s then (r2:real->A) s else (r1:real->A)(--s)` THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s` THEN ASM_CASES_TAC `&0 <= t` THEN ASM_REWRITE_TAC[] THENL
   [USE_THEN "ray2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A)(--t)) ((r2:real->A) s) =
                  --t + s` MP_TAC THENL
     [USE_THEN "cross" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "smooth" (fun th -> MP_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `(r1:real->A)(--t)`; `(r2:real->A) s`] MFD_DIST_SYM) th)) THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A)(--s)) ((r2:real->A) t) =
                  --s + t` SUBST1_TAC THENL
     [USE_THEN "cross" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((r1:real->A)(--s)) ((r1:real->A)(--t)) =
                  abs(--t - --s)` SUBST1_TAC THENL
     [USE_THEN "ray1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* A8: the limit rays.  Unit directions u1 k, u2 k at x with segment       *)
(* lengths l1 k, l2 k >= k whose broken paths are almost minimizing (the    *)
(* defect dd k tends to 0) have limit directions v1, v2 (CMPB_DIR_SUBSEQ,   *)
(* applied twice) with d(geo v1 s, geo v2 t) = s + t.                       *)

let APXT_RAY_PAIR = prove
 (`!top atlas (g:A->real^N^N) (x:A) (u1:num->real^N) u2 (l1:num->real) l2 (dd:num->real).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ x IN topspace top /\
     (!k. mfd_tnorm g x (u1 k) = &1 /\ mfd_tnorm g x (u2 k) = &1) /\
     (!k. &k <= l1 k /\ &k <= l2 k) /\
     (!k. l1 k + l2 k <=
          mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x (u1 k) (l1 k))
                                 (mfd_geo (top,atlas) g x (u2 k) (l2 k)) + dd k) /\
     (!e. &0 < e ==> ?N. !k. N <= k ==> dd k < e)
     ==> ?v1 v2. mfd_tnorm g x v1 = &1 /\ mfd_tnorm g x v2 = &1 /\
                 !s t. &0 <= s /\ &0 <= t
                       ==> mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x v1 s)
                                    (mfd_geo (top,atlas) g x v2 t) = s + t`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus smooth riem comp conn x unit len split dd" THEN
  SUBGOAL_THEN `!a b c:A. a IN topspace top /\ b IN topspace top /\ c IN topspace top
                ==> mfd_dist (top,atlas) (g:A->real^N^N) a c <=
                    mfd_dist (top,atlas) g a b + mfd_dist (top,atlas) g b c`
  (LABEL_TAC "tri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. mfd_tnorm (g:A->real^N^N) x v = &1
       ==> mfd_geo (top,atlas) g x v (&0) = x /\
           (!s. mfd_geo (top,atlas) g x v s IN topspace top) /\
           (!s. mfd_exp (top,atlas) g x (s % v) = mfd_geo (top,atlas) g x v s) /\
           (!s t. mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x v s)
                           (mfd_geo (top,atlas) g x v t) <= abs(t - s))`
  (LABEL_TAC "geo") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `v:real^N`] CMPB_GEO_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!k s. mfd_exp (top,atlas) (g:A->real^N^N) x (s % (u1:num->real^N) k) =
           mfd_geo (top,atlas) g x (u1 k) s) /\
    (!k s. mfd_exp (top,atlas) g x (s % (u2:num->real^N) k) =
           mfd_geo (top,atlas) g x (u2 k) s) /\
    (!k s. mfd_geo (top,atlas) g x (u1 k) s IN topspace top) /\
    (!k s. mfd_geo (top,atlas) g x (u2 k) s IN topspace top) /\
    (!k s t. mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x (u1 k) s)
                      (mfd_geo (top,atlas) g x (u1 k) t) <= abs(t - s)) /\
    (!k s t. mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x (u2 k) s)
                      (mfd_geo (top,atlas) g x (u2 k) t) <= abs(t - s))`
  (CONJUNCTS_THEN2 (LABEL_TAC "e1") (CONJUNCTS_THEN2 (LABEL_TAC "e2")
    (CONJUNCTS_THEN2 (LABEL_TAC "t1") (CONJUNCTS_THEN2 (LABEL_TAC "t2")
    (CONJUNCTS_THEN2 (LABEL_TAC "lip1") (LABEL_TAC "lip2")))))) THENL
   [SUBGOAL_THEN `!k. mfd_tnorm (g:A->real^N^N) x ((u1:num->real^N) k) = &1 /\
                      mfd_tnorm g x ((u2:num->real^N) k) = &1` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "geo" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `u1:num->real^N`] CMPB_DIR_SUBSEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `sub1:num->num`
    (CONJUNCTS_THEN2 (LABEL_TAC "v1n") (CONJUNCTS_THEN2 (LABEL_TAC "sub1")
       (LABEL_TAC "conv1"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `\n. (u2:num->real^N)((sub1:num->num) n)`] CMPB_DIR_SUBSEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v2:real^N` (X_CHOOSE_THEN `sub2:num->num`
    (CONJUNCTS_THEN2 (LABEL_TAC "v2n") (CONJUNCTS_THEN2 (LABEL_TAC "sub2")
       (LABEL_TAC "conv2"))))) THEN
  USE_THEN "v1n" (fun n -> USE_THEN "geo" (fun th -> MP_TAC(MATCH_MP th n))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v10") (CONJUNCTS_THEN2 (LABEL_TAC "v1top")
    (CONJUNCTS_THEN2 (LABEL_TAC "v1exp") (LABEL_TAC "v1lip")))) THEN
  USE_THEN "v2n" (fun n -> USE_THEN "geo" (fun th -> MP_TAC(MATCH_MP th n))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v20") (CONJUNCTS_THEN2 (LABEL_TAC "v2top")
    (CONJUNCTS_THEN2 (LABEL_TAC "v2exp") (LABEL_TAC "v2lip")))) THEN
  MAP_EVERY EXISTS_TAC [`v1:real^N`; `v2:real^N`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [(* upper bound through x *)
    USE_THEN "v1lip" (MP_TAC o SPECL [`s:real`; `&0`]) THEN
    USE_THEN "v2lip" (MP_TAC o SPECL [`&0`; `t:real`]) THEN
    USE_THEN "v10" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "v20" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "tri" (MP_TAC o SPECL [`mfd_geo (top,atlas) (g:A->real^N^N) x v1 s`; `x:A`;
                                    `mfd_geo (top,atlas) (g:A->real^N^N) x v2 t`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* lower bound: a contradiction with a small e *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x v1 s)
                           (mfd_geo (top,atlas) g x v2 t)` THEN
  ABBREV_TAC `e = (s + t - D) / &8` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "conv1" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`) o SPEC `s:real`) THEN
  USE_THEN "v1exp" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  USE_THEN "conv2" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`) o SPEC `t:real`) THEN
  REWRITE_TAC[] THEN
  USE_THEN "v2exp" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  USE_THEN "dd" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "N3")) THEN
  MP_TAC(SPEC `s + t:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  SUBGOAL_THEN
   `?k. s + t <= &k /\ (dd:num->real) k < e /\
        mfd_dist (top,atlas) (g:A->real^N^N) (mfd_geo (top,atlas) g x v1 s)
                 (mfd_geo (top,atlas) g x ((u1:num->real^N) k) s) < e /\
        mfd_dist (top,atlas) g (mfd_geo (top,atlas) g x v2 t)
                 (mfd_geo (top,atlas) g x ((u2:num->real^N) k) t) < e`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `n = N1 + N2 + N3 + M:num` THEN
    EXISTS_TAC `(sub1:num->num)((sub2:num->num) n)` THEN
    SUBGOAL_THEN `n <= (sub2:num->num) n /\ sub2 n <= (sub1:num->num)(sub2 n)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "sub1" (fun th1 -> USE_THEN "sub2" (fun th2 ->
        REWRITE_TAC[MATCH_MP MONOTONE_BIGGER th1; MATCH_MP MONOTONE_BIGGER th2]));
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      USE_THEN "N3" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "N1" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "N2" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "len" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  USE_THEN "split" (ASSUME_TAC o SPEC `k:num`) THEN
  USE_THEN "lip1" (ASSUME_TAC o SPECL [`k:num`; `(l1:num->real) k`; `s:real`]) THEN
  USE_THEN "lip2" (ASSUME_TAC o SPECL [`k:num`; `t:real`; `(l2:num->real) k`]) THEN
  USE_THEN "t1" (ASSUME_TAC o SPECL [`k:num`; `s:real`]) THEN
  USE_THEN "t2" (ASSUME_TAC o SPECL [`k:num`; `t:real`]) THEN
  USE_THEN "t1" (ASSUME_TAC o SPECL [`k:num`; `(l1:num->real) k`]) THEN
  USE_THEN "t2" (ASSUME_TAC o SPECL [`k:num`; `(l2:num->real) k`]) THEN
  USE_THEN "v1top" (ASSUME_TAC o SPEC `s:real`) THEN
  USE_THEN "v2top" (ASSUME_TAC o SPEC `t:real`) THEN
  ABBREV_TAC `a = mfd_geo (top,atlas) (g:A->real^N^N) x ((u1:num->real^N) k) s` THEN
  ABBREV_TAC `b = mfd_geo (top,atlas) (g:A->real^N^N) x ((u2:num->real^N) k) t` THEN
  ABBREV_TAC `P = mfd_geo (top,atlas) (g:A->real^N^N) x ((u1:num->real^N) k) (l1 k)` THEN
  ABBREV_TAC `Q = mfd_geo (top,atlas) (g:A->real^N^N) x ((u2:num->real^N) k) (l2 k)` THEN
  ABBREV_TAC `p1 = mfd_geo (top,atlas) (g:A->real^N^N) x v1 s` THEN
  ABBREV_TAC `p2 = mfd_geo (top,atlas) (g:A->real^N^N) x v2 t` THEN
  USE_THEN "smooth" (fun th -> ASSUME_TAC(MP
    (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
             `a:A`; `p1:A`] MFD_DIST_SYM) th)) THEN
  USE_THEN "tri" (MP_TAC o SPECL [`P:A`; `a:A`; `Q:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "tri" (MP_TAC o SPECL [`a:A`; `b:A`; `Q:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "tri" (MP_TAC o SPECL [`a:A`; `p1:A`; `b:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "tri" (MP_TAC o SPECL [`p1:A`; `p2:A`; `b:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* A9: two ends give a line. *)

let APXT_TWO_ENDS_LINE = prove
 (`!top atlas (g:A->real^N^N) K U1 U2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ connected_space top /\ compact_in top K /\
     U1 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
     U2 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
     ~(U1 = U2) /\ ~compact_in top (top closure_of U1) /\ ~compact_in top (top closure_of U2)
     ==> ?lam:real->A. !s t. lam s IN topspace top /\
                             mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s)`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus smooth riem comp conn cpt c1 c2 ne nc1 nc2" THEN
  SUBGOAL_THEN `!a b c:A. a IN topspace top /\ b IN topspace top /\ c IN topspace top
                ==> mfd_dist (top,atlas) (g:A->real^N^N) a c <=
                    mfd_dist (top,atlas) g a b + mfd_dist (top,atlas) g b c`
  (LABEL_TAC "tri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U1:A->bool) SUBSET topspace top /\ (U2:A->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `subtopology top (topspace top DIFF K:A->bool)`
                 CONNECTED_COMPONENTS_OF_SUBSET) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `U1:A->bool` th) THEN MP_TAC(SPEC `U2:A->bool` th)) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `?x0:A. x0 IN U1` (X_CHOOSE_TAC `x0:A`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `~compact_in top (top closure_of (U1:A->bool))` THEN
    ASM_REWRITE_TAC[CLOSURE_OF_EMPTY; COMPACT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `K:A->bool`; `x0:A`] APXT_COMPACT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real` (LABEL_TAC "D")) THEN
  SUBGOAL_THEN `!n. ?p q. p IN U1 /\ &n + D + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) x0 p /\
                          q IN U2 /\ &n + D + &1 <= mfd_dist (top,atlas) g x0 q`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `U1:A->bool`; `x0:A`; `&n + D + &1`] APXT_FAR_POINTS) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `U2:A->bool`; `x0:A`; `&n + D + &1`] APXT_FAR_POINTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `pp:num->A` (X_CHOOSE_THEN `qq:num->A` (LABEL_TAC "far"))) THEN
  SUBGOAL_THEN `!n. (pp:num->A) n IN topspace top /\ (qq:num->A) n IN topspace top`
  (LABEL_TAC "pqtop") THENL
   [GEN_TAC THEN USE_THEN "far" (MP_TAC o SPEC `n:num`) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?y. y IN K /\ y IN topspace top /\
            mfd_dist (top,atlas) (g:A->real^N^N) ((pp:num->A) n) y +
            mfd_dist (top,atlas) g y ((qq:num->A) n) =
            mfd_dist (top,atlas) g (pp n) (qq n)`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC APXT_SPLIT_POINT THEN
    MAP_EVERY EXISTS_TAC [`U1:A->bool`; `U2:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `xx:num->A` (LABEL_TAC "split")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `K:A->bool`; `xx:num->A`] APXT_CLUSTER_SEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `m:num->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mk") (LABEL_TAC "conv"))))) THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. &k + &1 <= mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k)) /\
        &k + &1 <= mfd_dist (top,atlas) g z ((qq:num->A)(m k))`
  (LABEL_TAC "farz") THENL
   [GEN_TAC THEN
    USE_THEN "far" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "D" (ASSUME_TAC o C MATCH_MP (ASSUME `(z:A) IN K`)) THEN
    SUBGOAL_THEN `&k <= &((m:num->num) k)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    USE_THEN "tri" (MP_TAC o SPECL [`x0:A`; `z:A`; `(pp:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "tri" (MP_TAC o SPECL [`x0:A`; `z:A`; `(qq:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?w1 w2. mfd_tnorm (g:A->real^N^N) z w1 = &1 /\ mfd_tnorm g z w2 = &1 /\
                mfd_geo (top,atlas) g z w1
                  (mfd_dist (top,atlas) g z ((pp:num->A)((m:num->num) k))) = pp(m k) /\
                mfd_geo (top,atlas) g z w2
                  (mfd_dist (top,atlas) g z ((qq:num->A)(m k))) = qq(m k)`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "farz" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
    USE_THEN "pqtop" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((pp:num->A)((m:num->num) k) = z) /\ ~((qq:num->A)(m k) = z)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `z:A`] MFD_DIST_REFL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `(pp:num->A)((m:num->num) k)`] APXT_SEGMENT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `z:A`; `(qq:num->A)((m:num->num) k)`] APXT_SEGMENT) THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool)
                                z ((pp:num->A)((m:num->num) k)) /\
                  mfd_joinable (top,atlas) z ((qq:num->A)(m k))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`w1:real^N`; `w2:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:num->real^N` (X_CHOOSE_THEN `w2:num->real^N`
    (LABEL_TAC "seg"))) THEN
  SUBGOAL_THEN
   `!k. &k <= mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k)) /\
        &k <= mfd_dist (top,atlas) g z ((qq:num->A)(m k))`
  (LABEL_TAC "len") THENL
   [GEN_TAC THEN USE_THEN "farz" (MP_TAC o SPEC `k:num`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k)) +
        mfd_dist (top,atlas) g z ((qq:num->A)(m k)) <=
        mfd_dist (top,atlas) g (pp(m k)) (qq(m k)) +
        &2 * mfd_dist (top,atlas) g ((xx:num->A)(m k)) z`
  (LABEL_TAC "almost") THENL
   [X_GEN_TAC `k:num` THEN
    USE_THEN "split" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "pqtop" (MP_TAC o SPEC `(m:num->num) k`) THEN STRIP_TAC THEN
    USE_THEN "tri" (MP_TAC o SPECL [`z:A`; `(xx:num->A)((m:num->num) k)`;
                                    `(pp:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "tri" (MP_TAC o SPECL [`z:A`; `(xx:num->A)((m:num->num) k)`;
                                    `(qq:num->A)((m:num->num) k)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "smooth" (fun th -> ASSUME_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `z:A`; `(xx:num->A)((m:num->num) k)`] MFD_DIST_SYM) th)) THEN
    USE_THEN "smooth" (fun th -> ASSUME_TAC(MP
      (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
               `(pp:num->A)((m:num->num) k)`; `(xx:num->A)((m:num->num) k)`]
              MFD_DIST_SYM) th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e ==> ?N. !k. N <= k
        ==> &2 * mfd_dist (top,atlas) (g:A->real^N^N) ((xx:num->A)((m:num->num) k)) z < e`
  (LABEL_TAC "ddc") THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `z:A`; `w1:num->real^N`; `w2:num->real^N`;
                 `\k. mfd_dist (top,atlas) (g:A->real^N^N) z ((pp:num->A)((m:num->num) k))`;
                 `\k. mfd_dist (top,atlas) (g:A->real^N^N) z ((qq:num->A)((m:num->num) k))`;
                 `\k. &2 * mfd_dist (top,atlas) (g:A->real^N^N) ((xx:num->A)((m:num->num) k)) z`]
                APXT_RAY_PAIR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC APXT_LINE_GLUE THEN
  MAP_EVERY EXISTS_TAC [`z:A`; `v1:real^N`; `v2:real^N`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* (B) the line gives an affine function.                                    *)
(* ========================================================================= *)

(* (B) A line in a complete manifold with sec >= 0 gives an affine function: *)
(* the Busemann function of the line (CMPSP_LINE_E_HYPS) satisfies the      *)
(* hypotheses of CMP_AFFINE_PARALLEL, which gives the unit parallel field X *)
(* with f(exp_x w) = f x + <w, X x>.                                        *)

let APXT_LINE_AFFINE = prove
 (`!top atlas (g:A->real^N^N) (lam:real->A).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 <= mfd_sectional atlas g x u v) /\
     (!s t. lam s IN topspace top /\ mfd_dist (top,atlas) g (lam s) (lam t) = abs(t - s))
     ==> ?f X. (!y z. mfd_joinable (top,atlas) y z
                      ==> abs(f y - f z) <= mfd_dist (top,atlas) g y z) /\
               (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
               (!x w. x IN topspace top
                      ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `lam:real->A`] CMPSP_LINE_E_HYPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `cmp_busemann (top,atlas) (g:A->real^N^N) lam`] CMP_AFFINE_PARALLEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `X:A->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`cmp_busemann (top,atlas) (g:A->real^N^N) lam`; `X:A->real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* (C) no cap carries an affine function with unit gradient.                *)
(* ========================================================================= *)

(* (C) No (C,eps)-cap in a complete manifold carrying an affine function f  *)
(* with unit gradient field X (f(exp_x w) = f x + <w, X x>): the geodesic   *)
(* through a point of the lower half of the cap's end neck in the direction *)
(* of X leaves the core side of the cap through the central sphere S in    *)
(* both directions, at distance at least about h/(2 eps), while f varies by *)
(* at most about sqrt(2) pi h on S.                                         *)

let APXT_AFFINE_NO_CAP = prove
 (`?eps0. &0 < eps0 /\
     !C eps top atlas (g:A->real^3^3) (f:A->real) (X:A->real^3) U Y.
       &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
       smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
       mfd_complete (top,atlas) g /\ connected_space top /\
       (!y z. mfd_joinable (top,atlas) y z ==> abs(f y - f z) <= mfd_dist (top,atlas) g y z) /\
       (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
       (!x w. x IN topspace top ==> f(mfd_exp (top,atlas) g x w) = f x + w dot (g x ** X x))
       ==> ~rfs_cap (top,atlas) g C eps U Y`,
  X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e3:real` STRIP_ASSUME_TAC (INST_TYPE [`:A`,`:A`] APX_CH_N4R_HOLDS) THEN
  EXISTS_TAC `min (min e1 e3) (&1 / &1024)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `f:A->real`; `X:A->real^3`;
    `U:A->bool`; `Y:A->bool`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `apx_ch_ctx top atlas (g:A->real^3^3) eps /\ apx_ch_n4r top atlas g eps`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`] o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `e1:real`)) (concl th))) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`] o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `e3:real`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 <= inv eps /\ eps < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &1024`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the diameter clause of the cap bounds f on U *)
  SUBGOAL_THEN `?B. !y1 y2. y1 IN U /\ y2 IN U
                            ==> mfd_dist_in (top,atlas) (g:A->real^3^3) U y1 y2 <= B`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
    REWRITE_TAC[rfs_cap] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (ASSUME_TAC o CONJUNCT2)) THEN
    EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y1:A`; `y2:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN U /\ y2 IN U ==> abs((f:A->real) y1 - f y2) <= B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX_CAP_JOINABLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`y1:A`; `y2:A`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `U:A->bool`; `y1:A`; `y2:A`] MFD_DIST_LE_DIST_IN) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) y1 y2` ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U y1 y2` THEN
      REWRITE_TAC[mfd_joinable_in; mfd_joinable] THEN MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:A`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `f:A->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_joinable")) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y1:A`; `y2:A`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `B:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the cap's end neck *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] APX22_CAP_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e0:real^3->A` (X_CHOOSE_THEN `z0:A` (X_CHOOSE_THEN `K:A->bool`
      STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e0:real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) z0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z0 e0` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ABBREV_TAC `h0 = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z0))` THEN
  SUBGOAL_THEN `&0 < h0` ASSUME_TAC THENL
   [EXPAND_TAC "h0" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0))` THEN
  ABBREV_TAC `S = IMAGE (e0:real^3->A) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (&0) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Q:A->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e0:real^3->A) (rfs_neck_dom eps)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the point y in the lower half at level -1/(2 eps) *)
  ABBREV_TAC `yv = exp(--inv(&2 * eps) / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `~(basis 1:real^3 = vec 0) /\ norm(basis 1:real^3) = &1` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[BASIS_NONZERO; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(yv:real^3) = --inv(&2 * eps) /\ ~(yv = vec 0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "yv" THEN
    SIMP_TAC[APX_SVAL_EXP_SCALE; ASSUME `~(basis 1:real^3 = vec 0)`;
             APX_SVAL_UNIT; ASSUME `norm(basis 1:real^3) = &1`; REAL_ADD_RID;
             VECTOR_MUL_EQ_0; REAL_EXP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(yv:real^3) IN apx_slab (--inv eps) (&0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = (e0:real^3->A) yv` THEN
  SUBGOAL_THEN `(y:A) IN Q /\ (yv:real^3) IN rfs_neck_dom eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "Q" THEN EXPAND_TAC "y" THEN ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] OPEN_IN_SUBSET) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* the geodesics through y in the directions +X y and -X y *)
  ABBREV_TAC `u = (X:A->real^3) y` THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^3^3) y u = &1 /\ mfd_tnorm g y (--u) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tnorm; MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
    EXPAND_TAC "u" THEN ASM_SIMP_TAC[SQRT_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^3^3) y = (:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`] MFD_HOPF_RINOW_POINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^3. mfd_tnorm (g:A->real^3^3) y v = &1 /\ (v = u \/ v = --u)
       ==> ?t. &0 < t /\ mfd_geo (top,atlas) g y v t IN S /\
               (!s. (f:A->real)(mfd_geo (top,atlas) g y v s) = f y + s * (v dot (g y ** u))) /\
               mfd_dist (top,atlas) g y (mfd_geo (top,atlas) g y v t) <= t`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vu")) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `v:real^3`] CMPB_GEO_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v0") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "vexp") (LABEL_TAC "lip")))) THEN
    SUBGOAL_THEN `!s. (f:A->real)(mfd_geo (top,atlas) (g:A->real^3^3) y v s) =
                      f y + s * (v dot (g y ** u))` (LABEL_TAC "fgeo") THENL
     [X_GEN_TAC `s:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:A`; `s % v:real^3`] o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `X:A->real^3`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_exp")) (concl th))) THEN
      ASM_REWRITE_TAC[DOT_LMUL];
      ALL_TAC] THEN
    ABBREV_TAC `T0 = abs B + &1` THEN
    SUBGOAL_THEN `~((mfd_geo (top,atlas) (g:A->real^3^3) y v T0) IN Q)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`mfd_geo (top,atlas) (g:A->real^3^3) y v T0`; `y:A`] o
        check (fun th -> is_forall (concl th) && can (find_term (fun t -> t = `B:real`)) (concl th) &&
               can (find_term (fun t -> t = `f:A->real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "fgeo" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `v dot ((g:A->real^3^3) y ** u) = &1 \/ v dot (g y ** u) = -- &1` MP_TAC THENL
       [USE_THEN "vu" (DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[DOT_LNEG] THEN
        EXPAND_TAC "u" THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "T0" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `v:real^3`; `T0:real`] GEOH_RAY_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `T0:real`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [EXPAND_TAC "T0" THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,T0]),top)
                    (mfd_geo (top,atlas) (g:A->real^3^3) y v)` ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool)
                     (mfd_geo (top,atlas) (g:A->real^3^3) y v) (&0) T0` THEN
      SIMP_TAC[mfd_c1_curve];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `mfd_geo (top,atlas) (g:A->real^3^3) y v`; `Q:A->bool`;
                   `&0`; `T0:real`] APXF_FIRST_TIME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "T0" THEN REAL_ARITH_TAC;
        EXISTS_TAC `T0:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN EXPAND_TAC "T0" THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^3^3) y v t1 IN top closure_of Q` MP_TAC THENL
       [MATCH_MP_TAC APXF_CLOSED_LEFT_CURVE THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `&0`; `T0:real`] THEN
        ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!w. (x:A) IN w /\ w SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `Q:A->bool` THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN
          ASM_REWRITE_TAC[]];
        MAP_EVERY UNDISCH_TAC
         [`K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) = Q`;
          `top closure_of Q SUBSET
           K UNION IMAGE (e0:real^3->A) (apx_slab (--inv eps) (&0)) UNION S`;
          `~(mfd_geo (top,atlas) (g:A->real^3^3) y v t1 IN Q)`] THEN
        SET_TAC[]];
      USE_THEN "lip" (MP_TAC o CONJUNCT2 o SPECL [`&0`; `t1:real`]) THEN
      USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the two exits through S *)
  FIRST_ASSUM(MP_TAC o SPEC `u:real^3` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `S:A->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geo")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--u:real^3` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `S:A->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_geo")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^3) dot ((g:A->real^3^3) y ** u) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DOT_LNEG]) THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `p1 = mfd_geo (top,atlas) (g:A->real^3^3) y u t1` THEN
  ABBREV_TAC `p2 = mfd_geo (top,atlas) (g:A->real^3^3) y (--u) t2` THEN
  SUBGOAL_THEN `?v1 v2:real^3. norm v1 = &1 /\ norm v2 = &1 /\
                               p1 = (e0:real^3->A) v1 /\ p2 = e0 v2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(p1:A) IN S`; `(p2:A) IN S`] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v1:real^3) IN rfs_neck_dom eps /\ (v2:real^3) IN rfs_neck_dom eps /\
                apx_sval v1 = &0 /\ apx_sval v2 = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[APX_SVAL_UNIT] THEN REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* distance bounds in the neck *)
  SUBGOAL_THEN `sqrt(&1 - eps) * h0 * inv(&2 * eps) <= t1 /\
                sqrt(&1 - eps) * h0 * inv(&2 * eps) <= t2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `min (abs(--inv(&2 * eps) - &0)) (&2 * inv eps - abs(--inv(&2 * eps)) - abs(&0))
                  = inv(&2 * eps)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps:real`; `z0:A`; `e0:real^3->A`; `yv:real^3`; `v1:real^3`]
                    APX_NECK_DIST_LOWER) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) y p1 <= t1` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `eps:real`; `z0:A`; `e0:real^3->A`; `yv:real^3`; `v2:real^3`]
                    APX_NECK_DIST_LOWER) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^3^3) y p2 <= t2` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 + t2 <= sqrt(&1 + eps) * h0 * (sqrt(&2) * pi)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `z0:A`; `e0:real^3->A`; `v1:real^3`; `v2:real^3`]
                  APX_NECK_DIST_UPPER) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p1:A`; `p2:A`] o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `f:A->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_joinable")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!s. (f:A->real)(mfd_geo (top,atlas) (g:A->real^3^3) y u s) = f y + s * &1` THEN
    UNDISCH_TAC `!s. (f:A->real)(mfd_geo (top,atlas) (g:A->real^3^3) y (--u) s) =
                     f y + s * -- &1` THEN
    DISCH_THEN(MP_TAC o SPEC `t2:real`) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `t1:real`) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* contradiction *)
  SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - eps) /\ sqrt(&1 + eps) <= &2 /\ sqrt(&2) * pi <= &24 / &5`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_SQRT2_PI] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&256 * h0 <= sqrt(&1 - eps) * h0 * inv(&2 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * h0 * inv(&2 * eps)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&1024 * h0 <= h0 * inv eps` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h0 * (sqrt(&2) * pi) <= &2 * h0 * (&24 / &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* (D) the body of the statement P2C_REQ_TWO_ENDS_NO_CAP.                    *)
(* ========================================================================= *)

(* (D) The body of A8: the right-hand side of P2C_REQ_TWO_ENDS_NO_CAP at    *)
(* type A.  eps0 comes from APXT_AFFINE_NO_CAP and does not depend on C.    *)

let APXT_TWO_ENDS_NO_CAP_BODY = prove
 (`?eps0. &0 < eps0 /\
      !C eps top atlas g.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space (top:A topology) /\
         smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
         (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas g x u v) /\
         (?K U1 U2. compact_in top K /\
                    U1 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                    U2 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                    ~(U1 = U2) /\ ~compact_in top (top closure_of U1) /\
                    ~compact_in top (top closure_of U2))
         ==> !U Y. ~rfs_cap (top,atlas) g C eps U Y`,
  X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nocap"))
    (INST_TYPE [`:A`,`:A`] APXT_AFFINE_NO_CAP) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `K:A->bool`; `U1:A->bool`; `U2:A->bool`] APXT_TWO_ENDS_LINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `lam:real->A`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `lam:real->A`] APXT_LINE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real` (X_CHOOSE_THEN `X:A->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `Y:A->bool`] THEN
  USE_THEN "nocap" (MP_TAC o SPECL [`C:real`; `eps:real`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `f:A->real`; `X:A->real^3`;
    `U:A->bool`; `Y:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

