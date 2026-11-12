(* ========================================================================= *)
(* Unit pc_p2b_capfix (Part 2B, MT Prop 9.79(3)): the uniform cap form       *)
(* P2B_PROP_9_79_CAP_FIX, hence P2B_PROP_9_79_SLICE_FIX, which is            *)
(* P2_PROP_9_79_SLICE, through P2BS_SLICE_FROM_CAP, and the Part 2C          *)
(* statements P2C_REQ_CAP_FIX, P2C_REQ_SLICE_FIX and P2C_REQ_SLICE_LOCAL     *)
(* (A21).  All five are corollaries of general forms whose target hypothesis *)
(* is: the target metric is complete, or psi U has compact closure in the    *)
(* target.                                                                   *)
(*                                                                           *)
(* - connectedness against a frontier; the re-centred sub-cap U0 = Y union   *)
(*   e'(annulus r0 r2) (P2BF_SUBCAP_TOP); the core splits of ball and        *)
(*   twisted caps (P2BF_BALL_SPLIT, P2BF_TWISTED_SPLIT);                     *)
(* - curves between open sets of real^3, paths on neck spheres, and the cut  *)
(*   and replace bound for intrinsic distances (P2BF_CUT_REPLACE);           *)
(* - an explicit modulus for the model volume ratio; clause 7 of the target  *)
(*   with explicit parameters (P2BF_CLAUSE7_GEN2);                           *)
(* - the end neck of a cap, C > sqrt(1 - eps) / eps, and the intrinsic       *)
(*   diameter of the sub-cap (P2BF_SUBCAP_DIAM, excursion replacement);      *)
(* - the sub-cap for ball and twisted cores, uniform neck transfer with      *)
(*   renormalization, the re-centred end neck, clause 7 on the sub-cap;      *)
(* - uniform constants (Ricci bound from Kr, margins, clause 7 eta);         *)
(* - the target volume (P2BF_T_VOL_GEN) and the uniform common lemma         *)
(*   P2BF_CAP_COMMON_UNIF_GEN;                                               *)
(* - radii of the sub-cap and the target chart data (ball, twisted);         *)
(* - the general forms P2BF_CAP_FIX_GEN and P2BF_SLICE_FIX_GEN;              *)
(* - the headlines and the Part 2C statements as corollaries.                *)
(* ========================================================================= *)

needs "src/pc_p2b_slice.ml";;

prioritize_real();;

type_invention_error := true;;

let P2BF_CONN_AVOID = prove
 (`!top c K (S:A->bool).
     connected_in top c /\ top frontier_of K SUBSET S /\ DISJOINT c S /\ ~(c SUBSET K)
     ==> DISJOINT c K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `c:A->bool`; `K:A->bool`]
                CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((c:A->bool) SUBSET K)` THEN
  UNDISCH_TAC `DISJOINT (c:A->bool) S` THEN
  UNDISCH_TAC `top frontier_of (K:A->bool) SUBSET S` THEN SET_TAC[]);;

let P2BF_CONN_INSIDE = prove
 (`!top c K (S:A->bool).
     connected_in top c /\ top frontier_of K SUBSET S /\ DISJOINT c S /\ ~(DISJOINT c K)
     ==> c SUBSET K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `c:A->bool`; `K:A->bool`; `S:A->bool`]
                P2BF_CONN_AVOID) THEN
  ASM_REWRITE_TAC[]);;

let P2BF_SUBCAP_TOP = prove
 (`!top atlas s (e:real^3->A) Y r0 r2.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     open_in top Y /\ compact_in top (top closure_of Y) /\
     top closure_of Y = Y UNION IMAGE e (sphere(vec 0,&1)) /\
     DISJOINT Y (IMAGE e (sphere(vec 0,&1))) /\
     top frontier_of (top closure_of Y) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     &0 < r0 /\ r0 < &1 /\ &1 < r2 /\ {y | r0 <= norm y /\ norm y <= r2} SUBSET s /\
     ~(IMAGE e (annulus (&1) r2) SUBSET top closure_of Y)
     ==> DISJOINT (IMAGE e (annulus (&1) r2)) (top closure_of Y) /\
         IMAGE e (annulus r0 (&1)) SUBSET Y /\
         open_in top (Y UNION IMAGE e (annulus r0 r2)) /\
         (Y UNION IMAGE e (annulus r0 r2)) DIFF top closure_of Y = IMAGE e (annulus (&1) r2) /\
         top closure_of (Y UNION IMAGE e (annulus r0 r2)) SUBSET
           top closure_of Y UNION IMAGE e {y | r0 <= norm y /\ norm y <= r2} /\
         compact_in top (top closure_of (Y UNION IMAGE e (annulus r0 r2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K = top closure_of (Y:A->bool)` THEN
  SUBGOAL_THEN
   `annulus r0 r2 SUBSET (s:real^3->bool) /\ annulus (&1) r2 SUBSET s /\
    annulus r0 (&1) SUBSET s /\ sphere(vec 0:real^3,&1) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `{y:real^3 | r0 <= norm y /\ norm y <= r2}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. u IN s /\ v IN s /\ (e:real^3->A) u = e v ==> u = v`
  (LABEL_TAC "INJ") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(ei:A->real^3) ((e:real^3->A) u) = u /\ ei(e v) = v` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t SUBSET s /\ DISJOINT t (sphere(vec 0:real^3,&1))
        ==> DISJOINT (IMAGE (e:real^3->A) t) (IMAGE e (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u:real^3 = v` ASSUME_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (t:real^3->bool) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `(v:real^3) IN sphere(vec 0,&1)` THEN UNDISCH_TAC `(u:real^3) IN t` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (e:real^3->A) (annulus (&1) r2)) (IMAGE e (sphere(vec 0,&1))) /\
    DISJOINT (IMAGE (e:real^3->A) (annulus r0 (&1))) (IMAGE e (sphere(vec 0,&1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_ELIM_THM;
                IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET K /\ IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET K`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:A->bool) = Y UNION IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e:real^3->A) (annulus (&1) r2)) K` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BF_CONN_AVOID THEN
    EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(DISJOINT (IMAGE (e:real^3->A) (annulus r0 (&1))) K)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    ABBREV_TAC `w0 = basis 1:real^3` THEN
    SUBGOAL_THEN `norm(w0:real^3) = &1` ASSUME_TAC THENL
     [EXPAND_TAC "w0" THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ABBREV_TAC `rho = min (&1 - r0) (r2 - &1)` THEN
    SUBGOAL_THEN `&0 < rho /\ rho <= &1 - r0 /\ rho <= r2 - &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ball(w0:real^3,rho) SUBSET annulus r0 (&1) UNION sphere(vec 0,&1) UNION annulus (&1) r2`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(norm(v:real^3) - &1) < rho` MP_TAC THENL
       [UNDISCH_TAC `dist(w0:real^3,v) < rho` THEN UNDISCH_TAC `norm(w0:real^3) = &1` THEN
        REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball(w0:real^3,rho) SUBSET s` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(w0:real^3,rho) SUBSET
                     annulus r0 (&1) UNION sphere(vec 0,&1) UNION annulus (&1) r2` THEN
      UNDISCH_TAC `annulus r0 (&1) SUBSET (s:real^3->bool)` THEN
      UNDISCH_TAC `annulus (&1) r2 SUBSET (s:real^3->bool)` THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET s` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in top (IMAGE (e:real^3->A) (ball(w0,rho)))` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->A) w0 IN top closure_of Y` MP_TAC THENL
     [REWRITE_TAC[ASSUME `top closure_of (Y:A->bool) = K`] THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET K` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_SPHERE_0];
      ALL_TAC] THEN
    REWRITE_TAC[IN_CLOSURE_OF] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (e:real^3->A) (ball(w0,rho))` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `IMAGE (e:real^3->A) (ball(w0,rho)) SUBSET
      IMAGE e (annulus r0 (&1)) UNION IMAGE e (sphere(vec 0,&1)) UNION
      IMAGE e (annulus (&1) r2)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(q:A) IN Y` THEN UNDISCH_TAC `(q:A) IN IMAGE (e:real^3->A) (ball(w0,rho))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (annulus r0 (&1))) K` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (annulus (&1) r2)) K` THEN
    UNDISCH_TAC `DISJOINT (Y:A->bool) (IMAGE (e:real^3->A) (sphere(vec 0,&1)))` THEN
    UNDISCH_TAC `(Y:A->bool) SUBSET K` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus r0 (&1)) SUBSET K` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BF_CONN_INSIDE THEN
    EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus r0 (&1)) SUBSET Y` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (annulus r0 (&1)) SUBSET K` THEN
    UNDISCH_TAC `(K:A->bool) = Y UNION IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (annulus r0 (&1)))
                          (IMAGE e (sphere(vec 0,&1)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in top (K UNION IMAGE (e:real^3->A) {y | r0 <= norm y /\ norm y <= r2})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    SUBGOAL_THEN `{y:real^3 | r0 <= norm y /\ norm y <= r2} = cball(vec 0,r2) DIFF ball(vec 0,r0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of (Y UNION IMAGE (e:real^3->A) (annulus r0 r2)) SUBSET
    K UNION IMAGE e {y | r0 <= norm y /\ norm y <= r2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (e:real^3->A) (annulus r0 r2) SUBSET
                    IMAGE e {y | r0 <= norm y /\ norm y <= r2}` MP_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
        REAL_ARITH_TAC;
        UNDISCH_TAC `(Y:A->bool) SUBSET K` THEN SET_TAC[]];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    SUBGOAL_THEN
     `annulus r0 r2 = annulus r0 (&1) UNION sphere(vec 0:real^3,&1) UNION annulus (&1) r2`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (annulus r0 (&1)) SUBSET Y` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (e:real^3->A) (annulus (&1) r2)) K` THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET K` THEN
    UNDISCH_TAC `(Y:A->bool) SUBSET K` THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `K UNION IMAGE (e:real^3->A) {y | r0 <= norm y /\ norm y <= r2}` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF]]);;

let P2BF_RADIAL_COLLAR = prove
 (`!(f:real^3->real^3) f' w.
     sphere_diffeo f f'
     ==> norm(radial_ext f' w) = norm w /\ radial_ext f (radial_ext f' w) = w`,
  REWRITE_TAC[sphere_diffeo] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN ASM_SIMP_TAC[]]);;

let P2BF_BALL_SPLIT = prove
 (`!top atlas (b:real^3->A) (e':real^3->A) Y (f:real^3->real^3) f'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ mfd_ball_chart top atlas b /\
     Y = IMAGE b (ball(vec 0,&1)) /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))
     ==> open_in top Y /\ compact_in top (top closure_of Y) /\
         top closure_of Y = Y UNION IMAGE e' (sphere(vec 0,&1)) /\
         DISJOINT Y (IMAGE e' (sphere(vec 0,&1))) /\
         top frontier_of (top closure_of Y) SUBSET IMAGE e' (sphere(vec 0,&1)) /\
         DISJOINT (IMAGE e' (annulus (&1) (&2))) (top closure_of Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `Y = IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASSUME_TAC(REWRITE_RULE[mfd_ball_chart] (ASSUME `mfd_ball_chart top atlas (b:real^3->A)`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`]
                APX_BALL_CORE_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `ball(vec 0:real^3,&2)`; `b:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bi:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                sphere(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                annulus (&1) (&2) SUBSET ball(vec 0:real^3,&2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0; annulus;
                IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. u IN ball(vec 0:real^3,&2) /\ v IN ball(vec 0,&2) /\
                      (b:real^3->A) u = b v ==> u = v`
  (LABEL_TAC "INJ") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(bi:A->real^3) ((b:real^3->A) u) = u /\ bi(b v) = v` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of IMAGE (b:real^3->A) (ball(vec 0,&1)) SUBSET
                IMAGE b (cball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^3->A) (ball(vec 0,&1)) SUBSET
                top closure_of IMAGE b (ball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (b:real^3->A) (ball(vec 0,&1))) (IMAGE b (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u:real^3 = v` MP_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      UNDISCH_TAC `(u:real^3) IN ball(vec 0,&1)` THEN
      UNDISCH_TAC `(v:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN
      DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [UNDISCH_TAC `top closure_of IMAGE (b:real^3->A) (ball(vec 0,&1)) SUBSET
                   IMAGE b (cball(vec 0,&1))` THEN
      SUBGOAL_THEN `cball(vec 0:real^3,&1) = ball(vec 0,&1) UNION sphere(vec 0,&1)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IMAGE_UNION] THEN SET_TAC[];
      ASM_REWRITE_TAC[UNION_SUBSET]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `w:real^3`] P2BF_RADIAL_COLLAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `u = radial_ext (f':real^3->real^3) w` THEN
    SUBGOAL_THEN `(u:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN annulus (&1) (&2)` THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:A) = b(u:real^3)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:A) IN IMAGE (b:real^3->A) (cball(vec 0,&1))` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u:real^3 = v` MP_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      UNDISCH_TAC `(u:real^3) IN annulus (&1) (&2)` THEN
      UNDISCH_TAC `(v:real^3) IN cball(vec 0,&1)` THEN
      REWRITE_TAC[IN_CBALL_0; annulus; IN_ELIM_THM] THEN
      DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC]]);;

let P2BF_TWIST_NORM = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) = inv(norm y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let P2BF_TWISTED_SPLIT = prove
 (`!top atlas (p:real^3->A) (e':real^3->A) Y (f:real^3->real^3) f'.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ rfs_twisted_chart top atlas p /\
     Y = IMAGE p (annulus (&1 / &2) (&2)) /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y)))
     ==> open_in top Y /\ compact_in top (top closure_of Y) /\
         top closure_of Y = Y UNION IMAGE e' (sphere(vec 0,&1)) /\
         DISJOINT Y (IMAGE e' (sphere(vec 0,&1))) /\
         top frontier_of (top closure_of Y) SUBSET IMAGE e' (sphere(vec 0,&1)) /\
         DISJOINT (IMAGE e' (annulus (&1) (&2))) (top closure_of Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `Y = IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`]
                APX_TWISTED_CORE_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `rfs_twisted_chart top atlas (p:real^3->A)` THEN
  REWRITE_TAC[rfs_twisted_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (LABEL_TAC "loc")) THEN
  ABBREV_TAC `CA = cball(vec 0:real^3,&2) DIFF ball(vec 0,&1 / &2)` THEN
  SUBGOAL_THEN
   `(CA:real^3->bool) SUBSET annulus (&1 / &4) (&4) /\
    annulus (&1 / &2) (&2) SUBSET (CA:real^3->bool) /\
    !y:real^3. y IN CA ==> &1 / &2 <= norm y /\ norm y <= &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "CA" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL_0; IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (annulus (&1 / &4) (&4)),top)
                               (p:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_ANNULUS; OPEN_BALL; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SET_RULE `(s:real^3->bool) SUBSET t ==> t INTER s = s`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(y:real^3,r)`; `p:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->A) CA)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (annulus (&1 / &4) (&4):real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    EXPAND_TAC "CA" THEN MATCH_MP_TAC COMPACT_DIFF THEN
    REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of (IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))) SUBSET
                IMAGE p CA` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. y IN annulus (&1 / &4) (&4) /\ z IN annulus (&1 / &4) (&4) /\
          (p:real^3->A) y = p z
          ==> norm z = norm y \/ norm z = inv(norm y)`
  (LABEL_TAC "NRM") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "id" (MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN MATCH_MP_TAC P2BF_TWIST_NORM THEN
    DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN annulus (&1 / &4) (&4)` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^3->A) CA SUBSET
                IMAGE p (annulus (&1 / &2) (&2)) UNION IMAGE p (sphere(vec 0,&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `CA:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `norm(y:real^3) = &1 / &2` THENL
     [DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `rfs_twist (y:real^3)` THEN
      CONJ_TAC THENL
       [USE_THEN "id" (MP_TAC o SPECL [`y:real^3`; `rfs_twist (y:real^3)`]) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN
          ASM_SIMP_TAC[APX_TWIST_SPHERE] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          SIMP_TAC[]];
        ASM_SIMP_TAC[IN_SPHERE_0; APX_TWIST_SPHERE]];
      ASM_CASES_TAC `norm(y:real^3) = &2` THENL
       [DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&2) SUBSET annulus (&1 / &4) (&4) /\
                annulus (&1 / &2) (&2) SUBSET (annulus (&1 / &4) (&4):real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
    CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (p:real^3->A) (annulus (&1 / &2) (&2)))
                         (IMAGE p (sphere(vec 0,&2)))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "NRM" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 < norm(u:real^3) /\ norm(u:real^3) < &2 /\ norm(v:real^3) = &2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(u:real^3) IN annulus (&1 / &2) (&2)` THEN
      UNDISCH_TAC `(v:real^3) IN sphere(vec 0,&2)` THEN
      REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(u:real^3)) < &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv(norm(u:real^3)) < inv(&1 / &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^3->A) (annulus (&1 / &2) (&2)) SUBSET
                top closure_of IMAGE p (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (p:real^3->A) CA` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[UNION_SUBSET]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `w:real^3`] P2BF_RADIAL_COLLAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `y = &2 % radial_ext (f':real^3->real^3) w` THEN
    SUBGOAL_THEN `(y:real^3) IN annulus (&2) (&4) /\ inv(&2) % y = radial_ext f' w`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; VECTOR_MUL_ASSOC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN
      UNDISCH_TAC `(w:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:A) = p(y:real^3)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:A) IN IMAGE (p:real^3->A) CA` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "NRM" (MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN annulus (&2) (&4)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 < norm(y:real^3) /\ norm(y:real^3) < &4 /\
                  &1 / &2 <= norm(z:real^3) /\ norm(z:real^3) <= &2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&2) (&4)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `CA:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(y:real^3)) < &1 / &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv(norm(y:real^3)) < inv(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A C^1 curve in an open set of real^3 is one in any larger open set (same  *)
(* length); a curve joining two points of a neck sphere inside a thin        *)
(* sub-annulus, of length at most sqrt(1 + eps) R^(-1/2) sqrt 2 pi           *)
(* (P2BF_SPHERE_PATH); intrinsic distances in W exceed those in U at most by *)
(* that length when the boundary of an open I inside W is a neck sphere      *)
(* (P2BF_CUT_REPLACE: first and last exit times of a curve,                  *)
(* GRGD_FIRST_TIME).                                                         *)
(* ========================================================================= *)

let P2BF_C1_CURVE_OPEN_MONO = prove
 (`!s t (c:real->real^N) a b.
     open s /\ open t /\ s SUBSET t /\
     mfd_c1_curve (subtopology euclidean s,open_set_atlas s) c a b
     ==> mfd_c1_curve (subtopology euclidean t,open_set_atlas t) c a b /\
         (!t'. t' IN real_interval[a,b] ==> c t' IN s) /\
         !G. mfd_length (open_set_atlas t) G c a b = mfd_length (open_set_atlas s) G c a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t'. t' IN real_interval[a,b] ==> (c:real->real^N) t' IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (c:real->real^N) a b` THEN
    REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (subtopology euclidean t,open_set_atlas t) (c:real->real^N) a b`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (subtopology euclidean s,open_set_atlas s) (c:real->real^N) a b` THEN
    REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; RFB_OPEN_SET_ATLAS_CASES] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2; FORALL_PAIR_THM; PAIR_EQ] THEN
    SIMP_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{r | r IN interval[lift a,lift b] /\ (c:real->real^N)(drop r) IN t} =
      {r | r IN interval[lift a,lift b] /\ c(drop r) IN s}`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^1` THEN
    ASM_CASES_TAC `r IN interval[lift a,lift b]` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:real->real^N)(drop r) IN s` (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `r IN interval[lift a,lift b]` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  ASM_SIMP_TAC[MFD_LENGTH_OPEN_SET_ATLAS]);;

let P2BF_SPHERE_PATH = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) rho h u1 u2.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
     &0 < h /\ h < rho /\ annulus (rho - h) (rho + h) SUBSET rfs_neck_dom eps /\
     u1 IN sphere(vec 0,rho) /\ u2 IN sphere(vec 0,rho)
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = e u1 /\ gamma(&1) = e u2 /\
                 (!t. t IN real_interval[&0,&1]
                      ==> gamma t IN IMAGE e (annulus (rho - h) (rho + h))) /\
                 mfd_length atlas g gamma (&0) (&1) <=
                 sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) * (sqrt(&2) * pi)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(u1:real^3) = rho /\ norm(u2:real^3) = rho` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u1:real^3) IN sphere(vec 0,rho)` THEN
    UNDISCH_TAC `(u2:real^3) IN sphere(vec 0,rho)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`annulus (rho - h) (rho + h):real^3->bool`; `u1:real^3`; `u2:real^3`]
                APX_MODEL_PATH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(u1:real^3) = rho` THEN
      ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `norm(u2:real^3) = rho` THEN
      ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `c:real->real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`annulus (rho - h) (rho + h):real^3->bool`; `rfs_neck_dom eps`;
                 `c:real->real^3`; `&0`; `&1`] P2BF_C1_CURVE_OPEN_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_ANNULUS; APX_NECK_DOM_OPEN]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `c:real->real^3`; `&0`; `&1`]
                APX_NECK_CURVE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `(e:real^3->A) o (c:real->real^3)` THEN ASM_REWRITE_TAC[o_THM] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
              mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                         (c:real->real^3) (&0) (&1)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + eps) /\
                &0 <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
      REWRITE_TAC[rfs_neck] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN
      REWRITE_TAC[rfs_neck] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(apx_sval u1 - apx_sval u2) + sqrt(&2) * pi` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[apx_sval; REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID; REAL_LE_REFL]);;

let P2BF_CUT_REPLACE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) rho h U W In p q.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps x e /\ eps < &1 /\
     &0 < h /\ h < rho /\ annulus (rho - h) (rho + h) SUBSET rfs_neck_dom eps /\
     open_in top In /\ In SUBSET W /\ W SUBSET U /\
     IMAGE e (annulus (rho - h) (rho + h)) SUBSET W /\
     (top closure_of In) INTER U SUBSET In UNION IMAGE e (sphere(vec 0,rho)) /\
     (!y1 y2. y1 IN W /\ y2 IN W ==> mfd_joinable_in (top,atlas) W y1 y2) /\
     p IN In /\ q IN In /\ mfd_joinable_in (top,atlas) U p q
     ==> mfd_dist_in (top,atlas) g W p q <=
         mfd_dist_in (top,atlas) g U p q +
         sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x)) * (sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) *
                  (sqrt(&2) * pi)` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) x` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) (sphere(vec 0,rho)) SUBSET W` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->A) (annulus (rho - h) (rho + h))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a <= b + D <=> a - D <= b`] THEN
  GEN_REWRITE_TAC (RAND_CONV) [mfd_dist_in] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) (U:A->bool) p q` THEN
    REWRITE_TAC[mfd_joinable_in] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real->A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `mfd_length atlas (g:A->real^3^3) c0 (&0) (&1)` THEN
    EXISTS_TAC `c0:real->A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `l:real` THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas (g:A->real^3^3) gamma (&0) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                               (gamma:real->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  ASM_CASES_TAC `!t. t IN real_interval[&0,&1] ==> (gamma:real->A) t IN In` THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= l /\ &0 <= D ==> a - D <= l`) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `(gamma:real->A)(&0) = p`)) THEN
    SUBST1_TAC(SYM(ASSUME `(gamma:real->A)(&1) = q`)) THEN
    MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(In:A->bool) SUBSET W` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `In:A->bool`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `t0:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `gamma:real->A`; `&0`; `&1`] MFD_LENGTH_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                               (\t. (gamma:real->A)(&0 + &1 - t))` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool)
                   (\t. (gamma:real->A)(&0 + &1 - t)) (&0) (&1)` THEN
    SIMP_TAC[mfd_c1_curve];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `\t. (gamma:real->A)(&0 + &1 - t)`; `In:A->bool`]
                GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `&0 + &1 - &0 = &1`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1 - t1` THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_ARITH `&0 + &1 - (&1 - t1) = t1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `s2:real` (STRIP_ASSUME_TAC o BETA_RULE))] THEN
  ABBREV_TAC `t2 = &1 - s2` THEN
  SUBGOAL_THEN `&0 <= t2 /\ t2 < &1 /\ ~((gamma:real->A) t2 IN In) /\
                (!s. t2 < s /\ s <= &1 ==> gamma s IN In)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~((gamma:real->A)(&0 + t2) IN In)` THEN REWRITE_TAC[REAL_ADD_LID];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&1 - s` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s2:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `&0 + &1 - (&1 - s) = s`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 <= t2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN In)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN top closure_of In /\ gamma t2 IN top closure_of In`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
        `!s t (x:A). s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `In:A->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
        ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(\t. (gamma:real->A)(&0 + &1 - t)) s2 IN top closure_of In` MP_TAC THENL
       [MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
        REPEAT STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC(SET_RULE `!s t (x:A). s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `In:A->bool` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `s2:real`)) (concl th))) THEN ASM_REWRITE_TAC[]];
        BETA_TAC THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 IN real_interval[&0,&1] /\ t2 IN real_interval[&0,&1]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN IMAGE (e:real^3->A) (sphere(vec 0,rho)) /\
                gamma t2 IN IMAGE e (sphere(vec 0,rho))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(gamma:real->A) t1 IN U /\ gamma t2 IN U` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        can (find_term ((=) `gamma:real->A`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(top closure_of In) INTER U SUBSET
                 In UNION IMAGE (e:real^3->A) (sphere(vec 0,rho))` THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN In)` THEN UNDISCH_TAC `~((gamma:real->A) t2 IN In)` THEN
    UNDISCH_TAC `(gamma:real->A) t1 IN top closure_of In` THEN
    UNDISCH_TAC `(gamma:real->A) t2 IN top closure_of In` THEN
    UNDISCH_TAC `(gamma:real->A) t1 IN U` THEN UNDISCH_TAC `(gamma:real->A) t2 IN U` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u2:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> concl th = `(gamma:real->A) t2 IN IMAGE (e:real^3->A) (sphere(vec 0,rho))`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `u1:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> concl th = `(gamma:real->A) t1 IN IMAGE (e:real^3->A) (sphere(vec 0,rho))`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `x:A`; `e:real^3->A`; `rho:real`; `h:real`; `u1:real^3`;
                 `u2:real^3`] P2BF_SPHERE_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top,atlas:((A->bool)#(A->real^3))->bool) (gamma:real->A) (&0) t1 /\
    mfd_c1_curve (top,atlas) gamma t1 t2 /\ mfd_c1_curve (top,atlas) gamma t2 (&1) /\
    mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) =
    mfd_length atlas g gamma (&0) t1 + mfd_length atlas g gamma t1 t2 +
    mfd_length atlas g gamma t2 (&1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `&0`; `t1:real`; `&1`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `gamma:real->A`; `t1:real`; `t2:real`; `&1`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_length atlas (g:A->real^3^3) gamma t1 t2` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_POS_LE THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist_in (top,atlas) (g:A->real^3^3) W p ((gamma:real->A) t1) <=
      mfd_length atlas g gamma (&0) t1 /\
    mfd_dist_in (top,atlas) g W (gamma t1) (gamma t2) <= D /\
    mfd_dist_in (top,atlas) g W (gamma t2) q <= mfd_length atlas g gamma t2 (&1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `(gamma:real->A)(&0) = p`)) THEN
      MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `s:real = t1` THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,rho)) SUBSET W` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(In:A->bool) SUBSET W` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `t1:real`)) (concl th) &&
          can (find_term ((=) `In:A->bool`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_length atlas (g:A->real^3^3) beta (&0) (&1)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME `(beta:real->A)(&0) = e(u1:real^3)`)) THEN
      SUBST1_TAC(SYM(ASSUME `(beta:real->A)(&1) = e(u2:real^3)`)) THEN
      MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (annulus (rho - h) (rho + h)) SUBSET W` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      SUBST1_TAC(SYM(ASSUME `(gamma:real->A)(&1) = q`)) THEN
      MATCH_MP_TAC MFD_DIST_IN_LE_LENGTH THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `s:real = t2` THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,rho)) SUBSET W` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(In:A->bool) SUBSET W` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `t2:real`)) (concl th) &&
          can (find_term ((=) `In:A->bool`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t1 IN W /\ gamma t2 IN W /\ p IN W /\ q IN W`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,rho)) SUBSET W` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,rho)) SUBSET W` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(p:A) IN In` THEN UNDISCH_TAC `(In:A->bool) SUBSET W` THEN SET_TAC[];
      UNDISCH_TAC `(q:A) IN In` THEN UNDISCH_TAC `(In:A->bool) SUBSET W` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `(gamma:real->A) t1 = (e:real^3->A) u1`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `(gamma:real->A) t2 = (e:real^3->A) u2`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `p:A`; `(e:real^3->A) u1`; `q:A`] MFD_DIST_IN_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `W:A->bool`; `(e:real^3->A) u1`; `(e:real^3->A) u2`; `q:A`]
                MFD_DIST_IN_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The model volume ratio with an explicit modulus                           *)
(* (P2BF_VMODEL_RATIO_EXPLICIT, from 1 <= cosh, sinh x <= x e^x and the mean *)
(* value theorem), and clause (7) of the target cap with the parameters th,  *)
(* eta, e0, rmin, Bv given explicitly (P2BF_CLAUSE7_GEN2, the second half of *)
(* P2BC_CLAUSE7), so that eta can be chosen uniformly. The target hypothesis *)
(* is: the target metric is complete, or the closure of the target region is *)
(* compact (P2BF_C7_TARGET_BALL_GEN for the balls of the target,             *)
(* P2BF_C7_POINT_GEN for one point).                                         *)
(* ========================================================================= *)

let P2BF_CS_NEG_BOUNDS = prove
 (`!K u. &0 <= K /\ &0 <= u
         ==> &1 <= cmp_cs (--K) u /\ cmp_cs (--K) u <= exp(sqrt K * u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; CMP_CS_FLAT; SQRT_0; REAL_MUL_LZERO; REAL_EXP_0;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMP_SN_NEG_CURV] THEN
  SUBGOAL_THEN `&0 <= sqrt K * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `x = sqrt K * u` THEN
  SUBGOAL_THEN `&0 < exp x /\ exp(--x) = inv(exp x) /\ &1 <= exp x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_NEG] THEN
    MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `a = exp x` THEN
  SUBGOAL_THEN `inv a <= &1 /\ &0 < inv a` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LT_INV_EQ]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `a + inv a - &2 = (a - &1) pow 2 / a` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (a - &1) pow 2 / a` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let P2BF_SN_NEG_BOUNDS = prove
 (`!K u. &0 <= K /\ &0 <= u
         ==> u <= cmp_sn (--K) u /\ cmp_sn (--K) u <= u * exp(sqrt K * u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\v. cmp_sn (--K) v - v`; `\v. cmp_cs (--K) v - &1`;
                   `{v:real | &0 <= v}`; `&0`; `u:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[CMP_SN_ZERO; REAL_SUB_REFL] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        X_GEN_TAC `v:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV] THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
        X_GEN_TAC `v:real` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`K:real`; `v:real`] P2BF_CS_NEG_BOUNDS) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    MP_TAC(ISPECL [`\v. v * exp(sqrt K * v) - cmp_sn (--K) v`;
                   `\v. (exp(sqrt K * v) + v * (sqrt K * exp(sqrt K * v))) - cmp_cs (--K) v`;
                   `{v:real | &0 <= v}`; `&0`; `u:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[CMP_SN_ZERO; REAL_MUL_LZERO; REAL_SUB_REFL] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        X_GEN_TAC `v:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX; CMP_SN_HAS_DERIV] THEN
        REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        X_GEN_TAC `v:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`K:real`; `v:real`] P2BF_CS_NEG_BOUNDS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `&0 <= v * (sqrt K * exp(sqrt K * v))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_EXP_POS_LE];
          ASM_REAL_ARITH_TAC]];
      REAL_ARITH_TAC]]);;

let P2BF_VMODEL_RATIO_EXPLICIT = prove
 (`!K rmin Bv th.
     &0 <= K /\ &0 < rmin /\ rmin <= Bv /\ &0 < th /\ th <= &1
     ==> !s t. rmin <= s /\ s <= t /\ t <= Bv /\
               t - s < th * rmin pow 3 / (&8 * Bv pow 2 * exp(&2 * sqrt K * Bv))
               ==> (&1 - th) * cmp_vmodel (:3) (--K) t <= cmp_vmodel (:3) (--K) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`--K:real`; `Bv + &1`] (INST_TYPE [`:3`,`:N`] CMPV_VMODEL_FACTS)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `c3 = &3 * measure(ball(vec 0:real^3,&1))` THEN
  ABBREV_TAC `V = cmp_vmodel (:3) (--K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c3` ASSUME_TAC THENL
   [EXPAND_TAC "c3" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[MEASURE_BALL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c3 * rmin pow 3 / &8` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. &0 < a /\ a <= b /\ b <= Bv
          ==> ?x. a <= x /\ x <= b /\ (V:real->real) b - V a = (c3 * cmp_sn (--K) x pow 2) * (b - a)`
  (LABEL_TAC "MVT") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real->real`; `\x. c3 * cmp_sn (--K) x pow 2`; `a:real`; `b:real`]
                  REAL_MVT_VERY_SIMPLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "has_real_derivative"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c3 * rmin pow 3 / &8 <= (V:real->real) s` ASSUME_TAC THENL
   [USE_THEN "MVT" (MP_TAC o SPECL [`s / &2`; `s:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 <= V(s / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `&0` && is_comb(lhs(concl th)))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Bv + &1`)) (concl th) &&
        not(can (find_term (fun t -> try fst(dest_const t) = "has_real_derivative"
                                     with Failure _ -> false)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`K:real`; `x:real`] P2BF_SN_NEG_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(s / &2) pow 2 <= cmp_sn (--K) x pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `rmin pow 3 <= s pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c3 * (s / &2) pow 2) * (s - s / &2) <=
                  (c3 * cmp_sn (--K) x pow 2) * (s - s / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `c3 * rmin pow 3 <= c3 * s pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c3 * (s / &2) pow 2) * (s - s / &2) = c3 * s pow 3 / &8` ASSUME_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s:real = t` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= th * v ==> (&1 - th) * v <= v`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c3 * rmin pow 3 / &8` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "MVT" (MP_TAC o SPECL [`s:real`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`K:real`; `x:real`] P2BF_SN_NEG_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `E = exp(&2 * sqrt K * Bv)` THEN
  SUBGOAL_THEN `&0 < E /\ cmp_sn (--K) x pow 2 <= Bv pow 2 * E` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(x * exp(sqrt K * x)) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "E" THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_2; GSYM REAL_EXP_ADD] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_ARITH `a + a = &2 * a`] THEN
      REWRITE_TAC[REAL_ARITH `&2 * a * b = &2 * (a * b)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V:real->real) t - V s <= c3 * th * rmin pow 3 / &8` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c3 * Bv pow 2 * E) * (t - s)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &8 * Bv pow 2 * E` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_ARITH `&0 < &8`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(t - s) * (&8 * Bv pow 2 * E) <= th * rmin pow 3` MP_TAC THENL
     [UNDISCH_TAC `t - s < th * rmin pow 3 / (&8 * Bv pow 2 * E)` THEN
      SUBGOAL_THEN `th * rmin pow 3 / (&8 * Bv pow 2 * E) =
                    (th * rmin pow 3) / (&8 * Bv pow 2 * E)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c3 * ((t - s) * (&8 * Bv pow 2 * E)) <= c3 * (th * rmin pow 3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `th * (c3 * rmin pow 3 / &8) <= th * (V:real->real) s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (V:real->real) s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c3 * rmin pow 3 / &8` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - th) * (V:real->real) t <= (&1 - th) * ((&1 + th) * V s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= th * th * (V:real->real) s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BF_C7_TARGET_BALL_GEN = prove
 (`!top' atlas' (g':B->real^3^3) eps z' e' Yc' W' y' r.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     (mfd_complete (top',atlas') g' \/ compact_in top' (top' closure_of W')) /\
     rfs_neck (top',atlas') g' eps z' e' /\ eps <= &1 / &4 /\
     (!w. w IN IMAGE e' (sphere(vec 0,&1))
          ==> mfd_scalar atlas' g' z' / &2 <= mfd_scalar atlas' g' w) /\
     top' frontier_of (top' closure_of Yc') SUBSET IMAGE e' (sphere(vec 0,&1)) /\
     top' closure_of Yc' SUBSET W' /\ IMAGE e' (rfs_neck_dom eps) SUBSET W' /\
     y' IN top' closure_of Yc' /\ &0 < r /\
     (?B. !q. q IN mfd_ball (top',atlas') g' y' r ==> mfd_scalar atlas' g' q <= B) /\
     sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' y' r)) = inv(r pow 2)
     ==> (!q. q IN mfd_ball (top',atlas') g' y' r
              ==> mfd_scalar atlas' g' q <= inv(r pow 2)) /\
         mfd_cball (top',atlas') g' y' r SUBSET W' /\
         compact_in top' (top' closure_of mfd_ball (top',atlas') g' y' r) /\
         top' closure_of mfd_ball (top',atlas') g' y' r SUBSET W' /\
         (!gamma. mfd_c1_curve (top',atlas') gamma (&0) (&1) /\ gamma(&0) = y' /\
                  mfd_length atlas' g' gamma (&0) (&1) < r
                  ==> !s. &0 <= s /\ s <= &1 ==> gamma s IN W')`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o check (is_exists o concl)) THEN
  SUBGOAL_THEN `!q. q IN mfd_ball (top',atlas') (g':B->real^3^3) y' r
                    ==> mfd_scalar atlas' g' q <= inv(r pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `inv(r pow 2)`)) THEN
    MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_cball (top',atlas') (g':B->real^3^3) y' r SUBSET W'` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BC_SC_CBALL_IN THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `z':B`; `e':real^3->B`; `Yc':B->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y':B) IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `Yc':B->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `top' closure_of mfd_ball (top',atlas') (g':B->real^3^3) y' r SUBSET
                mfd_cball (top',atlas') g' y' r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_complete" with Failure _ -> false))
          (concl th))) THENL
     [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `mfd_cball (top',atlas') (g':B->real^3^3) y' r` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      UNDISCH_TAC `mfd_complete (top',atlas') (g':B->real^3^3)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `top' closure_of (W':B->bool)` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      MATCH_MP_TAC CLOSURE_OF_MONO THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `mfd_cball (top',atlas') (g':B->real^3^3) y' r` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_cball (top',atlas') (g':B->real^3^3) y' r` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `g':B->real^3^3`; `eps:real`; `z':B`; `e':real^3->B`; `Yc':B->bool`;
                   `W':B->bool`; `y':B`; `r:real`; `r:real`; `gamma:real->B`]
                  P2BC_SC_CURVES_STAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_REFL] THEN
      SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas' (g':B->real^3^3) z'`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let P2BF_C7_POINT_GEN = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U U' psi psi'
    eps z e Yc y0 r ra r1 rb lam alpha kap K d th rmin Bv e0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas' g' /\
     (mfd_complete (top',atlas') g' \/ compact_in top' (top' closure_of U')) /\
     mfd_diffeo top atlas U top' atlas' U' psi psi' /\
     compact_in top (top closure_of U) /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     top frontier_of (top closure_of Yc) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Yc SUBSET U /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
     rfs_neck (top',atlas') g' eps (psi z) (psi o e) /\
     (!w. w IN IMAGE (psi o e) (sphere(vec 0,&1))
          ==> mfd_scalar atlas' g' (psi z) / &2 <= mfd_scalar atlas' g' w) /\
     top' frontier_of (top' closure_of IMAGE psi Yc) SUBSET
       IMAGE (psi o e) (sphere(vec 0,&1)) /\
     top' closure_of IMAGE psi Yc SUBSET U' /\
     IMAGE (psi o e) (rfs_neck_dom eps) SUBSET U' /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &4 <= mfd_scalar atlas' g' (psi w)) /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                lam * (v dot (g y ** v))) /\
     (!y v. y IN U
            ==> v dot (g y ** v) <=
                lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
     (!y. y IN U ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha) /\
     (!y w. y IN U ==> --(&2 * K) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w) /\
     (!r. &0 < r /\
          (?B. !z. z IN mfd_ball (top,atlas) g y0 r ==> mfd_scalar atlas g z <= B) /\
          sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y0 r)) = inv(r pow 2)
          ==> compact_in top (top closure_of mfd_ball (top,atlas) g y0 r) /\
              top closure_of mfd_ball (top,atlas) g y0 r SUBSET U /\
              ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y0 r) v /\
                  d <= v / r pow 3) /\
     (!s t. rmin <= s /\ s <= t /\ t <= Bv /\ t - s < e0
            ==> (&1 - th) * cmp_vmodel (:3) (--K) t <= cmp_vmodel (:3) (--K) s) /\
     y0 IN Yc /\ Yc SUBSET U /\ &0 < r /\
     (?B. !q. q IN mfd_ball (top',atlas') g' (psi y0) r ==> mfd_scalar atlas' g' q <= B) /\
     sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' (psi y0) r)) =
     inv(r pow 2) /\
     &1 <= lam /\ &0 <= alpha /\ &0 < kap /\ kap < &1 /\ &0 <= K /\ &0 <= d /\
     &0 <= th /\ th <= &1 /\
     &0 < ra /\ ra <= r1 /\ ra < rb /\ sqrt lam * r1 <= r /\ sqrt lam * r <= rb /\
     rb <= &5 / &4 * r /\
     sqrt lam * (rb - sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps) <= r /\
     inv(r pow 2) + alpha <= inv(ra pow 2) /\
     inv(rb pow 2) < (&1 - kap) * inv(r pow 2) - alpha /\
     rmin <= r1 /\ rb <= Bv /\ rb - r1 < e0
     ==> compact_in top' (top' closure_of mfd_ball (top',atlas') g' (psi y0) r) /\
         top' closure_of mfd_ball (top',atlas') g' (psi y0) r SUBSET U' /\
         ?v. mfd_has_volume (top',atlas') g' (mfd_ball (top',atlas') g' (psi y0) r) v /\
             d * (&1 - th) * ra pow 3 <= lam * sqrt lam * v`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `B:real` o check (fun th -> is_exists(concl th) &&
    can (find_term ((=) `(psi:A->B) y0`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&1 <= sqrt lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r1 <= r /\ r <= rb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lam * r1` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt lam * r` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN U` ASSUME_TAC THENL
   [MP_TAC(ASSUME `(Yc:A->bool) SUBSET U`) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Yc:A->bool) SUBSET topspace top /\ IMAGE (psi:A->B) Yc SUBSET topspace top'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (U':B->bool)`)) THEN
    UNDISCH_TAC `IMAGE (psi:A->B) U SUBSET U'` THEN
    UNDISCH_TAC `(Yc:A->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN top closure_of Yc /\ (psi:A->B) y0 IN top' closure_of IMAGE psi Yc`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `Yc:A->bool`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top':B topology`; `IMAGE (psi:A->B) Yc`] CLOSURE_OF_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `eps:real`; `(psi:A->B) z`; `(psi:A->B) o (e:real^3->A)`;
                 `IMAGE (psi:A->B) Yc`; `U':B->bool`; `(psi:A->B) y0`; `r:real`]
                P2BF_C7_TARGET_BALL_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`;
                 `eps:real`; `z:A`; `e:real^3->A`; `Yc:A->bool`; `y0:A`; `r:real`;
                 `ra:real`; `r1:real`; `rb:real`; `lam:real`; `alpha:real`; `kap:real`]
                P2BC_C7_SOURCE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `d:real`)) (concl th) &&
    not (can (find_term ((=) `th:real`)) (concl th)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `inv(r0 pow 2)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`;
                 `mfd_ball (top',atlas') (g':B->real^3^3) ((psi:A->B) y0) r`;
                 `(psi:A->B) y0`; `r:real`] P2BC_BALL_VOLUME_IN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MFD_BALL_OPEN; SUBSET_REFL]; STRIP_TAC] THEN
  EXISTS_TAC `mfd_volume (top',atlas') (g':B->real^3^3)
                (mfd_ball (top',atlas') g' ((psi:A->B) y0) r)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BC_C7_VOLUME THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
    `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
    `U:A->bool`; `U':B->bool`; `psi:A->B`; `psi':B->A`; `y0:A`; `r:real`;
    `r0:real`; `r1:real`; `K:real`; `rmin:real`; `Bv:real`; `e0:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) y0 rb` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BC_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^3^3) y0 rb` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BC_BALL_MONO THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BF_CLAUSE7_GEN2 = prove
 (`!top atlas (g:A->real^3^3) U Y eps z e Rn Rm K d th eta e0 rmin Bv.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top U /\ compact_in top (top closure_of U) /\ Y SUBSET U /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     top frontier_of (top closure_of Y) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Y SUBSET U /\ IMAGE e (rfs_neck_dom eps) SUBSET U /\
     &0 < Rn /\ Rn <= Rm /\
     (!y. y IN U ==> Rn <= mfd_scalar atlas g y /\ mfd_scalar atlas g y <= Rm) /\
     &0 <= K /\
     (!y w. y IN U ==> --(&2 * K) * (w dot (g y ** w)) <= mfd_ricci atlas g y w w) /\
     &0 <= d /\
     (!y r. y IN Y /\ &0 < r /\
            (?B. !z. z IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g z <= B) /\
            sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) = inv(r pow 2)
            ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                top closure_of mfd_ball (top,atlas) g y r SUBSET U /\
                ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                    d <= v / r pow 3) /\
     &0 <= th /\ th <= &1 /\ &0 < eta /\ eta <= &1 / &40 /\
     &4 * eta * sqrt(&2 / Rn) <= sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g z)) * inv eps /\
     &8 * eta * sqrt(&2 / Rn) <= e0 /\
     &0 < rmin /\ rmin <= sqrt(&1 / (&2 * Rm)) / &2 /\ &2 * sqrt(&2 / Rn) <= Bv /\
     (!s t. rmin <= s /\ s <= t /\ t <= Bv /\ t - s < e0
            ==> (&1 - th) * cmp_vmodel (:3) (--K) t <= cmp_vmodel (:3) (--K) s)
     ==> !top' atlas' (g':B->real^3^3) psi psi' lam alpha.
              hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
              riemannian_metric atlas' g' /\
              (mfd_complete (top',atlas') g' \/
               compact_in top' (top' closure_of IMAGE psi U)) /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_neck (top',atlas') g' eps (psi z) (psi o e) /\
              (!w. w IN IMAGE (psi o e) (sphere(vec 0,&1))
                   ==> mfd_scalar atlas' g' (psi z) / &2 <= mfd_scalar atlas' g' w) /\
              top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                IMAGE (psi o e) (sphere(vec 0,&1)) /\
              top' closure_of IMAGE psi Y SUBSET IMAGE psi U /\
              IMAGE (psi o e) (rfs_neck_dom eps) SUBSET IMAGE psi U /\
              (!w. w IN IMAGE e (sphere(vec 0,&1))
                   ==> mfd_scalar atlas g z / &4 <= mfd_scalar atlas' g' (psi w)) /\
              &1 <= lam /\ lam <= &1 + eta /\ &0 <= alpha /\ alpha <= eta * Rn / &8 /\
              (!y v. y IN U
                     ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                         lam * (v dot (g y ** v))) /\
              (!y v. y IN U
                     ==> v dot (g y ** v) <=
                         lam * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))) /\
              (!y. y IN U
                   ==> abs(mfd_scalar atlas' g' (psi y) - mfd_scalar atlas g y) <= alpha)
              ==> !y' r. y' IN IMAGE psi Y /\ &0 < r /\
                         (?B. !q. q IN mfd_ball (top',atlas') g' y' r
                                  ==> mfd_scalar atlas' g' q <= B) /\
                         sup(IMAGE (mfd_scalar atlas' g') (mfd_ball (top',atlas') g' y' r)) =
                         inv(r pow 2)
                         ==> compact_in top' (top' closure_of mfd_ball (top',atlas') g' y' r) /\
                             top' closure_of mfd_ball (top',atlas') g' y' r SUBSET
                               IMAGE psi U /\
                             ?v. mfd_has_volume (top',atlas') g'
                                   (mfd_ball (top',atlas') g' y' r) v /\
                                 (d * (&1 - th)) / (&1 + &16 * eta) <= v / r pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `rM = sqrt(&2 / Rn)` THEN
  SUBGOAL_THEN `&0 < rM` ASSUME_TAC THENL
   [EXPAND_TAC "rM" THEN MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) * inv eps` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) z` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MAP_EVERY X_GEN_TAC [`y':B`; `r:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y0:A` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE] o
    check (fun th -> can (find_term ((=) `y':B`)) (concl th) &&
                     is_binary "IN" (concl th))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `&1 <= sqrt lam /\ sqrt lam <= &1 + eta /\ sqrt lam pow 2 = lam`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:A) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `eta * Rn <= Rn / &40` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `eta * Rn <= (&1 / &40) * Rn ==> eta * Rn <= Rn / &40`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:A->B) y0 IN topspace top' /\
                (psi:A->B) y0 IN top' closure_of IMAGE psi Y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U)`)) THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `IMAGE (psi:A->B) Y`] CLOSURE_OF_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `eps:real`; `(psi:A->B) z`; `(psi:A->B) o (e:real^3->A)`;
                 `IMAGE (psi:A->B) Y`; `IMAGE (psi:A->B) U`; `(psi:A->B) y0`; `r:real`]
                P2BF_C7_TARGET_BALL_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `Rn / &2 <= inv(r pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
        `!a b c. Rn <= b /\ abs(a - b) <= c /\ c <= eta * Rn / &8 /\
                 eta * Rn <= Rn / &40 /\ &0 < Rn ==> Rn / &2 <= a`) THEN
      EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) y0` THEN EXISTS_TAC `alpha:real` THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(r pow 2) <= &2 * Rm` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `inv(r pow 2)` && is_comb(lhs(concl th)))) THEN
    MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(psi:A->B) y0` THEN ASM_SIMP_TAC[MFD_CENTRE_IN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `q:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:B) IN IMAGE (psi:A->B) U` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t x:B. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `top' closure_of mfd_ball (top',atlas') (g':B->real^3^3) (psi(y0:A)) r` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top':B topology`;
                     `mfd_ball (top',atlas') (g':B->real^3^3) (psi(y0:A)) r`]
                    CLOSURE_OF_SUBSET) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
        MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(q:B) IN IMAGE (psi:A->B) U` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
      `!b c. b <= Rm /\ abs(a - b) <= c /\ c <= eta * Rn / &8 /\
             eta * Rn <= Rn / &40 /\ &0 < Rn /\ Rn <= Rm ==> a <= &2 * Rm`) THEN
    EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) p` THEN EXISTS_TAC `alpha:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real`; `sqrt lam`; `r:real`; `Rn:real`; `Rm:real`; `L:real`;
                 `e0:real`; `alpha:real`] P2BC_C7_NUMERIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. &0 < r /\
        (?B. !z. z IN mfd_ball (top,atlas) g y0 r ==> mfd_scalar atlas g z <= B) /\
        sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) (mfd_ball (top,atlas) g y0 r)) =
        inv(r pow 2)
        ==> compact_in top (top closure_of mfd_ball (top,atlas) g y0 r) /\
            top closure_of mfd_ball (top,atlas) g y0 r SUBSET U /\
            ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y0 r) v /\
                d <= v / r pow 3`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Y:A->bool`)) (concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `B':real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`;
                 `eps:real`; `z:A`; `e:real^3->A`; `Y:A->bool`; `y0:A`; `r:real`;
                 `r / (sqrt lam * (&1 + eta))`; `r / sqrt lam`;
                 `sqrt lam * (&1 + eta) * r`; `lam:real`; `alpha:real`; `eta / &2`;
                 `K:real`; `d:real`; `th:real`; `rmin:real`; `Bv:real`; `e0:real`]
                P2BF_C7_POINT_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BC_C7_CONST THEN EXISTS_TAC `sqrt lam` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `d * (&1 - th) * (r / (sqrt lam * (&1 + eta))) pow 3 <=
               lam * sqrt lam * v` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The end neck of a cap, the lower bound sqrt(1 - eps) / eps < C, and the   *)
(* intrinsic diameter of the re-centred sub-cap (excursion replacement).     *)
(* ------------------------------------------------------------------------- *)

let P2BF_CAP_END_NECK = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y
     ==> ?z (e:real^3->A). rfs_neck (top,atlas) g eps z e /\
                           IMAGE e (rfs_neck_dom eps) SUBSET U`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`z:A`; `e:real^3->A`] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let P2BF_CAP_C_LOWER = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     hausdorff_space top /\ riemannian_metric atlas g /\
     rfs_cap (top,atlas) g C eps U Y /\ eps < &1
     ==> sqrt(&1 - eps) * inv eps < C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_CAP_JOINABLE) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC) o
    MATCH_MP P2BF_CAP_END_NECK) THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
  REWRITE_TAC[rfs_cap; rfs_sup_lt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) (K ALL_TAC))))))) THEN
  SUBGOAL_THEN `&0 < eps /\ &0 < mfd_scalar atlas (g:A->real^3^3) z /\
                (z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN U` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Rs = sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z <= Rs` ASSUME_TAC THENL
   [EXPAND_TAC "Rs" THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `d4 * mfd_scalar atlas (g:A->real^3^3) z` THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) y /
                                    mfd_scalar atlas g z` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `d4:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`y:A`; `z:A`] THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `ya = exp(--(inv(&2 * sqrt(&2) * eps))) % basis 1:real^3` THEN
  ABBREV_TAC `yb = exp(inv(&2 * sqrt(&2) * eps)) % basis 1:real^3` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(ya:real^3) IN rfs_neck_dom eps /\ (yb:real^3) IN rfs_neck_dom eps /\
    apx_sval ya = --(inv(&2 * eps)) /\ apx_sval yb = inv(&2 * eps)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ya"; "yb"] THEN
    REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; apx_sval; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID; REAL_ABS_EXP; LOG_EXP] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < inv(sqrt(&2) * eps) /\
                  inv(&2 * sqrt(&2) * eps) = inv(sqrt(&2) * eps) / &2 /\
                  sqrt(&2) * inv(&2 * sqrt(&2) * eps) = inv(&2 * eps)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
        UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `z:A`; `e:real^3->A`; `ya:real^3`; `yb:real^3`]
                APX_NECK_DIST_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `min (abs(--inv(&2 * eps) - inv(&2 * eps)))
                    (&2 * inv eps - abs(--inv(&2 * eps)) - abs(inv(&2 * eps))) = inv eps`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&2 * eps) /\ &2 * inv(&2 * eps) = inv eps` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) ya IN U /\ e yb IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
    UNDISCH_TAC `(ya:real^3) IN rfs_neck_dom eps` THEN
    UNDISCH_TAC `(yb:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^3^3) ((e:real^3->A) ya) (e yb) <= d3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U ((e:real^3->A) ya) (e yb)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIST_LE_DIST_IN THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d3:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`(e:real^3->A) ya`; `(e:real^3->A) yb`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(mfd_scalar atlas (g:A->real^3^3) z) /\
                sqrt(mfd_scalar atlas (g:A->real^3^3) z) <= sqrt Rs`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt Rs) <= inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= d4` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) z /
                                    mfd_scalar atlas g z` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `d4:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`z:A`; `z:A`] THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * inv(sqrt Rs) <= C * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt(&1 - eps) * inv eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) z)) <
                C * inv(sqrt(mfd_scalar atlas g z))` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RMUL_EQ]]);;

let P2BF_SUBCAP_DIAM = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) Y U U0 r0 r2 p q.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ eps < &1 /\
     open_in top Y /\ compact_in top (top closure_of Y) /\
     top closure_of Y = Y UNION IMAGE e (sphere(vec 0,&1)) /\
     &0 < r0 /\ r0 < &1 /\ &1 < r2 /\ {y | r0 <= norm y /\ norm y <= r2} SUBSET rfs_neck_dom eps /\
     IMAGE e (annulus r0 (&1)) SUBSET Y /\
     U0 = Y UNION IMAGE e (annulus r0 r2) /\ U0 SUBSET U /\
     (!y1 y2. y1 IN U0 /\ y2 IN U0 ==> mfd_joinable_in (top,atlas) U0 y1 y2) /\
     p IN U0 /\ q IN U0 /\ mfd_joinable_in (top,atlas) U p q
     ==> mfd_dist_in (top,atlas) g U0 p q <=
         mfd_dist_in (top,atlas) g U p q +
         sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g z)) * (sqrt(&2) * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r1 = (r0 + &1) / &2` THEN
  SUBGOAL_THEN `r0 < r1 /\ r1 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN U0 ==> x IN Y \/ ?w. &1 <= norm w /\ norm w < r2 /\ x = (e:real^3->A) w`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; annulus; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&1 <= norm(x':real^3)` THENL
     [DISJ2_TAC THEN EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[];
      DISJ1_TAC THEN
      UNDISCH_TAC `IMAGE (e:real^3->A) (annulus r0 (&1)) SUBSET Y` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b. &1 <= b /\ b < r2 /\
        !rho. b < rho /\ rho < r2
              ==> p IN Y UNION IMAGE (e:real^3->A) (annulus r1 rho) /\
                  q IN Y UNION IMAGE e (annulus r1 rho)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!x. x IN Y \/ (?w. &1 <= norm w /\ norm w < r2 /\ x = (e:real^3->A) w)
          ==> ?bx. &1 <= bx /\ bx < r2 /\
                   !rho. bx < rho ==> x IN Y UNION IMAGE e (annulus r1 rho)`
    (LABEL_TAC "BX") THENL
     [X_GEN_TAC `x:A` THEN STRIP_TAC THENL
       [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LE_REFL; IN_UNION];
        EXISTS_TAC `norm(w:real^3)` THEN ASM_REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `w:real^3` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME `(q:A) IN U0`)) THEN
                          MP_TAC(MATCH_MP th (ASSUME `(p:A) IN U0`))) THEN
    DISCH_THEN(fun th -> USE_THEN "BX" (fun bx ->
      X_CHOOSE_THEN `bp:real` STRIP_ASSUME_TAC (MATCH_MP bx th))) THEN
    DISCH_THEN(fun th -> USE_THEN "BX" (fun bx ->
      X_CHOOSE_THEN `bq:real` STRIP_ASSUME_TAC (MATCH_MP bx th))) THEN
    EXISTS_TAC `max bp bq` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rho = (b + r2) / &2` THEN ABBREV_TAC `h = (r2 - rho) / &2` THEN
  SUBGOAL_THEN `b < rho /\ rho < r2 /\ &0 < h /\ h < rho /\ r1 < rho - h /\ rho + h < r2 /\
                &1 < rho`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "rho"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rho:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `r1:real`)) (concl th) && can (find_term ((=) `b:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e` THEN
    SIMP_TAC[rfs_neck];
    DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `annulus (rho - h) (rho + h) SUBSET rfs_neck_dom eps /\
    (annulus (rho - h) (rho + h):real^3->bool) SUBSET annulus r0 r2 /\
    (annulus r1 rho:real^3->bool) SUBSET annulus r0 r2 /\
    annulus r1 rho SUBSET rfs_neck_dom eps /\
    {y:real^3 | r1 <= norm y /\ norm y <= rho} SUBSET rfs_neck_dom eps /\
    sphere(vec 0:real^3,r1) SUBSET annulus r0 (&1) /\
    sphere(vec 0:real^3,&1) SUBSET annulus r1 rho /\
    {y:real^3 | r1 <= norm y /\ norm y <= rho} SUBSET
      sphere(vec 0,r1) UNION annulus r1 rho UNION sphere(vec 0,rho)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY
     (MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{y:real^3 | r0 <= norm y /\ norm y <= r2}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC THEN
      NO_TAC) THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0; IN_UNION] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (Y UNION IMAGE (e:real^3->A) (annulus r1 rho))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (e:real^3->A) {y | r1 <= norm y /\ norm y <= rho})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
    SUBGOAL_THEN `{y:real^3 | r1 <= norm y /\ norm y <= rho} = cball(vec 0,rho) DIFF ball(vec 0,r1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `top closure_of (Y UNION IMAGE (e:real^3->A) (annulus r1 rho)) SUBSET
    top closure_of Y UNION IMAGE e {y | r1 <= norm y /\ norm y <= rho}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c d:A->bool. a SUBSET c /\ b SUBSET d
                                               ==> a UNION b SUBSET c UNION d`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
        MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
        GEN_TAC THEN REAL_ARITH_TAC];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(top closure_of (Y UNION IMAGE (e:real^3->A) (annulus r1 rho))) INTER U SUBSET
    (Y UNION IMAGE e (annulus r1 rho)) UNION IMAGE e (sphere(vec 0,rho))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!A B C D E F G Y U:A->bool.
        C SUBSET D UNION E UNION F /\ D SUBSET Y /\ G SUBSET E /\
        A SUBSET B UNION C /\ B = Y UNION G
        ==> A INTER U SUBSET (Y UNION E) UNION F`) THEN
    MAP_EVERY EXISTS_TAC
     [`top closure_of (Y:A->bool)`;
      `IMAGE (e:real^3->A) {y | r1 <= norm y /\ norm y <= rho}`;
      `IMAGE (e:real^3->A) (sphere(vec 0,r1))`;
      `IMAGE (e:real^3->A) (sphere(vec 0,&1))`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e:real^3->A) (annulus r0 (&1))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Y UNION IMAGE (e:real^3->A) (annulus r1 rho) SUBSET U0 /\
    IMAGE (e:real^3->A) (annulus (rho - h) (rho + h)) SUBSET U0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b c:A->bool. b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `!a b c:A->bool. b SUBSET c ==> b SUBSET a UNION c`) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BF_CUT_REPLACE THEN
  MAP_EVERY EXISTS_TAC [`e:real^3->A`; `rho:real`; `h:real`;
                        `Y UNION IMAGE (e:real^3->A) (annulus r1 rho)`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The re-centred source sub-cap U0 = Y union e'(annulus r0 r2) for ball and *)
(* twisted cores (openness, compact closure, U0 in U, the outer collar,      *)
(* joinability), uniform neck transfer with renormalization, the re-centred  *)
(* end neck e' o (c %), and the source clause 7 on U0.                       *)
(* ------------------------------------------------------------------------- *)

let P2BF_JOIN_TWO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W A B (a:A).
     smooth_manifold_atlas top atlas /\
     (!y1 y2. y1 IN A /\ y2 IN A ==> mfd_joinable_in (top,atlas) W y1 y2) /\
     (!y1 y2. y1 IN B /\ y2 IN B ==> mfd_joinable_in (top,atlas) W y1 y2) /\
     a IN A /\ a IN B
     ==> !y1 y2. y1 IN A UNION B /\ y2 IN A UNION B
                 ==> mfd_joinable_in (top,atlas) W y1 y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN A UNION B
                    ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) W y (a:A) /\
                        mfd_joinable_in (top,atlas) W a y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_IN_TRANS THEN EXISTS_TAC `a:A` THEN
  ASM_SIMP_TAC[]);;

let P2BF_SUBCAP_BALL = prove
 (`!top atlas (g:A->real^3^3) eps U Y (b:real^3->A) (e':real^3->A) z' f f' r0 r2 U0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
     Y = IMAGE b (ball(vec 0,&1)) /\
     rfs_neck (top,atlas) g eps z' e' /\ IMAGE e' (rfs_neck_dom eps) SUBSET U /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
     sphere_diffeo f f' /\ (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y)) /\
     &0 < r0 /\ r0 < &1 /\ &2 <= r2 /\
     {y:real^3 | r0 <= norm y /\ norm y <= r2} SUBSET rfs_neck_dom eps /\
     U0 = Y UNION IMAGE e' (annulus r0 r2)
     ==> open_in top U0 /\ compact_in top (top closure_of U0) /\ U0 SUBSET U /\
         top closure_of Y SUBSET U0 /\ IMAGE e' (annulus r0 r2) SUBSET U0 /\
         IMAGE b (ball(vec 0,&2)) SUBSET U0 /\
         IMAGE e' (annulus r0 (&1)) SUBSET Y /\
         U0 DIFF IMAGE b (cball(vec 0,&1)) = IMAGE e' (annulus (&1) r2) /\
         (!y1 y2. y1 IN U0 /\ y2 IN U0 ==> mfd_joinable_in (top,atlas) U0 y1 y2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`;
                 `e':real^3->A`; `Y:A->bool`; `f:real^3->real^3`; `f':real^3->real^3`]
                P2BF_BALL_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' e'` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1) (&2) ==> norm(radial_ext f y) = norm y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN
    UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN SIMP_TAC[sphere_diffeo];
    ALL_TAC] THEN
  ABBREV_TAC `v0 = (&3 / &2) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm(v0:real^3) = &3 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "v0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^3) IN annulus (&1) (&2) /\ v0 IN ball(vec 0,&2)` STRIP_ASSUME_TAC
  THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (e':real^3->A) (annulus (&1) r2) SUBSET top closure_of Y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `(e':real^3->A)(radial_ext f v0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `DISJOINT (IMAGE (e':real^3->A) (annulus (&1) (&2))) (top closure_of Y)` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(e':real^3->A)(radial_ext f v0)`) THEN
      SUBGOAL_THEN `(e':real^3->A)(radial_ext f v0) IN IMAGE e' (annulus (&1) (&2))`
        (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`; `Y:A->bool`; `r0:real`; `r2:real`]
                P2BF_SUBCAP_TOP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SYM(ASSUME `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)`)] THEN
    STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^3->A) (cball(vec 0,&1)) = top closure_of Y` ASSUME_TAC THENL
   [SUBGOAL_THEN `cball(vec 0:real^3,&1) = ball(vec 0,&1) UNION sphere(vec 0,&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_CBALL_0; IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    UNDISCH_TAC `top closure_of Y = Y UNION IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = IMAGE (b:real^3->A) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `Y = IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus r0 r2 /\
                annulus r0 r2 SUBSET rfs_neck_dom eps /\
                annulus (&1) (&2) SUBSET (annulus r0 r2:real^3->bool) /\
                ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{y:real^3 | r0 <= norm y /\ norm y <= r2}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(top:A topology) closure_of Y SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `top closure_of Y = Y UNION IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (annulus r0 r2) SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^3->A) (ball(vec 0,&2)) SUBSET U0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(y:real^3) <= &1` THENL
     [SUBGOAL_THEN `(b:real^3->A) y IN top closure_of Y` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1)) = top closure_of Y` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_CBALL_0];
        UNDISCH_TAC `top closure_of Y SUBSET (U0:A->bool)` THEN SET_TAC[]];
      SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(b:real^3->A) y = e'(radial_ext f y)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (annulus r0 r2) SUBSET U0` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      SUBGOAL_THEN `norm(radial_ext f (y:real^3)) = norm y` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `U0 SUBSET (U:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. a SUBSET c /\ b SUBSET c ==> a UNION b SUBSET c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Y = IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `U0 DIFF IMAGE (b:real^3->A) (cball(vec 0,&1)) =
                IMAGE (e':real^3->A) (annulus (&1) r2)` ASSUME_TAC THENL
   [UNDISCH_TAC `U0 DIFF top closure_of Y = IMAGE (e':real^3->A) (annulus (&1) r2)` THEN
    UNDISCH_TAC `IMAGE (b:real^3->A) (cball(vec 0,&1)) = top closure_of Y` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN U0 /\ y2 IN U0
                        ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U0 y1 y2`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN IMAGE (b:real^3->A) (ball(vec 0,&2)) /\ y2 IN IMAGE b (ball(vec 0,&2))
            ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U0 y1 y2`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `ball(vec 0:real^3,&2)`; `b:real^3->A`; `U0:A->bool`]
                  APX_PARAM_JOINABLE_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_BALL] THEN
      UNDISCH_TAC `mfd_ball_chart top (atlas:((A->bool)#(A->real^3))->bool) (b:real^3->A)` THEN
      REWRITE_TAC[mfd_ball_chart];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN IMAGE (e':real^3->A) (annulus r0 r2) /\ y2 IN IMAGE e' (annulus r0 r2)
            ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U0 y1 y2`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus r0 r2:real^3->bool`; `e':real^3->A`; `U0:A->bool`]
                  APX_PARAM_JOINABLE_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U0:A->bool`;
                 `IMAGE (b:real^3->A) (ball(vec 0,&2))`;
                 `IMAGE (e':real^3->A) (annulus r0 r2)`; `(b:real^3->A) v0`] P2BF_JOIN_TWO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(b:real^3->A) v0 = e'(radial_ext f v0)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(U0:A->bool) SUBSET IMAGE (b:real^3->A) (ball(vec 0,&2)) UNION
                                   IMAGE (e':real^3->A) (annulus r0 r2)` MP_TAC THENL
   [UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. a SUBSET b ==> a UNION c SUBSET b UNION c`) THEN
    UNDISCH_TAC `Y = IMAGE (b:real^3->A) (ball(vec 0,&1))` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(y1:A) IN U0` THEN UNDISCH_TAC `(y2:A) IN U0` THEN SET_TAC[]]);;

let P2BF_TWISTED_CLOSURE_EQ = prove
 (`!top atlas (p:real^3->A) (e':real^3->A) Y.
     rfs_twisted_chart top atlas p /\ Y = IMAGE p (annulus (&1 / &2) (&2)) /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
     top closure_of Y = Y UNION IMAGE e' (sphere(vec 0,&1))
     ==> IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} = top closure_of Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (p:real^3->A) (sphere(vec 0,&1 / &2)) SUBSET IMAGE p (sphere(vec 0,&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `rfs_twist (y:real^3)` THEN
    ASM_SIMP_TAC[IN_SPHERE_0; APX_TWIST_SPHERE] THEN
    UNDISCH_TAC `rfs_twisted_chart top (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A)` THEN
    REWRITE_TAC[rfs_twisted_chart] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `rfs_twist (y:real^3)`] o CONJUNCT1) THEN
    ASM_SIMP_TAC[annulus; IN_ELIM_THM; APX_TWIST_SPHERE] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
                annulus (&1 / &2) (&2) UNION sphere(vec 0,&1 / &2) UNION sphere(vec 0,&2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION; annulus; IN_SPHERE_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  UNDISCH_TAC `top closure_of Y = Y UNION IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `IMAGE (e':real^3->A) (sphere(vec 0,&1)) = IMAGE (p:real^3->A) (sphere(vec 0,&2))` THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `Y = IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))` THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `IMAGE (p:real^3->A) (sphere(vec 0,&1 / &2)) SUBSET IMAGE p (sphere(vec 0,&2))` THEN
  SET_TAC[]);;

let P2BF_SUBCAP_TWISTED = prove
 (`!top atlas (g:A->real^3^3) eps U Y (p:real^3->A) (e':real^3->A) z' f f' r0 r2 U0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
     Y = IMAGE p (annulus (&1 / &2) (&2)) /\
     rfs_neck (top,atlas) g eps z' e' /\ IMAGE e' (rfs_neck_dom eps) SUBSET U /\
     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))) /\
     &0 < r0 /\ r0 < &1 /\ &2 <= r2 /\
     {y:real^3 | r0 <= norm y /\ norm y <= r2} SUBSET rfs_neck_dom eps /\
     U0 = Y UNION IMAGE e' (annulus r0 r2)
     ==> open_in top U0 /\ compact_in top (top closure_of U0) /\ U0 SUBSET U /\
         top closure_of Y SUBSET U0 /\ IMAGE e' (annulus r0 r2) SUBSET U0 /\
         IMAGE p (annulus (&1 / &4) (&4)) SUBSET U0 /\
         IMAGE e' (annulus r0 (&1)) SUBSET Y /\
         U0 DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
           IMAGE e' (annulus (&1) r2) /\
         (!y1 y2. y1 IN U0 /\ y2 IN U0 ==> mfd_joinable_in (top,atlas) U0 y1 y2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                 `e':real^3->A`; `Y:A->bool`; `f:real^3->real^3`; `f':real^3->real^3`]
                P2BF_TWISTED_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' e'` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. norm(radial_ext f y) = norm y` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN
    UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN SIMP_TAC[sphere_diffeo];
    ALL_TAC] THEN
  ABBREV_TAC `v0 = (&3 / &2) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm(v0:real^3) = &3 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "v0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 % v0:real^3) IN annulus (&2) (&4) /\ inv(&2) % (&2 % v0) = v0 /\
                (&2 % v0:real^3) IN annulus (&1 / &4) (&4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (e':real^3->A) (annulus (&1) r2) SUBSET top closure_of Y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `(e':real^3->A)(radial_ext f v0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `DISJOINT (IMAGE (e':real^3->A) (annulus (&1) (&2))) (top closure_of Y)` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `(e':real^3->A)(radial_ext f v0)`) THEN
      SUBGOAL_THEN `(e':real^3->A)(radial_ext f v0) IN IMAGE e' (annulus (&1) (&2))`
        (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`; `Y:A->bool`; `r0:real`; `r2:real`]
                P2BF_SUBCAP_TOP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SYM(ASSUME `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)`)] THEN
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                 `e':real^3->A`; `Y:A->bool`] P2BF_TWISTED_CLOSURE_EQ) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus r0 r2 /\
                annulus r0 r2 SUBSET rfs_neck_dom eps /\
                annulus (&1 / &2) (&2) SUBSET (annulus (&1 / &4) (&4):real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN GEN_TAC THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{y:real^3 | r0 <= norm y /\ norm y <= r2}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(top:A topology) closure_of Y SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `top closure_of Y = Y UNION IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. b SUBSET c ==> a UNION b SUBSET a UNION c`) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (annulus r0 r2) SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&2) (&4) ==> (p:real^3->A) y IN U0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3->A) y = e'(radial_ext f (inv(&2) % y))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (e':real^3->A) (annulus r0 r2) SUBSET U0` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN annulus (&2) (&4)` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4)) SUBSET U0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `&1 / &2 <= norm(y:real^3) /\ norm y <= &2` THENL
     [SUBGOAL_THEN `(p:real^3->A) y IN top closure_of Y` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (p:real^3->A) {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
                     top closure_of Y` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        UNDISCH_TAC `(top:A topology) closure_of Y SUBSET U0` THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `&2 < norm(y:real^3)` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(y:real^3) IN annulus (&1 / &4) (&4)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ norm y < &1 / &2 /\ &1 / &4 < norm y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN annulus (&1 / &4) (&4)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(&1 / &2 <= norm(y:real^3) /\ norm y <= &2)` THEN
      UNDISCH_TAC `~(&2 < norm(y:real^3))` THEN
      SIMP_TAC[GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(rfs_twist (y:real^3)) = inv(norm y)` ASSUME_TAC THENL
     [MATCH_MP_TAC P2BF_TWIST_NORM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 < inv(norm(y:real^3)) /\ inv(norm y) < &4` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `norm(y:real^3)` THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `norm(y:real^3)` THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->A) y = p(rfs_twist y)` SUBST1_TAC THENL
     [UNDISCH_TAC `rfs_twisted_chart top (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A)` THEN
      REWRITE_TAC[rfs_twisted_chart] THEN
      DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `rfs_twist (y:real^3)`] o CONJUNCT1) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `U0 SUBSET (U:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. a SUBSET c /\ b SUBSET c ==> a UNION b SUBSET c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Y = IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))` THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `U0 DIFF IMAGE (p:real^3->A) {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
                IMAGE (e':real^3->A) (annulus (&1) r2)` ASSUME_TAC THENL
   [UNDISCH_TAC `U0 DIFF top closure_of Y = IMAGE (e':real^3->A) (annulus (&1) r2)` THEN
    UNDISCH_TAC `IMAGE (p:real^3->A) {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} =
                 top closure_of Y` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN U0 /\ y2 IN U0
                        ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U0 y1 y2`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN IMAGE (p:real^3->A) (annulus (&1 / &4) (&4)) /\
            y2 IN IMAGE p (annulus (&1 / &4) (&4))
            ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U0 y1 y2`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus (&1 / &4) (&4):real^3->bool`; `p:real^3->A`]
                  APX_LOCAL_PARAM_SMOOTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
      UNDISCH_TAC `rfs_twisted_chart top (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A)` THEN
      SIMP_TAC[rfs_twisted_chart];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus (&1 / &4) (&4):real^3->bool`; `p:real^3->A`; `U0:A->bool`]
                  APX_SMOOTH_JOINABLE_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_ANNULUS; APX_CONNECTED_ANNULUS3]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN IMAGE (e':real^3->A) (annulus r0 r2) /\ y2 IN IMAGE e' (annulus r0 r2)
            ==> mfd_joinable_in (top,atlas:((A->bool)#(A->real^3))->bool) U0 y1 y2`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus r0 r2:real^3->bool`; `e':real^3->A`; `U0:A->bool`]
                  APX_PARAM_JOINABLE_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
      EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U0:A->bool`;
                 `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))`;
                 `IMAGE (e':real^3->A) (annulus r0 r2)`; `(p:real^3->A) (&2 % v0)`]
                P2BF_JOIN_TWO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(p:real^3->A) (&2 % v0) = e'(radial_ext f v0)` SUBST1_TAC THENL
       [UNDISCH_TAC `!y. y IN annulus (&2) (&4) ==> (p:real^3->A) y = e'(radial_ext f (inv(&2) % y))` THEN
        DISCH_THEN(MP_TAC o SPEC `&2 % v0:real^3`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `(U0:A->bool) SUBSET IMAGE (p:real^3->A) (annulus (&1 / &4) (&4)) UNION
                                   IMAGE (e':real^3->A) (annulus r0 r2)` MP_TAC THENL
   [UNDISCH_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus r0 r2)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:A->bool. a SUBSET b ==> a UNION c SUBSET b UNION c`) THEN
    UNDISCH_TAC `Y = IMAGE (p:real^3->A) (annulus (&1 / &2) (&2))` THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(y1:A) IN U0` THEN UNDISCH_TAC `(y2:A) IN U0` THEN SET_TAC[]]);;

let P2BF_NECK_UNIF_RENORM = prove
 (`!eps1 eps2 Cr. &0 < eps1 /\ eps1 < eps2 /\ eps2 < &1 / &4 /\ &1 <= Cr
     ==> ?dn. &0 < dn /\
           !delta top atlas (g:A->real^3^3) U z e R0 top' atlas' (g':B->real^3^3) psi psi'.
              &0 < delta /\ delta <= dn /\
              smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
              rfs_neck (top,atlas) g eps1 z e /\ IMAGE e (rfs_neck_dom eps1) SUBSET U /\
              &0 < R0 /\ R0 <= Cr * mfd_scalar atlas g z /\
              smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_mclose (rfs_kreg delta) delta atlas U (\y. R0 %% g y)
                (\y. R0 %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> rfs_neck (top',atlas') g' eps2 (psi z) (psi o e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`]
    (MATCH_MP P2BS_NECK_UNIF (CONJ P2B_REQ_LRG_BASE P2B_REQ_LRG_RM_NEAR))) THEN
  DISCH_THEN(MP_TAC o SPECL [`eps1:real`; `eps2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NU"))) THEN
  SUBGOAL_THEN `&1 <= (&1 + Cr) pow rfs_kreg dN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `dN / (&1 + Cr) pow rfs_kreg dN` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) z /\
                mfd_param top atlas (rfs_neck_dom eps1) (e:real^3->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps1 z e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta <= dN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dN / (&1 + Cr) pow rfs_kreg dN` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ &1 * d <= x * d ==> d <= d * x`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_kreg dN <= rfs_kreg delta` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_KREG_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + R0 / mfd_scalar atlas (g:A->real^3^3) z) pow rfs_kreg dN * delta pow 2 <= dN pow 2`
  ASSUME_TAC THENL
   [ABBREV_TAC `Rz = mfd_scalar atlas (g:A->real^3^3) z` THEN
    SUBGOAL_THEN `R0 / Rz <= Cr` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= R0 / Rz` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + Cr) pow rfs_kreg dN * (dN / (&1 + Cr) pow rfs_kreg dN) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `q = (&1 + Cr) pow (rfs_kreg dN)` THEN
    SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `q * dN pow 2 / q pow 2 = dN pow 2 / q` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ &1 * d <= q * d ==> d <= d * q`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^3->A) (rfs_neck_dom eps1))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps1`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "NU" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `psi':B->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `IMAGE (psi:A->B) U`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BC_MCLOSE_RENORM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                        `IMAGE (psi:A->B) U`; `psi':B->A`; `rfs_kreg delta`; `delta:real`;
                        `R0:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2BF_DILATE_ANNULUS = prove
 (`!c a b. &0 < c ==> IMAGE (\w:real^3. c % w) (annulus a b) = annulus (c * a) (c * b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_LMUL_EQ];
    STRIP_TAC THEN EXISTS_TAC `inv c % x:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    SUBGOAL_THEN `&0 < inv c` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `c:real` THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `c:real` THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]]]);;

let P2BF_NECK_DOM_EXP = prove
 (`!eps. rfs_neck_dom eps =
         annulus (inv(exp(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))`,
  REWRITE_TAC[rfs_neck_dom; REAL_EXP_NEG]);;

let P2BF_END_NECK_SRC = prove
 (`!K0. (!y:real^3. ~(y = vec 0) ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2)
        ==> !top atlas (g:A->real^3^3) eps eps' z' (e':real^3->A).
              &0 < eps /\ (&4 + &576 * (&1 + abs K0)) * eps <= &1 / &2 /\
              &4 / &3 * eps <= eps' /\ riemannian_metric atlas g /\
              rfs_neck (top,atlas) g eps z' e'
              ==> rfs_neck (top,atlas) g ((&4 + &576 * (&1 + abs K0)) * eps)
                    (e' (exp(inv(sqrt(&2) * eps')) % basis 1))
                    (e' o (\w. exp(inv(sqrt(&2) * eps')) % w)) /\
                  IMAGE (e' o (\w. exp(inv(sqrt(&2) * eps')) % w)) (rfs_neck_dom eps') =
                    IMAGE e' (annulus (&1) (exp(inv(sqrt(&2) * eps')) *
                                          exp(inv(sqrt(&2) * eps')))) /\
                  IMAGE (e' o (\w. exp(inv(sqrt(&2) * eps')) % w))
                    (rfs_neck_dom ((&4 + &576 * (&1 + abs K0)) * eps)) SUBSET
                    IMAGE e' (rfs_neck_dom eps)`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "K0") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c = exp(inv(sqrt(&2) * eps'))` THEN
  ABBREV_TAC `y1 = c % basis 1:real^3` THEN
  SUBGOAL_THEN `&0 < eps' /\ eps < eps' /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y1:real^3) = c` ASSUME_TAC THENL
   [EXPAND_TAC "y1" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval (y1:real^3) = inv eps'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[apx_sval] THEN SUBST1_TAC(SYM(ASSUME `exp(inv(sqrt(&2) * eps')) = c`)) THEN REWRITE_TAC[LOG_EXP] THEN
    REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ abs(apx_sval y1) <= &3 / (&4 * eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[P2BF_NECK_DOM_EXP; annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `c < exp(inv(sqrt(&2) * eps))` ASSUME_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `exp(inv(sqrt(&2) * eps')) = c`)) THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `inv(exp(inv(sqrt(&2) * eps))) < &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < inv eps'` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH `&0 < &4`] THEN
      SUBGOAL_THEN `inv eps' * (&4 * eps) = (&4 * eps) / eps'` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `K0:real` APX_NECK_RECENTRE_GEN) THEN
    ANTS_TAC THENL [USE_THEN "K0" ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                               `g:A->real^3^3`; `eps:real`; `z':A`; `e':real^3->A`;
                               `y1:real^3`]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN REWRITE_TAC[P2BF_NECK_DOM_EXP] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P2BF_DILATE_ANNULUS; REAL_MUL_RINV; REAL_LT_IMP_NZ];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    SUBGOAL_THEN `c = norm(y1:real^3)` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC APX_DILATE_DOM THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let P2BF_SRC_CLAUSE7_SUB = prove
 (`!top atlas (g:A->real^3^3) eps z (e:real^3->A) U U0 Y d.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     rfs_neck (top,atlas) g eps z e /\ eps <= &1 / &4 /\
     (!w. w IN IMAGE e (sphere(vec 0,&1))
          ==> mfd_scalar atlas g z / &2 <= mfd_scalar atlas g w) /\
     open_in top Y /\
     top frontier_of (top closure_of Y) SUBSET IMAGE e (sphere(vec 0,&1)) /\
     top closure_of Y SUBSET U0 /\ IMAGE e (rfs_neck_dom eps) SUBSET U0 /\
     (!y r. y IN Y /\ &0 < r /\
            (?B. !q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= B) /\
            sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) = inv(r pow 2)
            ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                top closure_of mfd_ball (top,atlas) g y r SUBSET U /\
                ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                    d <= v / r pow 3)
     ==> !y r. y IN Y /\ &0 < r /\
               (?B. !q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= B) /\
               sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) = inv(r pow 2)
               ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                   top closure_of mfd_ball (top,atlas) g y r SUBSET U0 /\
                   ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                       d <= v / r pow 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C7"))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `r:real`] THEN STRIP_TAC THEN
  USE_THEN "C7" (MP_TAC o SPECL [`y:A`; `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ALL_TAC; EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^3^3) y r` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED] THEN
    REWRITE_TAC[SUBSET; mfd_ball; mfd_cball; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BC_SC_CBALL_IN THEN
  MAP_EVERY EXISTS_TAC [`eps:real`; `z:A`; `e:real^3->A`; `Y:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t:A->bool. y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `Y:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) q <=
                sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r))` MP_TAC THENL
   [MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
     [EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Uniform constants: the Ricci lower bound from Kr, the arithmetic of the   *)
(* diameter and volume margins, the clause 7 constants (rmin, Bv, K, e0 and  *)
(* eta in terms of C, eps' and Kr only), the excursion cost bound, and the   *)
(* polynomial conditions on alpha for the derivative clauses.                *)
(* ------------------------------------------------------------------------- *)

let P2BF_RICCI_LOWER_KR = prove
 (`!top atlas (g:A->real^3^3) U R0 Kr.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     U SUBSET topspace top /\ &0 < R0 /\
     (!y. y IN U ==> rfa_rmd2 0 atlas (\z. R0 %% g z) y <= Kr)
     ==> !y w. y IN U
               ==> --(&2 * ((&3 * sqrt(max Kr (&0))) / &2 * R0)) * (w dot (g y ** w)) <=
                   mfd_ricci atlas g y w w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`y:A`; `w:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN U` THEN UNDISCH_TAC `(U:A->bool) SUBSET topspace top` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y)))
                 (metric_local atlas (chart_at atlas y) (\z. R0 %% (g:A->real^3^3) z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `R0:real`]
                  RIEMANNIAN_METRIC_CMUL) THEN
    ASM_REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                    (\z. R0 %% (g:A->real^3^3) z)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`;
                 `max Kr (&0)`; `w:real^3`] (INST_TYPE [`:3`,`:N`] RFA_LRIC_BOUND)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max b (&0)`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[rfa_rmd2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y)))
                 (metric_local atlas (chart_at atlas y) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[METRIC_LOCAL_CMUL] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)))
                        (FST(chart_at atlas y))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A))
                    (g:A->real^3^3)`;
                 `R0:real`; `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)) y`;
                 `w:real^3`; `w:real^3`] (INST_TYPE [`:3`,`:N`] LRICCI_SCALE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3; GSYM mfd_ricci] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `y:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

let P2BF_SQRT_1_1 = prove
 (`!x. &0 <= x /\ x <= &1 / &10 ==> sqrt(&1 + x) <= &21 / &20`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC);;

let P2BF_SQRT_SA = prove
 (`!S a. &0 < S /\ &0 <= a /\ a <= S / &10
         ==> &0 < sqrt(S + a) /\ sqrt(S + a) <= &21 / &20 * sqrt S /\
             inv(sqrt S) <= &21 / &20 * inv(sqrt(S + a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt S /\ &0 < sqrt(S + a)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(S + a) <= &21 / &20 * sqrt S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(sqrt S) = (&21 / &20) * inv(&21 / &20 * sqrt S)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt S` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;

let P2BF_DIAM_ARITH = prove
 (`!C C' S a dl d3 D.
     &100 <= C /\ &2 * C <= C' /\ &0 < S /\ &0 <= a /\ a <= S / &10 /\
     &0 <= dl /\ dl <= &1 / &10 /\ &0 <= d3 /\ d3 < C * inv(sqrt S) /\
     &0 <= D /\ D <= &5 * sqrt C * inv(sqrt S)
     ==> sqrt(&1 + dl) * (d3 + D) < C' * inv(sqrt(S + a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:real`; `a:real`] P2BF_SQRT_SA) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `dl:real` P2BF_SQRT_1_1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `u = inv(sqrt S)` THEN ABBREV_TAC `v = inv(sqrt(S + a))` THEN
  SUBGOAL_THEN `&0 < u /\ &0 < v` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&10 <= sqrt C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&5 * sqrt C <= C / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt C pow 2 = C` (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th])
    THENL [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s * (s - &10) ==> &5 * s <= s pow 2 / &2`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d3 + D < &3 / &2 * C * u` ASSUME_TAC THENL
   [SUBGOAL_THEN `D <= (C / &2) * u` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&5 * sqrt C) * u` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + dl) * (d3 + D) <= &21 / &20 * (d3 + D)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * C * u <= &21 / &20 * (C' * v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C' * u` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `a * c * v = c * (a * v)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BF_VOL_ARITH = prove
 (`!C C' S a dl v.
     &1 <= C /\ &2 * C <= C' /\ &0 < S /\ &0 <= a /\ a <= S / &10 /\
     &0 <= dl /\ dl <= &1 / &10 /\ &0 <= v /\ v < C * inv(sqrt S) pow 3
     ==> (&1 + dl) * sqrt(&1 + dl) * v < C' * inv(sqrt(S + a)) pow 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:real`; `a:real`] P2BF_SQRT_SA) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `dl:real` P2BF_SQRT_1_1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `u = inv(sqrt S)` THEN ABBREV_TAC `w = inv(sqrt(S + a))` THEN
  SUBGOAL_THEN `&0 < u /\ &0 < w` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "w"] THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u pow 3 <= (&21 / &20) pow 3 * w pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + dl) * sqrt(&1 + dl) <= &11 / &10 * &21 / &20` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + dl) * sqrt(&1 + dl) * v <= (&11 / &10 * &21 / &20) * v` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&11 / &10 * &21 / &20) * v < (&11 / &10 * &21 / &20) * (C * u pow 3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * u pow 3 <= C * (&21 / &20) pow 3 * w pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * C * w pow 3 <= C' * w pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * w pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BF_C7_CONSTS = prove
 (`!C eps' k. &1 <= C /\ &0 < eps' /\ eps' <= &1 / &40 /\ &0 <= k
     ==> ?eta. &0 < eta /\ eta <= &1 / &40 /\
           !R0 Rz. &0 < R0 /\ &0 < Rz /\ Rz <= C * R0
             ==> &0 < inv(sqrt R0) / (&2 * sqrt(&2 * C)) /\
                 inv(sqrt R0) / (&2 * sqrt(&2 * C)) <= sqrt(&1 / (&2 * (C * R0))) / &2 /\
                 &2 * sqrt(&2 / (R0 / C)) <= &2 * sqrt(&2 * C) * inv(sqrt R0) /\
                 inv(sqrt R0) / (&2 * sqrt(&2 * C)) <= &2 * sqrt(&2 * C) * inv(sqrt R0) /\
                 &4 * eta * sqrt(&2 / (R0 / C)) <= sqrt(&1 - eps') * inv(sqrt Rz) * inv eps' /\
                 &8 * eta * sqrt(&2 / (R0 / C)) <=
                   &1 / &4 * (inv(sqrt R0) / (&2 * sqrt(&2 * C))) pow 3 /
                   (&8 * (&2 * sqrt(&2 * C) * inv(sqrt R0)) pow 2 *
                    exp(&2 * sqrt(k * R0) * (&2 * sqrt(&2 * C) * inv(sqrt R0))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = sqrt(&2 * C)` THEN
  SUBGOAL_THEN `&1 <= s /\ s pow 2 = &2 * C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt C` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `E = exp(&4 * s * sqrt k)` THEN
  SUBGOAL_THEN `&0 < E` ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * sqrt C /\ &0 < &8192 * s pow 6 * E` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &40) (min (inv(s * sqrt C)) (inv(&8192 * s pow 6 * E)))` THEN
  ABBREV_TAC `eta = min (&1 / &40) (min (inv(s * sqrt C)) (inv(&8192 * s pow 6 * E)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 / &40 /\ eta <= inv(s * sqrt C) /\
                eta <= inv(&8192 * s pow 6 * E)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `eta * (s * sqrt C) <= &1 /\ eta * (&8192 * s pow 6 * E) <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(s * sqrt C) * (s * sqrt C)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&8192 * s pow 6 * E) * (&8192 * s pow 6 * E)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`R0:real`; `Rz:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `q = sqrt R0` THEN
  SUBGOAL_THEN `&0 < q /\ q pow 2 = R0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `u = inv q` THEN
  SUBGOAL_THEN `&0 < u /\ q * u = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_RINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 / (R0 / C)) = s * u` SUBST1_TAC THENL
   [SUBGOAL_THEN `&2 / (R0 / C) = (&2 * C) * inv R0` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R0` THEN UNDISCH_TAC `&1 <= C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt((&2 * C) * inv R0) = sqrt(&2 * C) * sqrt(inv R0)` SUBST1_TAC THENL
     [ACCEPT_TAC(ISPECL [`&2 * C`; `inv R0`] SQRT_MUL); ALL_TAC] THEN
    ASM_REWRITE_TAC[SQRT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 / (&2 * (C * R0))) = u / s` SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 / (&2 * (C * R0)) = inv(&2 * C) * inv R0` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R0` THEN UNDISCH_TAC `&1 <= C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(inv(&2 * C) * inv R0) = sqrt(inv(&2 * C)) * sqrt(inv R0)`
    SUBST1_TAC THENL
     [ACCEPT_TAC(ISPECL [`inv(&2 * C)`; `inv R0`] SQRT_MUL); ALL_TAC] THEN
    ASM_REWRITE_TAC[SQRT_INV] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(k * R0) * u = sqrt k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LT_IMP_LE] THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    SUBGOAL_THEN `u / (&2 * s) = (&2 * s * u) * inv(&4 * s pow 2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &2 * s * u` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x * y <= x * &1 ==> x * y <= x`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `u / sqrt C <= inv(sqrt Rz)` ASSUME_TAC THENL
     [SUBGOAL_THEN `u / sqrt C = inv(sqrt C * q)` SUBST1_TAC THENL
       [EXPAND_TAC "u" THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "q" THEN
      SIMP_TAC[GSYM SQRT_MUL; REAL_LT_IMP_LE; ASSUME `&0 < R0`;
               REAL_ARITH `&1 <= C ==> &0 <= C`; ASSUME `&1 <= C`] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - eps') /\ &40 <= inv eps'` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&40 = inv(&1 / &40)` SUBST1_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&20 * (u / sqrt C) <= sqrt(&1 - eps') * inv(sqrt Rz) * inv eps'` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&20 * x <= (&1 / &2 * x) * &40 /\ (&1 / &2 * x) * &40 <= y
                               ==> &20 * x <= y`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        TRY REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c`) THEN
    SUBGOAL_THEN `&4 * eta * s * u = (&4 * (eta * (s * sqrt C))) * (u / sqrt C)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u / sqrt C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (u / sqrt C)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&2 * sqrt(k * R0) * (&2 * s * u) = &4 * s * sqrt k` SUBST1_TAC THENL
     [UNDISCH_TAC `sqrt(k * R0) * u = sqrt k` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &4 * (u / (&2 * s)) pow 3 / (&8 * (&2 * s * u) pow 2 * E) =
                  u * inv(&1024 * s pow 5 * E)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < u` THEN UNDISCH_TAC `&0 < s` THEN UNDISCH_TAC `&0 < E` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&8 * eta * s * u = u * (&8 * eta * s)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1024 * s pow 5 * E` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&1024 * s pow 5 * E) = &1 / (&1024 * s pow 5 * E)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `(&8 * eta * s) * &1024 * s pow 5 * E = eta * (&8192 * s pow 6 * E)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

let P2BF_D_BOUND = prove
 (`!eps Rz S C. &0 < eps /\ eps <= &1 / &10 /\ &0 < Rz /\ &0 < S /\ S <= C * Rz /\ &1 <= C
     ==> sqrt(&1 + eps) * inv(sqrt Rz) * (sqrt(&2) * pi) <= &5 * sqrt C * inv(sqrt S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Rz /\ &0 < sqrt S /\ &0 < sqrt C` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt Rz) <= sqrt C * inv(sqrt S)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt S <= sqrt C * sqrt Rz` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LT_IMP_LE; REAL_ARITH `&1 <= C ==> &0 <= C`] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt Rz) = sqrt C * inv(sqrt C * sqrt Rz)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt C` THEN UNDISCH_TAC `&0 < sqrt Rz` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * (sqrt(&2) * pi) <= &5` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&1 + eps) <= &21 / &20 /\ sqrt(&2) <= &1415 / &1000 /\ pi <= &63 / &20 /\
                  &0 <= sqrt(&1 + eps) /\ &0 <= sqrt(&2) /\ &0 <= pi`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
        REWRITE_TAC[PI_POS_LE]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&21 / &20 * (&1415 / &1000 * &63 / &20)` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * inv(sqrt Rz) * (sqrt(&2) * pi) =
                (sqrt(&1 + eps) * (sqrt(&2) * pi)) * inv(sqrt Rz)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&5 * sqrt C * inv(sqrt S) = &5 * (sqrt C * inv(sqrt S))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[PI_POS_LE; SQRT_POS_LE; REAL_ARITH `&0 <= &2`]];
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

let P2BF_ALPHA_POLY = prove
 (`!C alpha. &1 <= C /\ &0 <= alpha /\ alpha * C <= &1 / &320
     ==> &3 * alpha <= inv C /\
         alpha * (&1 + &3 * (&3 / &2 * C) pow 2 * inv C pow 2) <=
           ((&3 / &2 * C) pow 2 - C pow 2) * inv C pow 3 /\
         alpha * (&3 + &2 * (&3 / &2 * C) * inv C) <= (&3 / &2 * C - C) * inv C pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = inv C` THEN
  SUBGOAL_THEN `&0 < m /\ C * m = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_RINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha <= m / &320` ASSUME_TAC THENL
   [SUBGOAL_THEN `alpha = (alpha * C) * m` SUBST1_TAC THENL
     [UNDISCH_TAC `C * m = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &2 * C) pow 2 * m pow 2 = &9 / &4 /\
                ((&3 / &2 * C) pow 2 - C pow 2) * m pow 3 = &5 / &4 * m /\
                (&3 / &2 * C) * m = &3 / &2 /\
                (&3 / &2 * C - C) * m pow 2 = m / &2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `C * m = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The volume of the target region when the target metric is complete or the *)
(* closure of the target region is compact (P2BF_T_VOL_GEN), and the uniform *)
(* common lemma: from the sub-cap data, the target chart data and closeness  *)
(* on U with a delta depending only on C, C', eps, eps', Kr and dc, the      *)
(* target is a (C', eps')-cap on psi U0 with core psi Y                      *)
(* (P2BF_CAP_COMMON_UNIF_GEN).                                               *)
(* ------------------------------------------------------------------------- *)

let P2BF_T_VOL_K = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U psi psi' K v0 dl.
     hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\ &0 <= dl /\
     compact_in top' K /\ IMAGE psi U SUBSET K /\
     mfd_has_volume (top,atlas) g U v0 /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                (&1 + dl) * (v dot (g y ** v)))
     ==> ?v'. mfd_has_volume (top',atlas') g' (IMAGE psi U) v' /\
              v' <= (&1 + dl) * sqrt(&1 + dl) * v0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `K:B->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `wc:real`) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':B->real^3^3`; `IMAGE (psi:A->B) U`; `K:B->bool`; `wc:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN]; STRIP_TAC] THEN
  EXISTS_TAC `mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) U)` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U:A->bool`; `IMAGE (psi:A->B) U`; `psi:A->B`; `psi':B->A`; `U:A->bool`;
                 `v0:real`;
                 `mfd_volume (top',atlas') (g':B->real^3^3) (IMAGE (psi:A->B) U)`;
                 `&1 + dl`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

let P2BF_T_VOL_GEN = prove
 (`!top atlas (g:A->real^3^3) top' atlas' (g':B->real^3^3) U psi psi' x D v0 dl.
     hausdorff_space top' /\
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
     (mfd_complete (top',atlas') g' \/ compact_in top' (top' closure_of IMAGE psi U)) /\
     mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\ x IN U /\ &0 <= dl /\
     (!z1 z2. z1 IN IMAGE psi U /\ z2 IN IMAGE psi U
              ==> mfd_joinable_in (top',atlas') (IMAGE psi U) z1 z2 /\
                  mfd_dist_in (top',atlas') g' (IMAGE psi U) z1 z2 <= D) /\
     mfd_has_volume (top,atlas) g U v0 /\
     (!y v. y IN U
            ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                (&1 + dl) * (v dot (g y ** v)))
     ==> ?v'. mfd_has_volume (top',atlas') g' (IMAGE psi U) v' /\
              v' <= (&1 + dl) * sqrt(&1 + dl) * v0`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_complete" with Failure _ -> false))
        (concl th))) THENL
   [MATCH_MP_TAC P2BC_T_VOL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `psi':B->A`; `x:A`; `D:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BF_T_VOL_K THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `psi':B->A`;
                          `top' closure_of IMAGE (psi:A->B) U`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [mfd_diffeo] o check (fun th ->
        try fst(dest_const(fst(strip_comb(concl th)))) = "mfd_diffeo"
        with Failure _ -> false)) THEN
    SIMP_TAC[]]);;

let P2BF_CAP_COMMON_UNIF_GEN = prove
 (`!eps1B C C' eps eps' Kr dc.
     (!top' atlas' (g':B->real^3^3) eps z e.
         &0 < eps /\ eps <= eps1B /\ riemannian_metric atlas' g' /\
         rfs_neck (top',atlas') g' eps z e
         ==> !w. w IN IMAGE e (rfs_neck_dom eps)
                 ==> mfd_scalar atlas' g' z / &2 <= mfd_scalar atlas' g' w) /\
     P2B_REQ_LRG_DERIV_STATEMENT /\
     &100 <= C /\ &2 * C <= C' /\ &0 < eps /\ eps <= &1 / &10 /\
     &0 < eps' /\ eps' <= &1 / &40 /\ eps' <= eps1B /\ &0 < dc
     ==> ?delta. &0 < delta /\
       !top atlas (g:A->real^3^3) x U Y U0 zb eb r0 r2
        top' atlas' (g':B->real^3^3) psi psi'.
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
         open_in top U /\ open_in top Y /\ open_in top U0 /\
         compact_in top (top closure_of U0) /\
         x IN Y /\ Y SUBSET U0 /\ U0 SUBSET U /\
         (!y1 y2. y1 IN U /\ y2 IN U ==> mfd_joinable_in (top,atlas) U y1 y2) /\
         (!y1 y2. y1 IN U0 /\ y2 IN U0 ==> mfd_joinable_in (top,atlas) U0 y1 y2) /\
         (!y. y IN U ==> &0 < mfd_scalar atlas g y) /\
         rfs_sup_lt {mfd_dist_in (top,atlas) g U y1 y2 | y1,y2 | y1 IN U /\ y2 IN U}
                    (C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)))) /\
         rfs_sup_lt {mfd_scalar atlas g y2 / mfd_scalar atlas g y1 |
                     y1 IN U /\ y2 IN U} C /\
         (?v. mfd_has_volume (top,atlas) g U v /\
              v < C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U))) pow 3) /\
         (?d. inv C < d /\
              !y r. y IN Y /\ &0 < r /\
                    (?B. !q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= B) /\
                    sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) =
                    inv(r pow 2)
                    ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                        top closure_of mfd_ball (top,atlas) g y r SUBSET U0 /\
                        ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                            d <= v / r pow 3) /\
         rfs_sup_lt {sqrt(rfs_scalar_grad2 atlas g y) /
                     (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) | y IN U} C /\
         rfs_sup_lt {abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                     mfd_scalar atlas g y pow 2 | y IN U} C /\
         (!y l. y IN U /\ l <= 2
                ==> lrm_deriv_norm2 l
                      (metric_local atlas (chart_at atlas y)
                         (\z. mfd_scalar atlas g x %% g z))
                      (SND(chart_at atlas y) y) <= Kr) /\
         rfs_neck (top,atlas) g eps zb eb /\ rfs_neck (top,atlas) g eps' zb eb /\
         IMAGE eb (rfs_neck_dom eps) SUBSET U /\ IMAGE eb (rfs_neck_dom eps') SUBSET U0 /\
         top frontier_of (top closure_of Y) SUBSET IMAGE eb (sphere(vec 0,&1)) /\
         top closure_of Y SUBSET U0 /\ compact_in top (top closure_of Y) /\
         top closure_of Y = Y UNION IMAGE eb (sphere(vec 0,&1)) /\
         (!w. w IN IMAGE eb (rfs_neck_dom eps')
              ==> mfd_scalar atlas g zb / &2 <= mfd_scalar atlas g w) /\
         U0 = Y UNION IMAGE eb (annulus r0 r2) /\ &0 < r0 /\ r0 < &1 /\ &1 < r2 /\
         {y:real^3 | r0 <= norm y /\ norm y <= r2} SUBSET rfs_neck_dom eps /\
         IMAGE eb (annulus r0 (&1)) SUBSET Y /\
         hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
         riemannian_metric atlas' g' /\
         (mfd_complete (top',atlas') g' \/ compact_in top' (top' closure_of IMAGE psi U)) /\
         mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
         (!dl. &0 < dl /\ dl <= dc /\
               rfs_mclose (rfs_kreg dl) dl atlas U (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ((?b e e' z z' f f'.
                       mfd_ball_chart top' atlas' b /\
                       IMAGE b (ball(vec 0,&2)) SUBSET IMAGE psi U0 /\
                       IMAGE psi Y = IMAGE b (ball(vec 0,&1)) /\
                       rfs_neck (top',atlas') g' eps' z e /\
                       IMAGE e (rfs_neck_dom eps') = IMAGE psi U0 DIFF IMAGE b (cball(vec 0,&1)) /\
                       rfs_neck (top',atlas') g' eps' z' e' /\
                       IMAGE e' (rfs_neck_dom eps') SUBSET IMAGE psi U0 /\
                       IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
                       sphere_diffeo f f' /\
                       (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) \/
                    (?p e e' z z' f f'.
                       rfs_twisted_chart top' atlas' p /\
                       IMAGE p (annulus (&1 / &4) (&4)) SUBSET IMAGE psi U0 /\
                       IMAGE psi Y = IMAGE p (annulus (&1 / &2) (&2)) /\
                       rfs_neck (top',atlas') g' eps' z e /\
                       IMAGE e (rfs_neck_dom eps') =
                         IMAGE psi U0 DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
                       rfs_neck (top',atlas') g' eps' z' e' /\
                       IMAGE e' (rfs_neck_dom eps') SUBSET IMAGE psi U0 /\
                       IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
                       sphere_diffeo f f' /\
                       (!y. y IN annulus (&2) (&4)
                            ==> p y = e'(radial_ext f (inv(&2) % y))))) /\
                   rfs_neck (top',atlas') g' eps' (psi zb) (psi o eb) /\
                   top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                     IMAGE (psi o eb) (sphere(vec 0,&1)) /\
                   top' closure_of IMAGE psi Y SUBSET IMAGE psi U0 /\
                   IMAGE (psi o eb) (rfs_neck_dom eps') SUBSET IMAGE psi U0) /\
         rfs_mclose (rfs_kreg delta) delta atlas U
           (\y. mfd_scalar atlas g x %% g y)
           (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
         ==> rfs_cap (top',atlas') g' C' eps' (IMAGE psi U0) (IMAGE psi Y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "NSB") (CONJUNCTS_THEN2
    (LABEL_TAC "LRGD" o MATCH_MP P2B9S_LRG_D) STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&1 <= C /\ &0 < C /\ &0 <= (&3 * sqrt(max Kr (&0))) / &2` STRIP_ASSUME_TAC
  THENL
   [REPEAT CONJ_TAC THEN TRY SPDR7_ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `eps':real`; `(&3 * sqrt(max Kr (&0))) / &2`] P2BF_C7_CONSTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta7:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C7C")))) THEN
  ABBREV_TAC `alpha = eta7 / (&8 * C)` THEN
  SUBGOAL_THEN `&0 < alpha /\ alpha * (&8 * C) = eta7 /\ alpha <= &1 / (&320 * C)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha" THEN
    SUBGOAL_THEN `&0 < &8 * C` ASSUME_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ; ASSUME `&0 < eta7`;
             ASSUME `&0 < &8 * C`] THEN
    REWRITE_TAC[real_div] THEN
    SUBGOAL_THEN `inv(&320 * C) = (&1 / &40) * inv(&8 * C)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  USE_THEN "LRGD" (fun th -> MP_TAC(MATCH_MP (SPECL [`Kr:real`; `alpha:real`] th)
                                            (ASSUME `&0 < alpha`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `etaL:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Dform"))) THEN
  EXISTS_TAC `min (&1 / &10) (min etaL (min dc (eta7 / &2)))` THEN
  ABBREV_TAC `delta = min (&1 / &10) (min etaL (min dc (eta7 / &2)))` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= &1 / &10 /\ delta <= etaL /\ delta <= dc /\
                delta <= eta7 / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC o check (fun th -> is_exists(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "mfd_has_volume" with Failure _ -> false))
        (concl th) &&
    not (can (find_term ((=) `inv C`)) (concl th)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o check (fun th -> is_exists(concl th) &&
    can (find_term ((=) `inv C`)) (concl th))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `U0:A->bool`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `(top:A topology) closure_of Y`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "mfd_dist_in"
                                              with Failure _ -> false)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d9:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_grad2"
                                              with Failure _ -> false)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d10:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_lap"
                                              with Failure _ -> false)) (concl th) &&
                     can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                              with Failure _ -> false)) (concl th))) THEN
  SUBGOAL_THEN `(x:A) IN U0 /\ (x:A) IN U` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN Y` THEN UNDISCH_TAC `(Y:A->bool) SUBSET U0` THEN
    UNDISCH_TAC `(U0:A->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [EXPAND_TAC "R0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN U /\ y2 IN U
                        ==> mfd_scalar atlas (g:A->real^3^3) y2 <= d4 * mfd_scalar atlas g y1`
  (LABEL_TAC "RAT") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) y2 / mfd_scalar atlas g y1` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `d4:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`y2:A`; `y1:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= d4` ASSUME_TAC THENL
   [USE_THEN "RAT" (fun th -> MP_TAC(MATCH_MP (SPECL [`x:A`; `x:A`] th)
      (CONJ (ASSUME `(x:A) IN U`) (ASSUME `(x:A) IN U`)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 * R0 <= d4 * R0` MP_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> R0 / C <= mfd_scalar atlas (g:A->real^3^3) y /\
                               mfd_scalar atlas g y <= C * R0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "RAT" (fun th -> MP_TAC(MATCH_MP (SPECL [`y:A`; `x:A`] th)
      (CONJ (ASSUME `(y:A) IN U`) (ASSUME `(x:A) IN U`)))) THEN
    USE_THEN "RAT" (fun th -> MP_TAC(MATCH_MP (SPECL [`x:A`; `y:A`] th)
      (CONJ (ASSUME `(x:A) IN U`) (ASSUME `(y:A) IN U`)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `d4 * mfd_scalar atlas (g:A->real^3^3) y` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d4 * R0` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Rs = sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)` THEN
  SUBGOAL_THEN `(!y. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <= Rs) /\
                R0 <= Rs /\ Rs <= C * R0 /\ &0 < Rs`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!y. y IN U ==> mfd_scalar atlas (g:A->real^3^3) y <= Rs` ASSUME_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN EXPAND_TAC "Rs" THEN
      MATCH_MP_TAC ELEMENT_LE_SUP THEN CONJ_TAC THENL
       [EXISTS_TAC `C * R0` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R0 <= Rs` ASSUME_TAC THENL
     [EXPAND_TAC "R0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "Rs" THEN MATCH_MP_TAC REAL_SUP_LE THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      SPDR7_ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d3 /\ &0 <= v /\ &0 <= d9 /\ &0 <= d10` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U x x` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_DIST_IN_POS_LE THEN ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d3:real`)) (concl th))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`x:A`; `x:A`] THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `U:A->bool`; `v:real`] MFD_HAS_VOLUME_POS_LE) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(rfs_scalar_grad2 atlas (g:A->real^3^3) x) /
                  (mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC P2B9S_GRAD2_POS THEN
          EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
          MESON_TAC[OPEN_IN_SUBSET; SUBSET; ASSUME `open_in top (U:A->bool)`;
                    ASSUME `(x:A) IN U`];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE]];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d9:real`)) (concl th))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(rfs_scalar_lap atlas (g:A->real^3^3) x + &2 * rfs_ric_norm2 atlas g x) /
                  mfd_scalar atlas g x pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS; REAL_LE_POW_2];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `d10:real`)) (concl th))) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> rfa_rmd2 0 atlas (\z. R0 %% (g:A->real^3^3) z) y <= Kr /\
            rfa_rmd2 1 atlas (\z. R0 %% g z) y <= Kr /\
            rfa_rmd2 2 atlas (\z. R0 %% g z) y <= Kr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kr:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `delta:real` o
    check (fun th -> is_forall(concl th) && can (find_term ((=) `dc:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CH") STRIP_ASSUME_TAC)] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "rfs_mclose" with Failure _ -> false))
        (concl th))) THEN
  REWRITE_TAC[rfs_mclose] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN U
        ==> abs(mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y) -
                mfd_scalar atlas (g:A->real^3^3) y) <= alpha * R0 /\
            (!u v. ~collinear {vec 0,u,v}
                   ==> abs(mfd_sectional atlas (mfd_pullback_metric atlas atlas' psi g') y u v -
                           mfd_sectional atlas g y u v) <= alpha * R0) /\
            abs(rfs_scalar_grad2 atlas' g' (psi y) - rfs_scalar_grad2 atlas g y) <=
            alpha * R0 pow 3 /\
            abs(rfs_scalar_lap atlas' g' (psi y) - rfs_scalar_lap atlas g y) <= alpha * R0 pow 2 /\
            abs(rfs_ric_norm2 atlas' g' (psi y) - rfs_ric_norm2 atlas g y) <= alpha * R0 pow 2 /\
            (!v. v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                 (&1 + delta) * (v dot (g y ** v))) /\
            (!v. (&1 - delta) * (v dot (g y ** v)) <=
                 v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2B9S_CCOMP_TARGET_POINT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`;
                          `IMAGE (psi:A->B) U`; `psi':B->A`; `Kr:real`; `etaL:real`;
                          `d2:real`] THEN
    ASM_SIMP_TAC[] THEN TRY(CONJ_TAC THENL [USE_THEN "Dform" ACCEPT_TAC; ALL_TAC]) THEN
    SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN U ==> abs(mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y) -
                        mfd_scalar atlas (g:A->real^3^3) y) <= alpha * R0) /\
    (!y v. y IN U ==> v dot (mfd_pullback_metric atlas atlas' psi g' y ** v) <=
                      (&1 + delta) * (v dot (g y ** v))) /\
    (!y v. y IN U ==> (&1 - delta) * (v dot (g y ** v)) <=
                      v dot (mfd_pullback_metric atlas atlas' psi g' y ** v))`
  (CONJUNCTS_THEN2 (LABEL_TAC "ABS") (CONJUNCTS_THEN2 (LABEL_TAC "PBU") (LABEL_TAC "PBL")))
  THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo top (atlas:((A->bool)#(A->real^3))->bool) U0 top' (atlas':((B->bool)#(B->real^3))->bool) (IMAGE (psi:A->B) U0) psi psi'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `IMAGE (psi:A->B) U`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_complete (top',atlas') (g':B->real^3^3) \/
                compact_in top' (top' closure_of IMAGE (psi:A->B) U0)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_complete" with Failure _ -> false))
          (concl th))) THENL
     [DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `top' closure_of IMAGE (psi:A->B) U` THEN
      ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top' (IMAGE (psi:A->B) U0)` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_diffeo top (atlas:((A->bool)#(A->real^3))->bool) U0 top' (atlas':((B->bool)#(B->real^3))->bool) (IMAGE (psi:A->B) U0) psi psi'` THEN
    SIMP_TAC[mfd_diffeo];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y1 y2. y1 IN U /\ y2 IN U
             ==> mfd_dist_in (top,atlas) (g:A->real^3^3) U y1 y2 <= d3) /\
    (!y. y IN U ==> sqrt(rfs_scalar_grad2 atlas g y) /
                    (mfd_scalar atlas g y * sqrt(mfd_scalar atlas g y)) <= d9) /\
    (!y. y IN U ==> abs(rfs_scalar_lap atlas g y + &2 * rfs_ric_norm2 atlas g y) /
                    mfd_scalar atlas g y pow 2 <= d10)`
  (CONJUNCTS_THEN2 (LABEL_TAC "D3") (CONJUNCTS_THEN2 (LABEL_TAC "G9") (LABEL_TAC "L10")))
  THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d3:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`y1:A`; `y2:A`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d9:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `d10:real`)) (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha * C <= &1 / &320 /\ &0 <= alpha * R0 /\ alpha * R0 <= R0 / &320 /\
                &0 < R0 / C /\ alpha * R0 <= (R0 / C) / &320`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `alpha * C = eta7 / &8` ASSUME_TAC THENL
     [UNDISCH_TAC `alpha * (&8 * C) = eta7` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `alpha * C <= &1 / &320` ASSUME_TAC THENL
     [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `alpha * R0 = (alpha * C) * (R0 / C)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < R0 / C /\ R0 / C <= R0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &320) * (R0 / C)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC; SPDR7_ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &320) * (R0 / C)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U0 ==> R0 / C <= mfd_scalar atlas (g:A->real^3^3) y /\
                                mfd_scalar atlas g y <= Rs`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN U0` THEN UNDISCH_TAC `(U0:A->bool) SUBSET U` THEN SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `mfd_scalar atlas' (g':B->real^3^3)`;
                 `psi:A->B`; `U0:A->bool`; `R0 / C`; `Rs:real`; `alpha * R0`; `x:A`]
                P2BC_T_RANGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "ABS" MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:A) IN U0` THEN UNDISCH_TAC `(U0:A->bool) SUBSET U` THEN SET_TAC[];
      SPDR7_ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  ABBREV_TAC `Sp = sup(IMAGE (mfd_scalar atlas' (g':B->real^3^3)) (IMAGE (psi:A->B) U0))` THEN
  SUBGOAL_THEN `!y. y IN U0 ==> (y:A) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `(U0:A->bool) SUBSET U` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_sup_lt {mfd_scalar atlas' (g':B->real^3^3) y2 / mfd_scalar atlas' g' y1 |
                            y1 IN IMAGE (psi:A->B) U0 /\ y2 IN IMAGE psi U0} C'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BC_T_RATIO THEN
    MAP_EVERY EXISTS_TAC [`mfd_scalar atlas (g:A->real^3^3)`; `d4:real`;
                          `alpha * R0`; `R0 / C`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "RAT" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "ABS" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      SPDR7_ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `((R0 / C) / &320) * (&4 * (C' + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ARITH `(x / &320) * y = x * (y / &320)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D = sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:A->real^3^3) zb)) *
                  (sqrt(&2) * pi)` THEN
  SUBGOAL_THEN `(zb:A) IN U /\ (zb:A) IN U0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(zb:A) IN IMAGE (eb:real^3->A) (rfs_neck_dom eps')` MP_TAC THENL
     [MP_TAC(SPEC `eps':real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps' zb eb` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      UNDISCH_TAC `(zb:A) IN IMAGE (eb:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (eb:real^3->A) (rfs_neck_dom eps') SUBSET U0` THEN
    UNDISCH_TAC `(U0:A->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D /\ D <= &5 * sqrt C * inv(sqrt Rs)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LE THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[PI_POS_LE; SQRT_POS_LE; REAL_ARITH `&0 <= &2`]];
      MATCH_MP_TAC P2BF_D_BOUND THEN ASM_SIMP_TAC[] THEN
      EXPAND_TAC "Rs" THEN MATCH_MP_TAC REAL_SUP_LE THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `d4 * mfd_scalar atlas (g:A->real^3^3) zb` THEN CONJ_TAC THENL
         [USE_THEN "RAT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [SPDR7_ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2. y1 IN U0 /\ y2 IN U0
            ==> mfd_joinable_in (top,atlas) U0 y1 y2 /\
                mfd_dist_in (top,atlas) (g:A->real^3^3) U0 y1 y2 <= d3 + D`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `U0:A->bool`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable_in"
                                 with Failure _ -> false)) (concl th) &&
        not (can (find_term (fun t -> try fst(dest_const t) = "mfd_dist_in"
                                      with Failure _ -> false)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_dist_in (top,atlas) (g:A->real^3^3) U y1 y2 + D` THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC P2BF_SUBCAP_DIAM THEN
      MAP_EVERY EXISTS_TAC [`eb:real^3->A`; `Y:A->bool`; `r0:real`; `r2:real`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY SPDR7_ASM_REAL_ARITH_TAC THEN
      TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `U:A->bool`)) (concl th) &&
        not (can (find_term ((=) `U0:A->bool`)) (concl th)) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_joinable_in"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= d ==> x + e <= d + e`) THEN
      USE_THEN "D3" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U0:A->bool`; `psi:A->B`; `psi':B->A`; `d3 + D`; `delta:real`]
                P2BC_T_DIAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SPDR7_ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "PBU" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "TD")] THEN
  MP_TAC(SPECL [`C:real`; `C':real`; `Rs:real`; `alpha * R0`; `delta:real`; `d3:real`;
                `D:real`] P2BF_DIAM_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`C':real`; `Sp:real`; `Rs + alpha * R0`] P2BC_INV_SQRT_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U0:A->bool`; `U:A->bool`; `v:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `v0 = mfd_volume (top,atlas) (g:A->real^3^3) U0` THEN
  SUBGOAL_THEN `&0 <= v0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `U0:A->bool`; `v0:real`] MFD_HAS_VOLUME_POS_LE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                 `U0:A->bool`; `psi:A->B`; `psi':B->A`; `x:A`; `sqrt(&1 + delta) * (d3 + D)`;
                 `v0:real`; `delta:real`] P2BF_T_VOL_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SPDR7_ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "PBU" MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `v1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`C:real`; `C':real`; `Rs:real`; `alpha * R0`; `delta:real`; `v0:real`]
               P2BF_VOL_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `!y. y IN U0 ==> R0 / C <= mfd_scalar atlas (g:A->real^3^3) y /\
                                mfd_scalar atlas g y <= C * R0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Rs:real`)) (concl th) && can (find_term ((=) `U0:A->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y w. y IN U0
                      ==> --(&2 * ((&3 * sqrt(max Kr (&0))) / &2 * R0)) *
                          (w dot ((g:A->real^3^3) y ** w)) <= mfd_ricci atlas g y w w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BF_RICCI_LOWER_KR THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "rfa_rmd2" with Failure _ -> false))
          (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "C7C" (MP_TAC o SPECL [`R0:real`; `mfd_scalar atlas (g:A->real^3^3) zb`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `zb:A` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `C * R0`)) (concl th) && can (find_term ((=) `U:A->bool`)) (concl th) &&
      not (can (find_term ((=) `U0:A->bool`)) (concl th)))) THEN
    ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`(&3 * sqrt(max Kr (&0))) / &2 * R0`; `inv(sqrt R0) / (&2 * sqrt(&2 * C))`;
                 `&2 * sqrt(&2 * C) * inv(sqrt R0)`; `&1 / &4`] P2BF_VMODEL_RATIO_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SPDR7_ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U0:A->bool`; `Y:A->bool`; `eps':real`; `zb:A`; `eb:real^3->A`;
                 `R0 / C`; `C * R0`; `(&3 * sqrt(max Kr (&0))) / &2 * R0`; `d:real`;
                 `&1 / &4`; `eta7:real`;
                 `&1 / &4 * (inv(sqrt R0) / (&2 * sqrt(&2 * C))) pow 3 /
                  (&8 * (&2 * sqrt(&2 * C) * inv(sqrt R0)) pow 2 *
                   exp(&2 * sqrt((&3 * sqrt(max Kr (&0))) / &2 * R0) *
                       (&2 * sqrt(&2 * C) * inv(sqrt R0))))`;
                 `inv(sqrt R0) / (&2 * sqrt(&2 * C))`; `&2 * sqrt(&2 * C) * inv(sqrt R0)`]
                (INST_TYPE [`:B`,`:B`] P2BF_CLAUSE7_GEN2)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY SPDR7_ASM_REAL_ARITH_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R0:real` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SPDR7_ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN SPDR7_ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `inv C` THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]];
    DISCH_THEN(LABEL_TAC "C7")] THEN
  SUBGOAL_THEN `!w. w IN IMAGE (eb:real^3->A) (sphere(vec 0,&1))
                    ==> mfd_scalar atlas (g:A->real^3^3) zb / &4 <=
                        mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:A) IN IMAGE (eb:real^3->A) (rfs_neck_dom eps')` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps':real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:A) IN IMAGE (eb:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:A) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:A) IN IMAGE (eb:real^3->A) (rfs_neck_dom eps')` THEN
      UNDISCH_TAC `IMAGE (eb:real^3->A) (rfs_neck_dom eps') SUBSET U0` THEN
      UNDISCH_TAC `(U0:A->bool) SUBSET U` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) zb / &2 <= mfd_scalar atlas g w`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `zb:A`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "rfs_neck_dom" with Failure _ -> false))
            (concl th) &&
        not (can (find_term ((=) `g':B->real^3^3`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ABS" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(w:A) IN U`))) THEN
    SUBGOAL_THEN `alpha * R0 <= mfd_scalar atlas (g:A->real^3^3) zb / &4` MP_TAC THENL
     [SUBGOAL_THEN `R0 / C <= mfd_scalar atlas (g:A->real^3^3) zb` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SPDR7_ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) zb / &2 <= mfd_scalar atlas g w` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "NSB" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                  `g':B->real^3^3`; `eps':real`; `(psi:A->B) zb`;
                                  `(psi:A->B) o (eb:real^3->A)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!w. w IN IMAGE ((psi:A->B) o (eb:real^3->A)) (sphere(vec 0,&1))
                    ==> mfd_scalar atlas' (g':B->real^3^3) (psi zb) / &2 <=
                        mfd_scalar atlas' g' w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `eps':real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:B) IN IMAGE ((psi:A->B) o (eb:real^3->A)) (sphere(vec 0,&1))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y v. y IN U0
           ==> v dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** v) <=
               (&1 + &2 * delta) * (v dot ((g:A->real^3^3) y ** v))) /\
    (!y v. y IN U0
           ==> v dot (g y ** v) <=
               (&1 + &2 * delta) * (v dot (mfd_pullback_metric atlas atlas' psi g' y ** v)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:A` THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC]) THEN
    MP_TAC(SPECL [`delta:real`; `w dot ((g:A->real^3^3) y ** w)`;
                  `w dot (mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y ** w)`]
                 P2BC_QF_LAM) THEN
    (ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL
        [ASM_REWRITE_TAC[];
         SPDR7_ASM_REAL_ARITH_TAC;
         USE_THEN "PBL" (fun th -> ACCEPT_TAC(MATCH_MP (SPECL [`y:A`; `w:real^3`] th)
                                                       (ASSUME `(y:A) IN U`)));
         USE_THEN "PBU" (fun th -> ACCEPT_TAC(MATCH_MP (SPECL [`y:A`; `w:real^3`] th)
                                                       (ASSUME `(y:A) IN U`)))];
       SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha * R0 <= eta7 * (R0 / C) / &8` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `alpha * (&8 * C) = eta7` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  USE_THEN "C7" (MP_TAC o SPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                                 `g':B->real^3^3`; `psi:A->B`; `psi':B->A`;
                                 `&1 + &2 * delta`; `alpha * R0`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY SPDR7_ASM_REAL_ARITH_TAC THEN
    REPEAT STRIP_TAC THEN USE_THEN "ABS" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN(LABEL_TAC "C7T")] THEN
  MP_TAC(SPECL [`C:real`; `alpha:real`] P2BF_ALPHA_POLY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < inv C /\ inv C * R0 = R0 / C` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U0 ==> (y:A) IN topspace top /\ (psi:A->B) y IN topspace top'`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U0:A->bool)`));
      MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (IMAGE (psi:A->B) U0)`))] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  REWRITE_TAC[rfs_cap] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "CH" ACCEPT_TAC;
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_sup_lt] THEN
    EXISTS_TAC `sqrt(&1 + delta) * (d3 + D)` THEN CONJ_TAC THENL
     [SPDR7_ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`w:real`; `z1:B`; `z2:B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC) THEN
      USE_THEN "TD" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `(z1:B) IN IMAGE (psi:A->B) U0`)
              (ASSUME `(z2:B) IN IMAGE (psi:A->B) U0`)))) THEN
      SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    EXISTS_TAC `v1:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `C' * inv(sqrt(Rs + alpha * R0) pow 3) <= C' * inv(sqrt Sp pow 3)` THEN
    UNDISCH_TAC `(&1 + delta) * sqrt(&1 + delta) * v0 <
                 C' * inv(sqrt(Rs + alpha * R0)) pow 3` THEN
    UNDISCH_TAC `v1 <= (&1 + delta) * sqrt(&1 + delta) * v0` THEN
    REWRITE_TAC[REAL_POW_INV] THEN REAL_ARITH_TAC;
    EXISTS_TAC `(d * (&1 - &1 / &4)) / (&1 + &16 * eta7)` THEN CONJ_TAC THENL
     [ALL_TAC; USE_THEN "C7T" ACCEPT_TAC] THEN
    SUBGOAL_THEN `inv C' <= inv C / &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv C / &2 = inv(&2 * C)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN SPDR7_ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 + &16 * eta7` ASSUME_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `inv C' * (&1 + &16 * eta7) <= (inv C / &2) * (&7 / &5)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN SPDR7_ASM_REAL_ARITH_TAC;
        SPDR7_ASM_REAL_ARITH_TAC;
        SPDR7_ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SPDR7_ASM_REAL_ARITH_TAC;
    REWRITE_TAC[rfs_sup_lt] THEN
    EXISTS_TAC `&3 / &2 * C` THEN CONJ_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `(y:A) IN topspace top /\ (psi:A->B) y IN topspace top'`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\
                  inv C * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`; `C:real`]
                 P2B9S_GRAD_RATIO_IMP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
        SPDR7_ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d9:real` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`inv C`; `R0:real`; `C:real`; `&3 / &2 * C`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_grad2 atlas (g:A->real^3^3) y`;
                  `rfs_scalar_grad2 atlas' (g':B->real^3^3) ((psi:A->B) y)`; `alpha:real`]
                 P2B9S_MARGIN_GRAD_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN SPDR7_ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_GRAD_RATIO_BACK THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2B9S_GRAD2_POS THEN EXISTS_TAC `top':B topology` THEN ASM_REWRITE_TAC[];
      SPDR7_ASM_REAL_ARITH_TAC];
    REWRITE_TAC[rfs_sup_lt] THEN
    EXISTS_TAC `&3 / &2 * C` THEN CONJ_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:real` THEN X_GEN_TAC `z:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(y:A) IN U` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "PT" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN U`))) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y /\
                  inv C * R0 <= mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) y`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `C:real`] P2B9S_LAP_RATIO_IMP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d10:real` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`inv C`; `R0:real`; `C:real`; `&3 / &2 * C`;
                  `mfd_scalar atlas (g:A->real^3^3) y`;
                  `mfd_scalar atlas' (g':B->real^3^3) ((psi:A->B) y)`;
                  `rfs_scalar_lap atlas (g:A->real^3^3) y + &2 * rfs_ric_norm2 atlas g y`;
                  `rfs_scalar_lap atlas' (g':B->real^3^3) ((psi:A->B) y) +
                   &2 * rfs_ric_norm2 atlas' g' (psi y)`; `alpha:real`]
                 P2B9S_MARGIN_LAP_POLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN SPDR7_ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MATCH_MP_TAC P2B9S_LAP_RATIO_BACK THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The radii of the re-centred sub-cap (c = exp(1/(sqrt 2 eps'))) and the    *)
(* target chart data for ball and twisted cores: uniform thresholds from     *)
(* P2BF_NECK_UNIF_RENORM for the boundary neck and the re-centred end neck,  *)
(* P2BC_CHART_BALL / P2BC_CHART_TWISTED on U0, the target splits.            *)
(* ------------------------------------------------------------------------- *)

let P2BF_EXP_RADII = prove
 (`!eps eps' c. &0 < eps /\ &2 * eps < eps' /\ eps' <= &1 / &40 /\
                c = exp(inv(sqrt(&2) * eps'))
     ==> &2 <= c /\ &2 <= c * c /\ &0 < inv(c * c) /\ inv(c * c) < &1 /\ &1 < c * c /\
         inv(c * c) < inv c /\ c < c * c /\
         {y:real^3 | inv(c * c) <= norm y /\ norm y <= c * c} SUBSET rfs_neck_dom eps /\
         rfs_neck_dom eps' = annulus (inv c) c /\
         annulus (inv c) c SUBSET (annulus (inv(c * c)) (c * c):real^3->bool)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `c:real`)) THEN
  SUBGOAL_THEN `&0 < eps' /\ &0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= c` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= inv(sqrt(&2) * eps')` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * eps'` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(SPEC `inv(sqrt(&2) * eps')` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= c * c /\ &1 < c * c /\ c < c * c` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * c <= c * c` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(c * c) /\ inv(c * c) < &1 /\ inv(c * c) < inv c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_neck_dom eps' = annulus (inv c) c` ASSUME_TAC THENL
   [REWRITE_TAC[P2BF_NECK_DOM_EXP] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `c * c < exp(inv(sqrt(&2) * eps))` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `exp(inv(sqrt(&2) * eps')) = c`)) THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `inv(sqrt(&2)) * inv eps' + inv(sqrt(&2)) * inv eps' =
                  inv(sqrt(&2)) * (&2 * inv eps')` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * inv eps' = inv(eps' / &2)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[P2BF_NECK_DOM_EXP; SUBSET; annulus; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(c * c)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let P2BF_DC_BALL = prove
 (`!K0 eps eps' C.
     (!y:real^3. ~(y = vec 0) ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2) /\
     &0 < eps /\ &2 * (&4 + &576 * (&1 + abs K0)) * eps <= eps' /\ eps' <= &1 / &40 /\
     &1 <= C
     ==> ?dc. &0 < dc /\
           !dl top atlas (g:A->real^3^3) U Y b e' z' f f' x c U0
            top' atlas' (g':B->real^3^3) psi psi'.
              &0 < dl /\ dl <= dc /\
              hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\
              mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
              Y = IMAGE b (ball(vec 0,&1)) /\
              rfs_neck (top,atlas) g eps z' e' /\ IMAGE e' (rfs_neck_dom eps) SUBSET U /\
              IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
              sphere_diffeo f f' /\ (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y)) /\
              (!y. y IN U ==> mfd_scalar atlas g x <= C * mfd_scalar atlas g y) /\
              &0 < mfd_scalar atlas g x /\
              c = exp(inv(sqrt(&2) * eps')) /\
              U0 = Y UNION IMAGE e' (annulus (inv(c * c)) (c * c)) /\
              hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
              riemannian_metric atlas' g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_mclose (rfs_kreg dl) dl atlas U (\y. mfd_scalar atlas g x %% g y)
                (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> (?b e e' z z' f f'.
                     mfd_ball_chart top' atlas' b /\
                     IMAGE b (ball(vec 0,&2)) SUBSET IMAGE psi U0 /\
                     IMAGE psi Y = IMAGE b (ball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps' z e /\
                     IMAGE e (rfs_neck_dom eps') = IMAGE psi U0 DIFF IMAGE b (cball(vec 0,&1)) /\
                     rfs_neck (top',atlas') g' eps' z' e' /\
                     IMAGE e' (rfs_neck_dom eps') SUBSET IMAGE psi U0 /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) /\
                  rfs_neck (top',atlas') g' eps' (psi z') (psi o e') /\
                  top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                    IMAGE (psi o e') (sphere(vec 0,&1)) /\
                  top' closure_of IMAGE psi Y SUBSET IMAGE psi U0 /\
                  IMAGE (psi o e') (rfs_neck_dom eps') SUBSET IMAGE psi U0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K1 = &4 + &576 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&4 <= K1 /\ eps < eps' /\ &0 < K1 * eps /\ K1 * eps < eps' /\
                eps' < &1 / &4 /\ &2 * eps < eps' /\ K1 * eps <= &1 / &2 /\
                &4 / &3 * eps <= eps'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 <= K1` ASSUME_TAC THENL
     [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * eps <= K1 * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `C:real`]
               (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_NECK_UNIF_RENORM)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dn1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NU1"))) THEN
  MP_TAC(SPECL [`K1 * eps`; `eps':real`; `C:real`]
               (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_NECK_UNIF_RENORM)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dn2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NU2"))) THEN
  EXISTS_TAC `min dn1 dn2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `U0:A->bool`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `c:real`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `Y:A->bool`)) THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:A->bool) UNION IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c)) = U0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl <= dn1 /\ dl <= dn2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `c:real`] P2BF_EXP_RADII) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `rfs_neck_dom eps'`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `U:A->bool`; `Y:A->bool`; `b:real^3->A`; `e':real^3->A`;
                 `z':A`; `f:real^3->real^3`; `f':real^3->real^3`; `inv(c * c)`; `c * c`;
                 `U0:A->bool`] P2BF_SUBCAP_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `K0:real` P2BF_END_NECK_SRC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g:A->real^3^3`; `eps:real`; `eps':real`; `z':A`;
                             `e':real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `en = (e':real^3->A) o (\w. c % w)` THEN
  ABBREV_TAC `zn = (e':real^3->A) (c % basis 1)` THEN
  SUBGOAL_THEN `(z':A) IN U /\ (zn:A) IN U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' e'` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `(z':A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (K1 * eps) zn en` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(SPEC `K1 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom (K1 * eps)) SUBSET
                   IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `(zn:A) IN IMAGE (en:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top',atlas') (g':B->real^3^3) eps' ((psi:A->B) z') (psi o e') /\
                rfs_neck (top',atlas') g' eps' (psi zn) (psi o (en:real^3->A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "NU1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`dl:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `U:A->bool`; `mfd_scalar atlas (g:A->real^3^3) x`;
                            `psi':B->A`] THEN
      ASM_SIMP_TAC[];
      USE_THEN "NU2" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`dl:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `U:A->bool`; `mfd_scalar atlas (g:A->real^3^3) x`;
                            `psi':B->A`] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom (K1 * eps)) SUBSET
                   IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo top (atlas:((A->bool)#(A->real^3))->bool) U0 top' (atlas':((B->bool)#(B->real^3))->bool) (IMAGE (psi:A->B) U0) psi psi'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `IMAGE (psi:A->B) U`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom eps') SUBSET U0` ASSUME_TAC THENL
   [REWRITE_TAC[P2BF_NECK_DOM_EXP] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`; `U0:A->bool`;
                 `psi:A->B`; `psi':B->A`; `Y:A->bool`; `eps':real`; `b:real^3->A`;
                 `en:real^3->A`; `e':real^3->A`; `zn:A`; `z':A`; `f:real^3->real^3`;
                 `f':real^3->real^3`] P2BC_CHART_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(psi:A->B) o (b:real^3->A)`; `(psi:A->B) o (e':real^3->A)`;
                 `IMAGE (psi:A->B) Y`; `f:real^3->real^3`; `f':real^3->real^3`]
                P2BF_BALL_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(psi:A->B) o (b:real^3->A)`; `(psi:A->B) o (en:real^3->A)`;
                          `(psi:A->B) o (e':real^3->A)`; `(psi:A->B) zn`; `(psi:A->B) z'`;
                          `f:real^3->real^3`; `f':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `top' closure_of IMAGE (psi:A->B) Y =
                 IMAGE psi Y UNION IMAGE ((psi:A->B) o (e':real^3->A)) (sphere(vec 0,&1))` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:B->bool. a SUBSET c /\ b SUBSET c ==> a UNION b SUBSET c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:A->B) o (e':real^3->A)) (rfs_neck_dom eps')` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN
        ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ASM_REWRITE_TAC[]]);;

let P2BF_DC_TWISTED = prove
 (`!K0 eps eps' C.
     (!y:real^3. ~(y = vec 0) ==> lrm_deriv_norm2 0 (cylinder_flow (&0)) y <= K0 pow 2) /\
     &0 < eps /\ &2 * (&4 + &576 * (&1 + abs K0)) * eps <= eps' /\ eps' <= &1 / &40 /\
     &1 <= C
     ==> ?dc. &0 < dc /\
           !dl top atlas (g:A->real^3^3) U Y p e' z' f f' x c U0
            top' atlas' (g':B->real^3^3) psi psi'.
              &0 < dl /\ dl <= dc /\
              hausdorff_space top /\ smooth_manifold_atlas top atlas /\
              riemannian_metric atlas g /\
              rfs_twisted_chart top atlas p /\ IMAGE p (annulus (&1 / &4) (&4)) SUBSET U /\
              Y = IMAGE p (annulus (&1 / &2) (&2)) /\
              rfs_neck (top,atlas) g eps z' e' /\ IMAGE e' (rfs_neck_dom eps) SUBSET U /\
              IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
              sphere_diffeo f f' /\
              (!y. y IN annulus (&2) (&4) ==> p y = e'(radial_ext f (inv(&2) % y))) /\
              (!y. y IN U ==> mfd_scalar atlas g x <= C * mfd_scalar atlas g y) /\
              &0 < mfd_scalar atlas g x /\
              c = exp(inv(sqrt(&2) * eps')) /\
              U0 = Y UNION IMAGE e' (annulus (inv(c * c)) (c * c)) /\
              hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
              riemannian_metric atlas' g' /\
              mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
              rfs_mclose (rfs_kreg dl) dl atlas U (\y. mfd_scalar atlas g x %% g y)
                (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
              ==> (?p e e' z z' f f'.
                     rfs_twisted_chart top' atlas' p /\
                     IMAGE p (annulus (&1 / &4) (&4)) SUBSET IMAGE psi U0 /\
                     IMAGE psi Y = IMAGE p (annulus (&1 / &2) (&2)) /\
                     rfs_neck (top',atlas') g' eps' z e /\
                     IMAGE e (rfs_neck_dom eps') =
                       IMAGE psi U0 DIFF IMAGE p {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} /\
                     rfs_neck (top',atlas') g' eps' z' e' /\
                     IMAGE e' (rfs_neck_dom eps') SUBSET IMAGE psi U0 /\
                     IMAGE e' (sphere(vec 0,&1)) = IMAGE p (sphere(vec 0,&2)) /\
                     sphere_diffeo f f' /\
                     (!y. y IN annulus (&2) (&4)
                          ==> p y = e'(radial_ext f (inv(&2) % y)))) /\
                  rfs_neck (top',atlas') g' eps' (psi z') (psi o e') /\
                  top' frontier_of (top' closure_of IMAGE psi Y) SUBSET
                    IMAGE (psi o e') (sphere(vec 0,&1)) /\
                  top' closure_of IMAGE psi Y SUBSET IMAGE psi U0 /\
                  IMAGE (psi o e') (rfs_neck_dom eps') SUBSET IMAGE psi U0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K1 = &4 + &576 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&4 <= K1 /\ eps < eps' /\ &0 < K1 * eps /\ K1 * eps < eps' /\
                eps' < &1 / &4 /\ &2 * eps < eps' /\ K1 * eps <= &1 / &2 /\
                &4 / &3 * eps <= eps'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 <= K1` ASSUME_TAC THENL
     [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 * eps <= K1 * eps` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `C:real`]
               (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_NECK_UNIF_RENORM)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dn1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NU1"))) THEN
  MP_TAC(SPECL [`K1 * eps`; `eps':real`; `C:real`]
               (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_NECK_UNIF_RENORM)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dn2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NU2"))) THEN
  EXISTS_TAC `min dn1 dn2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `U0:A->bool`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `c:real`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `Y:A->bool`)) THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:A->bool) UNION IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c)) = U0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dl <= dn1 /\ dl <= dn2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `c:real`] P2BF_EXP_RADII) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `rfs_neck_dom eps'`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `U:A->bool`; `Y:A->bool`; `p:real^3->A`; `e':real^3->A`;
                 `z':A`; `f:real^3->real^3`; `f':real^3->real^3`; `inv(c * c)`; `c * c`;
                 `U0:A->bool`] P2BF_SUBCAP_TWISTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `K0:real` P2BF_END_NECK_SRC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                             `g:A->real^3^3`; `eps:real`; `eps':real`; `z':A`;
                             `e':real^3->A`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `en = (e':real^3->A) o (\w. c % w)` THEN
  ABBREV_TAC `zn = (e':real^3->A) (c % basis 1)` THEN
  SUBGOAL_THEN `(z':A) IN U /\ (zn:A) IN U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps z' e'` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `(z':A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) (K1 * eps) zn en` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(SPEC `K1 * eps` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom (K1 * eps)) SUBSET
                   IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `(zn:A) IN IMAGE (en:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top',atlas') (g':B->real^3^3) eps' ((psi:A->B) z') (psi o e') /\
                rfs_neck (top',atlas') g' eps' (psi zn) (psi o (en:real^3->A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "NU1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`dl:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `U:A->bool`; `mfd_scalar atlas (g:A->real^3^3) x`;
                            `psi':B->A`] THEN
      ASM_SIMP_TAC[];
      USE_THEN "NU2" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`dl:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `U:A->bool`; `mfd_scalar atlas (g:A->real^3^3) x`;
                            `psi':B->A`] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET U` THEN
      UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom (K1 * eps)) SUBSET
                   IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_diffeo top (atlas:((A->bool)#(A->real^3))->bool) U0 top' (atlas':((B->bool)#(B->real^3))->bool) (IMAGE (psi:A->B) U0) psi psi'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `IMAGE (psi:A->B) U`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom eps') SUBSET U0` ASSUME_TAC THENL
   [REWRITE_TAC[P2BF_NECK_DOM_EXP] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`; `U0:A->bool`;
                 `psi:A->B`; `psi':B->A`; `Y:A->bool`; `eps':real`; `p:real^3->A`;
                 `en:real^3->A`; `e':real^3->A`; `zn:A`; `z':A`; `f:real^3->real^3`;
                 `f':real^3->real^3`] P2BC_CHART_TWISTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(psi:A->B) o (p:real^3->A)`; `(psi:A->B) o (e':real^3->A)`;
                 `IMAGE (psi:A->B) Y`; `f:real^3->real^3`; `f':real^3->real^3`]
                P2BF_TWISTED_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(psi:A->B) o (p:real^3->A)`; `(psi:A->B) o (en:real^3->A)`;
                          `(psi:A->B) o (e':real^3->A)`; `(psi:A->B) zn`; `(psi:A->B) z'`;
                          `f:real^3->real^3`; `f':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `top' closure_of IMAGE (psi:A->B) Y =
                 IMAGE psi Y UNION IMAGE ((psi:A->B) o (e':real^3->A)) (sphere(vec 0,&1))` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b c:B->bool. a SUBSET c /\ b SUBSET c ==> a UNION b SUBSET c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:A->B) o (e':real^3->A)) (rfs_neck_dom eps')` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC APX_UNIT_SPHERE_NECK_DOM THEN
        ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The general forms.  P2BF_CAP_FIX_GEN (K = 2 K1, eps0 = min 1/40 of the    *)
(* neck-scalar thresholds; caps with C < 100 do not exist for eps <= 1/320;  *)
(* otherwise the uniform delta of P2BF_CAP_COMMON_UNIF_GEN with the chart    *)
(* thresholds of the previous section), then P2BF_SLICE_FIX_GEN (as in       *)
(* P2BS_SLICE_FROM_CAP).  The target hypothesis of both is: the target       *)
(* metric is complete, or psi U has compact closure in the target.           *)
(* ------------------------------------------------------------------------- *)

let P2BF_C_SMALL_ABSURD = prove
 (`!eps. &0 < eps /\ eps <= &1 / &320 ==> &100 <= sqrt(&1 - eps) * inv eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= sqrt(&1 - eps) /\ &320 <= inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&320 = inv(&1 / &320)` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) * &320` THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let P2BF_CAPFIX_TAIL_GEN_TAC dclab (chv:term) disj =
  SUBGOAL_THEN `(Y:A->bool) SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:A->bool) UNION IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c)) = U0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `eps':real`; `z':A`; `e':real^3->A`] P2BS_NECK_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom eps') SUBSET U0` ASSUME_TAC THENL
   [REWRITE_TAC[P2BF_NECK_DOM_EXP] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "NSA" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps':real`; `z':A`; `e':real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `?d. inv C < d /\
        !y r. y IN Y /\ &0 < r /\
              (?B. !q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= B) /\
              sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) (mfd_ball (top,atlas) g y r)) =
              inv(r pow 2)
              ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                  top closure_of mfd_ball (top,atlas) g y r SUBSET U0 /\
                  ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                      d <= v / r pow 3`
  ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o check (fun th ->
      is_exists(concl th) && can (find_term ((=) `inv C`)) (concl th))) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BF_SRC_CLAUSE7_SUB THEN
    MAP_EVERY EXISTS_TAC [`eps':real`; `z':A`; `e':real^3->A`; `U:A->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `eps':real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "COM" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
     `U:A->bool`; `Y:A->bool`; `U0:A->bool`; `z':A`; `e':real^3->A`; `inv(c * c)`; `c * c`;
     `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
     `psi:A->B`; `psi':B->A`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[GSYM REAL_POW_INV])) THEN
    TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `dl:real` THEN STRIP_TAC THEN
    USE_THEN dclab (MP_TAC o SPECL
      [`dl:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `U:A->bool`; `Y:A->bool`; chv; `e':real^3->A`; `z':A`; `f:real^3->real^3`;
       `f':real^3->real^3`; `x:A`; `c:real`; `U0:A->bool`; `top':B topology`;
       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`; `psi:A->B`; `psi':B->A`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN disj THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (psi:A->B) U0`; `IMAGE (psi:A->B) Y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];;


let SPDR7_CAPFIX_TAIL_TAC dclab (chv:term) disj =
  SUBGOAL_THEN `(Y:A->bool) SUBSET U0` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:A->bool) UNION IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c)) = U0` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `eps':real`; `z':A`; `e':real^3->A`] P2BS_NECK_SHRINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (rfs_neck_dom eps') SUBSET U0` ASSUME_TAC THENL
   [REWRITE_TAC[P2BF_NECK_DOM_EXP] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "NSA" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                  `g:A->real^3^3`; `eps':real`; `z':A`; `e':real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `?d. inv C < d /\
        !y r. y IN Y /\ &0 < r /\
              (?B. !q. q IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g q <= B) /\
              sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) (mfd_ball (top,atlas) g y r)) =
              inv(r pow 2)
              ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                  top closure_of mfd_ball (top,atlas) g y r SUBSET U0 /\
                  ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                      d <= v / r pow 3`
  ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o check (fun th ->
      is_exists(concl th) && can (find_term ((=) `inv C`)) (concl th))) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BF_SRC_CLAUSE7_SUB THEN
    MAP_EVERY EXISTS_TAC [`eps':real`; `z':A`; `e':real^3->A`; `U:A->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY SPDR7_ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `eps':real` APX_UNIT_SPHERE_NECK_DOM) THEN
    ANTS_TAC THENL [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(w:A) IN IMAGE (e':real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "COM" (MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`;
     `U:A->bool`; `Y:A->bool`; `U0:A->bool`; `z':A`; `e':real^3->A`; `inv(c * c)`; `c * c`;
     `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
     `psi:A->B`; `psi':B->A`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[GSYM REAL_POW_INV])) THEN
    TRY SPDR7_ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `dl:real` THEN STRIP_TAC THEN
    USE_THEN dclab (MP_TAC o SPECL
      [`dl:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
       `U:A->bool`; `Y:A->bool`; chv; `e':real^3->A`; `z':A`; `f:real^3->real^3`;
       `f':real^3->real^3`; `x:A`; `c:real`; `U0:A->bool`; `top':B topology`;
       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`; `psi:A->B`; `psi':B->A`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN SPDR7_ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN disj THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (psi:A->B) U0`; `IMAGE (psi:A->B) Y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];;

let P2BF_CAP_FIX_GEN = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U Y psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\
               (mfd_complete (top',atlas') g' \/
                compact_in top' (top' closure_of IMAGE (psi:A->B) U)) /\
               rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local atlas (chart_at atlas y)
                               (\z. mfd_scalar atlas g x %% g z))
                            (SND(chart_at atlas y) y) <= Kr) /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U' Y'. U' SUBSET IMAGE psi U /\
                           rfs_cap (top',atlas') g' C' eps' U' Y' /\ psi x IN Y'`,
  X_CHOOSE_THEN `K0:real` (LABEL_TAC "K0") APX_CYL0_RM_BOUND THEN
  MP_TAC(ISPEC `UNIV:A->bool` P2BC_NECK_SCALAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1A:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NSA"))) THEN
  MP_TAC(ISPEC `UNIV:B->bool` P2BC_NECK_SCALAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps1B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NSB"))) THEN
  ABBREV_TAC `K1 = &4 + &576 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&4 <= K1` ASSUME_TAC THENL [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `&2 * K1` THEN EXISTS_TAC `min (&1 / &40) (min eps1A eps1B)` THEN
  REPEAT CONJ_TAC THENL
   [SPDR7_ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&8 * eps <= &2 * K1 * eps` ASSUME_TAC THENL
   [SUBGOAL_THEN `&8 * eps <= (&2 * K1) * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * K1 * eps <= eps' /\ eps <= &1 / &320 /\ &0 < eps' /\ &2 * eps < eps'`
  STRIP_ASSUME_TAC THENL
   [SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&100 <= C` THENL
   [ALL_TAC;
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`] P2BF_CAP_C_LOWER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPEC `eps:real` P2BF_C_SMALL_ABSURD) THEN ASM_REWRITE_TAC[] THEN
    SPDR7_ASM_REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`K0:real`; `eps:real`; `eps':real`; `C:real`]
               (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_DC_BALL)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dcb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DCB"))) THEN
  MP_TAC(SPECL [`K0:real`; `eps:real`; `eps':real`; `C:real`]
               (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_DC_TWISTED)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dct:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DCT"))) THEN
  MP_TAC(SPECL [`eps1B:real`; `C:real`; `C':real`; `eps:real`; `eps':real`; `Kr:real`;
                `min dcb dct`] (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_CAP_COMMON_UNIF_GEN)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "NSB" ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ACCEPT_TAC P2B_REQ_LRG_DERIV; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN SPDR7_ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "COM")))] THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `x:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`; `psi':B->A`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_CAP_JOINABLE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [rfs_cap] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_cap"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CHS") (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))) THEN
  SUBGOAL_THEN `(Y:A->bool) SUBSET U` ASSUME_TAC THENL
   [REMOVE_THEN "CHS" (fun th -> LABEL_TAC "CHS" th THEN
      DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) th) THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (b:real^3->A) (ball(vec 0,&2))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (p:real^3->A) (annulus (&1 / &4) (&4))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN Y` THEN UNDISCH_TAC `(Y:A->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> mfd_scalar atlas (g:A->real^3^3) x <= C * mfd_scalar atlas g y`
  ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC o REWRITE_RULE[rfs_sup_lt] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfs_sup_lt"
                                                with Failure _ -> false)) (concl th) &&
                       not (can (find_term (fun t -> try fst(dest_const t) = "mfd_dist_in"
                                                     with Failure _ -> false)) (concl th)) &&
                       not (can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_grad2"
                                                     with Failure _ -> false)) (concl th)) &&
                       not (can (find_term (fun t -> try fst(dest_const t) = "rfs_scalar_lap"
                                                     with Failure _ -> false)) (concl th)))) THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g y` o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `d4:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) y` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d4 * mfd_scalar atlas (g:A->real^3^3) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN SPDR7_ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = exp(inv(sqrt(&2) * eps'))` THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`; `c:real`] P2BF_EXP_RADII) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SPDR7_ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `rfs_neck_dom eps'`)) THEN
  REMOVE_THEN "CHS" (DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:real^3->A` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `z':A`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
       STRIP_ASSUME_TAC))))))) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `Y:A->bool`)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (e':real^3->A) (sphere(vec 0,&1))`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `b:real^3->A`;
                   `e':real^3->A`; `Y:A->bool`; `f:real^3->real^3`; `f':real^3->real^3`]
                  P2BF_BALL_SPLIT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
      STRIP_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(top:A topology) closure_of Y`)) THEN
    ABBREV_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `U:A->bool`; `Y:A->bool`; `b:real^3->A`; `e':real^3->A`;
                   `z':A`; `f:real^3->real^3`; `f':real^3->real^3`; `inv(c * c)`; `c * c`;
                   `U0:A->bool`] P2BF_SUBCAP_BALL) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN SPDR7_ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SPDR7_CAPFIX_TAIL_TAC "DCB" `b:real^3->A` DISJ1_TAC;
    DISCH_THEN(X_CHOOSE_THEN `p:real^3->A` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':real^3->A` (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `z':A`
      (X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
       STRIP_ASSUME_TAC))))))) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `Y:A->bool`)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `IMAGE (e':real^3->A) (sphere(vec 0,&1))`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `p:real^3->A`;
                   `e':real^3->A`; `Y:A->bool`; `f:real^3->real^3`; `f':real^3->real^3`]
                  P2BF_TWISTED_SPLIT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
      STRIP_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(top:A topology) closure_of Y`)) THEN
    ABBREV_TAC `U0 = (Y:A->bool) UNION IMAGE (e':real^3->A) (annulus (inv(c * c)) (c * c))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `U:A->bool`; `Y:A->bool`; `p:real^3->A`; `e':real^3->A`;
                   `z':A`; `f:real^3->real^3`; `f':real^3->real^3`; `inv(c * c)`; `c * c`;
                   `U0:A->bool`] P2BF_SUBCAP_TWISTED) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN SPDR7_ASM_REAL_ARITH_TAC;
      STRIP_TAC] THEN
    SPDR7_CAPFIX_TAIL_TAC "DCT" `p:real^3->A` DISJ2_TAC]);;

let P2BF_SLICE_FIX_GEN = prove
 (`?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\
               (mfd_complete (top',atlas') g' \/
                compact_in top' (top' closure_of IMAGE (psi:A->B) U)) /\
               rfs_canonical_nbhd (top,atlas) g C eps x U /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local atlas (chart_at atlas y)
                               (\z. mfd_scalar atlas g x %% g z))
                            (SND(chart_at atlas y) y) <= Kr) /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               (U IN connected_components_of top
                ==> IMAGE psi U IN connected_components_of top') /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U'. U' SUBSET IMAGE psi U /\
                        rfs_canonical_nbhd (top',atlas') g' C' eps' (psi x) U'`,
  MP_TAC(INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_CAP_FIX_GEN) THEN
  DISCH_THEN(X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `epc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAP"))))) THEN
  MAP_EVERY EXISTS_TAC [`max (&2) Kc`; `min (&1 / &40) epc`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&2 * eps <= eps' /\ Kc * eps <= eps' /\ eps' <= &1 / &40 /\ eps' <= epc /\
                eps < eps' /\ eps' < &1 / &4`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * eps <= max (&2) Kc * eps /\ Kc * eps <= max (&2) Kc * eps`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `eps' <= min (&1 / &40) epc` THEN REWRITE_TAC[REAL_LE_MIN] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "CAP" (MP_TAC o SPECL [`C:real`; `eps:real`; `C':real`; `eps':real`; `Kr:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`]
    (MATCH_MP P2BS_NECK_UNIF (CONJ P2B_REQ_LRG_BASE P2B_REQ_LRG_RM_NEAR))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  MP_TAC(SPECL [`C:real`; `C':real`; `Kr:real`]
    (MATCH_MP P2BS_CCOMP_UNIF P2B_REQ_LRG_DERIV)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D3"))) THEN
  MP_TAC(SPECL [`eps:real`; `eps':real`] P2BS_ROUND_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D4"))) THEN
  EXISTS_TAC `min (min d1 d2) (min d3 d4)` THEN
  ABBREV_TAC `delta = min (min d1 d2) (min d3 d4)` THEN
  SUBGOAL_THEN `&0 < delta /\ delta <= d1 /\ delta <= d2 /\ delta <= d3 /\ delta <= d4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                       `x:A`; `U:A->bool`; `psi:A->B`; `psi':B->A`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN
   `!d. &0 < mfd_scalar atlas (g:A->real^3^3) x /\ delta <= d
        ==> rfs_mclose (rfs_kreg d) d atlas U
              (\y. mfd_scalar atlas (g:A->real^3^3) x %% g y)
              (\y. mfd_scalar atlas g x %%
                   mfd_pullback_metric atlas atlas' (psi:A->B) (g':B->real^3^3) y)`
  (LABEL_TAC "MC") THENL
   [X_GEN_TAC `d:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BS_MCLOSE_MONO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `IMAGE (psi:A->B) U`;
                          `psi':B->A`; `delta:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 (X_CHOOSE_THEN `e:real^3->A` STRIP_ASSUME_TAC)
    (DISJ_CASES_THEN2 (X_CHOOSE_THEN `Y:A->bool` STRIP_ASSUME_TAC)
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC)) o
    GEN_REWRITE_RULE I [rfs_canonical_nbhd] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_canonical_nbhd"
                     with Failure _ -> false)) THENL
   [SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x e` THEN SIMP_TAC[rfs_neck];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d2:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d2`)))) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `U:A->bool`)) THEN
    EXISTS_TAC `IMAGE ((psi:A->B) o (e:real^3->A)) (rfs_neck_dom eps')` THEN CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      MATCH_MP_TAC APX_NECK_DOM_MONO THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ1_TAC THEN
    EXISTS_TAC `(psi:A->B) o (e:real^3->A)` THEN REWRITE_TAC[] THEN
    USE_THEN "D2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`]
                    APX_CAP_CORE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:A) IN U` ASSUME_TAC THENL
       [SUBGOAL_THEN `(Y:A->bool) SUBSET top closure_of Y` MP_TAC THENL
         [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
        UNDISCH_TAC `top closure_of (Y:A->bool) SUBSET U` THEN
        UNDISCH_TAC `(x:A) IN Y` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
      REWRITE_TAC[rfs_cap] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d1:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d1`)))) THEN
    DISCH_TAC THEN
    USE_THEN "D1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                   `g:A->real^3^3`; `top':B topology`;
                                   `atlas':((B->bool)#(B->real^3))->bool`; `g':B->real^3^3`;
                                   `x:A`; `U:A->bool`; `Y:A->bool`; `psi:A->B`;
                                   `psi':B->A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `U':B->bool` (X_CHOOSE_THEN `Y':B->bool` STRIP_ASSUME_TAC))] THEN
    EXISTS_TAC `U':B->bool` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[rfs_canonical_nbhd] THEN DISJ2_TAC THEN DISJ1_TAC THEN
      EXISTS_TAC `Y':B->bool` THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `U IN connected_components_of (top:A topology)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
      SIMP_TAC[rfs_c_component];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
        REPEAT STRIP_TAC THEN
        UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
        REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d3:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d3`)))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (psi:A->B) U IN connected_components_of top'` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (psi:A->B) U` THEN REWRITE_TAC[SUBSET_REFL; rfs_canonical_nbhd] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "D3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `U IN connected_components_of (top:A topology)` ASSUME_TAC THENL
     [UNDISCH_TAC `rfs_round_component (top,atlas) (g:A->real^3^3) eps U` THEN
      SIMP_TAC[rfs_round_component];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x` ASSUME_TAC THENL
     [MATCH_MP_TAC P2B_MFD_SCALAR_POS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`] CONNECTED_COMPONENTS_OF_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN U` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `eps:real`; `U:A->bool`; `x:A`] APX_ROUND_SECTIONAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
      MAP_EVERY X_GEN_TAC [`u1:real^3`; `v1:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u1:real^3`; `v1:real^3`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < mfd_sectional atlas (g:A->real^3^3) x u1 v1 / q` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]];
      ALL_TAC] THEN
    USE_THEN "MC" (fun th -> MP_TAC(MATCH_MP (SPEC `d4:real` th)
      (CONJ (ASSUME `&0 < mfd_scalar atlas (g:A->real^3^3) x`) (ASSUME `delta <= d4`)))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (psi:A->B) U IN connected_components_of top'` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `IMAGE (psi:A->B) U` THEN REWRITE_TAC[SUBSET_REFL; rfs_canonical_nbhd] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "D4" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `x:A`; `psi':B->A`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Headlines and the Part 2C statements as corollaries of the general forms: *)
(* P2B_PROP_9_79_CAP_FIX and P2C_REQ_CAP_FIX (complete target),              *)
(* P2B_PROP_9_79_SLICE_FIX, P2_PROP_9_79_SLICE and P2C_REQ_SLICE_FIX         *)
(* (complete target), P2C_REQ_SLICE_LOCAL (A21: compact closure of psi U).   *)
(* ------------------------------------------------------------------------- *)

(* Derive a specialised form from a general one: same constants, and the
   same inner hypotheses except that the general form has a disjunction
   where the special form has its first disjunct. *)
let P2BF_FROM_GEN_TAC (gen:thm) : tactic =
  MP_TAC gen THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `eps0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))))) THEN
  MAP_EVERY EXISTS_TAC [`K:real`; `eps0:real`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (fun (asl,w) ->
     let vs,_ = strip_forall w in
     (MAP_EVERY X_GEN_TAC vs THEN DISCH_TAC THEN
      REMOVE_THEN "G" (MP_TAC o SPECL vs) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) (asl,w)) THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  EXISTS_TAC `delta:real` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (fun (asl,w) ->
     let vs,_ = strip_forall w in
     (MAP_EVERY X_GEN_TAC vs THEN DISCH_TAC THEN
      REMOVE_THEN "D" (MP_TAC o SPECL vs) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]) (asl,w));;

let P2B_PROP_9_79_CAP_FIX = prove
 (`!(u:A->bool) (w:B->bool). P2B_PROP_9_79_CAP_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_79_CAP_FIX_STATEMENT] THEN
  P2BF_FROM_GEN_TAC (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_CAP_FIX_GEN));;

let P2B_PROP_9_79_SLICE_FIX = prove
 (`!(u:A->bool) (w:B->bool). P2B_PROP_9_79_SLICE_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_PROP_9_79_SLICE_FIX_STATEMENT] THEN
  P2BF_FROM_GEN_TAC (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_SLICE_FIX_GEN));;

let P2_PROP_9_79_SLICE = prove
 (`!(u:A->bool) (w:B->bool). P2_PROP_9_79_SLICE_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] P2B_PROP_9_79_SLICE_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_SLICE_FIX_STATEMENT; P2_PROP_9_79_SLICE_STATEMENT]);;

let P2C_REQ_CAP_FIX = prove
 (`!(u:A->bool) (w:B->bool). P2C_REQ_CAP_FIX_STATEMENT u w`,
  REWRITE_TAC[P2C_REQ_CAP_FIX_STATEMENT;
              REWRITE_RULE[P2B_PROP_9_79_CAP_FIX_STATEMENT] P2B_PROP_9_79_CAP_FIX]);;

let P2C_REQ_SLICE_FIX = prove
 (`!(u:A->bool) (w:B->bool). P2C_REQ_SLICE_FIX_STATEMENT u w`,
  REWRITE_TAC[P2C_REQ_SLICE_FIX_STATEMENT;
              REWRITE_RULE[P2B_PROP_9_79_SLICE_FIX_STATEMENT] P2B_PROP_9_79_SLICE_FIX]);;

let P2C_REQ_SLICE_LOCAL = prove
 (`!(u:A->bool) (w:B->bool). P2C_REQ_SLICE_LOCAL_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_REQ_SLICE_LOCAL_STATEMENT] THEN
  P2BF_FROM_GEN_TAC (INST_TYPE [`:A`,`:A`; `:B`,`:B`] P2BF_SLICE_FIX_GEN));;

