(* ========================================================================= *)
(* pc_soul_topo: the topology at a soul (piece (c) of the statements of      *)
(* pc_p2b_c994req for MT Cor 9.94),                                          *)
(*   SOULT_SOUL_TOPOLOGY |- !w. P2B_SOUL_TOPOLOGY_STATEMENT w.               *)
(* Route: every compact set lies in a big ball chart about the soul          *)
(* (SOULB_BIG_BALL, pc_soul_ball); inside it the smooth Schoenflies theorem *)
(* (SCH_SCHOENFLIES_REQ, pc_sch_main) bounds every neck sphere by a ball    *)
(* chart that continues the neck chart or its inversion; the ball and the   *)
(* complement of the closed ball are the two sides of the sphere.  A ball   *)
(* on the side away from the soul contains a far neck point whose distance  *)
(* from the soul beats the sphere (APX_NECK_DIST_UPPER/LOWER,               *)
(* P2AS_FAR_BEATS_S), so d_p would have an interior maximum (P2AS_CASE_B),  *)
(* against regularity.  Part 2: the ball of the cap sphere is on the side   *)
(* of the soul.  Part 1 (the soul in the middle of a neck): two level       *)
(* spheres about the soul; both balls on its side would make the manifold   *)
(* compact, and d_p would have a global maximum.                            *)
(* ========================================================================= *)

needs "src/pc_sch_main.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_p2b_c994req.ml";;
needs "src/pc_soul_ball.ml";;
needs "src/pc_apx_neck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The two sides of the sphere of a ball chart c in a                       *)
(* connected Hausdorff manifold: c(ball 1) and the complement of            *)
(* c(cball 1), both open and connected (the complement of a collared        *)
(* closed ball is connected).                                                *)
(* ------------------------------------------------------------------------- *)

let SOULT_BALL_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (c:real^3->A).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ mfd_ball_chart top atlas c
     ==> open_in top (IMAGE c (ball(vec 0,&1))) /\
         connected_in top (IMAGE c (ball(vec 0,&1))) /\
         compact_in top (IMAGE c (cball(vec 0,&1))) /\
         closed_in top (IMAGE c (cball(vec 0,&1))) /\
         compact_in top (IMAGE c (sphere(vec 0,&1))) /\
         open_in top (IMAGE c (annulus (&1) (&2))) /\
         connected_in top (IMAGE c (annulus (&1) (&2))) /\
         open_in top (IMAGE c (ball(vec 0,&2))) /\
         IMAGE c (cball(vec 0,&1)) = IMAGE c (ball(vec 0,&1)) UNION IMAGE c (sphere(vec 0,&1)) /\
         DISJOINT (IMAGE c (ball(vec 0,&1))) (IMAGE c (sphere(vec 0,&1))) /\
         IMAGE c (ball(vec 0,&2)) = IMAGE c (cball(vec 0,&1)) UNION IMAGE c (annulus (&1) (&2)) /\
         DISJOINT (IMAGE c (cball(vec 0,&1))) (IMAGE c (annulus (&1) (&2))) /\
         IMAGE c (ball(vec 0,&2)) SUBSET topspace top /\ c(vec 0) IN IMAGE c (ball(vec 0,&1)) /\
         (!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ c x = c y ==> x = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball_chart] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c':A->real^3` STRIP_ASSUME_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  SUBGOAL_THEN `!x y. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ (c:real^3->A) x = c y
                      ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `ball(vec 0:real^3,&2)`; `c:real^3->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                cball(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                sphere(vec 0:real^3,&1) SUBSET ball(vec 0,&2) /\
                annulus (&1) (&2) SUBSET ball(vec 0:real^3,&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean (ball(vec 0:real^3,&2)),top) (c:real^3->A)`
  ASSUME_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. connected s /\ s SUBSET ball(vec 0,&2)
                                 ==> connected_in top (IMAGE (c:real^3->A) s)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^3,&2))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (c:real^3->A) (cball(vec 0,&1))) /\
                compact_in top (IMAGE (c:real^3->A) (sphere(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; COMPACT_SPHERE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CONNECTED_BALL];
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ball(vec 0:real^3,&2)`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[SCH1_ANNULUS_CONNECTED];
    REWRITE_TAC[GSYM IMAGE_UNION; BALL_UNION_SPHERE];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u:real^3 = v` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x y. x IN ball(vec 0:real^3,&2) /\ y IN ball(vec 0,&2) /\ (c:real^3->A) x = c y
               ==> x = y`) (concl th))) THEN ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(v:real^3) IN ball(vec 0,&1)` THEN
      UNDISCH_TAC `(v:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC];
    REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `u:real^3 = v` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x y. x IN ball(vec 0:real^3,&2) /\ y IN ball(vec 0,&2) /\ (c:real^3->A) x = c y
               ==> x = y`) (concl th))) THEN ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(v:real^3) IN cball(vec 0,&1)` THEN
      UNDISCH_TAC `(v:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[IN_CBALL_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ASM_MESON_TAC[OPEN_IN_SUBSET];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC]);;

(* Two set facts for the separation argument. *)

let SOULT_SEP_SET1 = prove
 (`!T0 C N B2 Q e1 e2:A->bool.
     T0 = C UNION Q /\ C INTER Q = {} /\ B2 INTER Q = N /\ C SUBSET B2 /\ ~(B2 = {}) /\
     Q SUBSET e1 UNION e2 /\ e1 INTER e2 INTER Q = {} /\ ~(e2 INTER Q = {}) /\
     N SUBSET e1
     ==> T0 SUBSET (B2 UNION (e1 INTER Q)) UNION (e2 INTER Q) /\
         (B2 UNION (e1 INTER Q)) INTER (e2 INTER Q) = {} /\
         ~(B2 UNION (e1 INTER Q) = {}) /\ ~(e2 INTER Q = {})`,
  SET_TAC[]);;

let SOULT_SEP_SET2 = prove
 (`!T0 C N B2 Q e1 e2:A->bool.
     T0 = C UNION Q /\ C INTER Q = {} /\ B2 INTER Q = N /\ C SUBSET B2 /\ ~(B2 = {}) /\
     Q SUBSET e1 UNION e2 /\ e1 INTER e2 INTER Q = {} /\ ~(e1 INTER Q = {}) /\
     N SUBSET e2
     ==> T0 SUBSET (e1 INTER Q) UNION (B2 UNION (e2 INTER Q)) /\
         (e1 INTER Q) INTER (B2 UNION (e2 INTER Q)) = {} /\
         ~(e1 INTER Q = {}) /\ ~(B2 UNION (e2 INTER Q) = {})`,
  SET_TAC[]);;

(* The complement of the closed ball is open and connected. *)

let SOULT_COMPLEMENT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (c:real^3->A).
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas c
     ==> open_in top (topspace top DIFF IMAGE c (cball(vec 0,&1))) /\
         connected_in top (topspace top DIFF IMAGE c (cball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = topspace top DIFF IMAGE (c:real^3->A) (cball(vec 0,&1))` THEN
  SUBGOAL_THEN `open_in top (Q:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONNECTED_IN] THEN CONJ_TAC THENL [EXPAND_TAC "Q" THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`e1:A->bool`; `e2:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (c:real^3->A) (annulus (&1) (&2)) SUBSET Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->A) (annulus (&1) (&2)) SUBSET e1 \/
                IMAGE (c:real^3->A) (annulus (&1) (&2)) SUBSET e2` MP_TAC THENL
   [UNDISCH_TAC `connected_in top (IMAGE (c:real^3->A) (annulus (&1) (&2)))` THEN
    REWRITE_TAC[CONNECTED_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:A->bool`; `e2:A->bool`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (IMAGE (c:real^3->A) (ball(vec 0,&2)) UNION ((e1:A->bool) INTER Q)) /\
    open_in top ((e2:A->bool) INTER Q) /\ open_in top ((e1:A->bool) INTER Q) /\
    open_in top (IMAGE (c:real^3->A) (ball(vec 0,&2)) UNION ((e2:A->bool) INTER Q))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_UNION; OPEN_IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `topspace top = IMAGE (c:real^3->A) (cball(vec 0,&1)) UNION Q /\
    IMAGE (c:real^3->A) (cball(vec 0,&1)) INTER Q = {} /\
    IMAGE (c:real^3->A) (ball(vec 0,&2)) INTER Q = IMAGE c (annulus (&1) (&2)) /\
    ~(IMAGE (c:real^3->A) (ball(vec 0,&2)) = {})`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    UNDISCH_TAC `IMAGE (c:real^3->A) (ball(vec 0,&2)) =
                 IMAGE c (cball(vec 0,&1)) UNION IMAGE c (annulus (&1) (&2))` THEN
    UNDISCH_TAC `IMAGE (c:real^3->A) (ball(vec 0,&2)) SUBSET topspace top` THEN
    UNDISCH_TAC `(c:real^3->A) (vec 0) IN IMAGE c (ball(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (c:real^3->A) (cball(vec 0,&1)) =
                 IMAGE c (ball(vec 0,&1)) UNION IMAGE c (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (c:real^3->A) (cball(vec 0,&1))) (IMAGE c (annulus (&1) (&2)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->A) (cball(vec 0,&1)) SUBSET IMAGE c (ball(vec 0,&2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `connected_space (top:A topology)` THEN
  REWRITE_TAC[connected_space; NOT_EXISTS_THM] THEN DISCH_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`IMAGE (c:real^3->A) (ball(vec 0,&2)) UNION (e1 INTER Q)`;
                                  `(e2:A->bool) INTER Q`]) THEN
    REWRITE_TAC[ASSUME `open_in top (IMAGE (c:real^3->A) (ball(vec 0,&2)) UNION
                                     ((e1:A->bool) INTER Q))`;
                ASSUME `open_in top ((e2:A->bool) INTER Q)`] THEN
    MATCH_MP_TAC SOULT_SEP_SET1;
    FIRST_X_ASSUM(MP_TAC o SPECL [`(e1:A->bool) INTER Q`;
                                  `IMAGE (c:real^3->A) (ball(vec 0,&2)) UNION (e2 INTER Q)`]) THEN
    REWRITE_TAC[ASSUME `open_in top ((e1:A->bool) INTER Q)`;
                ASSUME `open_in top (IMAGE (c:real^3->A) (ball(vec 0,&2)) UNION
                                     ((e2:A->bool) INTER Q))`] THEN
    MATCH_MP_TAC SOULT_SEP_SET2] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (c:real^3->A) (cball(vec 0,&1))`;
                        `IMAGE (c:real^3->A) (annulus (&1) (&2))`] THEN
  ASM_REWRITE_TAC[]);;

(* The two sides of the sphere. *)

let SOULT_BALL_SIDES = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (c:real^3->A) u v.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas c /\
     u IN topspace top DIFF IMAGE c (sphere(vec 0,&1)) /\
     v IN topspace top DIFF IMAGE c (sphere(vec 0,&1))
     ==> (connected_component_of
            (subtopology top (topspace top DIFF IMAGE c (sphere(vec 0,&1)))) u v <=>
          (u IN IMAGE c (ball(vec 0,&1)) <=> v IN IMAGE c (ball(vec 0,&1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`]
    SOULT_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `topspace top DIFF IMAGE (c:real^3->A) (sphere(vec 0,&1)) =
    IMAGE c (ball(vec 0,&1)) UNION (topspace top DIFF IMAGE c (cball(vec 0,&1))) /\
    DISJOINT (IMAGE (c:real^3->A) (ball(vec 0,&1)))
             (topspace top DIFF IMAGE c (cball(vec 0,&1)))`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[connected_component_of] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `T1:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `connected_in (subtopology top (topspace top DIFF
                   IMAGE (c:real^3->A) (sphere(vec 0,&1)))) (T1:A->bool)` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL
      [`IMAGE (c:real^3->A) (ball(vec 0,&1))`;
       `topspace top DIFF IMAGE (c:real^3->A) (cball(vec 0,&1))`] o CONJUNCT2) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN ASM_CASES_TAC `(u:A) IN IMAGE (c:real^3->A) (ball(vec 0,&1))` THENL
     [EXISTS_TAC `IMAGE (c:real^3->A) (ball(vec 0,&1))`;
      EXISTS_TAC `topspace top DIFF IMAGE (c:real^3->A) (cball(vec 0,&1))`] THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM SET_TAC[]]);;

(* A connected set off the sphere that meets the ball lies in it. *)

let SOULT_CONNECTED_IN_BALL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (c:real^3->A) T1.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas c /\ connected_in top T1 /\
     T1 SUBSET topspace top DIFF IMAGE c (sphere(vec 0,&1)) /\
     ~(T1 INTER IMAGE c (ball(vec 0,&1)) = {})
     ==> T1 SUBSET IMAGE c (ball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `c:real^3->A`]
    SOULT_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `connected_in top (T1:A->bool)` THEN
  REWRITE_TAC[CONNECTED_IN; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL
      [`IMAGE (c:real^3->A) (ball(vec 0,&1))`;
       `topspace top DIFF IMAGE (c:real^3->A) (cball(vec 0,&1))`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A ball chart away from the soul cannot contain a point                   *)
(* whose distance from the soul beats the whole sphere of the ball: d_p     *)
(* would have an interior maximum on the closed ball (P2AS_CASE_B).         *)
(* ------------------------------------------------------------------------- *)

let SOULT_BALL_NOT_FAR = prove
 (`!top atlas (g:B->real^3^3) p (c:real^3->B) z.
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     mfd_ball_chart top atlas c /\ ~(p IN IMAGE c (ball(vec 0,&1))) /\
     z IN IMAGE c (ball(vec 0,&1)) /\
     (!w. w IN IMAGE c (sphere(vec 0,&1))
          ==> mfd_dist (top,atlas) g p w < mfd_dist (top,atlas) g p z)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:B) IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `IMAGE (c:real^3->B) (cball(vec 0,&1))`; `p:B`]
    SOULB_COMPACT_DIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `R0:real`) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `IMAGE (c:real^3->B) (sphere(vec 0,&1))`; `z:B`; `z:B`; `&0`; `R0:real`]
    P2AS_CASE_B) THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:B` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&0 < mfd_dist (top,atlas) (g:B->real^3^3) p p` THEN
    ASM_SIMP_TAC[MFD_DIST_REFL; REAL_LT_REFL];
    ASM SET_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `z:B`] P2AS_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM SET_TAC[]; ASM SET_TAC[]];
      SIMP_TAC[]];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `R0:real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`;
                   `z:B`; `y:B`] SOULT_BALL_SIDES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2.  The cap sphere e(sphere 1) of an eps-neck bounds a              *)
(* ball chart on the side of the soul that continues e on the collar.  In  *)
(* a big ball about the soul (SOULB_BIG_BALL) the smooth Schoenflies        *)
(* theorem gives a ball chart c with c = e or c = e o inversion on          *)
(* annulus(3/4,2); in the second case the ball is the side of e(4/3 e1),    *)
(* away from the soul, and it contains the far neck point at level          *)
(* 1/(2 eps), which beats the sphere (P2AS_NECK_METRIC): SOULT_BALL_NOT_FAR. *)
(* ------------------------------------------------------------------------- *)

let SOULT_SVAL_HALF_TWO = prove
 (`!y:real^3. &1 / &2 <= norm y /\ norm y <= &2
              ==> ~(y = vec 0) /\ abs(apx_sval y) <= sqrt(&2)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 <= norm(vec 0:real^3)` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `log(&2) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      REWRITE_TAC[LOG_EXP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(norm(y:real^3)) <= log(&2) /\ log(&1 / &2) <= log(norm y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&1 / &2) = --log(&2)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC LOG_INV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(sqrt(&2)) = sqrt(&2)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The collar region of the cap sphere lies in the neck domain. *)

let SOULT_NECK_COLLAR = prove
 (`!eps. &0 < eps /\ eps <= &1 / &1024
         ==> compact(cball(vec 0:real^3,exp(sqrt(&2) / sqrt(&2))) DIFF
                     ball(vec 0,exp(--sqrt(&2) / sqrt(&2)))) /\
             cball(vec 0:real^3,exp(sqrt(&2) / sqrt(&2))) DIFF
             ball(vec 0,exp(--sqrt(&2) / sqrt(&2))) SUBSET rfs_neck_dom eps /\
             {y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} SUBSET
             cball(vec 0,exp(sqrt(&2) / sqrt(&2))) DIFF ball(vec 0,exp(--sqrt(&2) / sqrt(&2))) /\
             annulus (&1 / &2) (&2) SUBSET rfs_neck_dom eps`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&2) < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&1 / &1024)` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `sqrt(&2)`] APX_SUBSLAB) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2} SUBSET
                cball(vec 0,exp(sqrt(&2) / sqrt(&2))) DIFF ball(vec 0,exp(--sqrt(&2) / sqrt(&2)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SOULT_SVAL_HALF_TWO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `cball(vec 0:real^3,exp(sqrt(&2) / sqrt(&2))) DIFF
              ball(vec 0,exp(--sqrt(&2) / sqrt(&2)))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2}` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* The sphere of the Schoenflies ball. *)

let SOULT_SCHOENFLIES_NECK = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (b0:real^3->B) (n:real^3->B).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas b0 /\ mfd_neck_chart top atlas n /\
     IMAGE n (annulus (&1 / &2) (&2)) SUBSET IMAGE b0 (ball(vec 0,&1))
     ==> ?c. mfd_ball_chart top atlas c /\
             IMAGE c (sphere(vec 0,&1)) = IMAGE n (sphere(vec 0,&1)) /\
             ((!x. x IN annulus (&3 / &4) (&2) ==> c x = n x) \/
              (!x. x IN annulus (&3 / &4) (&2) ==> c x = n(inv(norm x pow 2) % x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[APX_SCHOENFLIES_REQ_STATEMENT]
           (ISPEC `UNIV:B->bool` SCH_SCHOENFLIES_REQ)) THEN
  DISCH_THEN(MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `b0:real^3->B`; `n:real^3->B`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^3->B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&3 / &4) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `w:B` THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> (c:real^3->B) x = n x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(x:real^3) pow 2) % x = x` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
      SIMP_TAC[IN_SPHERE_0; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* Points of the axis in the neck domain. *)

let SOULT_AXIS_IN_NECK = prove
 (`!eps t. &0 < eps /\ &0 < t /\ abs(sqrt(&2) * log t) < inv eps
           ==> t % basis 1:real^3 IN rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(log t) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    UNDISCH_TAC `abs(sqrt(&2) * log t) < inv eps` THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  SUBGOAL_THEN `t = exp(log t)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT; LOG_EXP] THEN ASM_REAL_ARITH_TAC);;

(* Part 2. *)

let SOULT_PART2 = prove
 (`!eps top atlas (g:B->real^3^3) p x0 (e:real^3->B).
     &0 < eps /\ eps <= &1 / &1024 /\
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     rfs_neck (top,atlas) g eps x0 e /\
     (!w1 w2. w1 IN IMAGE (e:real^3->B) (sphere(vec 0,&1)) /\ w2 IN IMAGE (e:real^3->B) (sphere(vec 0,&1))
              ==> mfd_dist (top,atlas) g w1 w2 <= &7 * inv(sqrt(mfd_scalar atlas g x0))) /\
     (!w. w IN IMAGE (e:real^3->B) (sphere(vec 0,&1))
          ==> inv(&4 * eps) * inv(sqrt(mfd_scalar atlas g x0)) <=
              mfd_dist (top,atlas) g w ((e:real^3->B)(exp(inv(&2 * sqrt(&2) * eps)) % basis 1))) /\
     apx_separates top (IMAGE (e:real^3->B) (sphere(vec 0,&1))) p ((e:real^3->B)(&4 / &3 % basis 1))
     ==> ?b f f'. mfd_ball_chart top atlas b /\ sphere_diffeo f f' /\
                  p IN IMAGE b (ball(vec 0,&1)) /\
                  IMAGE b (sphere(vec 0,&1)) = IMAGE (e:real^3->B) (sphere(vec 0,&1)) /\
                  (!y. y IN annulus (&1) (&2) ==> b y = (e:real^3->B)(radial_ext f y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`] P2AS_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` SOULT_NECK_COLLAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->B)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps x0 e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas (e:real^3->B)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`;
                 `IMAGE (e:real^3->B) (cball(vec 0,exp(sqrt(&2) / sqrt(&2))) DIFF
                                       ball(vec 0,exp(--sqrt(&2) / sqrt(&2))))`]
    SOULB_BIG_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:real^3->B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `b0:real^3->B`;
                 `e:real^3->B`] SOULT_SCHOENFLIES_NECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->B) (cball(vec 0,exp(sqrt(&2) / sqrt(&2))) DIFF
                                     ball(vec 0,exp(--sqrt(&2) / sqrt(&2))))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{y:real^3 | &1 / &2 <= norm y /\ norm y <= &2}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  SUBGOAL_THEN `(e:real^3->B)(&4 / &3 % basis 1) IN topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1)) /\
                (p:B) IN topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1)) /\
                ~(connected_component_of
                    (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
                    p ((e:real^3->B)(&4 / &3 % basis 1)))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_separates top (IMAGE (e:real^3->B) (sphere(vec 0,&1))) p
                   ((e:real^3->B)(&4 / &3 % basis 1))` THEN
    SIMP_TAC[apx_separates];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_TAC THENL
   [(* the ball chart continues e: it is on the side of the soul *)
    MAP_EVERY EXISTS_TAC [`c:real^3->B`; `\x:real^3. x`; `\x:real^3. x`] THEN
    ASM_REWRITE_TAC[SMT_SPHERE_DIFFEO_ID; SMT_RADIAL_EXT_ID] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&4 / &3 % basis 1:real^3 IN annulus (&3 / &4) (&2) /\
                    &4 / &3 % basis 1:real^3 IN ball(vec 0,&2) /\
                    ~(&4 / &3 % basis 1:real^3 IN ball(vec 0,&1))` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0; NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `(c:real^3->B)(&4 / &3 % basis 1) = (e:real^3->B)(&4 / &3 % basis 1)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~((e:real^3->B)(&4 / &3 % basis 1) IN IMAGE (c:real^3->B) (ball(vec 0,&1)))`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `(c:real^3->B)(&4 / &3 % basis 1)`)) THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `&4 / &3 % basis 1:real^3 = w` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!x y. x IN ball(vec 0:real^3,&2) /\ y IN ball(vec 0,&2) /\ (c:real^3->B) x = c y
                   ==> x = y`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^3) IN ball(vec 0,&1)` THEN
          REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`;
                     `p:B`; `(e:real^3->B)(&4 / &3 % basis 1)`] SOULT_BALL_SIDES) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    (* the ball chart continues the inversion: contradiction *)
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    ABBREV_TAC `rho = exp(inv(&2 * sqrt(&2) * eps))` THEN
    SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC REAL_LE_LSQRT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&2 <= inv(&2 * sqrt(&2) * eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &256)` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * eps` THEN CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 / &3 <= rho` ASSUME_TAC THENL
     [EXPAND_TAC "rho" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 + inv(&2 * sqrt(&2) * eps)` THEN REWRITE_TAC[REAL_EXP_LE_X] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!t. &5 / &4 <= t /\ t <= rho
                      ==> t % basis 1 IN rfs_neck_dom eps /\ ~(abs t = &1)` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC SOULT_AXIS_IN_NECK THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= log t /\ log t <= inv(&2 * sqrt(&2) * eps)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN `inv(&2 * sqrt(&2) * eps) = log rho` SUBST1_TAC THENL
           [EXPAND_TAC "rho" THEN REWRITE_TAC[LOG_EXP]; ALL_TAC] THEN
          MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `sqrt(&2) * inv(&2 * sqrt(&2) * eps) = inv(&2) * inv eps` ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < sqrt(&2)` THEN UNDISCH_TAC `&0 < eps` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= inv(&2) * m /\ &0 < m ==> abs x < m`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `inv(&2) * inv eps`)) THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `connected_component_of (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
        ((e:real^3->B)(&5 / &4 % basis 1)) ((e:real^3->B)(&4 / &3 % basis 1)) /\
      connected_component_of (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1))))
        ((e:real^3->B)(&4 / &3 % basis 1)) ((e:real^3->B)(rho % basis 1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2AS_AXIS_ARC THEN
      MAP_EVERY EXISTS_TAC [`eps:real`; `atlas:((B->bool)#(B->real^3))->bool`;
                            `g:B->real^3^3`; `x0:B`] THEN
      ASM_REWRITE_TAC[REAL_ARITH `&5 / &4 <= &4 / &3`] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^3->B)(&4 / &5 % basis 1) = (e:real^3->B)(&5 / &4 % basis 1)` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `&4 / &5 % basis 1:real^3` o check (fun th -> can (term_match []
        `!x. x IN annulus (&3 / &4) (&2) ==> (c:real^3->B) x = (e:real^3->B)(inv(norm x pow 2) % x)`)
        (concl th))) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->B)(&5 / &4 % basis 1) IN IMAGE (c:real^3->B) (ball(vec 0,&1))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `!u v. connected_component_of
                          (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,&1)))) u v
                        ==> (u IN IMAGE (c:real^3->B) (ball(vec 0,&1)) <=>
                             v IN IMAGE c (ball(vec 0,&1)))` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`;
                     `u:B`; `v:B`] SOULT_BALL_SIDES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->B)(&4 / &3 % basis 1) IN IMAGE (c:real^3->B) (ball(vec 0,&1)) /\
                  (e:real^3->B)(rho % basis 1) IN IMAGE (c:real^3->B) (ball(vec 0,&1))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((p:B) IN IMAGE (c:real^3->B) (ball(vec 0,&1)))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`;
                     `p:B`; `(e:real^3->B)(&4 / &3 % basis 1)`] SOULT_BALL_SIDES) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SOULT_BALL_NOT_FAR THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `p:B`; `c:real^3->B`;
                          `(e:real^3->B)(rho % basis 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `IMAGE (e:real^3->B) (sphere(vec 0,&1))`;
                   `(e:real^3->B)(&4 / &3 % basis 1)`; `(e:real^3->B)(rho % basis 1)`;
                   `&7 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))`;
                   `inv(&4 * eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))`]
      P2AS_FAR_BEATS_S) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        ONCE_REWRITE_TAC[CONNECTED_COMPONENT_OF_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&256` THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&4 * &1 / &1024)` THEN
          CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LE_INV2] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Level spheres of a neck.  The level sphere at level t is                 *)
(* e(sphere(exp(t / sqrt 2))), the central sphere of the rescaled neck      *)
(* chart y |-> e(exp(t / sqrt 2) % y); neck points on the same side of it   *)
(* are in one component of its complement; distances to it from a far      *)
(* axis point (APX_NECK_DIST_UPPER/LOWER).                                  *)
(* ------------------------------------------------------------------------- *)

let SOULT_SVAL_RADIUS = prove
 (`!t y:real^3. norm y = exp(t / sqrt(&2)) ==> apx_sval y = t`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[apx_sval; LOG_EXP] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` MP_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let SOULT_RADIUS_IN_NECK = prove
 (`!eps y:real^3. &0 < eps /\ ~(y = vec 0) /\ abs(apx_sval y) < inv eps
                  ==> y IN rfs_neck_dom eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) = norm y % (inv(norm y) % y)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm(y:real^3))) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    UNDISCH_TAC `abs(apx_sval(y:real^3)) < inv eps` THEN
    REWRITE_TAC[apx_sval; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM; NORM_MUL; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; REAL_LT_IMP_NZ;
               REAL_MUL_RID] THEN
  SUBGOAL_THEN `norm(y:real^3) = exp(log(norm y))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC);;

(* The rescaled neck chart at level t. *)

let SOULT_LEVEL_CHART = prove
 (`!eps top atlas (g:B->real^3^3) x0 (e:real^3->B) t.
     rfs_neck (top,atlas) g eps x0 e /\ abs t + &2 < inv eps
     ==> mfd_neck_chart top atlas (\y. (e:real^3->B)(exp(t / sqrt(&2)) % y)) /\
         IMAGE (\y. (e:real^3->B)(exp(t / sqrt(&2)) % y)) (sphere(vec 0,&1)) =
         IMAGE (e:real^3->B) (sphere(vec 0,exp(t / sqrt(&2)))) /\
         (!y. y IN annulus (&1 / &2) (&2)
              ==> exp(t / sqrt(&2)) % y IN rfs_neck_dom eps /\
                  abs(apx_sval(exp(t / sqrt(&2)) % y)) <= abs t + &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\ &0 < eps /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->B)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps x0 e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  ABBREV_TAC `lam = exp(t / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL [EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC REAL_LE_LSQRT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1 / &2) (&2)
                ==> ~(lam % y = vec 0) /\ abs(apx_sval(lam % y)) <= abs t + &2` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(SPEC `y:real^3` SOULT_SVAL_HALF_TWO) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    SUBGOAL_THEN `apx_sval(lam % y:real^3) = t + apx_sval y` SUBST1_TAC THENL
     [REWRITE_TAC[apx_sval; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; LOG_MUL; NORM_POS_LT] THEN
      EXPAND_TAC "lam" THEN REWRITE_TAC[LOG_EXP] THEN
      UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1 / &2) (&2) ==> lam % y IN rfs_neck_dom eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC SOULT_RADIUS_IN_NECK THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs t + &2` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN
    SUBGOAL_THEN `(\y. (e:real^3->B)(lam % y)) = e o (\y:real^3. lam % y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `annulus (lam * &1 / &2) (lam * &2):real^3->bool`;
                          `\y:real^3. inv lam % y`] THEN
    ASM_SIMP_TAC[SMT_DIFFEO_SCALING_ANNULUS] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z:real^3 = lam % (inv lam % z)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN annulus (lam * &1 / &2) (lam * &2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `w:B` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `lam % y:real^3` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_RID];
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `inv lam % y:real^3` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ]]]);;

(* Neck points on one side of a level sphere are in one component of its    *)
(* complement.                                                               *)

let SOULT_NECK_SIDE_COMP = prove
 (`!eps top atlas (g:B->real^3^3) x0 (e:real^3->B) lam y1 y2.
     rfs_neck (top,atlas) g eps x0 e /\ &0 < lam /\
     sphere(vec 0,lam) SUBSET rfs_neck_dom eps /\
     y1 IN rfs_neck_dom eps /\ y2 IN rfs_neck_dom eps /\
     ((norm y1 < lam /\ norm y2 < lam) \/ (lam < norm y1 /\ lam < norm y2))
     ==> connected_component_of
           (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,lam)))) (e y1) (e y2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`] P2AS_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. annulus a b SUBSET rfs_neck_dom eps /\ y1 IN annulus a b /\ y2 IN annulus a b /\
          DISJOINT (annulus a b) (sphere(vec 0:real^3,lam))
          ==> connected_component_of
                (subtopology top (topspace top DIFF IMAGE (e:real^3->B) (sphere(vec 0,lam))))
                (e y1) (e y2)` MATCH_MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[connected_component_of] THEN
    EXISTS_TAC `IMAGE (e:real^3->B) (annulus a b)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN;
                      SCH1_ANNULUS_CONNECTED];
      UNDISCH_TAC `DISJOINT (annulus a b) (sphere(vec 0:real^3,lam))` THEN
      UNDISCH_TAC `annulus a b SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `sphere(vec 0:real^3,lam) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `IMAGE (e:real^3->B) (rfs_neck_dom eps) SUBSET topspace top` THEN
      UNDISCH_TAC `!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps /\
                         (e:real^3->B) y = e z ==> y = z` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom eps = annulus (exp(--inv(sqrt(&2) * eps))) (exp(inv(sqrt(&2) * eps)))
                :real^3->bool` ASSUME_TAC THENL [REWRITE_TAC[rfs_neck_dom]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--inv(sqrt(&2) * eps)) < lam /\ lam < exp(inv(sqrt(&2) * eps))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sphere(vec 0:real^3,lam) SUBSET rfs_neck_dom eps` THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; rfs_neck_dom; annulus; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `lam % basis 1:real^3`) THEN
    REWRITE_TAC[NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MAP_EVERY EXISTS_TAC [`exp(--inv(sqrt(&2) * eps))`; `lam:real`];
    MAP_EVERY EXISTS_TAC [`lam:real`; `exp(inv(sqrt(&2) * eps))`]] THEN
  UNDISCH_TAC `(y1:real^3) IN rfs_neck_dom eps` THEN
  UNDISCH_TAC `(y2:real^3) IN rfs_neck_dom eps` THEN
  ASM_REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_ELIM_THM;
                  IN_SPHERE_0] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Distances: the diameter of a level sphere and its distance to an axis    *)
(* point at another level.                                                   *)

let SOULT_LEVEL_DISTS = prove
 (`!eps top atlas (g:B->real^3^3) x0 (e:real^3->B) t sig.
     hausdorff_space top /\ riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x0 e /\
     eps < &1 /\ abs t < inv eps /\ abs sig < inv eps
     ==> sphere(vec 0,exp(t / sqrt(&2))) SUBSET rfs_neck_dom eps /\
         exp(sig / sqrt(&2)) % basis 1 IN rfs_neck_dom eps /\
         (!w w'. w IN IMAGE (e:real^3->B) (sphere(vec 0,exp(t / sqrt(&2)))) /\
                 w' IN IMAGE (e:real^3->B) (sphere(vec 0,exp(t / sqrt(&2))))
                 ==> mfd_dist (top,atlas) g w w' <=
                     sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas g x0)) * (sqrt(&2) * pi)) /\
         (!w. w IN IMAGE (e:real^3->B) (sphere(vec 0,exp(t / sqrt(&2))))
              ==> sqrt(&1 - eps) * inv(sqrt(mfd_scalar atlas g x0)) *
                  min (abs(t - sig)) (&2 * inv eps - abs t - abs sig)
                  <= mfd_dist (top,atlas) g w ((e:real^3->B)(exp(sig / sqrt(&2)) % basis 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps x0 e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,exp(t / sqrt(&2)))
                           ==> y IN rfs_neck_dom eps /\ apx_sval y = t` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `apx_sval(y:real^3) = t` ASSUME_TAC THENL
     [MATCH_MP_TAC SOULT_SVAL_RADIUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SOULT_RADIUS_IN_NECK THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^3) = exp(t / sqrt(&2))` THEN
    REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `t / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(sig / sqrt(&2)) % basis 1:real^3 IN rfs_neck_dom eps /\
                apx_sval(exp(sig / sqrt(&2)) % basis 1:real^3) = sig` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `apx_sval(exp(sig / sqrt(&2)) % basis 1:real^3) = sig` ASSUME_TAC THENL
     [MATCH_MP_TAC SOULT_SVAL_RADIUS THEN REWRITE_TAC[P2AS_AXIS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SOULT_RADIUS_IN_NECK THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_EXP_NZ; BASIS_NONZERO] THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x0:B`; `e:real^3->B`; `x:real^3`; `x':real^3`]
      APX_NECK_DIST_UPPER) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID];
    REWRITE_TAC[IN_IMAGE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x0:B`; `e:real^3->B`; `x:real^3`;
                   `exp(sig / sqrt(&2)) % basis 1:real^3`] APX_NECK_DIST_LOWER) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The ball of a level sphere (Schoenflies in a big ball): the              *)
(* ball is one side of the level sphere, the complement of the closed ball  *)
(* the other; with the soul p a neck point on one side and a far axis point *)
(* on the other, the ball is the side of p (else SOULT_BALL_NOT_FAR).       *)
(* ------------------------------------------------------------------------- *)

let SOULT_LEVEL_SCHOENFLIES = prove
 (`!eps top atlas (g:B->real^3^3) x0 (e:real^3->B) (b0:real^3->B) t.
     hausdorff_space top /\ connected_space top /\ rfs_neck (top,atlas) g eps x0 e /\
     abs t + &2 < inv eps /\ mfd_ball_chart top atlas b0 /\
     IMAGE (\y. (e:real^3->B)(exp(t / sqrt(&2)) % y)) (annulus (&1 / &2) (&2)) SUBSET
     IMAGE b0 (ball(vec 0,&1))
     ==> ?c. mfd_ball_chart top atlas c /\
             IMAGE c (sphere(vec 0,&1)) = IMAGE (e:real^3->B) (sphere(vec 0,exp(t / sqrt(&2)))) /\
             ((!y. y IN rfs_neck_dom eps /\ norm y < exp(t / sqrt(&2))
                   ==> e y IN IMAGE c (ball(vec 0,&1))) /\
              (!y. y IN rfs_neck_dom eps /\ exp(t / sqrt(&2)) < norm y
                   ==> ~(e y IN IMAGE c (cball(vec 0,&1)))) \/
              (!y. y IN rfs_neck_dom eps /\ exp(t / sqrt(&2)) < norm y
                   ==> e y IN IMAGE c (ball(vec 0,&1))) /\
              (!y. y IN rfs_neck_dom eps /\ norm y < exp(t / sqrt(&2))
                   ==> ~(e y IN IMAGE c (cball(vec 0,&1)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`; `t:real`] SOULT_LEVEL_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`] P2AS_NECK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `lam = exp(t / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `b0:real^3->B`;
                 `\y. (e:real^3->B)(lam % y)`] SOULT_SCHOENFLIES_NECK) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^3->B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the two reference points and the sphere inside the neck *)
  SUBGOAL_THEN `&4 / &5 % basis 1:real^3 IN annulus (&1 / &2) (&2) /\
                &5 / &4 % basis 1:real^3 IN annulus (&1 / &2) (&2) /\
                &4 / &5 % basis 1:real^3 IN annulus (&3 / &4) (&2) /\
                &5 / &4 % basis 1:real^3 IN annulus (&3 / &4) (&2) /\
                &4 / &5 % basis 1:real^3 IN ball(vec 0,&1) /\
                &5 / &4 % basis 1:real^3 IN ball(vec 0,&2) /\
                ~(&5 / &4 % basis 1:real^3 IN cball(vec 0,&1)) /\
                norm(&4 / &5 % basis 1:real^3) = &4 / &5 /\
                norm(&5 / &4 % basis 1:real^3) = &5 / &4` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1 / &2) (&2) ==> lam % y IN rfs_neck_dom eps`
  (LABEL_TAC "LAMD") THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,lam) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y:real^3 = lam % (inv lam % y)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    USE_THEN "LAMD" MATCH_MP_TAC THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam % (&4 / &5 % basis 1):real^3 IN rfs_neck_dom eps /\
                lam % (&5 / &4 % basis 1):real^3 IN rfs_neck_dom eps /\
                norm(lam % (&4 / &5 % basis 1):real^3) < lam /\
                lam < norm(lam % (&5 / &4 % basis 1):real^3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "LAMD" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "LAMD" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* every neck point off the level sphere is in the component of a reference point *)
  SUBGOAL_THEN
   `!y. y IN rfs_neck_dom eps /\ ~(norm y = lam)
        ==> (e:real^3->B) y IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_SPHERE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `y:real^3 = y'` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps /\ (e:real^3->B) y = e z
               ==> y = z`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `sphere(vec 0:real^3,lam) SUBSET rfs_neck_dom eps` THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y y'. y IN rfs_neck_dom eps /\ y' IN rfs_neck_dom eps /\
           ((norm y < lam /\ norm y' < lam) \/ (lam < norm y /\ lam < norm y'))
           ==> ((e:real^3->B) y IN IMAGE (c:real^3->B) (ball(vec 0,&1)) <=>
                e y' IN IMAGE c (ball(vec 0,&1)))` (LABEL_TAC "SIDE") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    (MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`;
                    `(e:real^3->B) y`; `(e:real^3->B) y'`] SOULT_BALL_SIDES) THEN
     ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
       FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
         `!y. y IN rfs_neck_dom eps /\ ~(norm y = lam)
              ==> (e:real^3->B) y IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1))`)
         (concl th))) THEN
       ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
       DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC SOULT_NECK_SIDE_COMP THEN
       MAP_EVERY EXISTS_TAC [`eps:real`; `atlas:((B->bool)#(B->real^3))->bool`;
                             `g:B->real^3^3`; `x0:B`] THEN
       ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN rfs_neck_dom eps /\ ~(norm y = lam) /\
                    ~((e:real^3->B) y IN IMAGE (c:real^3->B) (ball(vec 0,&1)))
                    ==> ~(e y IN IMAGE c (cball(vec 0,&1)))` (LABEL_TAC "CLOSED") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> can (term_match []
      `!y. y IN rfs_neck_dom eps /\ ~(norm y = lam)
           ==> (e:real^3->B) y IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1))`)
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the two Schoenflies alternatives *)
  SUBGOAL_THEN `IMAGE (c:real^3->B) (ball(vec 0,&1)) SUBSET IMAGE c (cball(vec 0,&1))`
  ASSUME_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `~((c:real^3->B)(&5 / &4 % basis 1) IN IMAGE c (cball(vec 0,&1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&5 / &4 % basis 1:real^3 = w` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x y. x IN ball(vec 0:real^3,&2) /\ y IN ball(vec 0,&2) /\ (c:real^3->B) x = c y
               ==> x = y`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(w:real^3) IN cball(vec 0,&1)` THEN
      REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(w:real^3 IN cball(vec 0,&1))` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->B)(&4 / &5 % basis 1) IN IMAGE c (ball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `(c:real^3->B)(&4 / &5 % basis 1) = (e:real^3->B)(lam % (&4 / &5 % basis 1)) /\
                  (c:real^3->B)(&5 / &4 % basis 1) = (e:real^3->B)(lam % (&5 / &4 % basis 1))`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                            ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->B)(lam % (&4 / &5 % basis 1)) IN IMAGE (c:real^3->B) (ball(vec 0,&1)) /\
                  ~((e:real^3->B)(lam % (&5 / &4 % basis 1)) IN IMAGE (c:real^3->B) (ball(vec 0,&1)))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(c:real^3->B)(&4 / &5 % basis 1) = (e:real^3->B)(lam % (&4 / &5 % basis 1))` THEN
      UNDISCH_TAC `(c:real^3->B)(&5 / &4 % basis 1) = (e:real^3->B)(lam % (&5 / &4 % basis 1))` THEN
      UNDISCH_TAC `(c:real^3->B)(&4 / &5 % basis 1) IN IMAGE c (ball(vec 0,&1))` THEN
      UNDISCH_TAC `~((c:real^3->B)(&5 / &4 % basis 1) IN IMAGE c (cball(vec 0,&1)))` THEN
      UNDISCH_TAC `IMAGE (c:real^3->B) (ball(vec 0,&1)) SUBSET IMAGE c (cball(vec 0,&1))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [REMOVE_THEN "SIDE" (MP_TAC o SPECL [`y:real^3`; `lam % (&4 / &5 % basis 1):real^3`]) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "CLOSED" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `lam < norm(y:real^3)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "SIDE" (MP_TAC o SPECL [`y:real^3`; `lam % (&5 / &4 % basis 1):real^3`]) THEN
      ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN
    SUBGOAL_THEN `(c:real^3->B)(&4 / &5 % basis 1) = (e:real^3->B)(lam % (&5 / &4 % basis 1)) /\
                  (c:real^3->B)(&5 / &4 % basis 1) = (e:real^3->B)(lam % (&4 / &5 % basis 1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
          `&4 / &5 % basis 1:real^3 IN annulus (&3 / &4) (&2)`)]);
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
          `&5 / &4 % basis 1:real^3 IN annulus (&3 / &4) (&2)`)])] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->B)(lam % (&5 / &4 % basis 1)) IN IMAGE (c:real^3->B) (ball(vec 0,&1)) /\
                  ~((e:real^3->B)(lam % (&4 / &5 % basis 1)) IN IMAGE (c:real^3->B) (ball(vec 0,&1)))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(c:real^3->B)(&4 / &5 % basis 1) = (e:real^3->B)(lam % (&5 / &4 % basis 1))` THEN
      UNDISCH_TAC `(c:real^3->B)(&5 / &4 % basis 1) = (e:real^3->B)(lam % (&4 / &5 % basis 1))` THEN
      UNDISCH_TAC `(c:real^3->B)(&4 / &5 % basis 1) IN IMAGE c (ball(vec 0,&1))` THEN
      UNDISCH_TAC `~((c:real^3->B)(&5 / &4 % basis 1) IN IMAGE c (cball(vec 0,&1)))` THEN
      UNDISCH_TAC `IMAGE (c:real^3->B) (ball(vec 0,&1)) SUBSET IMAGE c (cball(vec 0,&1))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [REMOVE_THEN "SIDE" (MP_TAC o SPECL [`y:real^3`; `lam % (&5 / &4 % basis 1):real^3`]) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "CLOSED" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `norm(y:real^3) < lam` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "SIDE" (MP_TAC o SPECL [`y:real^3`; `lam % (&4 / &5 % basis 1):real^3`]) THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The side of the soul.  For a level sphere at level t, the                *)
(* soul p = e(yp) on one side and the axis point at level sig on the other, *)
(* with the level gap at least 1/(6 eps): the ball of the level sphere is   *)
(* the side of p.                                                            *)
(* ------------------------------------------------------------------------- *)

(* A point z inside a ball chart beats its boundary sphere: if the sphere   *)
(* has diameter at most sqrt(1 + eps) h sqrt(2) pi and is at distance at    *)
(* least sqrt(1 - eps) h D from z, with D >= 1/(6 eps), then the soul p is  *)
(* not outside the closed ball.                                              *)

let SOULT_DEEP_BEATS = prove
 (`!eps top atlas (g:B->real^3^3) p (c:real^3->B) z h D.
     &0 < eps /\ eps <= &1 / &1024 /\ &0 < h /\ inv(&6 * eps) <= D /\
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     mfd_ball_chart top atlas c /\
     (!w w'. w IN IMAGE c (sphere(vec 0,&1)) /\ w' IN IMAGE c (sphere(vec 0,&1))
             ==> mfd_dist (top,atlas) g w w' <= sqrt(&1 + eps) * h * (sqrt(&2) * pi)) /\
     (!w. w IN IMAGE c (sphere(vec 0,&1))
          ==> sqrt(&1 - eps) * h * D <= mfd_dist (top,atlas) g w z) /\
     z IN IMAGE c (ball(vec 0,&1)) /\ ~(p IN IMAGE c (cball(vec 0,&1)))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`]
    SOULT_BALL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (c:real^3->B) (sphere(vec 0,&1)) SUBSET topspace top /\
                IMAGE (c:real^3->B) (ball(vec 0,&1)) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:B) IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1)) /\
                (p:B) IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1)) /\
                ~(p IN IMAGE c (ball(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(z:B) IN IMAGE (c:real^3->B) (ball(vec 0,&1))`;
      `~((p:B) IN IMAGE (c:real^3->B) (cball(vec 0,&1)))`;
      `(p:B) IN topspace top`;
      `IMAGE (c:real^3->B) (cball(vec 0,&1)) =
       IMAGE c (ball(vec 0,&1)) UNION IMAGE c (sphere(vec 0,&1))`;
      `DISJOINT (IMAGE (c:real^3->B) (ball(vec 0,&1))) (IMAGE c (sphere(vec 0,&1)))`;
      `IMAGE (c:real^3->B) (ball(vec 0,&1)) SUBSET topspace top`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) <= &2 /\ &1 / &2 <= sqrt(&1 - eps) /\ &170 <= D`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&6 * eps)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&6 * &1 / &1024)` THEN
      CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&1 + eps) * h * (sqrt(&2) * pi) < sqrt(&1 - eps) * h * D`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&1 + eps) * h * (sqrt(&2) * pi) = h * (sqrt(&1 + eps) * (sqrt(&2) * pi)) /\
                  sqrt(&1 - eps) * h * D = h * (sqrt(&1 - eps) * D)`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * (sqrt(&2) * pi)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 / &2 * &170` THEN CONJ_TAC THENL
     [MP_TAC P2AS_SQRT2_PI THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SOULT_BALL_NOT_FAR THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `g:B->real^3^3`; `p:B`; `c:real^3->B`; `z:B`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `IMAGE (c:real^3->B) (sphere(vec 0,&1))`; `z:B`; `z:B`;
                 `sqrt(&1 + eps) * h * (sqrt(&2) * pi)`; `sqrt(&1 - eps) * h * D`]
    P2AS_FAR_BEATS_S) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL; TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `(z:B) IN topspace top DIFF IMAGE (c:real^3->B) (sphere(vec 0,&1))` THEN
    SET_TAC[];
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c:real^3->B`;
                   `z:B`; `p:B`] SOULT_BALL_SIDES) THEN
    ASM_REWRITE_TAC[]]);;

let SOULT_LEVEL_BALL = prove
 (`!eps top atlas (g:B->real^3^3) p x0 (e:real^3->B) (b0:real^3->B) t sig yp.
     &0 < eps /\ eps <= &1 / &1024 /\
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     rfs_neck (top,atlas) g eps x0 e /\
     abs t + &2 < inv eps /\ abs sig < inv eps /\
     inv(&6 * eps) <= min (abs(t - sig)) (&2 * inv eps - abs t - abs sig) /\
     mfd_ball_chart top atlas b0 /\
     IMAGE (\y. (e:real^3->B)(exp(t / sqrt(&2)) % y)) (annulus (&1 / &2) (&2)) SUBSET
     IMAGE b0 (ball(vec 0,&1)) /\
     yp IN rfs_neck_dom eps /\ e yp = p /\
     ((norm yp < exp(t / sqrt(&2)) /\ t < sig) \/ (exp(t / sqrt(&2)) < norm yp /\ sig < t))
     ==> ?c. mfd_ball_chart top atlas c /\
             IMAGE c (sphere(vec 0,&1)) = IMAGE (e:real^3->B) (sphere(vec 0,exp(t / sqrt(&2)))) /\
             (!y. y IN rfs_neck_dom eps /\ ~(norm y = exp(t / sqrt(&2))) /\
                  (norm y < exp(t / sqrt(&2)) <=> norm yp < exp(t / sqrt(&2)))
                  ==> e y IN IMAGE c (ball(vec 0,&1))) /\
             (!y. y IN rfs_neck_dom eps /\ ~(norm y = exp(t / sqrt(&2))) /\
                  ~(norm y < exp(t / sqrt(&2)) <=> norm yp < exp(t / sqrt(&2)))
                  ==> ~(e y IN IMAGE c (cball(vec 0,&1))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`; `b0:real^3->B`; `t:real`]
    SOULT_LEVEL_SCHOENFLIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^3->B` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `lam = exp(t / sqrt(&2))` THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `x0:B`; `e:real^3->B`] P2AS_NECK_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the far axis point zs and its side *)
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`; `t:real`; `sig:real`] SOULT_LEVEL_DISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `zs = exp(sig / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `norm(zs:real^3) = exp(sig / sqrt(&2))` ASSUME_TAC THENL
   [EXPAND_TAC "zs" THEN REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    REWRITE_TAC[real_abs; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t < sig ==> lam < norm(zs:real^3)) /\ (sig < t ==> norm(zs:real^3) < lam)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ];
    ALL_TAC] THEN
  (* the soul and the far point are on opposite sides *)
  SUBGOAL_THEN `~(norm(zs:real^3) = lam) /\ ~(norm(yp:real^3) = lam) /\
                ~(norm(zs:real^3) < lam <=> norm(yp:real^3) < lam)` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `t < sig`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the far point in the ball and the soul outside the closed ball is absurd *)
  SUBGOAL_THEN
   `(e:real^3->B) zs IN IMAGE (c:real^3->B) (ball(vec 0,&1)) /\
    ~(p IN IMAGE c (cball(vec 0,&1))) ==> F`
  (LABEL_TAC "DEEP") THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `p:B`; `c:real^3->B`; `(e:real^3->B) zs`;
                   `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x0))`;
                   `min (abs(t - sig)) (&2 * inv eps - abs t - abs sig)`] SOULT_DEEP_BEATS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `rfs_neck_dom eps`)) (concl th))) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "S1") (LABEL_TAC "S2")) THEN
  ASM_CASES_TAC `norm(yp:real^3) < lam` THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [USE_THEN "S1" MATCH_MP_TAC; USE_THEN "S2" MATCH_MP_TAC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `y:real^3` (concl th)))) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `F ==> p`) THEN USE_THEN "DEEP" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "S1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:real^3->B) yp = p`)) THEN
      USE_THEN "S2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN USE_THEN "DEEP" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "S1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:real^3->B) yp = p`)) THEN
      USE_THEN "S2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [USE_THEN "S1" MATCH_MP_TAC; USE_THEN "S2" MATCH_MP_TAC] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `y:real^3` (concl th)))) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Part 1.  If the soul p were in the middle two thirds of an               *)
(* eps-neck, the balls of the level spheres one unit above and below p      *)
(* would both be on the side of p (SOULT_LEVEL_BALL), the manifold would be *)
(* the union of the two closed balls, hence compact, and d_p would have a   *)
(* global maximum away from p, against regularity.                          *)
(* ------------------------------------------------------------------------- *)

let SOULT_TWO_BALLS = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (c1:real^3->B) c2 z.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     mfd_ball_chart top atlas c1 /\ mfd_ball_chart top atlas c2 /\
     IMAGE c2 (sphere(vec 0,&1)) SUBSET IMAGE c1 (ball(vec 0,&1)) /\
     z IN topspace top /\ ~(z IN IMAGE c1 (cball(vec 0,&1))) /\
     z IN IMAGE c2 (ball(vec 0,&1))
     ==> topspace top = IMAGE c1 (cball(vec 0,&1)) UNION IMAGE c2 (cball(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c1:real^3->B`]
    SOULT_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c2:real^3->B`]
    SOULT_BALL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c1:real^3->B`]
    SOULT_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (c1:real^3->B) (cball(vec 0,&1)) SUBSET topspace top /\
                IMAGE (c2:real^3->B) (cball(vec 0,&1)) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IN_SUBSET_TOPSPACE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c2:real^3->B`;
                 `topspace top DIFF IMAGE (c1:real^3->B) (cball(vec 0,&1))`]
    SOULT_CONNECTED_IN_BALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC
       [`IMAGE (c2:real^3->B) (sphere(vec 0,&1)) SUBSET IMAGE (c1:real^3->B) (ball(vec 0,&1))`;
        `IMAGE (c1:real^3->B) (cball(vec 0,&1)) =
         IMAGE c1 (ball(vec 0,&1)) UNION IMAGE c1 (sphere(vec 0,&1))`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(z:B) IN topspace top`; `~((z:B) IN IMAGE (c1:real^3->B) (cball(vec 0,&1)))`;
        `(z:B) IN IMAGE (c2:real^3->B) (ball(vec 0,&1))`] THEN
      SET_TAC[]];
    DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`topspace top DIFF IMAGE (c1:real^3->B) (cball(vec 0,&1)) SUBSET
     IMAGE (c2:real^3->B) (ball(vec 0,&1))`;
    `IMAGE (c1:real^3->B) (cball(vec 0,&1)) SUBSET topspace top`;
    `IMAGE (c2:real^3->B) (cball(vec 0,&1)) SUBSET topspace top`;
    `IMAGE (c2:real^3->B) (cball(vec 0,&1)) =
     IMAGE c2 (ball(vec 0,&1)) UNION IMAGE c2 (sphere(vec 0,&1))`] THEN
  SET_TAC[]);;

(* A compact manifold has no soul (with another point). *)

let SOULT_COMPACT_NO_SOUL = prove
 (`!top atlas (g:B->real^3^3) p q.
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     compact_in top (topspace top) /\ q IN topspace top /\ ~(q = p)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`] MFD_DIST_CONTINUOUS_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\y. mfd_dist (top,atlas) (g:B->real^3^3) p y) (topspace top)`
               REAL_COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_compact_def; IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:B topology` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(p:B) IN topspace top` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:B` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SUP"))) THEN
  SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:B->real^3^3) p q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p:B`; `q:B`] P2AS_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(xs:B = p)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    REMOVE_THEN "SUP" (MP_TAC o SPEC `q:B`) THEN
    ASM_SIMP_TAC[MFD_DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `topspace top:B->bool`; `xs:B`] P2AS_LOCAL_MAX_NOT_REGULAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:B` THEN STRIP_TAC THEN USE_THEN "SUP" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Part 1. *)

let SOULT_PART1 = prove
 (`!eps top atlas (g:B->real^3^3) p x0 (e:real^3->B).
     &0 < eps /\ eps <= &1 / &1024 /\
     hausdorff_space top /\ connected_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\
     (!x. x IN topspace top /\ ~(x = p) ==> p2b_dist_regular (top,atlas) g p x) /\
     rfs_neck (top,atlas) g eps x0 e
     ==> ~(p IN IMAGE e (rfs_neck_dom (&3 / &2 * eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `yp:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  MP_TAC(SPECL [`&3 / &2 * eps`; `yp:real^3`] APX_SVAL_NECK_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `x0:B`; `e:real^3->B`] P2AS_NECK_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `sp = apx_sval(yp:real^3)` THEN
  ABBREV_TAC `T6 = inv(&6 * eps)` THEN
  SUBGOAL_THEN `&1024 <= inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&1 / &1024)` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs sp < &2 / &3 * inv eps /\ &6 * T6 = inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `abs sp < inv(&3 / &2 * eps)` THEN REWRITE_TAC[REAL_INV_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      EXPAND_TAC "T6" THEN REWRITE_TAC[REAL_INV_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(yp:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MATCH_MP_TAC SOULT_RADIUS_IN_NECK THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the far axis point and the level inequalities *)
  ABBREV_TAC `zs = exp((sp + &1 + T6) / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `exp((sp - &1) / sqrt(&2)) < exp((sp + &1) / sqrt(&2)) /\
                exp((sp + &1) / sqrt(&2)) < norm(zs:real^3) /\
                norm(yp:real^3) < exp((sp + &1) / sqrt(&2)) /\
                exp((sp - &1) / sqrt(&2)) < norm(yp:real^3)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(yp:real^3) = exp(sp / sqrt(&2)) /\
                  norm(zs:real^3) = exp((sp + &1 + T6) / sqrt(&2))` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "sp" THEN REWRITE_TAC[apx_sval] THEN
        ASM_SIMP_TAC[REAL_FIELD `&0 < s ==> (s * x) / s = x`; EXP_LOG; NORM_POS_LT];
        EXPAND_TAC "zs" THEN REWRITE_TAC[NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
        REWRITE_TAC[real_abs; REAL_EXP_POS_LE]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(zs:real^3) IN rfs_neck_dom eps /\
                sphere(vec 0:real^3,exp((sp - &1) / sqrt(&2))) SUBSET rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `x0:B`; `e:real^3->B`; `sp - &1`; `sp + &1 + T6`]
      SOULT_LEVEL_DISTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->B) zs IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->B) (rfs_neck_dom eps) SUBSET topspace top` THEN
    UNDISCH_TAC `(zs:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the big ball containing both level collars *)
  ABBREV_TAC `m = &2 / &3 * inv eps + &3` THEN
  SUBGOAL_THEN `&0 < m /\ m < inv eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `m:real`] APX_SUBSLAB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e:real^3->B)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:B->real^3^3) eps x0 e` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`;
                 `IMAGE (e:real^3->B) (cball(vec 0,exp(m / sqrt(&2))) DIFF
                                       ball(vec 0,exp(--m / sqrt(&2))))`]
    SOULB_BIG_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:real^3->B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. abs t <= abs sp + &1
        ==> IMAGE (\y. (e:real^3->B)(exp(t / sqrt(&2)) % y)) (annulus (&1 / &2) (&2)) SUBSET
            IMAGE (b0:real^3->B) (ball(vec 0,&1))` (LABEL_TAC "COLLAR") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e:real^3->B) (cball(vec 0,exp(m / sqrt(&2))) DIFF
                                     ball(vec 0,exp(--m / sqrt(&2))))` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `x0:B`; `e:real^3->B`; `t:real`] SOULT_LEVEL_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`eps:real`; `exp(t / sqrt(&2)) % y:real^3`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!v:real^3. ~(v = vec 0) /\ abs(apx_sval v) <= m ==> v IN S`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\y. (e:real^3->B)(exp((sp + &1) / sqrt(&2)) % y)) (annulus (&1 / &2) (&2)) SUBSET
    IMAGE (b0:real^3->B) (ball(vec 0,&1)) /\
    IMAGE (\y. (e:real^3->B)(exp((sp - &1) / sqrt(&2)) % y)) (annulus (&1 / &2) (&2)) SUBSET
    IMAGE (b0:real^3->B) (ball(vec 0,&1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "COLLAR" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the two level balls *)
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `p:B`; `x0:B`; `e:real^3->B`; `b0:real^3->B`;
                 `sp + &1`; `sp + &1 + T6`; `yp:real^3`] SOULT_LEVEL_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^3->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "C1IN") (LABEL_TAC "C1OUT"))))) THEN
  MP_TAC(ISPECL [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `p:B`; `x0:B`; `e:real^3->B`; `b0:real^3->B`;
                 `sp - &1`; `sp - &1 - T6`; `yp:real^3`] SOULT_LEVEL_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^3->B` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "C2IN") (K ALL_TAC))))) THEN
  (* the manifold is the union of the two closed balls *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c1:real^3->B`;
                 `c2:real^3->B`; `(e:real^3->B) zs`] SOULT_TWO_BALLS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "C1IN" MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `sphere(vec 0:real^3,exp((sp - &1) / sqrt(&2))) SUBSET rfs_neck_dom eps` THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      USE_THEN "C1OUT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "C2IN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `compact_in top (IMAGE (c1:real^3->B) (cball(vec 0,&1))) /\
                compact_in top (IMAGE (c2:real^3->B) (cball(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c1:real^3->B`]
        SOULT_BALL_FACTS);
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `c2:real^3->B`]
        SOULT_BALL_FACTS)] THEN
    ANTS_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2);
    ALL_TAC] THEN
  MATCH_MP_TAC SOULT_COMPACT_NO_SOUL THEN
  MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                        `g:B->real^3^3`; `p:B`; `(e:real^3->B) zs`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `topspace top:B->bool`)) THEN
    MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `zs:real^3 = yp` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps /\ (e:real^3->B) y = e z
               ==> y = z`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem SOULT_SOUL_TOPOLOGY |- !w.                              *)
(* P2B_SOUL_TOPOLOGY_STATEMENT w, with eps0 = min eps2 (1/1024), eps2 from  *)
(* P2AS_NECK_METRIC (the central sphere has diameter at most 7 h and the    *)
(* axis points at levels +-1/(2 eps) are at distance at least h/(4 eps)).  *)
(* ------------------------------------------------------------------------- *)

let SOULT_SOUL_TOPOLOGY = prove
 (`!w:B->bool. P2B_SOUL_TOPOLOGY_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_SOUL_TOPOLOGY_STATEMENT] THEN
  MP_TAC(INST_TYPE [`:B`,`:A`] P2AS_NECK_METRIC) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NM"))) THEN
  EXISTS_TAC `min eps2 (&1 / &1024)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`eps:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:B->real^3^3`; `p:B`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:B`; `e:real^3->B`] THEN DISCH_TAC THEN
    MATCH_MP_TAC SOULT_PART1 THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `z:B`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`z:B`; `e:real^3->B`] THEN STRIP_TAC THEN
    USE_THEN "NM" (MP_TAC o SPECL [`eps:real`; `top:B topology`;
                                   `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                                   `z:B`; `e:real^3->B`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
    MATCH_MP_TAC SOULT_PART2 THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `g:B->real^3^3`; `z:B`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `u:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:B`; `inv(&2 * sqrt(&2) * eps)`] o check (fun th ->
        can (find_term ((=) `inv(&4 * eps)`)) (concl th))) THEN
      ASM_REWRITE_TAC[]]]);;

